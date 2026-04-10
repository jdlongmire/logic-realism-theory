"""Security hardening for LRT chatbot.

Provides input sanitization, prompt injection detection, rate limiting,
and output filtering. All user input passes through this module before
reaching the LLM.
"""

import json
import os
import re
import time
import logging
from collections import defaultdict
from datetime import datetime, date
from pathlib import Path

logger = logging.getLogger(__name__)

# --- Configuration ---

MAX_QUERY_LENGTH = 2000  # characters
MAX_HISTORY_TURNS = 20
RATE_LIMIT_WINDOW = 60   # seconds
RATE_LIMIT_MAX = 15       # queries per window per session

# Daily query caps
DAILY_GLOBAL_CAP = 100    # total queries per day across all sessions
DAILY_SESSION_CAP = 50    # queries per session per day

# Audit log location
AUDIT_LOG_DIR = Path(__file__).parent / 'logs'

# --- Prompt injection detection ---

# Patterns that indicate an attempt to override system instructions.
# Each is (compiled regex, description) for logging.
_INJECTION_PATTERNS = [
    # Direct instruction override attempts
    (re.compile(r'ignore\s+(all\s+)?(previous|prior|above|earlier)\s+(instructions?|prompts?|rules?|context)',
                re.IGNORECASE), 'instruction override'),
    (re.compile(r'disregard\s+(all\s+)?(previous|prior|above|earlier)',
                re.IGNORECASE), 'instruction override'),
    (re.compile(r'forget\s+(all\s+)?(previous|your)\s+(instructions?|rules?|prompts?)',
                re.IGNORECASE), 'instruction override'),

    # Role reassignment
    (re.compile(r'you\s+are\s+now\s+a', re.IGNORECASE), 'role reassignment'),
    (re.compile(r'pretend\s+(you\s+are|to\s+be)\s+a', re.IGNORECASE), 'role reassignment'),
    (re.compile(r'act\s+as\s+(if\s+you\s+are\s+)?a\s+different', re.IGNORECASE), 'role reassignment'),
    (re.compile(r'switch\s+to\s+.{0,20}\s+mode', re.IGNORECASE), 'role reassignment'),
    (re.compile(r'enter\s+.{0,20}\s+mode', re.IGNORECASE), 'role reassignment'),

    # System prompt extraction
    (re.compile(r'(print|show|display|reveal|output|repeat|echo)\s+(your\s+)?(system\s+)?(prompt|instructions?|rules?)',
                re.IGNORECASE), 'prompt extraction'),
    (re.compile(r'what\s+(are|is)\s+your\s+(system\s+)?(prompt|instructions?|rules?)',
                re.IGNORECASE), 'prompt extraction'),

    # Delimiter injection (trying to close the context block and inject new instructions)
    (re.compile(r'===\s*(SYSTEM|INSTRUCTIONS?|NEW\s+RULES?|OVERRIDE)', re.IGNORECASE), 'delimiter injection'),
    (re.compile(r'---\s*(SYSTEM|INSTRUCTIONS?|NEW\s+RULES?|BEGIN)', re.IGNORECASE), 'delimiter injection'),
    (re.compile(r'<\s*/?\s*(system|instruction|prompt|rule)', re.IGNORECASE), 'tag injection'),

    # Code execution / tool use attempts
    (re.compile(r'(run|execute|eval|call)\s+(this\s+)?(code|command|script|function|tool)',
                re.IGNORECASE), 'code execution'),
    (re.compile(r'```\s*(python|bash|sh|javascript|js)\s*\n.*?(import|exec|eval|os\.|subprocess)',
                re.IGNORECASE | re.DOTALL), 'code injection'),

    # Data exfiltration (narrow: command + target, not bare keywords)
    (re.compile(r'(curl|wget)\s+https?://', re.IGNORECASE), 'data exfiltration'),
    (re.compile(r'(send|post|exfiltrate|leak)\s+.{0,30}(api[_\s]?key|password|secret|credential|\.env)',
                re.IGNORECASE), 'data exfiltration'),

    # Jailbreak patterns
    (re.compile(r'(DAN|do\s+anything\s+now|jailbreak|bypass\s+safety)', re.IGNORECASE), 'jailbreak'),
    (re.compile(r'(hypothetically|in\s+theory|for\s+educational\s+purposes).{0,30}(ignore|override|bypass)',
                re.IGNORECASE), 'hedged jailbreak'),
]

# Strings that should never appear in output (case-insensitive check)
_OUTPUT_BLOCKLIST = [
    'GEMINI_API_KEY',
    'api_key',
    'api key',
    'password',
    'secret',
    '.env',
    'GMAIL_APP_PASSWORD',
]


# --- Rate limiter ---

class RateLimiter:
    """Simple in-memory per-session rate limiter."""

    def __init__(self, window: int = RATE_LIMIT_WINDOW,
                 max_requests: int = RATE_LIMIT_MAX):
        self.window = window
        self.max_requests = max_requests
        self._requests: dict[str, list[float]] = defaultdict(list)

    def check(self, session_id: str) -> tuple[bool, str]:
        """Check if request is allowed. Returns (allowed, message)."""
        now = time.time()
        # Prune old entries
        self._requests[session_id] = [
            t for t in self._requests[session_id]
            if now - t < self.window
        ]

        if len(self._requests[session_id]) >= self.max_requests:
            wait = int(self.window - (now - self._requests[session_id][0])) + 1
            return False, (f'Rate limit reached ({self.max_requests} queries per '
                          f'{self.window}s). Please wait {wait} seconds.')

        self._requests[session_id].append(now)
        return True, ''

    def cleanup(self):
        """Remove stale sessions."""
        now = time.time()
        stale = [sid for sid, times in self._requests.items()
                 if all(now - t > self.window * 10 for t in times)]
        for sid in stale:
            del self._requests[sid]


# Global rate limiter instance
rate_limiter = RateLimiter()


# --- Daily quota tracker (persists to disk) ---

class DailyQuotaTracker:
    """Tracks daily query counts per session and globally.

    State persists to a JSON file so quotas survive restarts.
    """

    def __init__(self, state_file: Path | None = None,
                 global_cap: int = DAILY_GLOBAL_CAP,
                 session_cap: int = DAILY_SESSION_CAP):
        self.global_cap = global_cap
        self.session_cap = session_cap
        self._state_file = state_file or (AUDIT_LOG_DIR / 'daily_quota.json')
        self._state_file.parent.mkdir(parents=True, exist_ok=True)
        self._load()

    def _load(self):
        """Load state from disk, resetting if date has changed."""
        try:
            if self._state_file.exists():
                data = json.loads(self._state_file.read_text())
                if data.get('date') == str(date.today()):
                    self._global_count = data.get('global', 0)
                    self._session_counts = data.get('sessions', {})
                    return
        except (json.JSONDecodeError, KeyError):
            pass
        # New day or corrupt file — reset
        self._global_count = 0
        self._session_counts: dict[str, int] = {}

    def _save(self):
        """Persist current state to disk."""
        try:
            self._state_file.write_text(json.dumps({
                'date': str(date.today()),
                'global': self._global_count,
                'sessions': self._session_counts,
            }))
        except OSError as e:
            logger.error('Failed to persist quota state: %s', e)

    def check(self, session_id: str) -> tuple[bool, str]:
        """Check if query is within daily caps. Returns (allowed, message)."""
        # Reload in case date rolled over
        today = str(date.today())
        try:
            if self._state_file.exists():
                data = json.loads(self._state_file.read_text())
                if data.get('date') != today:
                    self._global_count = 0
                    self._session_counts = {}
        except (json.JSONDecodeError, OSError):
            pass

        if self._global_count >= self.global_cap:
            return False, ('Daily capacity has been reached. '
                          'Please try again tomorrow.')

        session_count = self._session_counts.get(session_id, 0)
        if session_count >= self.session_cap:
            return False, (f'You\'ve reached the daily limit of {self.session_cap} queries. '
                          'Please try again tomorrow.')

        return True, ''

    def record(self, session_id: str):
        """Record a successful query."""
        self._global_count += 1
        self._session_counts[session_id] = self._session_counts.get(session_id, 0) + 1
        self._save()

    @property
    def global_count(self) -> int:
        return self._global_count


# Global quota tracker instance
daily_quota = DailyQuotaTracker()


# --- Persistent audit logger ---

class AuditLogger:
    """Append-only security audit log.

    Writes one JSON object per line to a date-stamped log file.
    """

    def __init__(self, log_dir: Path | None = None):
        self._log_dir = log_dir or AUDIT_LOG_DIR
        self._log_dir.mkdir(parents=True, exist_ok=True)

    def _log_file(self) -> Path:
        return self._log_dir / f'audit_{date.today().isoformat()}.jsonl'

    def log(self, event_type: str, session_id: str, **kwargs):
        """Write an audit event."""
        entry = {
            'ts': datetime.utcnow().isoformat() + 'Z',
            'event': event_type,
            'session': session_id,
            **kwargs,
        }
        try:
            with open(self._log_file(), 'a') as f:
                f.write(json.dumps(entry) + '\n')
        except OSError as e:
            logger.error('Audit log write failed: %s', e)


# Global audit logger instance
audit_log = AuditLogger()


# --- Input sanitization ---

def sanitize_input(query: str) -> tuple[str, list[str]]:
    """Sanitize user input. Returns (cleaned_query, list_of_warnings).

    Warnings are logged but not shown to the user (to avoid
    teaching attackers what was detected).
    """
    warnings = []

    # Length check
    if len(query) > MAX_QUERY_LENGTH:
        query = query[:MAX_QUERY_LENGTH]
        warnings.append(f'Query truncated to {MAX_QUERY_LENGTH} characters')

    # Strip null bytes and control characters (except newlines)
    cleaned = re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]', '', query)
    if cleaned != query:
        warnings.append('Control characters stripped')
        query = cleaned

    return query, warnings


def detect_injection(query: str) -> tuple[bool, str | None]:
    """Check for prompt injection patterns.

    Returns (is_suspicious, pattern_type).
    Does NOT block by default — the caller decides policy.
    """
    for pattern, description in _INJECTION_PATTERNS:
        if pattern.search(query):
            logger.warning('Injection attempt detected: %s | query: %s',
                          description, query[:200])
            return True, description

    return False, None


# --- Output filtering ---

def filter_output(response: str) -> str:
    """Filter LLM output to prevent information leakage."""
    filtered = response

    # Check for blocklisted strings
    for blocked in _OUTPUT_BLOCKLIST:
        if blocked.lower() in filtered.lower():
            # Replace with redaction
            pattern = re.compile(re.escape(blocked), re.IGNORECASE)
            filtered = pattern.sub('[REDACTED]', filtered)
            logger.warning('Output contained blocklisted string: %s', blocked)

    return filtered


def sanitize_error(error: Exception) -> str:
    """Return a safe error message that doesn't leak internals."""
    # Log the real error
    logger.error('Chat error: %s', str(error), exc_info=True)

    # Provide helpful message for known transient errors
    err_str = str(error)
    if '503' in err_str or 'UNAVAILABLE' in err_str or '429' in err_str:
        return ('The language model is temporarily unavailable due to high demand. '
                'Please try again in a moment.')

    # Return generic message for unknown errors
    return ('I encountered an error processing your question. '
            'Please try rephrasing or ask a different question about LRT.')
