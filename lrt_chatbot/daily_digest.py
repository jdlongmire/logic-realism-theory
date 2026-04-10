#!/usr/bin/env python3
"""LRT Daily Digest — collects chatbot usage, git activity, issues, and Lean status.

Run via cron at 7 AM:
  0 7 * * * cd /media/jdlongmire/Macro-Drive-2TB/GitHub_Repos/logic-realism-theory/lrt_chatbot && python3 daily_digest.py

Sends summary email to JD via SMTP.
"""

import json
import smtplib
import subprocess
import sys
from datetime import datetime, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path

# --- Config ---
REPO_ROOT = Path(__file__).parent.parent
CHATBOT_DIR = Path(__file__).parent
LOGS_DIR = CHATBOT_DIR / 'logs'
LEAN_DIR = REPO_ROOT / 'formalization'

RECIPIENT = 'longmire.jd@gmail.com'
SENDER = 'thinxai.jdl@gmail.com'
SMTP_HOST = 'smtp.gmail.com'
SMTP_PORT = 587

# ThinxS .env has the working app password
THINXS_ENV = Path('/media/jdlongmire/Macro-Drive-2TB/GitHub_Repos/ThinxS/.env')


def get_app_password() -> str:
    """Read Gmail app password directly from ThinxS .env (no dotenv)."""
    for line in THINXS_ENV.read_text().splitlines():
        line = line.strip()
        if line.startswith('GMAIL_APP_PASSWORD='):
            val = line.split('=', 1)[1].strip()
            # Strip quotes if present
            if val.startswith(("'", '"')) and val.endswith(val[0]):
                val = val[1:-1]
            return val
    raise RuntimeError('GMAIL_APP_PASSWORD not found in ThinxS .env')


def get_yesterday() -> str:
    """Return yesterday's date as YYYY-MM-DD."""
    return (datetime.now() - timedelta(days=1)).strftime('%Y-%m-%d')


def chatbot_summary(date: str) -> dict:
    """Parse audit log for the given date."""
    log_file = LOGS_DIR / f'audit_{date}.jsonl'
    if not log_file.exists():
        return {'queries': 0, 'sessions': set(), 'injections_blocked': 0, 'modes': {}, 'sample_queries': []}

    queries = 0
    sessions = set()
    injections = 0
    modes = {}

    for line in log_file.read_text().splitlines():
        if not line.strip():
            continue
        entry = json.loads(line)
        event = entry.get('event', '')

        if event == 'query':
            queries += 1
            sessions.add(entry.get('session', 'unknown'))
            mode = entry.get('mode', 'unknown')
            modes[mode] = modes.get(mode, 0) + 1
        elif event == 'injection_blocked':
            injections += 1

    return {
        'queries': queries,
        'sessions': sessions,
        'injections_blocked': injections,
        'modes': modes,
    }


def git_activity(date: str) -> list[str]:
    """Get git commits from the given date."""
    try:
        result = subprocess.run(
            ['git', 'log', f'--since={date} 00:00', f'--until={date} 23:59:59',
             '--pretty=format:%h %s (%an)', '--no-merges'],
            capture_output=True, text=True, cwd=REPO_ROOT, timeout=10
        )
        commits = [l for l in result.stdout.strip().splitlines() if l]
        return commits
    except Exception as e:
        return [f'Error fetching git log: {e}']


def github_issues() -> list[str]:
    """Get open GitHub issues."""
    try:
        result = subprocess.run(
            ['gh', 'issue', 'list', '--repo', 'jdlongmire/logic-realism-theory',
             '--state', 'open', '--limit', '10', '--json', 'number,title,labels'],
            capture_output=True, text=True, timeout=15
        )
        if result.returncode != 0:
            return [f'gh error: {result.stderr.strip()}']
        issues = json.loads(result.stdout)
        lines = []
        for i in issues:
            labels = ', '.join(l['name'] for l in i.get('labels', []))
            label_str = f' [{labels}]' if labels else ''
            lines.append(f"#{i['number']}: {i['title']}{label_str}")
        return lines if lines else ['No open issues']
    except Exception as e:
        return [f'Error fetching issues: {e}']


def lean_status() -> dict:
    """Check Lean axiom/sorry counts."""
    lean_src = LEAN_DIR / 'LrtFormalization'
    if not lean_src.exists():
        return {'axioms': '?', 'sorries': '?', 'build': 'unknown'}

    try:
        # Count axioms
        ax_result = subprocess.run(
            ['grep', '-rh', '^axiom', str(lean_src), '--include=*.lean'],
            capture_output=True, text=True, timeout=10
        )
        axiom_count = len([l for l in ax_result.stdout.splitlines() if l.strip()])

        # Count sorries
        sorry_result = subprocess.run(
            ['grep', '-r', 'sorry', str(lean_src), '--include=*.lean'],
            capture_output=True, text=True, timeout=10
        )
        sorry_lines = [l for l in sorry_result.stdout.splitlines()
                       if 'sorry' in l and 'no sorry' not in l.lower()]
        sorry_count = len(sorry_lines)

        return {'axioms': axiom_count, 'sorries': sorry_count}
    except Exception as e:
        return {'axioms': '?', 'sorries': '?', 'error': str(e)}


def build_digest(date: str) -> str:
    """Build the digest email body in plain text."""
    chat = chatbot_summary(date)
    commits = git_activity(date)
    issues = github_issues()
    lean = lean_status()

    lines = [
        f'LRT Daily Digest: {date}',
        '=' * 40,
        '',
        '## LRT Chatbot (lrtchat.thinxai.net)',
        f'  Queries: {chat["queries"]}',
        f'  Unique sessions: {len(chat["sessions"])}',
        f'  Injection attempts blocked: {chat["injections_blocked"]}',
    ]

    if chat['modes']:
        mode_str = ', '.join(f'{m}: {c}' for m, c in chat['modes'].items())
        lines.append(f'  Modes: {mode_str}')

    lines += [
        '',
        '## Git Activity (logic-realism-theory)',
    ]
    if commits:
        for c in commits:
            lines.append(f'  {c}')
    else:
        lines.append('  No commits')

    lines += [
        '',
        '## Open GitHub Issues',
    ]
    for i in issues:
        lines.append(f'  {i}')

    lines += [
        '',
        '## Lean Formalization',
        f'  Axioms: {lean.get("axioms", "?")}',
        f'  Sorries: {lean.get("sorries", "?")}',
    ]

    lines += [
        '',
        '---',
        'Generated by lrt_chatbot/daily_digest.py',
    ]

    return '\n'.join(lines)


def send_email(subject: str, body: str) -> None:
    """Send digest via Gmail SMTP."""
    password = get_app_password()

    msg = MIMEMultipart('alternative')
    msg['Subject'] = subject
    msg['From'] = SENDER
    msg['To'] = RECIPIENT
    msg.attach(MIMEText(body, 'plain'))

    with smtplib.SMTP(SMTP_HOST, SMTP_PORT) as server:
        server.starttls()
        server.login(SENDER, password)
        server.sendmail(SENDER, RECIPIENT, msg.as_string())


def main():
    # Default to yesterday; accept date arg for testing
    if len(sys.argv) > 1:
        date = sys.argv[1]
    else:
        date = get_yesterday()

    digest = build_digest(date)

    if '--dry-run' in sys.argv:
        print(digest)
        return

    subject = f'LRT Daily Digest: {date}'
    send_email(subject, digest)
    print(f'Digest sent for {date}')


if __name__ == '__main__':
    main()
