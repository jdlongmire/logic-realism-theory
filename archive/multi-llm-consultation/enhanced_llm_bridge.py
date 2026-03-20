#!/usr/bin/env python3
"""
Enhanced Multi-LLM API Bridge with Caching, Quality Scoring, and Retry Logic
Phase 1 Improvements for Logic Field Theory Research
"""

import json
import asyncio
import aiohttp
import time
import hashlib
import sqlite3
from typing import Dict, List, Any, Optional, Tuple
from pathlib import Path
from dataclasses import dataclass, asdict
from enum import Enum
import re


class QueryType(Enum):
    """Types of queries with different optimization strategies."""
    LEAN_PROOF = "lean_proof"
    PEER_REVIEW = "peer_review"
    THEORY_QUESTION = "theory_question"
    GENERAL = "general"


@dataclass
class QualityScores:
    """Multi-dimensional quality scores for LLM responses."""
    lean_code_quality: float = 0.0      # Working Lean 4 syntax
    mathlib_citations: float = 0.0      # Specific theorem names
    step_by_step: float = 0.0           # Proof strategy clarity
    correctness_confidence: float = 0.0 # Self-assessed confidence
    actionability: float = 0.0          # Can immediately use?
    overall: float = 0.0                # Weighted average

    def to_dict(self) -> Dict[str, float]:
        return asdict(self)


class ResponseCache:
    """SQLite-based cache for LLM responses with intelligent TTL."""

    def __init__(self, db_path: str = "./llm_cache.db"):
        self.db_path = db_path
        self._init_db()

    def _init_db(self):
        """Initialize SQLite database with schema."""
        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()

        cursor.execute("""
            CREATE TABLE IF NOT EXISTS query_cache (
                cache_key TEXT PRIMARY KEY,
                prompt TEXT NOT NULL,
                prompt_type TEXT NOT NULL,
                responses_json TEXT NOT NULL,
                quality_scores_json TEXT,
                created_at REAL NOT NULL,
                accessed_at REAL,
                access_count INTEGER DEFAULT 1,
                ttl_seconds INTEGER NOT NULL
            )
        """)

        # Index for cleanup of expired entries
        cursor.execute("""
            CREATE INDEX IF NOT EXISTS idx_expiry
            ON query_cache(created_at, ttl_seconds)
        """)

        conn.commit()
        conn.close()

    def _generate_cache_key(self, prompt: str, query_type: QueryType,
                           temperature: float) -> str:
        """Generate SHA256 cache key from query parameters."""
        key_material = f"{prompt}|{query_type.value}|{temperature}"
        return hashlib.sha256(key_material.encode()).hexdigest()

    def _get_ttl(self, query_type: QueryType) -> int:
        """Get TTL in seconds based on query type."""
        ttls = {
            QueryType.LEAN_PROOF: 7 * 24 * 3600,      # 7 days
            QueryType.PEER_REVIEW: 1 * 24 * 3600,     # 1 day
            QueryType.THEORY_QUESTION: 30 * 24 * 3600, # 30 days
            QueryType.GENERAL: 7 * 24 * 3600          # 7 days
        }
        return ttls.get(query_type, 7 * 24 * 3600)

    def get(self, prompt: str, query_type: QueryType,
            temperature: float) -> Optional[Dict[str, Any]]:
        """Retrieve cached response if valid."""
        cache_key = self._generate_cache_key(prompt, query_type, temperature)

        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()

        cursor.execute("""
            SELECT responses_json, quality_scores_json, created_at, ttl_seconds
            FROM query_cache
            WHERE cache_key = ?
        """, (cache_key,))

        row = cursor.fetchone()

        if row is None:
            conn.close()
            return None

        responses_json, quality_json, created_at, ttl = row

        # Check if expired
        if time.time() - created_at > ttl:
            # Expired, delete it
            cursor.execute("DELETE FROM query_cache WHERE cache_key = ?", (cache_key,))
            conn.commit()
            conn.close()
            return None

        # Update access stats
        cursor.execute("""
            UPDATE query_cache
            SET accessed_at = ?, access_count = access_count + 1
            WHERE cache_key = ?
        """, (time.time(), cache_key))

        conn.commit()
        conn.close()

        responses = json.loads(responses_json)
        quality_scores_data = json.loads(quality_json) if quality_json else None

        # Reconstruct best_response from cached data
        best_response = None
        if responses and responses[0].get('success'):
            best = responses[0]
            best_response = {
                'source': best['source'],
                'content': best['content'],
                'quality': best.get('quality_score', 0.0)
            }

        return {
            'responses': responses,
            'quality_scores': quality_scores_data,
            'best_response': best_response,
            'from_cache': True,
            'query_type': query_type.value
        }

    def put(self, prompt: str, query_type: QueryType, temperature: float,
            responses: List[Dict[str, Any]], quality_scores: Optional[Dict[str, Any]] = None):
        """Store response in cache."""
        cache_key = self._generate_cache_key(prompt, query_type, temperature)
        ttl = self._get_ttl(query_type)

        # Convert QualityScores objects to dicts if needed
        if quality_scores:
            serializable_scores = {}
            for key, val in quality_scores.items():
                if hasattr(val, 'to_dict'):
                    serializable_scores[key] = val.to_dict()
                else:
                    serializable_scores[key] = val
        else:
            serializable_scores = None

        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()

        cursor.execute("""
            INSERT OR REPLACE INTO query_cache
            (cache_key, prompt, prompt_type, responses_json, quality_scores_json,
             created_at, accessed_at, access_count, ttl_seconds)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            cache_key,
            prompt,
            query_type.value,
            json.dumps(responses),
            json.dumps(serializable_scores) if serializable_scores else None,
            time.time(),
            time.time(),
            1,
            ttl
        ))

        conn.commit()
        conn.close()

    def cleanup_expired(self):
        """Remove expired cache entries."""
        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()

        cursor.execute("""
            DELETE FROM query_cache
            WHERE (? - created_at) > ttl_seconds
        """, (time.time(),))

        deleted = cursor.rowcount
        conn.commit()
        conn.close()

        return deleted

    def get_stats(self) -> Dict[str, Any]:
        """Get cache statistics."""
        conn = sqlite3.connect(self.db_path)
        cursor = conn.cursor()

        cursor.execute("SELECT COUNT(*), SUM(access_count) FROM query_cache")
        total_entries, total_accesses = cursor.fetchone()

        cursor.execute("""
            SELECT prompt_type, COUNT(*), AVG(access_count)
            FROM query_cache
            GROUP BY prompt_type
        """)

        by_type = {row[0]: {'count': row[1], 'avg_accesses': row[2]}
                   for row in cursor.fetchall()}

        conn.close()

        return {
            'total_entries': total_entries or 0,
            'total_accesses': total_accesses or 0,
            'by_type': by_type
        }


class QualityScorer:
    """Score LLM responses on multiple quality dimensions."""

    def __init__(self):
        # Lean 4 vs Lean 3 indicators
        self.lean3_patterns = [
            r'import analysis\.',
            r'import data\.',
            r'import tactic\.',
            r'\bbegin\s',
            r'\send\b',
            r"cases'",
        ]

        self.lean4_patterns = [
            r'import Mathlib\.',
            r'\bby\s',
            r'\bobtain\b',
            r'\brcases\b',
        ]

    def score_response(self, response: str, query_type: QueryType,
                      source: str) -> QualityScores:
        """Score a single response on multiple dimensions."""
        scores = QualityScores()

        if query_type == QueryType.LEAN_PROOF:
            scores = self._score_lean_proof(response)
        elif query_type == QueryType.PEER_REVIEW:
            scores = self._score_peer_review(response)
        elif query_type == QueryType.THEORY_QUESTION:
            scores = self._score_theory(response)
        else:
            scores = self._score_general(response)

        # Calculate weighted overall score
        scores.overall = self._calculate_overall(scores, query_type)

        return scores

    def _score_lean_proof(self, response: str) -> QualityScores:
        """Score Lean proof response."""
        scores = QualityScores()

        # Lean code quality (0.0 - 1.0)
        has_code_block = bool(re.search(r'```lean', response, re.IGNORECASE))
        if has_code_block:
            scores.lean_code_quality += 0.3

        # Check for Lean 4 (not Lean 3)
        lean3_count = sum(1 for p in self.lean3_patterns if re.search(p, response))
        lean4_count = sum(1 for p in self.lean4_patterns if re.search(p, response))

        if lean4_count > 0 and lean4_count > lean3_count:
            scores.lean_code_quality += 0.4
        elif lean3_count > lean4_count:
            scores.lean_code_quality -= 0.2  # Penalty for Lean 3

        if 'sorry' not in response.lower() and has_code_block:
            scores.lean_code_quality += 0.3

        # Mathlib citations (0.0 - 1.0)
        mathlib_theorems = re.findall(r'\b\w+\.\w+\.\w+', response)
        mathlib_imports = re.findall(r'import Mathlib\.[\w.]+', response)
        scores.mathlib_citations = min(1.0, (len(mathlib_theorems) + len(mathlib_imports) * 2) / 10.0)

        # Step-by-step (0.0 - 1.0)
        has_numbered_steps = bool(re.search(r'^\s*\d+\.', response, re.MULTILINE))
        has_sections = response.count('##') + response.count('**Step')
        scores.step_by_step = min(1.0, (int(has_numbered_steps) * 0.5 + has_sections * 0.1))

        # Actionability (0.0 - 1.0)
        has_alternatives = 'alternative' in response.lower() or 'instead' in response.lower()
        has_explanation = len(response) > 500  # Detailed response
        scores.actionability = (int(has_alternatives) * 0.4 + int(has_explanation) * 0.3 +
                               int(has_code_block) * 0.3)

        return scores

    def _score_peer_review(self, response: str) -> QualityScores:
        """Score peer review response."""
        scores = QualityScores()

        # Look for structured feedback
        has_sections = response.count('##') + response.count('###')
        has_numbered = bool(re.search(r'^\s*\d+\.', response, re.MULTILINE))
        scores.step_by_step = min(1.0, (has_sections * 0.2 + int(has_numbered) * 0.5))

        # Look for specific citations/references
        has_citations = bool(re.search(r'\[[\d,\s]+\]', response))
        has_theorems = bool(re.search(r'Theorem \d+', response))
        scores.mathlib_citations = (int(has_citations) * 0.5 + int(has_theorems) * 0.5)

        # Actionability - concrete suggestions
        concrete_words = ['suggest', 'recommend', 'should', 'could', 'consider', 'add', 'clarify']
        concrete_count = sum(response.lower().count(word) for word in concrete_words)
        scores.actionability = min(1.0, concrete_count / 10.0)

        # Correctness confidence - looks for hedging
        hedge_words = ['might', 'maybe', 'possibly', 'unclear', 'ambiguous']
        hedge_count = sum(response.lower().count(word) for word in hedge_words)
        scores.correctness_confidence = max(0.0, 1.0 - hedge_count / 5.0)

        return scores

    def _score_theory(self, response: str) -> QualityScores:
        """Score theory question response."""
        scores = QualityScores()

        # Citations and references
        has_citations = bool(re.search(r'\[\d+\]', response))
        has_equations = bool(re.search(r'\$.*\$', response))
        scores.mathlib_citations = (int(has_citations) * 0.5 + int(has_equations) * 0.5)

        # Step-by-step explanation
        has_structure = response.count('##') + response.count('###')
        has_numbered = bool(re.search(r'^\s*\d+\.', response, re.MULTILINE))
        scores.step_by_step = min(1.0, has_structure * 0.2 + int(has_numbered) * 0.5)

        # Depth and detail
        word_count = len(response.split())
        scores.actionability = min(1.0, word_count / 1000.0)

        return scores

    def _score_general(self, response: str) -> QualityScores:
        """Score general response."""
        scores = QualityScores()

        # Basic quality heuristics
        has_structure = bool(re.search(r'^\s*#+\s', response, re.MULTILINE))
        has_numbered = bool(re.search(r'^\s*\d+\.', response, re.MULTILINE))
        scores.step_by_step = (int(has_structure) * 0.5 + int(has_numbered) * 0.5)

        word_count = len(response.split())
        scores.actionability = min(1.0, word_count / 500.0)

        return scores

    def _calculate_overall(self, scores: QualityScores, query_type: QueryType) -> float:
        """Calculate weighted overall score based on query type."""
        if query_type == QueryType.LEAN_PROOF:
            weights = {
                'lean_code_quality': 0.40,
                'mathlib_citations': 0.25,
                'step_by_step': 0.15,
                'actionability': 0.20
            }
        elif query_type == QueryType.PEER_REVIEW:
            weights = {
                'step_by_step': 0.30,
                'actionability': 0.35,
                'correctness_confidence': 0.20,
                'mathlib_citations': 0.15
            }
        elif query_type == QueryType.THEORY_QUESTION:
            weights = {
                'step_by_step': 0.30,
                'mathlib_citations': 0.30,
                'actionability': 0.40
            }
        else:
            weights = {
                'step_by_step': 0.50,
                'actionability': 0.50
            }

        total = 0.0
        for dimension, weight in weights.items():
            total += getattr(scores, dimension) * weight

        return total


class EnhancedMultiLLMBridge:
    """Enhanced Multi-LLM bridge with caching, quality scoring, and retry logic."""

    def __init__(self, config_path: str = "./api_config.json"):
        """Initialize enhanced bridge."""
        self.config_path = config_path
        self.config = self._load_config()
        self.cache = ResponseCache()
        self.scorer = QualityScorer()
        self.session_logs = []
        self.cache_hits = 0
        self.cache_misses = 0

    def _load_config(self) -> Dict[str, Any]:
        """Load API configuration from JSON file."""
        try:
            with open(self.config_path, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            print(f"Error: Configuration file {self.config_path} not found.")
            raise
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in configuration file: {e}")
            raise

    def detect_query_type(self, prompt: str) -> QueryType:
        """Auto-detect query type from prompt content."""
        prompt_lower = prompt.lower()

        # Lean proof indicators
        lean_indicators = ['lean', 'theorem', 'proof', 'sorry', 'mathlib', 'tactic']
        if any(ind in prompt_lower for ind in lean_indicators):
            return QueryType.LEAN_PROOF

        # Peer review indicators
        review_indicators = ['review', 'feedback', 'critique', 'improve', 'section']
        if any(ind in prompt_lower for ind in review_indicators):
            return QueryType.PEER_REVIEW

        # Theory question indicators
        theory_indicators = ['why', 'how', 'explain', 'derive', 'prove that', 'show that']
        if any(ind in prompt_lower for ind in theory_indicators):
            return QueryType.THEORY_QUESTION

        return QueryType.GENERAL

    async def _query_with_retry(self, query_func, prompt: str,
                                max_attempts: int = 3) -> Dict[str, Any]:
        """Execute query with exponential backoff retry."""
        for attempt in range(max_attempts):
            try:
                result = await query_func(prompt)
                if result.get('success'):
                    return result

                # If not successful, retry with backoff
                if attempt < max_attempts - 1:
                    backoff = 2 ** attempt  # 1s, 2s, 4s
                    await asyncio.sleep(backoff)

            except asyncio.TimeoutError:
                if attempt < max_attempts - 1:
                    backoff = 2 ** attempt
                    await asyncio.sleep(backoff)
                else:
                    return {
                        'source': query_func.__name__.replace('query_', ''),
                        'success': False,
                        'error': 'Timeout after retries'
                    }
            except Exception as e:
                if attempt < max_attempts - 1:
                    backoff = 2 ** attempt
                    await asyncio.sleep(backoff)
                else:
                    return {
                        'source': query_func.__name__.replace('query_', ''),
                        'success': False,
                        'error': str(e)
                    }

        return {
            'source': query_func.__name__.replace('query_', ''),
            'success': False,
            'error': 'Max retries exceeded'
        }

    async def query_grok(self, prompt: str) -> Dict[str, Any]:
        """Query Grok API asynchronously."""
        headers = {
            "Authorization": f"Bearer {self.config['api_keys']['grok']}",
            "Content-Type": "application/json"
        }

        payload = {
            "messages": [
                {"role": "system", "content": self.config['lean_specific_prompts']['system_prompt']},
                {"role": "user", "content": prompt}
            ],
            "model": "grok-3",
            "temperature": self.config['default_settings']['temperature'],
            "max_tokens": self.config['default_settings']['max_tokens']
        }

        async with aiohttp.ClientSession() as session:
            async with session.post(
                self.config['endpoints']['grok'],
                headers=headers,
                json=payload,
                timeout=aiohttp.ClientTimeout(total=self.config['default_settings']['timeout_seconds'])
            ) as response:
                if response.status == 200:
                    result = await response.json()
                    return {
                        "source": "grok",
                        "success": True,
                        "content": result['choices'][0]['message']['content'],
                        "model": "grok-3"
                    }
                else:
                    return {
                        "source": "grok",
                        "success": False,
                        "error": f"HTTP {response.status}: {await response.text()}"
                    }

    async def query_chatgpt(self, prompt: str) -> Dict[str, Any]:
        """Query ChatGPT API asynchronously."""
        headers = {
            "Authorization": f"Bearer {self.config['api_keys']['chatgpt']}",
            "Content-Type": "application/json"
        }

        payload = {
            "model": "gpt-4",
            "messages": [
                {"role": "system", "content": self.config['lean_specific_prompts']['system_prompt']},
                {"role": "user", "content": prompt}
            ],
            "temperature": self.config['default_settings']['temperature'],
            "max_tokens": self.config['default_settings']['max_tokens']
        }

        async with aiohttp.ClientSession() as session:
            async with session.post(
                self.config['endpoints']['chatgpt'],
                headers=headers,
                json=payload,
                timeout=aiohttp.ClientTimeout(total=self.config['default_settings']['timeout_seconds'])
            ) as response:
                if response.status == 200:
                    result = await response.json()
                    return {
                        "source": "chatgpt",
                        "success": True,
                        "content": result['choices'][0]['message']['content'],
                        "model": "gpt-4"
                    }
                else:
                    return {
                        "source": "chatgpt",
                        "success": False,
                        "error": f"HTTP {response.status}: {await response.text()}"
                    }

    async def query_gemini(self, prompt: str) -> Dict[str, Any]:
        """Query Gemini API asynchronously."""
        url = f"{self.config['endpoints']['gemini']}?key={self.config['api_keys']['gemini']}"

        payload = {
            "contents": [
                {
                    "parts": [
                        {"text": f"{self.config['lean_specific_prompts']['system_prompt']}\n\n{prompt}"}
                    ]
                }
            ],
            "generationConfig": {
                "temperature": self.config['default_settings']['temperature'],
                "maxOutputTokens": self.config['default_settings']['max_tokens']
            }
        }

        async with aiohttp.ClientSession() as session:
            async with session.post(
                url,
                json=payload,
                timeout=aiohttp.ClientTimeout(total=self.config['default_settings']['timeout_seconds'])
            ) as response:
                if response.status == 200:
                    result = await response.json()
                    content = result['candidates'][0]['content']['parts'][0]['text']
                    return {
                        "source": "gemini",
                        "success": True,
                        "content": content,
                        "model": "gemini-pro"
                    }
                else:
                    return {
                        "source": "gemini",
                        "success": False,
                        "error": f"HTTP {response.status}: {await response.text()}"
                    }

    async def consult_all_experts(self, prompt: str, query_type: QueryType = QueryType.GENERAL,
                                  use_cache: bool = True) -> Dict[str, Any]:
        """Query all LLM experts with caching, retry, and quality scoring."""

        # Check cache first
        if use_cache:
            cached = self.cache.get(prompt, query_type,
                                   self.config['default_settings']['temperature'])
            if cached:
                self.cache_hits += 1
                print(f"[CACHE HIT] Retrieved from cache (query_type: {query_type.value})")
                return cached
            else:
                self.cache_misses += 1

        print(f"Consulting expert LLMs (query_type: {query_type.value})...")

        # Query all experts with retry logic
        tasks = [
            self._query_with_retry(self.query_grok, prompt),
            self._query_with_retry(self.query_chatgpt, prompt),
            self._query_with_retry(self.query_gemini, prompt)
        ]

        responses = await asyncio.gather(*tasks, return_exceptions=True)

        # Handle exceptions
        formatted_responses = []
        for i, result in enumerate(responses):
            if isinstance(result, Exception):
                formatted_responses.append({
                    "source": ["grok", "chatgpt", "gemini"][i],
                    "success": False,
                    "error": str(result)
                })
            else:
                formatted_responses.append(result)

        # Score responses
        quality_scores = {}
        for response in formatted_responses:
            if response.get('success'):
                scores = self.scorer.score_response(
                    response['content'],
                    query_type,
                    response['source']
                )
                quality_scores[response['source']] = scores.to_dict()
                response['quality_score'] = scores.overall

        # Sort by quality score
        formatted_responses.sort(
            key=lambda r: r.get('quality_score', 0.0),
            reverse=True
        )

        # Identify best response
        best_response = None
        if formatted_responses and formatted_responses[0].get('success'):
            best = formatted_responses[0]
            best_response = {
                'source': best['source'],
                'content': best['content'],
                'quality': best.get('quality_score', 0.0)
            }

        result = {
            'responses': formatted_responses,
            'quality_scores': quality_scores,
            'best_response': best_response,
            'from_cache': False,
            'query_type': query_type.value
        }

        # Cache the result
        if use_cache:
            self.cache.put(prompt, query_type,
                          self.config['default_settings']['temperature'],
                          formatted_responses, quality_scores)

        return result

    async def consult_lean_proof(self, code: str, issue: str,
                                context: str = "") -> Dict[str, Any]:
        """Specialized consultation for Lean 4 proof problems."""
        prompt = f"""
LEAN 4 PROOF CONSULTATION

ISSUE: {issue}

CODE:
```lean
{code}
```

CONTEXT: {context}

Please provide:
1. Specific Mathlib theorem names and imports
2. Working Lean 4 code snippets (not Lean 3!)
3. Step-by-step proof strategy
4. Alternative approaches if applicable

Focus on actionable, implementable solutions with proper Lean 4 syntax.
"""
        return await self.consult_all_experts(prompt, QueryType.LEAN_PROOF)

    async def consult_peer_review(self, section: str, focus_area: str = "general") -> Dict[str, Any]:
        """Specialized consultation for peer review feedback."""
        prompt = f"""
PEER REVIEW REQUEST

FOCUS AREA: {focus_area}

SECTION TO REVIEW:
{section}

Please provide:
1. Strengths of the current presentation
2. Specific areas for improvement
3. Clarity and correctness concerns
4. Concrete suggestions for enhancement
5. Missing citations or references (if applicable)

Provide structured, actionable feedback suitable for publication.
"""
        return await self.consult_all_experts(prompt, QueryType.PEER_REVIEW)

    async def consult_theory(self, question: str, context: str = "") -> Dict[str, Any]:
        """Specialized consultation for theory questions."""
        prompt = f"""
THEORY QUESTION

QUESTION: {question}

CONTEXT: {context}

Please provide:
1. Clear explanation from first principles
2. Relevant mathematical formulations
3. Citations to key papers/theorems (if applicable)
4. Step-by-step derivations
5. Implications and connections to related concepts
"""
        return await self.consult_all_experts(prompt, QueryType.THEORY_QUESTION)

    def print_results_with_scores(self, result: Dict[str, Any]):
        """Print results with quality scores."""
        if result.get('from_cache'):
            print("\n[CACHE] Retrieved from cache")

        print(f"\n[QUERY TYPE] {result.get('query_type', 'unknown')}")
        print("=" * 70)

        responses = result.get('responses', [])
        quality_scores = result.get('quality_scores', {})

        for i, response in enumerate(responses, 1):
            source = response.get('source', 'unknown')
            success = response.get('success', False)

            if success:
                overall_score = response.get('quality_score', 0.0)
                print(f"\n{i}. {source.upper()} - Quality Score: {overall_score:.2f}/1.0")

                # Show detailed scores if available
                if source in quality_scores:
                    scores = quality_scores[source]
                    print(f"   Dimensions:")
                    for dim, val in scores.items():
                        if dim != 'overall' and val > 0:
                            print(f"     - {dim}: {val:.2f}")

                # Show preview of response
                content = response.get('content', '')
                preview = content[:300] + "..." if len(content) > 300 else content
                print(f"\n   {preview}\n")
            else:
                print(f"\n{i}. {source.upper()} - FAILED")
                print(f"   Error: {response.get('error', 'Unknown error')}")

    def get_cache_stats(self) -> Dict[str, Any]:
        """Get cache statistics with hit/miss tracking."""
        base_stats = self.cache.get_stats()

        # Add session hit/miss tracking
        total_requests = self.cache_hits + self.cache_misses
        hit_rate = self.cache_hits / total_requests if total_requests > 0 else 0.0

        return {
            **base_stats,
            'cache_hits': self.cache_hits,
            'cache_misses': self.cache_misses,
            'hit_rate': hit_rate
        }

    def cleanup_cache(self) -> int:
        """Clean up expired cache entries."""
        return self.cache.cleanup_expired()

    async def health_check(self) -> Dict[str, Any]:
        """
        Check health of all APIs with simple test query.

        Returns dict with:
        - overall_status: 'healthy', 'degraded', or 'unhealthy'
        - api_status: dict of {api_name: {'status': bool, 'response_time': float, 'error': str}}
        - healthy_count: number of working APIs
        - timestamp: when check was performed
        """
        import time

        test_prompt = "Respond with just the word 'OK'."
        results = {
            'timestamp': time.time(),
            'api_status': {},
            'healthy_count': 0
        }

        # Test each API individually
        apis = [
            ('grok', self.query_grok),
            ('chatgpt', self.query_chatgpt),
            ('gemini', self.query_gemini)
        ]

        for api_name, api_func in apis:
            start = time.time()
            try:
                response = await asyncio.wait_for(api_func(test_prompt), timeout=10.0)
                elapsed = time.time() - start

                if response.get('success'):
                    results['api_status'][api_name] = {
                        'status': True,
                        'response_time': elapsed,
                        'message': 'OK'
                    }
                    results['healthy_count'] += 1
                else:
                    results['api_status'][api_name] = {
                        'status': False,
                        'response_time': elapsed,
                        'error': response.get('error', 'Unknown error')
                    }
            except asyncio.TimeoutError:
                results['api_status'][api_name] = {
                    'status': False,
                    'response_time': 10.0,
                    'error': 'Timeout after 10 seconds'
                }
            except Exception as e:
                results['api_status'][api_name] = {
                    'status': False,
                    'response_time': time.time() - start,
                    'error': str(e)
                }

        # Determine overall status
        if results['healthy_count'] == 3:
            results['overall_status'] = 'healthy'
        elif results['healthy_count'] > 0:
            results['overall_status'] = 'degraded'
        else:
            results['overall_status'] = 'unhealthy'

        return results

    def print_health_check(self, health: Dict[str, Any]):
        """Print formatted health check results."""
        print("=" * 70)
        print("API HEALTH CHECK")
        print("=" * 70)

        status_emoji = {
            'healthy': '[OK]',
            'degraded': '[WARN]',
            'unhealthy': '[FAIL]'
        }

        print(f"\nOverall Status: {status_emoji.get(health['overall_status'], '[?]')} {health['overall_status'].upper()}")
        print(f"Healthy APIs: {health['healthy_count']}/3")

        print("\nAPI Status:")
        for api_name, status in health['api_status'].items():
            if status['status']:
                print(f"  [OK] {api_name.upper()}: {status['response_time']:.2f}s")
            else:
                print(f"  [FAIL] {api_name.upper()}: {status.get('error', 'Unknown')}")

        print("=" * 70)


# CLI Interface
async def cli_main():
    """CLI interface for team consultations."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Multi-LLM Consultation System for Logic Field Theory Research",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # General query (auto-detect type)
  python enhanced_llm_bridge.py --query "How does quantum entanglement work?"

  # Lean proof consultation
  python enhanced_llm_bridge.py --query "Need help with HasDerivAt proof" --mode lean

  # Peer review
  python enhanced_llm_bridge.py --query "Review my paper section" --mode review

  # Theory question
  python enhanced_llm_bridge.py --query "Explain Bell's theorem" --mode theory

  # Health check
  python enhanced_llm_bridge.py --health-check

  # Disable cache
  python enhanced_llm_bridge.py --query "My question" --no-cache
        """
    )

    parser.add_argument('--query', type=str, help='Query text to send to LLMs')
    parser.add_argument('--mode', type=str, choices=['lean', 'review', 'theory', 'general', 'auto'],
                       default='auto', help='Consultation mode (default: auto-detect)')
    parser.add_argument('--models', type=str, default='all',
                       help='Comma-separated list of models (grok,chatgpt,gemini) or "all"')
    parser.add_argument('--no-cache', action='store_true',
                       help='Disable cache for this query')
    parser.add_argument('--health-check', action='store_true',
                       help='Run API health check')
    parser.add_argument('--cache-stats', action='store_true',
                       help='Show cache statistics')
    parser.add_argument('--cleanup-cache', action='store_true',
                       help='Clean up expired cache entries')
    parser.add_argument('--output', type=str, choices=['full', 'best', 'json'],
                       default='full', help='Output format (default: full)')

    args = parser.parse_args()

    bridge = EnhancedMultiLLMBridge()

    # Health check
    if args.health_check:
        print("Running API health check...")
        health = await bridge.health_check()
        bridge.print_health_check(health)
        return

    # Cache stats
    if args.cache_stats:
        stats = bridge.get_cache_stats()
        print("=" * 70)
        print("CACHE STATISTICS")
        print("=" * 70)
        print(f"Total entries: {stats['total_entries']}")
        print(f"Total accesses: {stats['total_accesses']}")
        print(f"Cache hits: {stats['cache_hits']}")
        print(f"Cache misses: {stats['cache_misses']}")
        print(f"Hit rate: {stats['hit_rate']:.1%}")
        print("\nBy type:")
        for qtype, data in stats.get('by_type', {}).items():
            print(f"  {qtype}: {data['count']} entries, {data['avg_accesses']:.1f} avg accesses")
        print("=" * 70)
        return

    # Cleanup cache
    if args.cleanup_cache:
        deleted = bridge.cleanup_cache()
        print(f"Cleaned up {deleted} expired cache entries")
        return

    # Query required if not running special commands
    if not args.query:
        parser.print_help()
        print("\nError: --query is required unless using --health-check, --cache-stats, or --cleanup-cache")
        return

    # Determine query type
    if args.mode == 'auto':
        query_type = bridge.detect_query_type(args.query)
        print(f"[AUTO-DETECT] Query type: {query_type.value}")
    else:
        mode_map = {
            'lean': QueryType.LEAN_PROOF,
            'review': QueryType.PEER_REVIEW,
            'theory': QueryType.THEORY_QUESTION,
            'general': QueryType.GENERAL
        }
        query_type = mode_map[args.mode]

    # Execute query
    use_cache = not args.no_cache
    result = await bridge.consult_all_experts(args.query, query_type, use_cache=use_cache)

    # Output results (handle Unicode encoding for Windows)
    import sys
    if sys.platform == 'win32':
        sys.stdout.reconfigure(encoding='utf-8')

    if args.output == 'json':
        print(json.dumps(result, indent=2))
    elif args.output == 'best':
        best = result.get('best_response')
        if best:
            print("=" * 70)
            print(f"BEST RESPONSE ({best['source'].upper()}) - Quality: {best['quality']:.2f}")
            print("=" * 70)
            # Handle potential Unicode characters
            try:
                print(best['content'])
            except UnicodeEncodeError:
                print(best['content'].encode('utf-8', errors='replace').decode('utf-8'))
        else:
            print("No successful responses received")
    else:  # full
        bridge.print_results_with_scores(result)

        # Show cache stats
        print("\n" + "=" * 70)
        stats = bridge.get_cache_stats()
        print(f"Cache Statistics: {stats}")


# Example usage (for library import)
async def example_usage():
    """Example usage of enhanced bridge (for documentation)."""
    bridge = EnhancedMultiLLMBridge()

    # Example 1: Lean proof consultation
    print("=" * 70)
    print("EXAMPLE 1: Lean Proof Consultation")
    print("=" * 70)

    result = await bridge.consult_lean_proof(
        code="theorem example (x : ℝ) : x + 0 = x := by sorry",
        issue="Need to prove basic arithmetic property",
        context="Learning Lean 4 basics"
    )

    bridge.print_results_with_scores(result)

    # Show cache stats
    print("\n" + "=" * 70)
    stats = bridge.get_cache_stats()
    print(f"Cache Statistics: {stats}")


if __name__ == "__main__":
    asyncio.run(cli_main())
