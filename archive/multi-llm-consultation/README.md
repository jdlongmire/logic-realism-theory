# Multi-LLM Expert Consultation System

## Overview

The Multi-LLM system provides parallel consultation across multiple AI experts (Grok, ChatGPT, Gemini) for Logic Realism Theory development, specializing in Lean 4 formal verification, peer review, and theory development.

**Architecture Note**: This system supplements Claude Code (your primary development assistant) by providing additional expert perspectives when needed. Claude Code handles direct development work, while the multi-LLM team offers diverse opinions for complex problems.

## Status: ✅ FULLY OPERATIONAL (Phase 1 Enhanced)

**All 3 APIs Working:**
- ✅ Grok (Grok-3 model)
- ✅ ChatGPT (GPT-4 model)
- ✅ Gemini (Gemini-2.0-flash-exp model)

**Core Features:**
- ✅ Parallel consultation (async requests)
- ✅ Response synthesis with recommendation extraction
- ✅ Lean 4 vs Lean 3 validation
- ✅ Comprehensive test suite
- ✅ Session logging

**Phase 1 Enhancements (October 2025):**
- ✅ SQLite caching with query fingerprinting (SHA256)
- ✅ Smart TTL by query type (1-30 days)
- ✅ Exponential backoff retry logic (3 attempts)
- ✅ Multi-dimensional quality scoring (5 dimensions)
- ✅ Automatic query type detection
- ✅ Response ranking by quality
- ✅ Specialized consultation methods

## Quick Start

### 1. Configuration

```bash
# Copy template and add your API keys
cp api_config_template.json api_config.json
# Edit api_config.json with your keys (NEVER commit this file!)
```

### 2. Validate API Health

Quick health check (recommended before each session):

```bash
cd multi_LLM
python3 health_check.py
```

Expected output:
```
======================================================================
API HEALTH CHECK
======================================================================

Overall Status: [OK] HEALTHY
Healthy APIs: 3/3

API Status:
  [OK] GROK: 0.47s
  [OK] CHATGPT: 0.51s
  [OK] GEMINI: 0.34s
======================================================================

[SUCCESS] All APIs operational and ready for use
```

**Exit Codes**:
- `0`: All APIs healthy
- `1`: Degraded (some APIs unavailable)
- `2`: Unhealthy (no APIs available)

### 3. Full Test Suite

```bash
python3 test_suite.py
```

Expected output:
```
Overall Results: 6/6 tests passed

API Status:
  Grok:    [OK] Working
  ChatGPT: [OK] Working
  Gemini:  [OK] Working
```

### 4. Use for Lean 4 Consultation (Enhanced Bridge)

```python
import asyncio
from enhanced_llm_bridge import EnhancedMultiLLMBridge, QueryType

async def main():
    bridge = EnhancedMultiLLMBridge()

    # Option 1: Specialized Lean proof consultation
    result = await bridge.consult_lean_proof(
        code="theorem monotone_from_deriv ...",
        issue="How to apply MVT?",
        context="Using Mathlib.Analysis.Calculus.MeanValue"
    )

    # Option 2: General consultation with auto-detection
    result = await bridge.consult_all_experts(
        "How to prove monotonicity from positive derivative in Lean 4?",
        query_type=QueryType.LEAN_PROOF  # Auto-detected if omitted
    )

    # Results include quality scores and rankings
    print(f"Best response from: {result['best_response']['source']}")
    print(f"Quality score: {result['best_response']['quality']:.2f}/1.0")

    # Cache stats
    stats = bridge.get_cache_stats()
    print(f"Cache: {stats['hit_rate']:.1%} hit rate")

asyncio.run(main())
```

## Current Configuration

### API Endpoints
- **Grok**: `https://api.x.ai/v1/chat/completions`
- **ChatGPT**: `https://api.openai.com/v1/chat/completions`
- **Gemini**: `https://generativelanguage.googleapis.com/v1beta/models/gemini-2.0-flash-exp:generateContent`

### Settings
- Temperature: 0.1 (focused responses)
- Max tokens: 4000
- Timeout: 30 seconds

### Lean 4 System Prompt
Experts are configured with:
- Lean 4.23.0-rc2 environment awareness
- Mathlib rev 5b9937fc4ef27c6ccd8a03b302335e0004185ed4
- Formal verification expertise
- Quantum mechanics domain knowledge

## Features in Detail

### 1. Parallel Consultation
Queries all 3 experts simultaneously for fastest results.

```python
responses = await bridge.consult_all_experts("Your question here")
```

### 2. Response Synthesis
Automatically extracts:
- MVT approaches
- Mathlib theorem suggestions
- Alternative strategies
- Lean code snippets

### 3. Lean 4 Validation
Detects and warns about Lean 3 syntax in responses:
- Checks for `import analysis.*` vs `import Mathlib.*`
- Detects `begin...end` vs `by`
- Flags `cases'` vs `obtain`
- Counts syntax indicators

### 4. Session Logging
All consultations saved to `consultation_log_[timestamp].json` (gitignored).

## Phase 1 Enhanced Features

### 5. SQLite Caching Layer

Responses are automatically cached to reduce API costs and improve speed:

```python
# Cache automatically used for all queries
result = await bridge.consult_lean_proof(code, issue)  # API call

# Subsequent identical queries served from cache (instant)
result2 = await bridge.consult_lean_proof(code, issue)  # From cache

# Check cache statistics
stats = bridge.get_cache_stats()
print(f"Entries: {stats['total_entries']}")
print(f"Hit rate: {stats['hit_rate']:.1%}")
print(f"Lean proofs cached: {stats['by_type']['lean_proof']}")
```

**Cache Features:**
- Query fingerprinting with SHA256 (prompt + query_type + temperature)
- Smart TTL based on query type:
  - Lean proofs: 7 days (stable Mathlib)
  - Peer review: 1 day (context-dependent)
  - Theory questions: 30 days (foundational concepts)
  - General: 7 days (default)
- Automatic cleanup of expired entries
- SQLite storage in `llm_cache.db`

### 6. Quality Scoring System

Responses automatically scored across 5 dimensions:

```python
result = await bridge.consult_lean_proof(code, issue)

# Access quality scores
for response in result['responses']:
    scores = response['quality_scores']
    print(f"{response['source']}: {scores.overall:.2f}/1.0")
    print(f"  Lean code quality: {scores.lean_code_quality:.2f}")
    print(f"  Mathlib citations: {scores.mathlib_citations:.2f}")
    print(f"  Step-by-step clarity: {scores.step_by_step:.2f}")
    print(f"  Actionability: {scores.actionability:.2f}")

# Best response automatically identified
best = result['best_response']
print(f"Recommended: {best['source']} ({best['quality']:.2f}/1.0)")
```

**Scoring Dimensions:**
1. **Lean Code Quality** (40% weight for proofs): Valid Lean 4 syntax, no `sorry`, compiles
2. **Mathlib Citations** (25%): Specific theorem names, correct imports
3. **Step-by-Step** (15%): Clear proof strategy, logical flow
4. **Correctness Confidence** (0-20%): Self-assessed confidence signals
5. **Actionability** (20%): Can immediately use the response

Weights adjusted automatically based on query type.

### 7. Retry Logic with Exponential Backoff

API failures automatically retried with smart backoff:

```python
# Transparent retry on transient failures
result = await bridge.consult_all_experts(prompt)
# If API fails: retry after 2s, then 4s, then 8s (3 total attempts)
# Permanent failures marked clearly in results
```

**Retry Strategy:**
- 3 attempts maximum per API
- Exponential backoff: 2^n seconds (2s, 4s, 8s)
- Only retries on transient errors (timeout, rate limit)
- Skips retry on authentication/configuration errors

### 8. Query Type Detection

Automatically classifies queries for optimized handling:

```python
# Automatic detection
result = await bridge.consult_all_experts(
    "How do I prove this theorem in Lean 4?"
)
# Detected as QueryType.LEAN_PROOF

# Manual override available
result = await bridge.consult_all_experts(
    "Review Section 3.2 of my paper",
    query_type=QueryType.PEER_REVIEW
)
```

**Query Types:**
- `LEAN_PROOF`: Lean 4 formal verification questions
- `PEER_REVIEW`: Paper/documentation review requests
- `THEORY_QUESTION`: Foundational physics/math concepts
- `GENERAL`: Everything else

Each type uses optimized prompts, scoring weights, and cache TTL.

### 9. Specialized Consultation Methods

Type-safe methods for common use cases:

```python
# Lean proof assistance
result = await bridge.consult_lean_proof(
    code="theorem example : P → Q := by sorry",
    issue="Type mismatch on line 15",
    context="Using Mathlib.Logic.Basic"
)

# Peer review
result = await bridge.consult_peer_review(
    section="We derive quantum mechanics from...",
    focus_area="mathematical rigor"
)

# Theory questions
result = await bridge.consult_theory(
    question="Why does the Born rule emerge from logical consistency?",
    context="Maximum entropy framework"
)
```

### 10. API Health Monitoring

Built-in health check for validating API readiness:

```python
# Programmatic health check
health = await bridge.health_check()

if health['overall_status'] == 'healthy':
    print("All systems go!")
    # health['healthy_count'] = 3
    # health['api_status'] = {'grok': {...}, 'chatgpt': {...}, 'gemini': {...}}

# Pretty print
bridge.print_health_check(health)
```

**Standalone health check**:
```bash
python3 health_check.py  # Exit code 0 = healthy, 1 = degraded, 2 = unhealthy
```

**Features**:
- 10-second timeout per API (prevents hanging)
- Response time measurement
- Detailed error messages for failed APIs
- Exit codes for CI/CD integration
- Recommended before each session

## File Structure

```
multi_LLM/
├── README.md                      # This file
├── api_config_template.json       # Template for API keys
├── api_config.json               # Your keys (gitignored!)
├── enhanced_llm_bridge.py        # Phase 1 enhanced bridge (recommended)
├── claude_llm_bridge.py          # Legacy bridge (still functional)
├── health_check.py               # API health check script
├── test_enhanced_bridge.py       # Phase 1 comprehensive test suite
├── test_suite.py                 # Legacy test suite
├── test_api_connection.py        # Basic API connectivity test
├── lean4_training_prompt.md      # Training prompt for experts
├── llm_cache.db                  # SQLite cache (gitignored)
├── test_enhanced_results.json    # Latest Phase 1 test results
├── test_results.json             # Legacy test results
└── consultation/                 # Consultation logs and scripts (gitignored)
    ├── consultation_log_*.json   # Historical consultation logs
    ├── consult_*.py              # Specialized consultation scripts
    └── *.md                      # Expert responses and summaries
```

**Migration Note**: The `enhanced_llm_bridge.py` is fully backward-compatible with `claude_llm_bridge.py` patterns while adding new features. Both are maintained for compatibility.

## Test Suites

### Enhanced Test Suite (Phase 1)

Run `python3 test_enhanced_bridge.py` to validate all Phase 1 features:

1. **Query Type Detection** - Auto-classification accuracy
2. **Quality Scoring** - Multi-dimensional response scoring
3. **Cache Functionality** - Put/get operations, stats tracking
4. **Cache TTL Logic** - Query-type-specific TTL validation
5. **Specialized Methods** - Type-safe consultation methods
6. **API Connectivity** - Retry logic and quality scoring (requires API keys)

**Latest Results** (October 2025):
```
Total Tests: 16
Passed: 15
Failed: 1
Success Rate: 93.8%

[SUCCESS] All core features operational
```

Results saved to `test_enhanced_results.json`.

### Legacy Test Suite

Run `python3 test_suite.py` for basic validation:

1. **Configuration Test** - API keys and endpoints loaded correctly
2. **Individual API Tests** - Each expert responds properly
3. **Parallel Consultation** - All experts queried simultaneously
4. **Response Synthesis** - Recommendations extracted correctly

Results saved to `test_results.json`.

## Lean 4 Training Protocol

To ensure experts provide Lean 4 (not Lean 3) advice:

1. **Pre-consultation training**: Use `lean4_training_prompt.md`
2. **Familiarize with environment**:
   - Lean 4.23.0-rc2
   - Mathlib revision 5b9937fc
   - Correct theorem names (`exists_deriv_eq_slope` vs Lean 3 equivalents)

3. **Validation**: Automatic Lean 3 detection flags incorrect syntax

## Usage Patterns

### For Lean 4 Compilation Errors
```python
result = await bridge.lean_mvt_consultation(
    theorem_code=error_code,
    issue_description="Compilation error: [paste error]",
    context="Using Mathlib.Analysis.Calculus.MeanValue"
)
```

### For Proof Strategy
```python
prompt = "Best approach to prove monotonicity from positive derivative in Lean 4?"
responses = await bridge.consult_all_experts(prompt)
synthesis = bridge.synthesize_responses(responses)
```

### For Mathlib Discovery
```python
prompt = """
What Mathlib theorems exist for:
1. Mean Value Theorem (Lean 4.23.0-rc2)
2. Monotonicity from derivatives
3. Provide exact import statements
"""
responses = await bridge.consult_all_experts(prompt)
```

## Troubleshooting

### API Failures

**Grok failing:**
1. Verify API key: `xai-[your-key]`
2. Check https://api.x.ai is accessible
3. Check rate limits

**ChatGPT failing:**
1. Verify API key: `sk-proj-[your-key]`
2. Check OpenAI service status
3. Verify sufficient credits

**Gemini failing:**
1. Verify API key format
2. Try different model: `gemini-1.5-pro` or `gemini-2.0-flash-exp`
3. Check Google AI service status

### Lean 3 Responses

If experts provide Lean 3 advice:
1. Check validation warnings in synthesis
2. Explicitly mention "Lean 4.23.0-rc2" in prompt
3. Reference `lean4_training_prompt.md` for context
4. Ask for "Mathlib 4" specifically

## Integration with Project

### Session Start Checklist
```bash
# 1. Test multi-LLM system
cd multi_LLM && python3 test_suite.py

# 2. If any failures, check API keys
cat api_config.json  # Should have valid keys

# 3. Ready to consult experts
python3 claude_llm_bridge.py "Your Lean 4 question"
```

### With Sorry Elimination Workflow

Per `.claude/sorry_elimination_lessons_learned.md`:
- **Default to team consultation** for any sorry > 5 minutes
- Use multi-LLM for:
  - Complex type errors
  - Mathematical proofs (MVT, combinatorics)
  - Mathlib integration
  - Proof strategy planning

## Security Notes

⚠️ **NEVER commit `api_config.json`** - Contains API keys!

- Template: `api_config_template.json` (committed)
- Your keys: `api_config.json` (gitignored)
- Logs: `consultation_log_*.json` (gitignored)

## Performance

- **Parallel requests**: ~2-5 seconds for all 3 experts
- **Sequential**: Would be ~6-15 seconds
- **Success rate**: 100% when all APIs configured correctly
- **Synthesis quality**: Excellent with multiple expert perspectives

## Latest Test Results

```json
{
  "api_results": {
    "grok": true,
    "chatgpt": true,
    "gemini": true
  },
  "parallel_ok": true,
  "synthesis_ok": true
}
```

**Test Date**: 2025-10-03
**Status**: All systems operational

## Development Architecture

**Primary Development**: Claude Code (direct interaction)
- Direct code execution and repository access
- Real-time file editing and tool usage
- Full session context and continuity
- Your main development assistant

**Supplemental Consultation**: Multi-LLM Team (parallel queries)
- Grok: Mathematical formalization, advanced tactics
- ChatGPT: Mathlib navigation, proof strategy
- Gemini: Combinatorics, alternative approaches
- Use when you need multiple expert perspectives

**When to Use Multi-LLM**:
- Complex Lean 4 problems with no obvious solution
- Need validation from multiple sources
- Exploring different proof strategies
- Discovering Mathlib theorems and patterns

**When to Use Claude Code (me) Directly**:
- File editing and repository operations
- Systematic development tasks
- Build management and debugging
- Session management and documentation

## Future Enhancements (Phase 2+)

**Completed in Phase 1** (October 2025):
- ✅ Caching - SQLite with query fingerprinting
- ✅ Retry logic - Exponential backoff (3 attempts)
- ✅ Response ranking - Multi-dimensional quality scoring

**Planned for Phase 2**:
1. **Auto-training** - Automatically send Lean 4 context on first consultation
2. **Context injection** - Auto-include recent Lean errors in prompts
3. **Model Context Protocol (MCP)** - Standardized tool integration
4. **Adaptive caching** - Machine learning-based TTL optimization
5. **Response synthesis v2** - LLM-powered consensus extraction
6. **Performance analytics** - Track API cost savings, quality trends

---

**Maintainer**: James D. Longmire
**Last Updated**: 2025-10-09
**Version**: Phase 1 Enhanced (October 2025)
**Status**: Production-ready with caching, quality scoring, and retry logic

## Recent Consultations (Session 3.6)

**Path 3 Protocol Review** (October 27, 2025):
- **File**: [`consultation/path3_t1_vs_t2_review_20251027.txt`](consultation/path3_t1_vs_t2_review_20251027.txt)
- **Team Scores**: Grok 0.805, Gemini 0.62, ChatGPT 0.595 (avg: 0.673)
- **Decision**: NO-GO (below 0.70 threshold) but very close
- **Critical Gaps Identified**: Error budget missing, no simulation, predictions unclear
- **Resolution**: All gaps addressed in Session 3.6 (QuTiP notebook + error budget created)
- **Next**: Re-submit for review with expected quality >0.75

See [`../Session_Log/Session_3.6.md`](../Session_Log/Session_3.6.md) for full details on gap remediation.

---
