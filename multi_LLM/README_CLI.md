# Multi-LLM Consultation System - CLI Usage

## Quick Start

The consultation system is now fully operational with a command-line interface.

### Basic Usage

```bash
# Auto-detect query type
python enhanced_llm_bridge.py --query "Your question here"

# Specify mode explicitly
python enhanced_llm_bridge.py --query "How to prove HasDerivAt in Lean 4?" --mode lean
python enhanced_llm_bridge.py --query "Review this section..." --mode review
python enhanced_llm_bridge.py --query "Explain Bell's theorem" --mode theory

# Get only the best response
python enhanced_llm_bridge.py --query "Your question" --output best

# Disable cache for fresh responses
python enhanced_llm_bridge.py --query "Your question" --no-cache
```

### Consultation Modes

- **`lean`**: Lean 4 proof assistance (syntax, tactics, Mathlib theorems)
- **`review`**: Peer review feedback (structure, clarity, citations)
- **`theory`**: Theory questions (derivations, explanations, physics)
- **`general`**: General queries
- **`auto`** (default): Automatically detect mode from query content

### Output Formats

- **`full`** (default): All responses with quality scores
- **`best`**: Only the highest-scoring response
- **`json`**: Machine-readable JSON output

### Utility Commands

```bash
# Check API health
python enhanced_llm_bridge.py --health-check

# View cache statistics
python enhanced_llm_bridge.py --cache-stats

# Clean up expired cache entries
python enhanced_llm_bridge.py --cleanup-cache

# Show help
python enhanced_llm_bridge.py --help
```

## Sprint 7 Integration

### For Lean Proof Guidance

```bash
cd multi_LLM
python enhanced_llm_bridge.py --query "
I'm trying to prove constraint_has_deriv_at in Lean 4:

theorem constraint_has_deriv_at (ε : ℝ) (h_pos : ε > 0) :
  HasDerivAt C (ConstraintRate ε) ε := by
  sorry

Where C(ε) = γ * ε * (1 - Real.exp(-ε/ε₀))

I need to use product rule and chain rule. What are the correct Mathlib theorems?
" --mode lean --output best
```

### For Peer Review

```bash
python enhanced_llm_bridge.py --query "
Review this theorem statement for clarity and correctness:

THEOREM D.1: The graph Laplacian H = D - A emerges as the unique natural
Hamiltonian from three independent principles...

[paste theorem text]
" --mode review
```

## Quality Scoring

Responses are automatically scored on:
- **Lean queries**: Code quality, Mathlib citations, actionability
- **Reviews**: Structure, concrete suggestions, confidence
- **Theory**: Citations, step-by-step explanation, depth

Results are sorted by quality score (0.0-1.0).

## Caching

- **Lean proofs**: Cached for 7 days
- **Peer reviews**: Cached for 1 day
- **Theory questions**: Cached for 30 days
- **General queries**: Cached for 7 days

Cache saves API calls and provides instant responses for repeated queries.

## Troubleshooting

### Unicode Errors on Windows
Fixed automatically - system reconfigures stdout to UTF-8.

### API Configuration
Ensure `api_config.json` exists with valid API keys for:
- Grok (X.AI)
- ChatGPT (OpenAI)
- Gemini (Google)

### Network Issues
System has built-in retry logic with exponential backoff (3 attempts).

---

**Last Updated**: 2025-10-10
**Status**: Fully operational ✅
