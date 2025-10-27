#!/bin/bash

# Path 3 Multi-LLM Consultation Submission Script
#
# This script submits the Path 3 protocol review request to the multi-LLM team
# for validation before applying for enhanced IBM Quantum access.
#
# Date: October 27, 2025
# Author: James D. (JD) Longmire (via Claude Code)

echo "=============================================================================="
echo "Path 3 Protocol Multi-LLM Consultation Submission"
echo "=============================================================================="
echo ""

# Check if consultation request exists
if [ ! -f "multi_LLM/consultation/path3_protocol_review_request.md" ]; then
    echo "ERROR: Consultation request not found!"
    echo "Expected: multi_LLM/consultation/path3_protocol_review_request.md"
    exit 1
fi

echo "Consultation Request: multi_LLM/consultation/path3_protocol_review_request.md"
echo ""

# Build the query from the consultation request
QUERY="# Path 3 Protocol Review Request

Please review the complete Path 3 experimental protocol for testing Logic Realism Theory.

**Key Hypothesis**:
- LRT Prediction: T2 < T1 (superposition states less stable)
- QM Prediction: T2 ≈ T1 (no fundamental state preference)

**Resource Commitment**: ~120 hours quantum time (~\$12K if purchasing)

**Documents to Review**:
1. Complete protocol: theory/predictions/T1_vs_T2_Protocol.md (986 lines)
2. Implementation scripts: scripts/path3_t1_vs_t2/ (5 files, ~39 KB)
3. Consultation request: multi_LLM/consultation/path3_protocol_review_request.md

**Critical Questions** (30 total across 6 categories):
1. Design Validation: Does T1 vs T2 comparison avoid logical equivalence trap?
2. LRT Prediction Clarity: Is T2 < T1 well-justified? What magnitude?
3. Confound Assessment: Is T2echo adequate? What about drift, readout errors?
4. Resource Optimization: Can we reduce shots, points, or backends?
5. Falsification Criteria: What constitutes clear FOR/AGAINST evidence?
6. Alternative Approaches: Should we test Path 5 (frequency shift) instead?

**For Each LLM, Please Provide**:
1. Overall Assessment (Score 0-1): Is the protocol scientifically sound?
2. Critical Issues: Any fatal flaws?
3. Suggested Improvements: How to strengthen design?
4. Resource Assessment: Over/under-allocating?
5. Prediction Clarity: Are LRT and QM predictions truly distinct?
6. Go/No-Go Recommendation: Proceed with enhanced access application?

**Decision Threshold**: Quality score ≥ 0.70 required to proceed

Please read the full consultation request for complete details and context."

echo "Submitting to multi-LLM team (Grok-3, GPT-4, Gemini-2.0)..."
echo ""

# Submit via enhanced_llm_bridge.py
python multi_LLM/enhanced_llm_bridge.py \
    --query "$QUERY" \
    --mode review \
    --models all \
    --output full \
    2>&1 | tee "multi_LLM/consultation/path3_protocol_review_results_$(date +%Y%m%d_%H%M%S).txt"

EXIT_CODE=$?

echo ""
echo "=============================================================================="

if [ $EXIT_CODE -eq 0 ]; then
    echo "✅ Consultation submitted successfully!"
    echo ""
    echo "Results saved to: multi_LLM/consultation/path3_protocol_review_results_*.txt"
    echo ""
    echo "Next Steps:"
    echo "  1. Review results for quality scores and consensus"
    echo "  2. If quality score ≥ 0.70: Proceed with enhanced access application"
    echo "  3. If quality score < 0.70: Revise protocol based on feedback"
else
    echo "❌ Consultation submission failed (exit code: $EXIT_CODE)"
    echo ""
    echo "Possible issues:"
    echo "  - API keys not configured (.env file missing?)"
    echo "  - Network connectivity issues"
    echo "  - Rate limiting"
    echo ""
    echo "Check multi_LLM/enhanced_llm_bridge.py --health-check"
fi

echo "=============================================================================="
