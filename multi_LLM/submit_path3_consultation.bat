@echo off
REM Path 3 Multi-LLM Consultation Submission Script (Windows)
REM
REM This script submits the Path 3 protocol review request to the multi-LLM team
REM for validation before applying for enhanced IBM Quantum access.
REM
REM Date: October 27, 2025
REM Author: James D. (JD) Longmire (via Claude Code)

echo ==============================================================================
echo Path 3 Protocol Multi-LLM Consultation Submission
echo ==============================================================================
echo.

REM Check if consultation request exists
if not exist "multi_LLM\consultation\path3_protocol_review_request.md" (
    echo ERROR: Consultation request not found!
    echo Expected: multi_LLM\consultation\path3_protocol_review_request.md
    exit /b 1
)

echo Consultation Request: multi_LLM\consultation\path3_protocol_review_request.md
echo.

REM Build the query
set "QUERY=# Path 3 Protocol Review Request. Please review the complete Path 3 experimental protocol for testing Logic Realism Theory. Key Hypothesis: LRT Prediction T2 less than T1 (superposition states less stable), QM Prediction T2 approximately T1 (no fundamental state preference). Resource Commitment: ~120 hours quantum time. Documents: theory/predictions/T1_vs_T2_Protocol.md, scripts/path3_t1_vs_t2/, multi_LLM/consultation/path3_protocol_review_request.md. Provide: Overall Assessment score 0-1, Critical Issues, Suggested Improvements, Resource Assessment, Prediction Clarity, Go/No-Go Recommendation. Decision Threshold: Quality score greater than or equal to 0.70 required to proceed."

echo Submitting to multi-LLM team (Grok-3, GPT-4, Gemini-2.0)...
echo.

REM Submit via enhanced_llm_bridge.py
python multi_LLM\enhanced_llm_bridge.py --query "%QUERY%" --mode review --models all --output full > "multi_LLM\consultation\path3_protocol_review_results_%date:~-4,4%%date:~-10,2%%date:~-7,2%_%time:~0,2%%time:~3,2%%time:~6,2%.txt" 2>&1

if %ERRORLEVEL% equ 0 (
    echo.
    echo ==============================================================================
    echo Success! Consultation submitted successfully!
    echo.
    echo Results saved to: multi_LLM\consultation\path3_protocol_review_results_*.txt
    echo.
    echo Next Steps:
    echo   1. Review results for quality scores and consensus
    echo   2. If quality score greater than or equal to 0.70: Proceed with enhanced access application
    echo   3. If quality score less than 0.70: Revise protocol based on feedback
    echo ==============================================================================
) else (
    echo.
    echo ==============================================================================
    echo Error! Consultation submission failed (exit code: %ERRORLEVEL%^)
    echo.
    echo Possible issues:
    echo   - API keys not configured (.env file missing?^)
    echo   - Network connectivity issues
    echo   - Rate limiting
    echo.
    echo Check: python multi_LLM\enhanced_llm_bridge.py --health-check
    echo ==============================================================================
)
