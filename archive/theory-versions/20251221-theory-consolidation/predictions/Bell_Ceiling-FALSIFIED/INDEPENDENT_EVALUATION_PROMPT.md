# Independent Evaluation Prompt: Bell Ceiling Pre-Registration

**Purpose**: Request independent verification of Bell Ceiling prediction materials before pre-registration submission.

**Context**: This is a pre-registration for a quantum computing experiment to test Logic Realism Theory (LRT), which predicts a ceiling on Bell test violations below the standard quantum mechanical Tsirelson bound.

---

## Background

**Logic Realism Theory (LRT)** proposes that quantum mechanics emerges from logical consistency constraints (the Three Fundamental Laws of Logic: Identity, Non-Contradiction, Excluded Middle). One testable prediction is that Bell test CHSH measurements should show an intrinsic ceiling below the Tsirelson bound due to unavoidable logical costs of measurement.

**Prediction**:
- Standard QM: S_max = 2√2 ≈ 2.828 (Tsirelson bound)
- LRT: S_max ≈ 2.71 ± 0.01 (4.1% reduction)

**This experiment** would test this prediction via zero-noise extrapolation of CHSH measurements on IonQ Aria or Quantinuum H2.

---

## Your Task

Please conduct an **independent, critical evaluation** of the pre-registration materials to identify any:
1. **Statistical errors** or miscalculations
2. **Internal inconsistencies** between documents
3. **Overclaims** or misleading statements
4. **Missing information** required for pre-registration
5. **Methodological flaws** in the experimental design
6. **Computational errors** in notebooks
7. **Logical gaps** in the theoretical derivation

**Be brutally honest.** This is the last check before permanent pre-registration. Finding errors now is valuable.

---

## Key Artifacts to Review

### 1. Primary Pre-Registration Document
**File**: `theory/predictions/Bell_Ceiling/protocol_lrt_bell.yaml`
- Formatted for AsPredicted.org submission
- Contains: hypotheses, methods, analysis plan, decision rules
- **Check**: Internal consistency, statistical justifications, falsification criteria

### 2. Executed Computational Notebooks
**Notebook 08**: `notebooks/Logic_Realism/08_Bell_Anomaly_Modeling.ipynb`
- Purpose: Derive geometric factor α = 3/4
- **Check**: All cells executed? Derivation logic sound? Results match protocol?

**Notebook 09**: `notebooks/Logic_Realism/09_Bell_Ceiling_QuTiP_Validation.ipynb`
- Purpose: QuTiP simulation validation of predictions
- **Check**: All cells executed? Tsirelson bound reproduced? Statistical significance calculation (Cell 21) correct?

### 3. Experimental Protocol
**File**: `theory/predictions/Bell_Ceiling/Bell_Ceiling_Protocol.md` (12,000 words)
- Complete experimental design, platform selection, error budget
- **Check**: Platform justifications, shot allocation, error budget calculations, resource requirements

### 4. Theoretical Derivation
**File**: `theory/predictions/Bell_Ceiling/Alpha_Derivation_Results.md`
- Derivation of α geometric factor via three approaches
- **Check**: Mathematical rigor, physical interpretation, connection to η parameter

### 5. Tracking Documents
**File**: `theory/predictions/Bell_Ceiling/README.md`
- Status tracking, file inventory, timeline
- **Check**: Claims accurate? Status markers consistent with actual deliverables?

**File**: `theory/predictions/Bell_Ceiling/PRE_REGISTRATION_SANITY_CHECK.md`
- Internal sanity check (v2) conducted before your evaluation
- **Check**: Did our sanity check miss anything?

### 6. Previous Error Documentation
**File**: `theory/predictions/Bell_Ceiling/SANITY_CHECK_RESULTS.md`
- First sanity check and cross-reference with T2/T1 lessons learned
- Context: We already found and corrected an 8.5σ → 4.1σ overclaim

**File**: `theory/predictions/T2-T1/LESSONS_LEARNED_T2_T1_PREDICTION.md`
- Documents a previous baseline assumption error in T2/T1 prediction
- **Check**: Did we repeat similar mistakes in Bell Ceiling?

---

## Specific Verification Checklist

### A. Notebook Execution Verification

Check both notebooks are fully executed using this Python verification:

```python
import json
for nb_path in ['notebooks/Logic_Realism/08_Bell_Anomaly_Modeling.ipynb',
                'notebooks/Logic_Realism/09_Bell_Ceiling_QuTiP_Validation.ipynb']:
    nb = json.load(open(nb_path, 'r', encoding='utf-8'))
    code = [c for c in nb['cells'] if c.get('cell_type') == 'code']
    outs = [c for c in code if c.get('outputs')]
    print(f'{nb_path}: {len(outs)}/{len(code)} cells with outputs')
```

**Expected**: Both notebooks should show all code cells have outputs.

### B. Statistical Claims Consistency

Check for any remaining overclaims:

```bash
grep -r "8\.5.*σ\|8\.5.*sigma" theory/predictions/Bell_Ceiling/*.md theory/predictions/Bell_Ceiling/*.yaml | grep -v "98.5" | grep -v "Rigetti" | grep -v "SANITY_CHECK" | grep -v "EVALUATION_PROMPT"
```

Verify 4.1σ appears in key documents:

```bash
grep "4\.1" theory/predictions/Bell_Ceiling/README.md theory/predictions/Bell_Ceiling/Bell_Ceiling_Protocol.md theory/predictions/Bell_Ceiling/protocol_lrt_bell.yaml
```

**Expected**:
- No "8.5σ" references (we corrected this overclaim)
- "4.1σ" or "4.14σ" should appear in all key documents

### C. Key Numbers Match Notebooks

Extract from **Notebook 09, Cell 21** (significance calculation):
- Should show: Significance ≈ 4.14σ with N=10,000 shots per correlation
- Formula: Δ / (√2 × δS) where Δ = 0.117, δS = 0.02

**Check protocol_lrt_bell.yaml line ~114** matches this calculation.

Extract from **Notebook 09, Cell 1** (LRT prediction):
- Tsirelson: 2.828427
- LRT: 2.711277
- Reduction: 4.14%

**Check these values appear correctly in**:
- README.md
- Bell_Ceiling_Protocol.md
- protocol_lrt_bell.yaml
- Alpha_Derivation_Results.md

### D. Error Budget Verification

**From Bell_Ceiling_Protocol.md Section 7** (Error Budget):
- Systematic errors: ±0.011
- Statistical errors: ±0.018
- Total: ±0.021 (should be √(0.011² + 0.018²))

**Verify**:
```python
import math
systematic = 0.011
statistical = 0.018
total = math.sqrt(systematic**2 + statistical**2)
print(f"Total uncertainty: {total:.3f}")  # Should be 0.021
```

### E. Shot Budget Verification

**From protocol_lrt_bell.yaml**:
- 10,000 shots per correlation per noise level
- 4 correlations (CHSH terms)
- 5 noise levels
- Total: Should be 200,000 shots

**IonQ Aria cost**: 200,000 × $0.00035 = $70 (verify)

### F. Platform Requirements

**From executed notebook**: Signal is 4.14% (0.117/2.828)

**Minimum gate fidelity** (from Bell_Ceiling_Protocol.md):
- Should be >99.4% (derived from error budget)
- IBM Quantum (99.5%): Marked "MARGINAL"
- IonQ Aria (99.8%): Marked "GOOD"
- Quantinuum H2 (99.9%): Marked "EXCELLENT"

**Check**: Do these fidelities make sense given the 4.14% signal?

### G. Falsification Criterion

**From protocol_lrt_bell.yaml** (decision rules):
- If S₀ > 2.77: Reject LRT (falsified)
- If S₀ < 2.74: Support LRT
- If 2.74 < S₀ < 2.77: Inconclusive

**Check**:
- Is 2.77 reasonable? (It's midpoint between 2.71 and 2.828)
- Are the boundaries symmetric?
- Is there margin for measurement uncertainty?

---

## Critical Questions to Answer

1. **Notebook Execution**: Are both notebooks fully executed with all outputs present?

2. **Statistical Accuracy**: Is the 4.1σ significance claim correct?
   - Check Notebook 09 Cell 21 calculation
   - Verify formula: σ = Δ / (√2 × δS) not σ = Δ / δS

3. **Overclaim Detection**: Are there any remaining exaggerated claims?
   - Any "8.5σ" references? (Should be none)
   - Any "99.8% fidelity required" claims? (Should be "99.4%")
   - Any "highly significant" without quantification?

4. **Internal Consistency**: Do all documents cite the same numbers?
   - Tsirelson bound: 2.828 or 2.828427?
   - LRT prediction: 2.71 or 2.711?
   - Significance: 4.1σ or 4.14σ?

5. **Baseline Verification**: Is the Tsirelson bound (2√2 ≈ 2.828) cited correctly?
   - Check against Tsirelson (1980) paper
   - Verify Notebook 09 Cell 5 reproduces it exactly

6. **Methodological Soundness**: Is the zero-noise extrapolation approach valid?
   - 5 noise levels sufficient?
   - Linear/quadratic/exponential fits appropriate?
   - Can extrapolation separate intrinsic from environmental effects?

7. **Transparency**: Are limitations honestly acknowledged?
   - IBM Q marked "marginal" not "sufficient"?
   - Inconclusive region (2.74-2.77) acknowledged?
   - Type II error risk with lower fidelity platforms?

8. **Pre-registration Completeness**: Does protocol_lrt_bell.yaml contain all required elements?
   - Hypothesis (H1 vs H0)
   - Method (detailed enough to replicate)
   - Analysis plan (pre-committed, no flexibility)
   - Decision rules (falsification criteria clear)
   - Data management (storage, availability)
   - Conflict of interest (declared)

---

## Evaluation Output Format

Please provide:

### 1. Executive Summary
- Overall assessment (PASS / CONDITIONAL PASS / FAIL)
- Critical issues found (if any)
- Recommendation (proceed / revise / reject)

### 2. Detailed Findings

For each check (A-G above):
- ✅ PASS: Brief confirmation
- ⚠️ WARNING: Concern but not blocking
- ❌ FAIL: Critical error requiring fix

### 3. Specific Errors

List any:
- **Statistical errors** with correct calculation
- **Inconsistencies** with specific line numbers
- **Overclaims** with evidence
- **Missing information** with what's needed

### 4. Strengths

What did we do well? (Honest assessment, not cheerleading)

### 5. Overall Recommendation

Should we:
- **PROCEED** with pre-registration as-is
- **REVISE** specific items (list them)
- **REJECT** pre-registration (fundamental flaws)

---

## Context: Previous Errors Found

**For calibration**, here are errors we already found and corrected:

1. **8.5σ overclaim** (13 instances across 5 documents):
   - Claimed: 8.5σ with 10K shots
   - Actual: 4.14σ with 10K shots
   - Error: Wrong formula (used 0.014 instead of 0.0283 for combined uncertainty)
   - Status: CORRECTED

2. **Fidelity requirement** (3 instances):
   - Claimed: >99.8% required
   - Actual: >99.4% required (from error budget)
   - Status: CORRECTED (but 99.8% still recommended)

3. **Notebook execution status**:
   - Initially claimed: "validation complete"
   - Actual: Notebooks had zero outputs (not executed)
   - Status: CORRECTED (both notebooks now fully executed)

**Your job**: Find anything else we missed.

---

## Notes

- **Be skeptical**: Assume we made mistakes until proven otherwise
- **Check calculations**: Don't trust claims, verify in notebooks
- **Compare sources**: If documents disagree, notebook is ground truth
- **Flag ambiguity**: Pre-registration must be unambiguous
- **No cheerleading**: We want critical review, not validation

**Repository location**: `logic-realism-theory/`

**Primary contact**: README.md should have ORCID and contact info

---

## Deliverable

Please save your evaluation report as:
`theory/predictions/Bell_Ceiling/INDEPENDENT_EVALUATION_REPORT.md`

**Thank you for your critical review!**

---

**Prompt Created**: 2025-11-05
**For**: Independent evaluation before AsPredicted.org pre-registration submission
**Version**: 1.0
