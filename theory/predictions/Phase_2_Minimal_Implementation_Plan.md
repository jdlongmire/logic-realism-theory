# Phase 2: Minimal Implementation Plan - Logical State-Dependent Error Test

**Date Created:** 2025-10-26
**Status:** Ready for Implementation
**Parent Design:** `Logical_State_Dependent_Error_Test_Design.md`
**Multi-LLM Review:** Quality 0.69, Unanimous "Proceed" (2025-10-26)

---

## Overview

This document defines the minimal implementation required to validate the statistical model before proceeding to full-scale simulation (Phase 3).

**Critical Success Criterion:** VIF = 1 (verified computationally)

**Key Principle:** Validate regression assumptions with minimal data before investing in N=10,000 runs.

---

## Phase 2 Objectives

1. **Implement minimal T2 characterization** (N=100 samples)
2. **Verify VIF = 1 mathematically and computationally**
3. **Test residual analysis framework**
4. **Confirm baseline model fit quality (R² for QM prediction)**
5. **Address team feedback** (GST prep, crosstalk check, drift monitoring)

**NOT in Phase 2:**
- ❌ Full N=10,000 simulation (that's Phase 3)
- ❌ Hardware implementation (computational only)
- ❌ Full GST (just verify framework compatibility)

---

## Implementation Steps

### Step 1: Simulation Environment Setup (30 minutes)

**Files to create:**
- `notebooks/quantum_simulations/phase2_minimal_implementation.ipynb`

**Environment:**
```python
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from scipy.stats import linregress
from statsmodels.stats.outliers_influence import variance_inflation_factor
```

**Simulated Qubit Parameters:**
```python
# Realistic IBM qubit parameters
T1 = 100e-6  # seconds (100 μs amplitude damping)
T_phi = 150e-6  # seconds (pure dephasing)
T2 = 1 / (1/T1 + 1/T_phi)  # ~60 μs

# Duration sweep
T_min = 0  # μs
T_max = 5 * T2  # ~300 μs (5 T2 times)
N_points = 20  # Minimal sampling
```

**Success Criterion:** Environment runs without errors

---

### Step 2: Baseline T2 Characterization (1 hour)

**Goal:** Establish p_T2(T) baseline prediction from standard QM

**Protocol:**
1. Prepare |+⟩ state (X gate on |0⟩)
2. Wait duration T (varying from 0 to 5*T2)
3. Measure in X basis
4. Repeat N=100 times per T value

**Simulation:**
```python
def simulate_ramsey(T, T2, N_shots=100):
    """
    Simulate Ramsey experiment with T2 decoherence.

    Returns:
        p_log_B: Probability of measuring |−⟩ (logical "wrong" state)
    """
    # QM prediction for |+⟩ state after time T
    p_minus_theory = (1 - np.exp(-T / T2)) / 2

    # Sample with shot noise
    counts_minus = np.random.binomial(N_shots, p_minus_theory)
    p_log_B_observed = counts_minus / N_shots

    return p_log_B_observed, p_minus_theory
```

**Data Collection:**
```python
results = []
for T in T_sweep:
    p_obs, p_theory = simulate_ramsey(T, T2, N_shots=100)
    results.append({
        'T': T,
        'p_observed': p_obs,
        'p_predicted': p_theory
    })

df_baseline = pd.DataFrame(results)
```

**Verification:**
- Fit exponential: p(T) = A * (1 - exp(-T/T2_fit))
- Check: T2_fit ≈ T2_true (within 10%)
- Visualize: Plot observed vs predicted

**Success Criterion:** T2 recovered to within ±10% of input value

---

### Step 3: VIF Validation (Critical!)

**Mathematical Proof (reference):**

For single-predictor model:
```
Δp(T) = β_LRT * T + ε

VIF = 1 / (1 - R²) where R² is from regressing T on... nothing (no other predictors)

Therefore: VIF = 1 (by definition)
```

**Computational Verification:**

```python
from statsmodels.stats.outliers_influence import variance_inflation_factor

# Prepare data
X = df_baseline[['T']].values  # Predictor matrix (single column)
y = df_baseline['p_observed'] - df_baseline['p_predicted']  # Residuals

# Calculate VIF for T
vif_T = variance_inflation_factor(X, 0)  # Index 0 for first (only) predictor

print(f"VIF(T) = {vif_T:.6f}")
assert abs(vif_T - 1.0) < 1e-6, f"VIF should be 1.0, got {vif_T}"
```

**Why This Matters:**

Session 2.5 had VIF = ∞ due to A/B circuit comparison. This design MUST have VIF = 1 to be valid.

**Success Criterion:** VIF = 1.000000 (to 6 decimal places)

---

### Step 4: Residual Analysis Framework (1 hour)

**Goal:** Verify that residual regression can detect artificial LRT signal

**Procedure:**

1. **Null Case (QM only):**
   ```python
   # Residuals from pure QM simulation
   Δp_null = df_baseline['p_observed'] - df_baseline['p_predicted']

   # Regression
   slope_null, intercept_null, r_value, p_value, std_err = linregress(
       df_baseline['T'], Δp_null
   )

   print(f"Null case: β_LRT = {slope_null:.6e} ± {std_err:.6e}")
   print(f"p-value: {p_value:.3f}")
   ```

   **Expected:** β_LRT ≈ 0, p-value > 0.05 (no LRT effect)

2. **Artificial LRT Signal:**
   ```python
   # Add synthetic LRT error: p_LRT = 0.02 * (T / T2)
   p_LRT_synthetic = 0.02 * (df_baseline['T'] / T2)
   df_baseline['p_observed_LRT'] = df_baseline['p_predicted'] + p_LRT_synthetic

   # Add shot noise
   df_baseline['p_observed_LRT'] += np.random.normal(0, 0.01, len(df_baseline))

   # Residuals
   Δp_LRT = df_baseline['p_observed_LRT'] - df_baseline['p_predicted']

   # Regression
   slope_LRT, intercept_LRT, r_value, p_value, std_err = linregress(
       df_baseline['T'], Δp_LRT
   )

   print(f"LRT case: β_LRT = {slope_LRT:.6e} ± {std_err:.6e}")
   print(f"p-value: {p_value:.3e}")
   ```

   **Expected:** β_LRT > 0, p-value < 0.001 (detects LRT effect)

**Success Criterion:**
- Null case: p > 0.05
- LRT case: p < 0.001

---

### Step 5: Baseline Model Quality (30 minutes)

**Goal:** Verify QM prediction fits data well (before looking for deviations)

**Metrics:**

1. **R² (coefficient of determination):**
   ```python
   from sklearn.metrics import r2_score

   R2 = r2_score(df_baseline['p_observed'], df_baseline['p_predicted'])
   print(f"R² = {R2:.4f}")
   ```

   **Expected:** R² > 0.95 (QM prediction explains >95% of variance)

2. **Residual Normality:**
   ```python
   from scipy.stats import shapiro

   stat, p_value = shapiro(Δp_null)
   print(f"Shapiro-Wilk test: p = {p_value:.3f}")
   ```

   **Expected:** p > 0.05 (residuals are normally distributed)

3. **Residual Mean:**
   ```python
   print(f"Mean(Δp) = {np.mean(Δp_null):.6e}")
   ```

   **Expected:** |Mean| < 0.001 (no systematic bias)

**Success Criterion:**
- R² > 0.95
- Residuals pass normality test
- Mean residual ≈ 0

---

### Step 6: Team Feedback Integration (1 hour)

#### 6.1 Gate Set Tomography (GST) Preparation

**Team Concern:** RB gives average error, GST gives gate-specific errors

**Phase 2 Action:**
- ✅ Verify simulation can track gate-level fidelities
- ✅ Add placeholder for GST noise model (not full GST yet)
- ❌ NOT implementing full GST (that's Phase 3 robustness check)

**Code Addition:**
```python
# Placeholder for gate-specific errors (Phase 3)
gate_fidelities = {
    'X': 0.9995,  # X gate fidelity
    'H': 0.9993,  # Hadamard fidelity
    'measure_X': 0.998  # X-basis measurement fidelity
}

# Phase 2: Just verify we can incorporate this
# Phase 3: Use GST-calibrated values
```

#### 6.2 Crosstalk Monitoring

**Team Concern:** Multi-qubit crosstalk could confound results

**Phase 2 Action:**
- ✅ Single-qubit simulation (no crosstalk)
- ✅ Document that Phase 3 should check idle qubit states
- ❌ NOT simulating full multi-qubit system yet

**Documentation:**
```python
# Phase 2: Single qubit only (no crosstalk)
# Phase 3: Check neighboring qubits remain in |0⟩ during Ramsey
```

#### 6.3 Frequency Drift Tracking

**Team Concern:** Qubit frequency drifts could mimic LRT signal

**Phase 2 Action:**
- ✅ Add timestamp to each simulation run
- ✅ Include "drift check" placeholder (constant frequency in Phase 2)
- ❌ NOT simulating drift (that's Phase 3 robustness)

**Code Addition:**
```python
import time

results.append({
    'T': T,
    'p_observed': p_obs,
    'p_predicted': p_theory,
    'timestamp': time.time(),  # For drift analysis in Phase 3
    'qubit_freq': 5.0e9  # Fixed in Phase 2, variable in Phase 3
})
```

**Success Criterion:** Framework ready for Phase 3 extensions

---

## Phase 2 Deliverables

### 1. Notebook (Primary Deliverable)
**File:** `notebooks/quantum_simulations/phase2_minimal_implementation.ipynb`

**Sections:**
1. Environment setup
2. T2 characterization (N=100)
3. VIF validation (mathematical + computational)
4. Residual analysis (null + synthetic LRT)
5. Baseline model quality (R², normality, mean)
6. Team feedback integration (placeholders)
7. Summary: Go/No-Go for Phase 3

### 2. Validation Report
**File:** `theory/predictions/Phase_2_Validation_Report.md`

**Contents:**
```markdown
# Phase 2 Validation Report

## Success Criteria Results

| Criterion | Target | Result | Pass/Fail |
|-----------|--------|--------|-----------|
| T2 Recovery | ±10% | ±X% | ✓/✗ |
| VIF | 1.000000 | X.XXXXXX | ✓/✗ |
| Null β_LRT | p > 0.05 | p = X.XXX | ✓/✗ |
| LRT β_LRT | p < 0.001 | p = X.XXX | ✓/✗ |
| R² | > 0.95 | X.XX | ✓/✗ |
| Residual Normality | p > 0.05 | p = X.XXX | ✓/✗ |

## Decision: PROCEED TO PHASE 3 / REVISE PHASE 2

## Rationale:
[Explanation of results]
```

### 3. Updated Session Log
**File:** `Session_Log/Session_2.6.md` → `Session_2.7.md` (or increment)

**Include:**
- Phase 2 completion
- All validation results
- Decision to proceed (or not)
- Lessons learned

---

## Success Criteria Summary

**ALL must pass to proceed to Phase 3:**

1. ✅ **VIF = 1.000000** (to 6 decimal places) - CRITICAL
2. ✅ **T2 recovery within ±10%** (T2_fit / T2_true ∈ [0.9, 1.1])
3. ✅ **Null case:** β_LRT ≈ 0, p > 0.05
4. ✅ **LRT case:** β_LRT > 0, p < 0.001 (synthetic signal detected)
5. ✅ **R² > 0.95** (QM prediction fits well)
6. ✅ **Residual normality:** Shapiro-Wilk p > 0.05
7. ✅ **Framework ready** for GST, crosstalk, drift (placeholders in place)

**If ANY criterion fails:**
- Document failure in validation report
- Revise Phase 2 design
- Do NOT proceed to Phase 3

**If ALL pass:**
- Create Phase 3 plan (N=10,000 simulation)
- Proceed with full-scale implementation

---

## Estimated Time

**Total Phase 2 Time:** 4-5 hours

- Step 1 (Setup): 30 min
- Step 2 (T2 Characterization): 1 hour
- Step 3 (VIF Validation): 30 min
- Step 4 (Residual Analysis): 1 hour
- Step 5 (Baseline Quality): 30 min
- Step 6 (Team Feedback): 1 hour
- Documentation: 30 min

**Computational Requirements:**
- Hardware: Any laptop (N=100 is trivial)
- Runtime: <5 minutes total

---

## Risk Mitigation

### Risk 1: VIF ≠ 1.0

**Likelihood:** Very low (mathematical proof exists)
**Impact:** High (invalidates entire approach)
**Mitigation:** If VIF ≠ 1.0, re-examine data structure (likely implementation bug)

### Risk 2: T2 Recovery Fails

**Likelihood:** Low (simple exponential fit)
**Impact:** Medium (suggests simulation error)
**Mitigation:** Check simulation noise model, increase N_shots

### Risk 3: Null Case Detects False Signal

**Likelihood:** Low (pure QM simulation)
**Impact:** High (residual analysis framework broken)
**Mitigation:** Check random seed, increase trials, verify baseline subtraction

### Risk 4: LRT Case Fails to Detect Signal

**Likelihood:** Low (synthetic signal is strong)
**Impact:** Medium (suggests power analysis issue)
**Mitigation:** Increase synthetic signal strength, check noise levels

---

## Next Steps After Phase 2

### If Phase 2 Succeeds:

1. Create `Phase_3_Full_Simulation_Plan.md`
2. Scale to N=10,000 samples
3. Implement alternative functional forms (exponential, non-parametric)
4. Add robustness checks (Y-basis, GST, crosstalk, drift)
5. Statistical power analysis

### If Phase 2 Fails:

1. Document failure mode in validation report
2. Consult multi-LLM team for debugging
3. Revise Phase 2 design
4. Re-run minimal implementation
5. Do NOT proceed to Phase 3 until all criteria pass

---

## Team Consultation Integration

**Multi-LLM Review (2025-10-26):**
- Quality: 0.69
- Decision: Unanimous "Proceed"
- Key Recommendations:
  1. Use GST not just RB (planned for Phase 3)
  2. Monitor crosstalk (planned for Phase 3)
  3. Track frequency drift (planned for Phase 3)

**Phase 2 Response:**
- ✅ Framework ready for all three concerns
- ✅ Placeholders in code for Phase 3 extensions
- ✅ Single-qubit only (avoids crosstalk complexity)

---

## File Locations

**Created in Phase 2:**
- `notebooks/quantum_simulations/phase2_minimal_implementation.ipynb` (notebook)
- `theory/predictions/Phase_2_Validation_Report.md` (results)
- `Session_Log/Session_X.Y.md` (updated session log)

**References:**
- `theory/predictions/Logical_State_Dependent_Error_Test_Design.md` (parent design)
- `multi_LLM/consultation/logical_state_error_review_20251026.json` (team review)

---

**Status:** Ready for implementation
**Next Action:** Create `phase2_minimal_implementation.ipynb` notebook
**Estimated Completion:** 1 session (4-5 hours)
