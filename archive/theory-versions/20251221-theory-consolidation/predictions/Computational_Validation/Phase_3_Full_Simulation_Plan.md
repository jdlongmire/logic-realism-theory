# Phase 3: Full-Scale Simulation Plan - Logical State-Dependent Error Test

**Date Created:** 2025-10-26
**Status:** Ready for Implementation
**Parent Design:** `Logical_State_Dependent_Error_Test_Design.md`
**Phase 2 Results:** VIF = 1.0 verified, all success criteria passed

---

## Overview

Phase 3 scales the validated Phase 2 framework to full N=10,000 simulation with comprehensive robustness checks and alternative functional forms.

**Goal:** Generate publication-quality results for LRT's "logical state-dependent error" prediction

**Key Innovation from Phase 2:** VIF = 1 (single-predictor residual analysis) eliminates multicollinearity

---

## Phase 3 Objectives

1. **Scale to N=10,000** - Statistical power for detecting p_LRT ≥ 0.01 (1% excess error)
2. **Alternative functional forms** - Test exponential, polynomial, non-parametric models
3. **Robustness checks** - Y-basis, GST, crosstalk, frequency drift
4. **Power analysis** - Validate detection threshold experimentally
5. **Sensitivity analysis** - Parameter variations (T1, T2, qubit type)
6. **Statistical rigor** - Bootstrap confidence intervals, permutation tests

---

## Implementation Steps

### Step 1: Scaled Baseline Simulation (2 hours)

**Scale parameters from Phase 2:**

| Parameter | Phase 2 (Minimal) | Phase 3 (Full) | Reason |
|-----------|-------------------|----------------|--------|
| N_shots | 100 | 10,000 | Reduce shot noise from 10% to 1% |
| N_points | 20 | 50 | Higher resolution for functional form testing |
| T_max | 5*T2 | 10*T2 | Extend to see long-time behavior |
| Duration sweep | Linear | Logarithmic + Linear | Better sampling at short times |

**Duration sampling strategy:**
```python
# Logarithmic sampling for short times (where most decoherence happens)
T_log = np.logspace(np.log10(1e-6), np.log10(T2), 25)  # 1 μs to T2

# Linear sampling for long times
T_lin = np.linspace(T2, 10*T2, 25)  # T2 to 10*T2

# Combined sweep
T_sweep = np.sort(np.concatenate([T_log, T_lin[1:]]))  # Remove duplicate at T2
N_points = len(T_sweep)  # 49 points total
```

**Computational requirements:**
- Shots: N_points * N_shots = 49 * 10,000 = 490,000 measurements
- Runtime: ~10-15 minutes (depending on hardware)
- Memory: ~500 MB (storing full dataset)

**Success criteria:**
- T2 recovery within ±5% (tighter than Phase 2's ±10%)
- VIF = 1.000000 (must remain 1 at scale)
- R² > 0.98 (higher threshold than Phase 2's 0.95)

---

### Step 2: Alternative Functional Forms (1.5 hours)

**Why test alternatives:** Linear model (β_LRT * T) may be too restrictive. LRT might predict non-linear excess error.

**Models to test:**

#### 2.1 Linear (Baseline)
```
Δp(T) = β_LRT * T + ε
```
**Rationale:** Simplest model, already validated in Phase 2

#### 2.2 Exponential Decay
```
Δp(T) = A * (1 - exp(-T / τ_LRT)) + ε
```
**Rationale:** If LRT error saturates (like T2 decoherence), exponential may fit better

**Parameters:**
- A: Asymptotic excess error
- τ_LRT: LRT timescale (may differ from T2)

#### 2.3 Power Law
```
Δp(T) = β_LRT * T^α + ε
```
**Rationale:** If LRT error accumulates non-linearly with time

**Parameters:**
- α: Power (α=1 is linear, α<1 is sublinear, α>1 is superlinear)

#### 2.4 Non-Parametric (Smoothing Spline)
```python
from scipy.interpolate import UnivariateSpline

# Fit spline to residuals
spline = UnivariateSpline(T_sweep, Δp, s=smoothing_factor)
Δp_fit = spline(T_sweep)
```
**Rationale:** Model-free approach, captures any functional form

**Model comparison metrics:**
- **AIC (Akaike Information Criterion):** AIC = 2k - 2ln(L)
- **BIC (Bayesian Information Criterion):** BIC = k*ln(n) - 2ln(L)
- **Adjusted R²:** R²_adj = 1 - (1 - R²) * (n - 1) / (n - k - 1)

**Best model:** Lowest AIC/BIC with highest R²_adj

**Implementation:**
```python
models = {
    'linear': lambda T, beta: beta * T,
    'exponential': lambda T, A, tau: A * (1 - np.exp(-T / tau)),
    'power': lambda T, beta, alpha: beta * T**alpha
}

results = {}
for name, func in models.items():
    popt, pcov = curve_fit(func, T_sweep, Δp)
    residuals = Δp - func(T_sweep, *popt)
    sse = np.sum(residuals**2)
    n = len(T_sweep)
    k = len(popt)  # Number of parameters

    AIC = 2*k - 2*np.log(likelihood(sse, n))
    BIC = k*np.log(n) - 2*np.log(likelihood(sse, n))

    results[name] = {'AIC': AIC, 'BIC': BIC, 'params': popt}

# Select best model
best_model = min(results, key=lambda x: results[x]['AIC'])
```

---

### Step 3: Robustness Checks (3 hours)

#### 3.1 Y-Basis Measurement (30 min)

**Phase 2:** X-basis only (measure |+⟩ state)
**Phase 3:** Add Y-basis measurement

**Why:** Verify excess error is not basis-dependent artifact

**Protocol:**
1. Initialize |+⟩ (same as Phase 2)
2. Wait duration T
3. **Measure in Y-basis** (instead of X-basis)
4. Expected (QM): p(|−_Y⟩) ≈ p_T2 (same decoherence)
5. Expected (LRT): If LRT is real, should see similar excess p_LRT in Y-basis

**Statistical test:**
```python
# Compare X-basis vs Y-basis excess error
p_LRT_X = slope_X  # From X-basis regression
p_LRT_Y = slope_Y  # From Y-basis regression

# Test if p_LRT_X ≈ p_LRT_Y (should be similar if LRT is basis-independent)
t_stat, p_value = scipy.stats.ttest_ind(residuals_X, residuals_Y)

if p_value > 0.05:
    print("✓ Basis-independent (LRT excess error same in X and Y)")
else:
    print("✗ Basis-dependent artifact (excess error differs by basis)")
```

**Success criterion:** p_LRT_X ≈ p_LRT_Y (within error bars)

#### 3.2 GST-Calibrated Gate Errors (1 hour)

**Phase 2:** Placeholder gate fidelities
**Phase 3:** Use realistic GST-calibrated error rates

**Realistic IBM gate errors** (from literature):
- H gate: F = 0.9995 (0.05% error)
- X gate: F = 0.9993 (0.07% error)
- Measurement (X-basis): F = 0.998 (0.2% error)

**Depolarizing channel model:**
```python
def apply_gate_error(state, fidelity):
    """Apply depolarizing noise to quantum state."""
    p_error = 1 - fidelity
    if np.random.rand() < p_error:
        # Apply random Pauli error (X, Y, or Z)
        error = np.random.choice(['X', 'Y', 'Z'])
        state = apply_pauli(state, error)
    return state
```

**Verification:**
- Run baseline characterization WITH gate errors
- Compare T2_fit vs T2_true (should still recover within ±5%)
- Check if gate errors wash out LRT signal (if so, need higher precision hardware)

**Success criterion:** T2 recovery with gate errors within ±10%, residual analysis still works

#### 3.3 Crosstalk Monitoring (1 hour)

**Phase 2:** Single qubit only
**Phase 3:** Simulate 2-qubit system, monitor idle qubit

**Setup:**
- Qubit 0: Active (Ramsey experiment)
- Qubit 1: Idle (should stay in |0⟩)

**Crosstalk model:**
```python
def simulate_crosstalk(state_0, state_1, crosstalk_strength=0.01):
    """
    Apply crosstalk: Idle qubit picks up noise from active qubit.

    Args:
        state_0: Active qubit state
        state_1: Idle qubit state (should be |0⟩)
        crosstalk_strength: Coupling strength (0.01 = 1% leakage)

    Returns:
        state_0, state_1 (possibly with crosstalk-induced errors)
    """
    # With probability crosstalk_strength, idle qubit flips
    if np.random.rand() < crosstalk_strength:
        state_1 = apply_pauli(state_1, 'X')  # Flip idle qubit
    return state_0, state_1
```

**Monitoring:**
```python
# After Ramsey sequence, measure idle qubit
p_idle_flipped = counts_1 / N_shots

if p_idle_flipped < 0.05:  # Less than 5% crosstalk
    print("✓ Crosstalk negligible")
else:
    print(f"⚠ Crosstalk detected: {p_idle_flipped*100:.1f}% idle qubit errors")
```

**Success criterion:** Idle qubit error < 5%, or correct for crosstalk in baseline

#### 3.4 Frequency Drift Tracking (30 min)

**Phase 2:** Constant qubit frequency (5 GHz)
**Phase 3:** Simulate realistic frequency drift

**Drift model:**
```python
def simulate_frequency_drift(qubit_freq_0, drift_rate=1e3):
    """
    Simulate slow frequency drift over time.

    Args:
        qubit_freq_0: Initial frequency (Hz)
        drift_rate: Drift rate (Hz/s), typical ~1 kHz/s

    Returns:
        qubit_freq(t): Frequency as function of time
    """
    return lambda t: qubit_freq_0 + drift_rate * t
```

**Time-series analysis:**
```python
# Record timestamp and frequency for each measurement
df['timestamp_rel'] = df['timestamp'] - df['timestamp'].min()
df['qubit_freq'] = 5.0e9 + 1e3 * df['timestamp_rel']  # 1 kHz/s drift

# Check if frequency drift correlates with residuals
correlation = np.corrcoef(df['qubit_freq'], df['residual'])[0, 1]

if abs(correlation) < 0.3:  # Weak correlation
    print("✓ Frequency drift not confounding LRT signal")
else:
    print(f"⚠ Frequency drift may confound (correlation = {correlation:.2f})")
    print("  Recommendation: Interleave measurements or correct for drift")
```

**Success criterion:** |correlation| < 0.3, or include drift term in regression

---

### Step 4: Power Analysis (1 hour)

**Goal:** Experimentally validate that N=10,000 can detect p_LRT ≥ 0.01

**Procedure:**

1. **Simulate range of effect sizes:**
```python
effect_sizes = [0.005, 0.01, 0.02, 0.05, 0.10]  # 0.5% to 10% excess error

for p_LRT_injected in effect_sizes:
    # Add synthetic LRT signal
    p_observed = p_predicted + p_LRT_injected * (T / T2)

    # Regression
    slope, _, _, p_value, _ = linregress(T, p_observed - p_predicted)

    # Record power (fraction of times p < 0.05)
    detected = p_value < 0.05
    power[p_LRT_injected].append(detected)

# Calculate power for each effect size
power_curve = {eff: np.mean(power[eff]) for eff in effect_sizes}
```

2. **Plot power curve:**
```python
plt.plot(effect_sizes, [power_curve[eff] for eff in effect_sizes], 'o-')
plt.axhline(0.80, linestyle='--', label='80% power')
plt.xlabel('LRT Effect Size p_LRT')
plt.ylabel('Statistical Power (1 - β)')
plt.title('Power Analysis: N=10,000 shots')
```

3. **Minimum Detectable Effect (MDE):**
```python
# Effect size where power = 0.80
MDE = effect_sizes[np.argmin(np.abs(np.array([power_curve[eff] for eff in effect_sizes]) - 0.80))]
print(f"Minimum Detectable Effect: p_LRT ≥ {MDE:.3f} ({MDE*100:.1f}%)")
```

**Success criterion:** MDE ≤ 0.01 (can detect 1% excess error with 80% power)

---

### Step 5: Sensitivity Analysis (1.5 hours)

**Goal:** Test if results are robust to parameter variations

**Parameters to vary:**

#### 5.1 T1 Variation (Amplitude Damping)
```python
T1_values = [50e-6, 100e-6, 200e-6]  # 50 μs to 200 μs

for T1 in T1_values:
    T2 = 1 / (1/T1 + 1/T_phi)  # Recalculate T2
    # Run full analysis
    # Record p_LRT estimate
```

**Expected:** p_LRT / T2 should be constant (relative effect)

#### 5.2 T_phi Variation (Pure Dephasing)
```python
T_phi_values = [100e-6, 150e-6, 300e-6]  # 100 μs to 300 μs
```

**Expected:** p_LRT depends on T2 (total coherence), not T1/T_phi ratio

#### 5.3 Qubit Type (Architecture Dependence)
```python
qubit_params = {
    'IBM_superconducting': {'T1': 100e-6, 'T_phi': 150e-6},
    'IonQ_trapped_ion': {'T1': 1e-3, 'T_phi': 2e-3},  # Much longer coherence
    'Rigetti_superconducting': {'T1': 80e-6, 'T_phi': 100e-6}
}
```

**Test:** Does p_LRT scale with qubit quality (T2)?

**Success criterion:** Consistent p_LRT/T2 ratio across qubit types (±20%)

---

### Step 6: Statistical Rigor (1 hour)

#### 6.1 Bootstrap Confidence Intervals
```python
def bootstrap_slope(T, Δp, n_bootstrap=1000):
    """Calculate bootstrap CI for β_LRT."""
    slopes = []
    for _ in range(n_bootstrap):
        # Resample with replacement
        indices = np.random.choice(len(T), size=len(T), replace=True)
        T_boot = T[indices]
        Δp_boot = Δp[indices]

        # Regression
        slope, _, _, _, _ = linregress(T_boot, Δp_boot)
        slopes.append(slope)

    # 95% CI
    ci_lower = np.percentile(slopes, 2.5)
    ci_upper = np.percentile(slopes, 97.5)

    return ci_lower, ci_upper

ci_lower, ci_upper = bootstrap_slope(T_sweep, Δp)
print(f"β_LRT = {slope:.2e} [{ci_lower:.2e}, {ci_upper:.2e}] (95% CI)")
```

#### 6.2 Permutation Test (Non-Parametric)
```python
def permutation_test(T, Δp, n_permutations=10000):
    """Test H0: β_LRT = 0 via permutation."""
    # Observed slope
    slope_obs, _, _, _, _ = linregress(T, Δp)

    # Null distribution
    slopes_null = []
    for _ in range(n_permutations):
        # Permute residuals (breaks T-Δp relationship if H0 true)
        Δp_perm = np.random.permutation(Δp)
        slope_perm, _, _, _, _ = linregress(T, Δp_perm)
        slopes_null.append(slope_perm)

    # P-value: fraction of null slopes ≥ observed
    p_value = np.mean(np.array(slopes_null) >= slope_obs)

    return p_value

p_perm = permutation_test(T_sweep, Δp)
print(f"Permutation test p-value: {p_perm:.4f}")
```

**Success criterion:** Consistent p-values across parametric and non-parametric tests

---

## Phase 3 Deliverables

### 1. Main Notebook
**File:** `notebooks/quantum_simulations/phase3_full_simulation.ipynb`

**Sections:**
1. Scaled baseline (N=10,000, 49 points)
2. VIF verification at scale
3. Alternative functional forms (model selection)
4. Robustness checks (Y-basis, GST, crosstalk, drift)
5. Power analysis (MDE calculation)
6. Sensitivity analysis (T1, T_phi, qubit type)
7. Statistical rigor (bootstrap, permutation)
8. Summary and conclusions

### 2. Results Report
**File:** `theory/predictions/Phase_3_Results_Report.md`

**Contents:**
- Executive summary (Did we detect LRT effect?)
- All success criteria results (tabulated)
- Best-fit model (functional form selection)
- Robustness check outcomes
- Power and sensitivity analysis
- Confidence intervals and p-values
- Recommendations for hardware validation

### 3. Figures (Publication Quality)
**Files:** `notebooks/outputs/phase3_*.png`

1. `phase3_full_characterization.png` - Full N=10,000 T2 characterization
2. `phase3_model_comparison.png` - AIC/BIC comparison of functional forms
3. `phase3_robustness_checks.png` - Y-basis, GST, crosstalk, drift results
4. `phase3_power_curve.png` - Statistical power vs effect size
5. `phase3_sensitivity_analysis.png` - Parameter variation results
6. `phase3_final_results.png` - Best-fit model with confidence bands

### 4. Updated Session Log
**File:** `Session_Log/Session_2.8.md` (or 2.7 continued)

**Document:**
- Phase 3 implementation progress
- All numerical results
- Decision: Proceed to Phase 4 or revise
- Lessons learned

---

## Success Criteria Summary

**ALL must pass to claim LRT validation:**

| Criterion | Target | Why Critical |
|-----------|--------|--------------|
| T2 Recovery | ±5% | Tighter tolerance at scale |
| VIF | 1.000000 | Must remain 1 at N=10,000 |
| R² | > 0.98 | Higher fit quality threshold |
| Best Model AIC | Lowest | Functional form selection |
| Y-Basis Consistency | p > 0.05 | Not basis-dependent artifact |
| GST Robustness | T2 within ±10% | Gate errors don't break analysis |
| Crosstalk | < 5% idle error | Negligible multi-qubit effects |
| Drift Correlation | |r| < 0.3 | Frequency drift not confounding |
| MDE | ≤ 0.01 | Can detect 1% excess error |
| Bootstrap CI | Excludes 0 if LRT | Rigorous uncertainty |
| Permutation p | < 0.05 if LRT | Non-parametric confirmation |

**If LRT effect detected (β_LRT > 0, p < 0.001):**
- Report effect size with confidence intervals
- Best-fit functional form
- All robustness checks passed
- Recommendation: Proceed to hardware validation

**If no LRT effect (β_LRT ≈ 0, p > 0.05):**
- Report upper bound on p_LRT (e.g., p_LRT < 0.005 at 95% confidence)
- Implications for LRT theory
- Recommendations: Test alternative predictions (Rabi frequency test)

---

## Estimated Time and Resources

**Total Phase 3 Time:** 10-12 hours
- Implementation: 8-10 hours
- Analysis and documentation: 2-3 hours
- Debugging and refinement: 1-2 hours

**Computational Requirements:**
- Shots: 490,000 (49 points * 10,000 shots)
- Runtime: 15-30 minutes (depends on vectorization)
- Memory: ~1 GB peak
- Disk: ~50 MB (saved results + plots)

**Hardware:** Any modern laptop (2020+) can run this

---

## Integration with Multi-LLM Team Feedback

**Grok's Recommendations (Quality 0.81):**
1. ✓ GST instead of RB → Phase 3 Step 3.2
2. ✓ Crosstalk monitoring → Phase 3 Step 3.3
3. ✓ Frequency drift tracking → Phase 3 Step 3.4

**Gemini's Recommendations (Quality 0.74):**
1. ✓ Alternative functional forms → Phase 3 Step 2
2. ✓ Y-basis robustness → Phase 3 Step 3.1
3. ✓ Cross-validation with Rabi → Phase 4 (if LRT detected)

**ChatGPT's Recommendations (Quality 0.52):**
1. ✓ Sensitivity analysis → Phase 3 Step 5
2. ✓ Power analysis → Phase 3 Step 4

**All team feedback integrated in Phase 3 plan.**

---

## Risk Mitigation

### Risk 1: No LRT Effect Detected

**Likelihood:** Unknown (depends on LRT predictions)
**Impact:** High (theory not validated)
**Mitigation:**
- Report upper bounds on p_LRT
- Test alternative LRT predictions (Rabi frequency test)
- Refine theory or parameter estimates

### Risk 2: Confounds Dominate

**Likelihood:** Medium (GST errors, crosstalk, drift)
**Impact:** High (cannot isolate LRT effect)
**Mitigation:**
- All robustness checks explicitly test for confounds
- Include confound terms in regression if necessary
- Use higher-fidelity simulation if gate errors wash out signal

### Risk 3: Functional Form Mismatch

**Likelihood:** Low (multiple forms tested)
**Impact:** Medium (underfitting/overfitting)
**Mitigation:**
- AIC/BIC model selection prevents overfitting
- Non-parametric spline as fallback

### Risk 4: Insufficient Power

**Likelihood:** Very Low (Phase 2 power analysis predicted N=10,000 sufficient)
**Impact:** High (false negative)
**Mitigation:**
- Step 4 validates power experimentally
- If MDE > 0.01, scale to N=20,000 or higher

---

## Next Steps After Phase 3

### If LRT Effect Detected

1. **Phase 4: Final Documentation**
   - Comprehensive results report
   - Paper integration (Section 4 revision)
   - Hardware validation recommendations

2. **Cross-Validation**
   - Run "Logical Inertia" (Rabi) test
   - Check if both predictions align

3. **Hardware Validation**
   - IBM Quantum, IonQ, or Rigetti platforms
   - Real qubit experiments

### If No LRT Effect

1. **Upper Bounds Report**
   - p_LRT < X at 95% confidence
   - Implications for theory

2. **Alternative Predictions**
   - Pivot to Rabi frequency test
   - Test other LRT predictions from paper

3. **Theory Refinement**
   - Consult multi-LLM team
   - Revise parameter estimates or predictions

---

**Status:** Ready for implementation
**Next Action:** Create `phase3_full_simulation.ipynb` notebook
**Estimated Completion:** 1-2 sessions (10-12 hours total work)
