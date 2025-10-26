# Quantum Simulation Implementation Plan
## Fixing β Discrepancy (100x-500x Too Large)

**Status**: Planning Phase
**Current β**: 56.98 ± 22.79 (n=30)
**Target β**: 0.1 - 0.5 (n≥10,000)
**Confidence**: Implementation fixes should bring β into predicted range

---

## Root Cause Analysis Summary

**Primary Hypothesis**: Missing normalization terms in simplified model

**Current Model** (WRONG):
```
log(p_log) = α + β * ΔS
```

**Correct Model** (from paper):
```
log p_log = α + γ(d) + η log p_phys + β ΔS_sys + Σ θ_j C_j + ε
```

**Missing Terms**:
- γ(d): Code distance effect (varied d=3,5,7)
- η log(p_phys): Physical error rate scaling
- Σ θ_j C_j: Control variables (gate time, SPAM, etc.)

**Result**: β absorbs effects of missing terms → 100x inflation

---

## Implementation Roadmap

### Phase 1: Implement Proper QEC ⚠️ CRITICAL

**Problem**: Current simulation uses single qubits, not real QEC code

**Fix Options** (in order of complexity):

#### Option A: 3-Qubit Repetition Code (Simplest)
- **Library**: Pure Qiskit (no external dependencies)
- **Implementation**:
  - Encode: |0⟩_L = |000⟩, |1⟩_L = |111⟩
  - Syndrome measurement: Check parity of adjacent pairs
  - Decoding: Majority vote
- **Pros**: Simple, well-understood, already partially implemented
- **Cons**: Low code distance (d=3), limited error correction
- **Effort**: 2-4 hours

#### Option B: Small Surface Code (Recommended)
- **Library**: `qiskit-qec` (community package)
- **Implementation**:
  - Distance d=3 surface code (9 data qubits, 8 syndrome qubits)
  - Stabilizer measurements
  - Minimum-weight perfect matching decoder
- **Pros**: Realistic QEC, scales to d=5,7, standard in literature
- **Cons**: More complex, requires qiskit-qec installation
- **Effort**: 1-2 days

#### Option C: Steane Code (Alternative)
- **Library**: `qiskit-qec` or custom implementation
- **Implementation**: [[7,1,3]] CSS code
- **Pros**: Allows transversal gates, well-studied
- **Cons**: Similar complexity to surface code
- **Effort**: 1-2 days

**Recommendation**: Start with Option A (3-qubit repetition) to validate approach, then move to Option B (surface code d=3) for final validation.

**Implementation Steps** (Option A):
1. Create `LogicalQubit` class:
   - `encode(physical_state)` → 3-qubit state
   - `measure_syndrome()` → detect errors
   - `decode(syndrome)` → apply correction
2. Refactor sequences to use logical qubits:
   - Low-entropy: Logical identity cycles (no errors injected)
   - High-entropy: Logical identity cycles (with resets between)
3. Measure logical error rate: `p_log = (# incorrect final states) / n_trials`

---

### Phase 2: Refine Error Modeling ⚠️ CRITICAL

**Problem**: Current noise too simple (uniform amplitude damping)

**Fix**: Implement realistic, time-dependent noise models

#### Sub-task 2.1: Multiple Noise Types

**Current**:
```python
noise_op = qutip.to_kraus(qutip.amplitude_damping(noise_level))
```

**Target**:
```python
# Per-gate noise (Qiskit 2.x AerSimulator)
noise_model = NoiseModel()

# 1-qubit gate errors (thermal + depolarizing)
thermal_error = thermal_relaxation_error(t1=100e-6, t2=50e-6, time=50e-9)
depol_error = depolarizing_error(0.001, 1)
combined_1q = thermal_error.compose(depol_error)

# 2-qubit gate errors
depol_2q = depolarizing_error(0.01, 2)

# Measurement errors
readout_error = depolarizing_error(0.01, 1)

noise_model.add_all_qubit_quantum_error(combined_1q, ['u', 'x', 'h', ...])
noise_model.add_all_qubit_quantum_error(depol_2q, ['cx', 'cz'])
noise_model.add_all_qubit_quantum_error(readout_error, 'measure')
```

**Benefit**: Separates decoherence (T1, T2) from gate errors → more realistic

#### Sub-task 2.2: Time-Matched Sequences ⚠️ CRITICAL

**Problem**: Low-entropy and high-entropy sequences may have different durations → confounds ΔS measurement

**Fix**:
1. Calculate circuit duration for each sequence:
   - Low-entropy: `t_low = n_gates_low * t_gate`
   - High-entropy: `t_high = n_gates_high * t_gate + n_meas * t_meas + n_reset * t_reset`
2. Add padding (identity gates or delays) to equalize:
   - `if t_low < t_high: add_delays(low_circuit, t_high - t_low)`
3. Verify in simulation:
   - `assert abs(t_low - t_high) < t_gate` (within one gate time)

**Critical Insight**: This is likely the main source of β inflation. If high-entropy sequences take longer, they accumulate more decoherence noise, creating spurious correlation with ΔS.

#### Sub-task 2.3: Realistic QEC Cycles

**Low-Entropy Sequence** (should have ΔS ≈ 0):
```python
# Unitary QEC cycle (no measurement/reset)
def low_entropy_qec_cycle():
    qc = QuantumCircuit(...)
    qc.barrier()
    # Encode logical qubit
    qc.cx(data[0], data[1])
    qc.cx(data[0], data[2])
    qc.barrier()
    # NO syndrome measurement (keep coherence)
    # NO reset
    qc.barrier()
    # Decode (reverse encoding for identity operation)
    qc.cx(data[0], data[2])
    qc.cx(data[0], data[1])
    return qc
```

**High-Entropy Sequence** (should have ΔS > 0):
```python
# QEC cycle with mid-circuit measurement/reset
def high_entropy_qec_cycle():
    qc = QuantumCircuit(...)
    qc.barrier()
    # Encode logical qubit
    qc.cx(data[0], data[1])
    qc.cx(data[0], data[2])
    qc.barrier()
    # Syndrome measurement (collapses state)
    qc.cx(data[0], syndrome[0])
    qc.cx(data[1], syndrome[0])
    qc.measure(syndrome[0], syndrome_bits[0])
    # Reset syndrome qubit
    qc.reset(syndrome[0])
    qc.barrier()
    # Apply correction based on syndrome
    # ... (conditional gates)
    # Decode
    qc.cx(data[0], data[2])
    qc.cx(data[0], data[1])
    return qc
```

**Key Difference**: High-entropy includes measurement/reset → increases system entropy

**Verify**: Use `qiskit.quantum_info.entropy(ρ)` to confirm ΔS > 0 for high-entropy

---

### Phase 3: Increase Sample Size

**Current**: n = 30
**Target**: n ≥ 10,000
**Paper Requirement**: N ~ 10^4 - 10^5 gate cycles

**Implementation**:
1. Parametrize `n_samples` in script
2. Run convergence test:
   - Plot β vs n for n ∈ {100, 500, 1000, 5000, 10000}
   - Verify β stabilizes (convergence)
   - Report standard error: SE(β) = σ_β / sqrt(n)
3. Computational cost:
   - n=30: ~2 minutes
   - n=10,000: ~11 hours (estimate)
   - Optimization: Parallelize with multiprocessing

**Optimization Strategy**:
```python
from multiprocessing import Pool

def run_trial(trial_id):
    # Run single trial, return (Delta_S, p_log)
    ...

with Pool(processes=8) as pool:
    results = pool.map(run_trial, range(n_samples))
```

**Expected speedup**: ~8x on 8-core machine → 11 hours → 1.4 hours

---

### Phase 4: Implement Full Regression Model

**Current** (WRONG):
```python
slope, intercept, r, p, se = stats.linregress(Delta_S, log_p_log)
beta = slope
```

**Target** (CORRECT):
```python
import statsmodels.api as sm

# Independent variables
X = pd.DataFrame({
    'code_distance': d_values,           # γ(d)
    'log_p_phys': np.log(p_phys_values), # η log(p_phys)
    'Delta_S': Delta_S_values,           # β ΔS_sys
    'gate_time': t_gate_values,          # θ_1 (control)
    'spam_error': spam_values            # θ_2 (control)
})
X = sm.add_constant(X)  # Add intercept α

# Dependent variable
y = log_p_log_values

# Fit full model
model = sm.OLS(y, X).fit()
print(model.summary())

# Extract β coefficient
beta = model.params['Delta_S']
beta_se = model.bse['Delta_S']
beta_pvalue = model.pvalues['Delta_S']

# Hypothesis test: H0: β = 0 vs H1: β > 0
print(f"β = {beta:.4f} ± {beta_se:.4f}, p = {beta_pvalue:.4e}")
```

**Variables to Vary**:
1. **Code distance d**: {3, 5, 7} (requires implementing d=5, d=7 codes)
2. **Physical error rate p_phys**: {10^-4, 10^-3, 10^-2}
3. **Entropy change ΔS**: Manipulated via sequence type (natural variation)
4. **Gate time** (control): Equalize across sequences
5. **SPAM error** (control): Measure and include as covariate

**Expected Result**:
- β should drop to ~0.1-0.5 range
- γ(d) and η log(p_phys) should absorb the effects previously inflating β
- R² should increase (better fit)

---

### Phase 5: Add Control Variables

#### Control 1: Gate Time Matching ⚠️ CRITICAL

**Implementation**:
```python
def calculate_circuit_duration(qc):
    # Count operations
    n_1q = qc.count_ops().get('u', 0) + qc.count_ops().get('h', 0) + ...
    n_2q = qc.count_ops().get('cx', 0) + qc.count_ops().get('cz', 0)
    n_meas = qc.count_ops().get('measure', 0)
    n_reset = qc.count_ops().get('reset', 0)

    # Calculate total time
    t_total = n_1q * t_1q_gate + n_2q * t_2q_gate + n_meas * t_meas + n_reset * t_reset
    return t_total

# Equalize durations
t_low = calculate_circuit_duration(low_entropy_circuit)
t_high = calculate_circuit_duration(high_entropy_circuit)

if t_low < t_high:
    # Add delays to low-entropy circuit
    low_entropy_circuit.delay(t_high - t_low, unit='s')
elif t_high < t_low:
    # Add delays to high-entropy circuit
    high_entropy_circuit.delay(t_low - t_high, unit='s')

# Verify
assert abs(t_low - t_high) < 1e-9  # Within 1 ns
```

#### Control 2: State Preparation and Measurement (SPAM) Errors

**Implementation**:
```python
# Measure SPAM error independently
def measure_spam_error(n_trials=1000):
    errors = 0
    for _ in range(n_trials):
        qc = QuantumCircuit(1, 1)
        qc.initialize([1, 0], 0)  # Prepare |0⟩
        qc.measure(0, 0)          # Measure immediately
        result = simulator.run(qc, shots=1).result()
        if result.get_counts().get('1', 0) > 0:
            errors += 1
    return errors / n_trials

spam_error = measure_spam_error()
print(f"SPAM error rate: {spam_error:.4e}")

# Include as covariate in regression
X['spam_error'] = spam_error  # Constant for all trials (or vary if testing different prep methods)
```

#### Control 3: Leakage (Optional)

**Implementation** (if using multi-level systems):
```python
# Monitor population in non-computational states
# Requires qutrit simulation or leakage detection circuits
# Skip for initial implementation (focus on qubits only)
```

---

## Implementation Timeline

### Week 1: Prototype (3-Qubit Repetition Code)
- **Day 1-2**: Implement 3-qubit repetition code QEC
  - `LogicalQubit` class
  - Encode/syndrome/decode methods
  - Test with known errors
- **Day 3-4**: Refactor sequences
  - Low-entropy: Unitary logical identity cycles
  - High-entropy: Logical identity with syndrome measurement
  - Verify ΔS ≈ 0 (low) and ΔS > 0 (high)
- **Day 5**: Time-matching implementation
  - Calculate circuit durations
  - Add padding/delays
  - Verify t_low ≈ t_high
- **Day 6**: Run small-scale test (n=1,000)
  - Check if β drops closer to predicted range
  - Debug if still inflated
- **Day 7**: Document results
  - Update notebook with prototype
  - Record β value
  - Assess if approach is working

**Deliverable**: Working 3-qubit repetition code simulation with n=1,000, β closer to 0.1-0.5

### Week 2: Full Model Implementation
- **Day 8-10**: Implement full regression model
  - Vary code distance d (may need surface code for d>3)
  - Vary physical error rate p_phys
  - Add control variables
  - Use statsmodels for multivariate regression
- **Day 11-12**: Scale to n=10,000
  - Implement parallelization
  - Run overnight (~2 hours with 8 cores)
  - Verify convergence
- **Day 13**: Statistical analysis
  - Fit full model
  - Extract β ± SE
  - Report R², p-value
  - Check if β ∈ [0.1, 0.5]
- **Day 14**: Documentation and review
  - Update notebook with full implementation
  - Create validation report
  - Apply auditor protocol (check claims)
  - Update session log

**Deliverable**: Complete simulation with n≥10,000, full regression model, β in predicted range

### Week 3: Surface Code Extension (If Time Permits)
- **Day 15-17**: Implement surface code d=3
  - Install qiskit-qec
  - Configure surface code
  - Implement MWPM decoder
- **Day 18-19**: Run with surface code
  - n=10,000 trials
  - Compare to repetition code results
- **Day 20-21**: Hardware preparation
  - Prepare IBM Quantum deployment
  - Apply for enhanced access
  - Create hardware submission script

**Deliverable**: Surface code validation ready for hardware deployment

---

## Success Criteria

### Minimum Success (Gate for claiming validation)
- ✅ β ∈ [0.05, 1.0] (within order of magnitude of prediction)
- ✅ n ≥ 10,000 samples
- ✅ p < 0.01 (statistically significant)
- ✅ Time-matched sequences (|t_low - t_high| < t_gate)
- ✅ Full regression model (includes γ(d), η log(p_phys))
- ✅ R² > 0.3 (reasonable fit)

### Target Success (Strong evidence)
- 🎯 β ∈ [0.1, 0.5] (matches paper's prediction)
- 🎯 n ≥ 100,000 samples (statistical power > 0.8 at α = 0.01)
- 🎯 p < 0.001 (highly significant)
- 🎯 R² > 0.5 (good fit)
- 🎯 Surface code implementation (realistic QEC)
- 🎯 Hardware validation (IBM Quantum)

### Failure Criteria (Reject LRT prediction)
- ❌ β ≤ 0 (wrong sign)
- ❌ β not significantly different from 0 (p > 0.05)
- ❌ β >> 1.0 even after fixes (indicates fundamental model mismatch)

---

## Risk Mitigation

### Risk 1: β Still Inflated After Fixes
**Mitigation**:
- Check each fix incrementally (ablation study)
- Verify time-matching first (likely main culprit)
- Test with idealized (zero physical noise) case → should get β ≈ 0

### Risk 2: Computational Time Exceeds Resources
**Mitigation**:
- Use cloud compute (Google Colab, AWS)
- Optimize code (Cython, numba)
- Reduce n_samples to minimum required for power analysis

### Risk 3: Surface Code Implementation Too Complex
**Mitigation**:
- Start with 3-qubit repetition code (simpler)
- Only implement surface code if repetition code validates successfully
- Use qiskit-qec library (don't reinvent)

---

## Open Questions

1. **What is the minimum code distance needed?**
   - Paper uses d=3,5,7. Can we validate with just d=3?
   - Answer: Start with d=3, extend if time permits

2. **Should we implement error correction or just error detection?**
   - Full correction requires decoding algorithm (MWPM)
   - Detection only requires syndrome measurement
   - Answer: Full correction (more realistic)

3. **How to handle time-varying noise?**
   - IBM devices have time-dependent T1, T2
   - Answer: Use static noise model for simulation, document limitation

4. **What about correlated errors?**
   - Surface codes vulnerable to correlated errors
   - Answer: Start with independent errors, document as future work

---

## References

**LRT Paper**: Section 4 (Empirical Testability), lines 310-407
- Full regression model: Eq. (31)
- Statistical power analysis: lines 380-390
- Predicted β: 0.1 - 0.5

**Qiskit Documentation**:
- Noise models: https://qiskit.org/documentation/aer/noise.html
- Quantum info: https://qiskit.org/documentation/quantum_info.html

**qiskit-qec**:
- GitHub: https://github.com/qiskit-community/qiskit-qec
- Surface codes tutorial: https://qiskit.org/textbook/ch-quantum-hardware/error-correction-repetition-code.html

---

**Document Status**: Planning Complete
**Next Action**: Begin Week 1 Day 1 implementation (3-qubit repetition code)
**Owner**: Claude Code
**Last Updated**: October 26, 2025
