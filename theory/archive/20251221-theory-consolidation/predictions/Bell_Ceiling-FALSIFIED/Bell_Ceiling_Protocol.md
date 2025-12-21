# Bell Ceiling Test Protocol

**Version**: 1.0
**Date**: 2025-11-05
**Status**: Draft (pre-registration pending)
**Principal Investigator**: James D. Longmire (ORCID: 0009-0009-1383-7698)

---

## Executive Summary

This protocol describes an experimental test of Logic Realism Theory's (LRT) prediction that the maximum CHSH violation is **below** the Tsirelson bound due to intrinsic measurement costs.

**Key Prediction**:
- **Standard QM**: S_max = 2√2 ≈ 2.828 (Tsirelson bound)
- **LRT**: S_max = 2.71 ± 0.01 (4.1% reduction)
- **Falsification**: If S₀ > 2.77 (zero-noise), LRT is falsified

**Method**: Measure CHSH at 5 noise levels, extrapolate to zero noise

**Platform**: IonQ Aria (recommended) or Quantinuum H2

**Resources**: 200,000 shots, $70-300, 2-3 weeks execution

---

## 1. Scientific Background

### 1.1 The Tsirelson Bound

Standard quantum mechanics predicts a maximum violation of the CHSH inequality:

$$\mathcal{S}_{\text{max}} = 2\sqrt{2} \approx 2.828$$

This bound arises from the structure of quantum correlations and is considered **fundamental** in QM.

### 1.2 LRT Prediction

Logic Realism Theory posits that measurement carries **intrinsic logical cost** due to enforcement of the Law of Excluded Middle (EM constraint). This predicts a **ceiling below Tsirelson**:

$$\mathcal{S}_{\text{LRT}}^{\text{max}} = 2\sqrt{2} \cdot (1 - \alpha \cdot \eta^2)$$

Where:
- **α = 3/4**: Geometric factor (derived from S₄ permutohedron structure)
- **η ≈ 0.235**: EM coupling strength (from variational optimization)
- **α·η² ≈ 0.0415**: Total reduction factor

**Result**: S_LRT^max = 2.711 ± 0.010

### 1.3 Physical Mechanism

**Bell measurement process**:
1. Prepare maximally entangled state |Φ⁺⟩ = (|00⟩ + |11⟩)/√2
2. Alice and Bob each perform measurement (collapse from superposition → definite outcome)
3. Each collapse is a **K-transition** with cost ~η
4. Two correlated measurements → combined cost α·η²

**Key distinction**: This cost is **intrinsic** (not environmental), persisting even with perfect isolation.

### 1.4 Why This Test is Clean

**Advantages over other LRT predictions**:
1. **Single number**: One measurement (S₀) falsifies theory
2. **No overlap**: LRT violates QM's fundamental bound (not within allowed range)
3. **Standard protocol**: Uses established Bell test methodology
4. **Extrapolation**: Zero-noise limit isolates intrinsic effect from environmental noise

---

## 2. Hypothesis and Predictions

### 2.1 Primary Hypothesis (H1)

**LRT prediction**: The maximum CHSH value, in the zero-environmental-noise limit, is:

$$\mathcal{S}_0^{\text{LRT}} = 2.711 \pm 0.010$$

This is 0.117 (4.1%) below the Tsirelson bound.

### 2.2 Null Hypothesis (H0)

**Standard QM**: The maximum CHSH value equals the Tsirelson bound:

$$\mathcal{S}_0^{\text{QM}} = 2\sqrt{2} \approx 2.828$$

### 2.3 Falsification Criterion

**Decision rule**:
- If S₀ (extrapolated zero-noise) > **2.77** → **Reject H1** (LRT falsified)
- If S₀ < **2.74** → **Support H1** (LRT evidence)
- If 2.74 < S₀ < 2.77 → **Inconclusive** (refine measurement)

**Rationale**: Midpoint (2.77) provides symmetric decision boundary with margin for uncertainty.

### 2.4 Statistical Power

**Signal**: Δ = S_QM - S_LRT = 0.117
**Uncertainty** (per noise level): δS ≈ 2/√N = 0.02 (N=10,000 shots per correlation)
**Combined uncertainty**: σ_combined ≈ √2 × δS ≈ 0.0283 (comparing two measurements)
**Significance**: Δ/σ_combined ≈ 0.117/0.0283 ≈ **4.1σ**

**Probability of Type I error** (falsely rejecting QM): p < 3.4×10⁻⁵
**Probability of Type II error** (failing to detect LRT if true): p < 0.01

---

## 3. Platform Selection

### 3.1 Requirements

To observe the 4.1% LRT signal, we need:

1. **High gate fidelity**: >99.8% (LRT signal = 0.117, gate errors must be << 0.117/10 gates ≈ 0.012)
2. **High measurement fidelity**: >99.5% (errors should not dominate signal)
3. **Stable calibration**: Drifts < 0.01 per hour
4. **Two-qubit entangling gates**: High-fidelity Bell state preparation
5. **Mid-circuit measurement**: Optional (not required for this protocol)

### 3.2 Platform Comparison

| Platform | Gate Fidelity | Meas. Fidelity | Coherence | Cost/Shot | Verdict |
|----------|---------------|----------------|-----------|-----------|---------|
| **IBM Quantum (Heron)** | ~99.5% | ~99.0% | T1~100μs | ~$0.00 (free tier) | ⚠️ Marginal |
| **IonQ Aria** | ~99.8% | ~99.7% | T1~1s | ~$0.00035 | ✓ Good |
| **Quantinuum H2** | ~99.9% | ~99.8% | T1~10s | ~$0.0015 | ✓✓ Excellent |
| **Rigetti Aspen-M** | ~99.0% | ~98.5% | T1~50μs | ~$0.00 (cloud) | ❌ Insufficient |

### 3.3 Recommended Platform: IonQ Aria

**Justification**:
1. **Fidelity**: 99.8% gates, 99.7% measurement (sufficient for 4.1% signal)
2. **Stability**: Trapped ion qubits have long coherence times (T1 ~1s)
3. **Cost**: $70 for full experiment (200K shots × $0.00035/shot)
4. **Availability**: Commercial access via AWS Braket, Azure Quantum
5. **Track record**: Successfully used for high-precision Bell tests

**Alternative**: Quantinuum H2 if higher precision desired (cost: $300)

---

## 4. Circuit Design

### 4.1 Bell State Preparation

**Target state**: |Φ⁺⟩ = (|00⟩ + |11⟩)/√2

**Circuit**:
```
q0: ─H─●─
       │
q1: ───X─
```

**Gates**:
- Hadamard (H) on qubit 0
- CNOT (●─X) with control on qubit 0, target on qubit 1

**Expected fidelity**: F_prep = F_H × F_CNOT ≈ 0.998 × 0.998 ≈ 0.996

### 4.2 CHSH Measurement Angles

**Alice's measurements** (qubit 0):
- a: Rotate by 0° (measure in Z basis) → **No rotation needed**
- a': Rotate by 90° (measure in X basis) → **Apply H gate**

**Bob's measurements** (qubit 1):
- b: Rotate by 45° → **Apply Ry(π/4)**
- b': Rotate by -45° → **Apply Ry(-π/4)**

**Rotation gates**:
- Ry(θ) = exp(-iθY/2) = cos(θ/2)I - i·sin(θ/2)Y

### 4.3 Complete Circuit (Example: E(a,b))

Measure correlation E(a,b) where Alice uses angle a=0° and Bob uses b=45°:

```
      ┌───┐
q0: ──┤ H ├──●────────M──
      └───┘┌─┴─┐┌────┐│
q1: ───────┤ X ├┤Ry(π/4)├M──
            └───┘└────┘
```

1. Prepare |Φ⁺⟩: H on q0, CNOT(q0→q1)
2. Alice rotation: None (a=0°, measure Z)
3. Bob rotation: Ry(π/4) on q1
4. Measure both qubits in computational basis

**Four circuits needed**:
- E(a,b): Bob Ry(π/4)
- E(a,b'): Bob Ry(-π/4)
- E(a',b): Alice H, Bob Ry(π/4)
- E(a',b'): Alice H, Bob Ry(-π/4)

### 4.4 Circuit Depth and Gate Count

**Per correlation measurement**:
- Preparation: 2 gates (H + CNOT)
- Rotation: 0-2 gates (H and/or Ry)
- Total: 2-4 gates

**Coherence requirement**: Circuit time << T2
- Gate time: ~1-10 μs (ion traps)
- Total circuit time: ~10-40 μs
- T2 (IonQ Aria): ~1 s
- Ratio: 0.00001-0.00004 (excellent)

---

## 5. Measurement Protocol

### 5.1 Noise Level Parametrization

To enable zero-noise extrapolation, measure at **5 noise levels**:

| Level | Depolarizing p | Method | Purpose |
|-------|----------------|--------|---------|
| **0** | 0% | Native gates | Best-case (intrinsic noise only) |
| **1** | 0.5% | Idle time: +10 μs | Slight degradation |
| **2** | 1.0% | Idle time: +20 μs | Moderate noise |
| **3** | 2.0% | Idle time: +40 μs | Higher noise |
| **4** | 5.0% | Idle time: +100 μs | Maximum noise (for fit quality) |

**Implementation**: Insert identity gates with controlled idle times to induce T1/T2 decay.

**Calibration**: Measure T1 and T2 before experiment to convert idle time → depolarizing parameter.

### 5.2 Shot Allocation

**Per noise level, per correlation**:
- Shots: 10,000
- Reason: Gives δS ≈ 0.02 per correlation, 4.1σ significance for distinguishing S_QM from S_LRT

**Total shots**:
- 5 noise levels × 4 correlations × 10,000 shots = **200,000 shots**

**Execution time** (IonQ Aria):
- Circuit time: ~40 μs
- Overhead: ~100 μs (setup, measurement, readout)
- Per shot: ~140 μs
- Total: 200,000 × 140 μs ≈ 28 seconds (actual execution)
- With queue/calibration: ~2-3 hours

### 5.3 Randomization and Blinding

**Randomization**:
1. **Circuit order**: Shuffle 20 circuits (5 noise × 4 correlations) randomly
2. **Shot order**: Interleave measurements (not 10K consecutive shots per circuit)
3. **Calibration**: Re-calibrate every 1,000 shots (mitigate drift)

**Blinding**:
1. **Data collection**: Raw counts saved with masked noise labels (analyst doesn't know which is level 0)
2. **Analysis code**: Pre-committed to GitHub (locked before data collection)
3. **Unblinding**: Only after analysis complete and results documented

**Purpose**: Prevent experimenter bias in data analysis.

### 5.4 Calibration and Validation

**Pre-experiment calibration**:
1. Single-qubit gate fidelity (randomized benchmarking)
2. Two-qubit gate fidelity (CNOT benchmarking)
3. T1 and T2 measurement (exponential decay fits)
4. Measurement fidelity (state preparation and measurement)

**In-experiment validation**:
1. Bell state fidelity check (tomography on 1% of shots)
2. Monitor for drift (recalibrate if fidelity drops >0.5%)
3. Parity checks (ensure E_ab, E_ab', E_a'b, E_a'b' are consistent)

**Post-experiment validation**:
1. Classical bound check: S should never exceed 2 (sanity check)
2. Tsirelson check: S at lowest noise should be ≤ 2.83 (within QM)
3. Monotonicity: S should decrease with increasing noise

---

## 6. Data Analysis Plan

### 6.1 Correlation Calculation

For each measurement setting (a,b) at noise level p:

1. **Count outcomes**: N_00, N_01, N_10, N_11 (total N = 10,000)
2. **Calculate correlation**:
   $$E(a,b) = \frac{N_{00} + N_{11} - N_{01} - N_{10}}{N}$$
3. **Uncertainty**:
   $$\delta E = \frac{2}{\sqrt{N}} \approx 0.02$$

### 6.2 CHSH Value Construction

For each noise level p:

$$\mathcal{S}(p) = E(a,b;p) + E(a,b';p) + E(a',b;p) - E(a',b';p)$$

**Uncertainty** (propagated):
$$\delta S = \sqrt{4 \times (\delta E)^2} = 2\delta E \approx 0.04$$

### 6.3 Zero-Noise Extrapolation

**Fit models** (test all three):

1. **Linear**: $S(p) = S_0 + c_1 \cdot p$
2. **Quadratic**: $S(p) = S_0 + c_1 \cdot p + c_2 \cdot p^2$
3. **Exponential**: $S(p) = S_0 + A(1 - e^{-p/p_0})$

**Procedure**:
1. Perform weighted least-squares fit for each model
2. Extract S₀ (zero-noise intercept) and uncertainty δS₀
3. Select best model based on χ² / DOF (degrees of freedom)
4. Report S₀ from best-fit model

**Expected results** (from QuTiP simulation):
- **QM scenario**: S₀ ≈ 2.828 ± 0.01
- **LRT scenario**: S₀ ≈ 2.711 ± 0.01

### 6.4 Hypothesis Testing

**Test statistic**:
$$z = \frac{S_0 - S_{\text{LRT}}}{\sqrt{\delta S_0^2 + \delta S_{\text{LRT}}^2}}$$

Where:
- S₀: Measured zero-noise CHSH
- S_LRT = 2.711: LRT prediction
- δS₀: Uncertainty from fit
- δS_LRT = 0.010: LRT theoretical uncertainty

**Decision rules**:
- If |z| < 2.5 (2.5σ): **Consistent with LRT**
- If z > 5 (S₀ significantly above S_LRT): **Reject LRT, support QM**
- If z < -5: **Unexpected** (below LRT prediction)

---

## 7. Error Budget

### 7.1 Systematic Errors

| Source | Magnitude | Mitigation | Residual |
|--------|-----------|------------|----------|
| **Gate errors** | ~0.002 per gate × 4 gates | High-fidelity platform | **±0.008** |
| **Measurement errors** | ~0.003 per qubit × 2 qubits | SPAM correction | **±0.006** |
| **Calibration drift** | ~0.01 per hour | Recalibrate every 1K shots | **±0.002** |
| **Crosstalk** | ~0.001 (ion traps minimal) | Use non-adjacent qubits | **±0.001** |
| **Leakage** | ~0.001 (to non-computational levels) | Leakage detection | **±0.001** |
| **Classical bound violation** | 0 (enforced) | Sanity check | **0** |

**Total systematic** (quadrature sum): ±0.011

### 7.2 Statistical Errors

**Per correlation** (N=10,000):
$$\delta E_{\text{stat}} = \frac{2}{\sqrt{10000}} = 0.02$$

**Per CHSH value**:
$$\delta S_{\text{stat}} = 2 \times 0.02 = 0.04$$

**After extrapolation** (5 noise levels):
$$\delta S_0 \approx \frac{\delta S}{\sqrt{5}} \approx 0.018$$

### 7.3 Total Uncertainty

$$\delta S_0^{\text{total}} = \sqrt{(\delta S_0^{\text{stat}})^2 + (\delta S_0^{\text{sys}})^2}$$
$$= \sqrt{0.018^2 + 0.011^2} \approx 0.021$$

**Final measurement precision**: S₀ ± 0.02

**Comparison to signal**:
- Signal: Δ = 0.117
- Uncertainty: δS₀ = 0.021
- Significance: Δ/δS₀ ≈ **5.6σ**

(Note: This accounts for both statistical uncertainty (4.1σ with 10K shots per correlation) and systematic errors from extrapolation.)

---

## 8. Resource Requirements

### 8.1 Quantum Hardware

**Platform**: IonQ Aria (recommended)

**Qubit allocation**: 2 qubits (any pair with low crosstalk)

**Shot budget**: 200,000 total
- 5 noise levels × 4 correlations × 10,000 shots/correlation

**Execution time**:
- Circuit runtime: ~28 seconds (200K × 140μs)
- With overhead (queue, calibration): 2-3 hours
- Recommended: Split into 5 jobs (one per noise level, ~30 min each)

### 8.2 Cost Estimate

**IonQ Aria** ($0.00035/shot):
- 200,000 shots × $0.00035 = **$70**

**Quantinuum H2** ($0.0015/shot):
- 200,000 shots × $0.0015 = **$300**

**IBM Quantum** (free tier):
- Included in open access (but fidelity marginal)

**Recommendation**: Budget $70-300 depending on platform choice.

### 8.3 Human Resources

**Principal Investigator** (20 hours):
- Protocol finalization: 4 hours
- Pre-registration: 2 hours
- Platform setup and testing: 4 hours
- Data collection oversight: 2 hours
- Data analysis: 6 hours
- Manuscript preparation: 2 hours

**Optional Consultant** (quantum hardware specialist):
- Circuit optimization: 2-4 hours
- Calibration validation: 2 hours

### 8.4 Computational Resources

**Classical computing** (minimal):
- Data analysis: Standard laptop (Python, NumPy, SciPy, Matplotlib)
- Storage: <1 MB (raw counts and metadata)
- Processing time: <1 hour (extrapolation fits and plots)

---

## 9. Timeline

### Phase 1: Preparation (Week 1)
- **Day 1-2**: Finalize protocol, incorporate feedback
- **Day 3**: Pre-register at AsPredicted.org
- **Day 4-5**: Set up platform access (IonQ/Quantinuum account)
- **Day 6-7**: Develop and test circuit code, blind analysis pipeline

### Phase 2: Execution (Week 2)
- **Day 8**: Calibration and validation (T1, T2, gate fidelities)
- **Day 9-10**: Data collection (5 noise levels, ~6 hours total with queue time)
- **Day 11**: Validation checks (Bell state fidelity, classical bound)
- **Day 12**: Data backup and archiving

### Phase 3: Analysis (Week 3)
- **Day 13-14**: Run blind analysis pipeline (extrapolation fits)
- **Day 15**: Unblind and interpret results
- **Day 16-17**: Sensitivity analysis and cross-checks
- **Day 18-19**: Draft results section
- **Day 20-21**: Manuscript preparation and submission

**Total duration**: 3 weeks from protocol finalization to manuscript submission

---

## 10. Success Criteria and Falsification

### 10.1 Experimental Success Criteria

The experiment is considered **technically successful** if:

1. ✅ All 200,000 shots collected without hardware failures
2. ✅ Calibration remains stable (fidelity drift < 0.5%)
3. ✅ Classical bound not violated (all S(p) ≤ 2.2, allowing for noise)
4. ✅ Monotonicity observed (S decreases with increasing noise)
5. ✅ Extrapolation fits have good quality (χ²/DOF < 2)

These criteria ensure data quality regardless of theoretical outcome.

### 10.2 LRT Falsification Criteria

**LRT is falsified if**:

$$S_0 > 2.77 \quad \text{with} \quad p\text{-value} < 0.01$$

**Interpretation**:
- Zero-noise CHSH exceeds midpoint between LRT and QM predictions
- Statistical significance: >2.5σ deviation from LRT prediction
- **Conclusion**: Tsirelson bound is fundamental (QM correct, LRT wrong)

### 10.3 LRT Support Criteria

**LRT is supported if**:

$$S_0 < 2.74 \quad \text{with} \quad p\text{-value} < 0.01$$

**Interpretation**:
- Zero-noise CHSH significantly below Tsirelson bound
- Consistent with LRT prediction within uncertainty
- **Conclusion**: Evidence for intrinsic measurement cost (LRT mechanism)

### 10.4 Inconclusive Outcome

**If** $2.74 < S_0 < 2.77$:

**Action**:
1. Increase shot count (e.g., 50K shots per correlation → 2σ improvement)
2. Use higher-fidelity platform (Quantinuum H2 if not already used)
3. Add intermediate noise levels (improve extrapolation)
4. Consider systematic error sources (crosstalk, leakage)

**Reason**: Signal-to-noise may be insufficient with current parameters.

### 10.5 Unexpected Outcomes

**If** $S_0 > 2.83$ (above Tsirelson):
- **Interpretation**: Fundamental issue with experiment (impossible in QM)
- **Action**: Check for calibration errors, crosstalk, data analysis bugs
- **Do not publish** until resolved

**If** $S_0 < 2.60$ (far below LRT):
- **Interpretation**: Excessive decoherence not captured by noise model
- **Action**: Re-examine T1/T2 measurements, check for unexpected noise sources
- **Report** as anomalous result requiring further investigation

---

## 11. Ethical Considerations

### 11.1 Pre-registration

**Commitment**: This protocol will be pre-registered at **AsPredicted.org** before data collection.

**Purpose**:
- Prevent p-hacking (choosing analysis method after seeing data)
- Ensure transparency in hypothesis testing
- Document any deviations from planned protocol

**Pre-registration content**:
- Hypothesis (H1: S₀ ≤ 2.71, H0: S₀ = 2.828)
- Method (5 noise levels, extrapolation, blinding)
- Analysis plan (fit models, decision rules)
- Falsification criteria (S₀ > 2.77)

### 11.2 Data Availability

**All data will be made publicly available** upon publication:
- Raw shot counts (all 200K measurements)
- Metadata (noise levels, timestamps, calibration data)
- Analysis code (Python scripts for extrapolation and plotting)
- Pre-registration document (AsPredicted.org link)

**Repository**: Zenodo (with DOI) + GitHub (code)

### 11.3 Conflicts of Interest

**Declaration**: The PI (J.D. Longmire) is the developer of Logic Realism Theory and has a vested interest in supporting the theory. To mitigate bias:

1. **Blind analysis**: Noise level labels masked during analysis
2. **Pre-committed code**: Analysis pipeline locked before data collection
3. **Independent review**: Request external physicist to verify analysis

### 11.4 Publication Plan

**Regardless of outcome**:
- Results will be published in peer-reviewed journal
- Negative result (LRT falsified) will be reported transparently
- No selective reporting of favorable data

**Target journals**:
- *Physical Review Letters* (if strong result)
- *Physical Review A* (detailed technical report)
- ArXiv preprint (immediate dissemination)

---

## 12. References

### 12.1 Theoretical Foundation

1. **Longmire, J.D.** (2025). *Logic Realism Theory: Deriving Quantum Mechanics from Logical Consistency*. Logic Realism Theory Repository. https://github.com/jdlongmire/logic-realism-theory

2. **Tsirelson, B.S.** (1980). "Quantum generalizations of Bell's inequality". *Letters in Mathematical Physics*. 4(2): 93–100. doi:10.1007/BF00417500

3. **Clauser, J.F., Horne, M.A., Shimony, A., Holt, R.A.** (1969). "Proposed experiment to test local hidden-variable theories". *Physical Review Letters*. 23(15): 880–884. doi:10.1103/PhysRevLett.23.880

### 12.2 Experimental Methods

4. **Aspect, A., Dalibard, J., Roger, G.** (1982). "Experimental test of Bell's inequalities using time-varying analyzers". *Physical Review Letters*. 49(25): 1804–1807. doi:10.1103/PhysRevLett.49.1804

5. **Hensen, B., et al.** (2015). "Loophole-free Bell inequality violation using electron spins separated by 1.3 kilometres". *Nature*. 526: 682–686. doi:10.1038/nature15759

6. **Shalm, L.K., et al.** (2015). "Strong loophole-free test of local realism". *Physical Review Letters*. 115(25): 250402. doi:10.1103/PhysRevLett.115.250402

### 12.3 Platform Documentation

7. **IonQ Aria**. Technical specifications. https://ionq.com/quantum-systems/aria

8. **Quantinuum H2**. System Model H2 Product Data Sheet. https://www.quantinuum.com/hardware/h2

9. **IBM Quantum Heron**. IBM Quantum System Two. https://www.ibm.com/quantum/systems

### 12.4 Data Analysis

10. **Ekert, A., et al.** (2002). "Direct estimations of linear and nonlinear functionals of a quantum state". *Physical Review Letters*. 88(21): 217901. doi:10.1103/PhysRevLett.88.217901

11. **Řeháček, J., et al.** (2007). "Multiple-photon resolving fiber-loop detector". *Physical Review A*. 76(4): 043820. doi:10.1103/PhysRevA.76.043820

---

## Appendix A: Circuit Specifications (OpenQASM 3)

### A.1 Bell State Preparation + Measure E(a,b)

```qasm
OPENQASM 3.0;
include "stdgates.inc";

// Qubits
qubit[2] q;
bit[2] c;

// Bell state |Φ⁺⟩
h q[0];
cx q[0], q[1];

// Alice: a=0° (no rotation, measure Z)
// Bob: b=45° (rotate by π/4)
ry(pi/4) q[1];

// Measure
measure q -> c;
```

### A.2 Complete Circuit Set

**E(a,b)**: Bob Ry(π/4)
**E(a,b')**: Bob Ry(-π/4)
**E(a',b)**: Alice H, Bob Ry(π/4)
**E(a',b')**: Alice H, Bob Ry(-π/4)

(Full code available in repository: `/scripts/bell_ceiling_test/`)

---

## Appendix B: Noise Insertion Method

### B.1 Depolarizing Noise via Idle Time

To parametrically add noise, insert identity gates with controlled idle times:

```python
def add_noise_level(circuit, noise_param_p):
    """
    Add depolarizing noise by inserting idle time.

    Parameters:
    - circuit: Qiskit QuantumCircuit
    - noise_param_p: Target depolarizing probability (0-0.05)

    Returns:
    - Modified circuit with idle time
    """
    # Calibrated T1 and T2 (example values for IonQ Aria)
    T1 = 1.0  # seconds
    T2 = 1.0  # seconds

    # Calculate idle time to achieve desired p
    # Depolarizing: p ≈ 1 - exp(-t/T_eff), T_eff ≈ (T1 + T2)/2
    T_eff = (T1 + T2) / 2
    t_idle = -T_eff * np.log(1 - noise_param_p)

    # Insert barrier (idle time) after Bell state preparation
    circuit.barrier()
    circuit.delay(t_idle, unit='s')
    circuit.barrier()

    return circuit
```

### B.2 Validation

Before experiment, verify noise calibration:
1. Prepare |+⟩ state
2. Insert idle time corresponding to each noise level
3. Measure in X basis
4. Calculate fidelity F = (1 + ⟨X⟩)/2
5. Confirm F ≈ 1 - p (expected depolarizing)

---

## Appendix C: Analysis Code Structure

### C.1 Blind Analysis Pipeline

```python
# File: blind_analysis.py
# Pre-committed to GitHub before data collection

import numpy as np
from scipy.optimize import curve_fit

def load_blinded_data(filename):
    """Load data with masked noise labels"""
    # Noise level IDs randomized (analyst doesn't know which is 0%)
    return data, noise_labels_masked

def calculate_correlations(counts):
    """E(a,b) = (N_00 + N_11 - N_01 - N_10) / N"""
    N_00, N_01, N_10, N_11 = counts
    N = sum(counts)
    return (N_00 + N_11 - N_01 - N_10) / N

def calculate_chsh(E_ab, E_abp, E_apb, E_apbp):
    """S = E(a,b) + E(a,b') + E(a',b) - E(a',b')"""
    return E_ab + E_abp + E_apb - E_apbp

def fit_extrapolation(noise_levels, S_values):
    """Fit S(p) and extract S_0"""
    # Try linear, quadratic, exponential
    # Return best fit based on χ²/DOF
    pass

def unblind_and_interpret(S_0, delta_S_0):
    """Compare to predictions after analysis complete"""
    S_LRT = 2.711
    S_QM = 2.828

    z_LRT = (S_0 - S_LRT) / delta_S_0
    z_QM = (S_0 - S_QM) / delta_S_0

    if z_LRT > 5:
        print("Result: LRT falsified, QM supported")
    elif z_QM < -5:
        print("Result: QM bound violated, LRT supported")
    else:
        print("Result: Inconclusive or intermediate")

    return z_LRT, z_QM
```

---

## Appendix D: Pre-Registration Checklist

Before submitting to AsPredicted.org:

- [ ] Hypothesis clearly stated (H1: S₀ ≤ 2.71, H0: S₀ = 2.828)
- [ ] Method fully specified (5 noise levels, extrapolation fits)
- [ ] Sample size justified (200K shots, power analysis)
- [ ] Analysis plan committed (fit models, decision rules)
- [ ] Falsification criteria defined (S₀ > 2.77)
- [ ] Primary outcome identified (S₀, zero-noise extrapolated CHSH)
- [ ] Blinding procedure described (masked noise labels)
- [ ] Code repository public (GitHub, analysis pipeline)
- [ ] Data availability plan (Zenodo DOI upon publication)
- [ ] Conflicts of interest declared (PI is theory developer)

**Submission date**: [To be filled before data collection]
**AsPredicted.org ID**: [To be filled after submission]

---

**Protocol Version**: 1.0
**Status**: Draft for review
**Next Steps**: Peer review → Pre-registration → Execution
**Contact**: James D. Longmire (james.longmire@example.com)

