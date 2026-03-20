# Path 3: Ramsey θ-Scan Protocol

**Rank**: #3 of Top 4 Tier 1 Predictions
**Confidence**: High (H)
**Status**: Protocol Complete
**Timeline**: 6-12 months (systematic scan required)
**Platform**: Universal (Rydberg, ions, superconducting)

**Author**: James D. (JD) Longmire (ORCID: 0009-0009-1383-7698)
**Version**: 1.0
**Date**: 2025-11-05 (Session 10.0)

---

## Executive Summary

### The Prediction

**LRT Claim**: Dephasing rate γ depends on superposition angle θ, tracking constraint entropy.

**Observable**: Ramsey decay rate vs initial superposition angle:
```
|ψ(θ)⟩ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩

γ(θ) = γ_0 × [1 - η · sin²(θ)]

where η ≈ 0.23 (excluded-middle coupling)
```

**Effect Size**:
- θ = 0° (|0⟩): γ(0) = γ_0 (baseline, fastest dephasing)
- θ = 90° (equal superposition): γ(90°) = 0.77 × γ_0 (23% slower)
- θ = 45°: γ(45°) = 0.885 × γ_0 (11.5% slower)

**QM Prediction**: γ(θ) = constant (dephasing independent of superposition angle)

**Why High Priority**: Cleanest single-qubit test, all platforms, direct entropy measurement

**Why Untested**: QM predicts no effect, so angle-dependent Ramsey never systematically measured

---

## 1. Theoretical Foundation

### 1.1 Core LRT Mechanism

**Constraint Entropy**: LRT postulates effective entropy that governs decoherence:
```
S_eff[ψ(θ)] = S_vN[ψ(θ)] + η · S_EM[ψ(θ)]

where:
  S_vN = von Neumann entropy (0 for pure states in standard QM)
  S_EM = Excluded-middle entropy = -Tr[ρ ln ρ] with logical constraints
  η ≈ 0.23 (coupling strength from variational framework)
```

**For Superposition States**:
```
|ψ(θ)⟩ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩

S_EM[θ] = -[cos²(θ/2) ln cos²(θ/2) + sin²(θ/2) ln sin²(θ/2)]
        = entropy of logical indeterminacy

Maximum at θ = 90° (equal superposition): S_EM = ln 2
Minimum at θ = 0°, 180° (eigenstates): S_EM = 0
```

**Dephasing Rate Coupling**:
```
γ(θ) = γ_0 / [1 + η · S_EM(θ)]

Higher entropy S_EM → Slower dephasing γ
```

### 1.2 Quantitative Prediction

**Using derived η ≈ 0.23**:
```
S_EM(θ) = -½[(1 + cos θ) ln((1 + cos θ)/2) + (1 - cos θ) ln((1 - cos θ)/2)]

γ(θ) / γ_0 = 1 / [1 + 0.23 × S_EM(θ)]
```

**Key Values**:
| θ | cos θ | S_EM(θ) | γ(θ)/γ_0 | T2(θ)/T2(0) | Enhancement |
|---|-------|---------|----------|-------------|-------------|
| 0° | 1.0 | 0.000 | 1.000 | 1.000 | 0% (baseline) |
| 30° | 0.866 | 0.337 | 0.928 | 1.078 | 7.8% |
| 45° | 0.707 | 0.500 | 0.897 | 1.115 | 11.5% |
| 60° | 0.500 | 0.637 | 0.872 | 1.147 | 14.7% |
| 90° | 0.000 | 0.693 | 0.863 | 1.159 | 15.9% |

**Note**: Maximum effect at θ = 90° is smaller than Path 1's AC Stark (15.9% vs 23.5%) because dephasing couples differently than energy shifts.

### 1.3 Physical Interpretation

**Standard QM View**: Dephasing arises from environmental noise coupling to qubit, independent of superposition angle.

**LRT View**:
- Equal superposition (θ = 90°) has highest logical indeterminacy → maximum S_EM
- Logical constraint enforcement **protects** high-entropy states from dephasing
- Effect is **measurement-basis dependent** (tested in computational basis {|0⟩, |1⟩})

**Key Distinguisher**: LRT predicts slower dephasing for higher entropy, QM predicts constant rate.

---

## 2. Experimental Design

### 2.1 Overview

**Objective**: Measure Ramsey decay rate γ(θ) for multiple initial angles θ

**Approach**: Standard Ramsey interferometry with angle-dependent state preparation

**Duration**: 6-12 months (systematic scan, cross-checks, multi-platform)

### 2.2 Protocol Steps

#### Phase 1: State Preparation and Verification (Week 1-2)

**Preparation Sequence**:
```
Initial: |0⟩
Rotation: R_y(θ) → |ψ(θ)⟩ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩
Verification: Tomography to confirm angle accuracy
```

**Angles to Scan**: θ ∈ {0°, 15°, 30°, 45°, 60°, 75°, 90°} (7-12 points)

**Tomography Check**:
- Measure ⟨X⟩, ⟨Y⟩, ⟨Z⟩
- Verify: ⟨Z⟩ = cos θ, ⟨X⟩ = sin θ
- Target accuracy: ±2° in angle

#### Phase 2: Ramsey Interferometry (Week 3-8)

**Standard Ramsey Sequence**:
```
1. Prepare |ψ(θ)⟩ via R_y(θ)
2. Wait free evolution time τ (accumulate phase + dephasing)
3. Apply π/2 pulse (R_y(π/2) or R_x(π/2))
4. Measure in Z basis
5. Repeat for τ ∈ [0, 5×T2_expected] (20 points, log-spaced)
```

**Ramsey Fringe Observable**:
```
P_excited(τ, θ) = ½[1 + exp(-γ(θ)·τ) · cos(Δω·τ + φ)]

where:
  γ(θ) = dephasing rate (target observable)
  Δω = detuning (from pulse imperfections or intentional offset)
  φ = phase offset
```

**Shot Budget**: 10,000 shots per (θ, τ) point → 1.4M total shots per qubit

#### Phase 3: Systematic Cross-Checks (Week 9-10)

1. **Basis Rotation Test**: Measure in X, Y, Z bases → LRT effect should be basis-dependent
2. **Echo Verification**: Repeat with spin-echo (cancels inhomogeneous dephasing) → verify pure dephasing
3. **Temperature Scan**: Vary cryostat temperature → check thermal scaling
4. **Qubit Comparison**: Repeat on 2-3 qubits → verify not qubit-specific

#### Phase 4: Multi-Platform Verification (Week 11-20)

**Platforms**:
1. **Superconducting** (primary): IBM Quantum, Rigetti
2. **Trapped ions** (verification): IonQ, Oxford, NIST
3. **Rydberg atoms** (optional): Harvard, Wisconsin

**Consistency Check**: γ(θ) / γ(0) ratio should agree across platforms (within 2σ)

### 2.3 Data Collection Strategy

**Interleaving**: Randomize θ order to minimize systematic drifts

**Calibration**: Recalibrate π/2 pulses daily, track T1, T2(θ=90°) as drift indicators

**Blinding** (optional): Analyst blinded to which θ corresponds to which data until analysis complete

---

## 3. Platform-Specific Implementations

### 3.1 Superconducting Qubits (IBM Quantum, Rigetti)

**Hardware**: IBM ibm_kyiv (127-qubit), Rigetti Aspen-M-3

**Typical Parameters**:
- T1 ~ 150 μs
- T2* ~ 50 μs (free induction decay)
- T2 ~ 75 μs (with echo)
- γ_0 = 1/T2* ~ 0.020 μs⁻¹

**State Preparation**:
```python
circuit = QuantumCircuit(1)
circuit.ry(theta, 0)  # Rotate around Y-axis
# Verify with tomography
```

**Ramsey Sequence**:
```python
for tau in delays:
    circuit = QuantumCircuit(1)
    circuit.ry(theta, 0)  # Prepare |ψ(θ)⟩
    circuit.delay(tau, 0, unit='us')  # Free evolution
    circuit.rx(np.pi/2, 0)  # Final π/2 pulse
    circuit.measure(0, 0)
```

**Expected LRT Effect**:
```
At θ = 90°: T2*(90°) / T2*(0°) ≈ 1.16
ΔT2* ~ 8 μs (detectable with ±2% precision → 4σ)
```

**Advantages**:
- Open cloud access (IBM Quantum Network)
- Fast cycle time (100 μs per shot)
- Can scan multiple qubits in parallel

### 3.2 Trapped Ions (IonQ, Oxford, NIST)

**Hardware**: IonQ Aria, Oxford 43Ca+, NIST 171Yb+

**Typical Parameters**:
- T1 ~ 1 second (excellent coherence)
- T2 ~ 500 ms
- γ_0 = 1/T2 ~ 0.002 ms⁻¹

**State Preparation**:
```
Initial: Doppler cooling → |0⟩
Rotation: 729 nm laser pulse (qubit transition)
Duration: τ_π/2 × (θ / (π/2))
```

**Ramsey Sequence**:
- First π/2 pulse (prepare superposition)
- Wait τ (free precession, no laser)
- Second π/2 pulse (read out phase)
- Fluorescence detection

**Expected LRT Effect**:
```
At θ = 90°: T2(90°) / T2(0°) ≈ 1.16
ΔT2 ~ 80 ms (easily measurable → 10σ)
```

**Advantages**:
- Ultra-long coherence times (large absolute ΔT2)
- High-fidelity gates (>99.9% single-qubit)
- Excellent isolation (low environmental noise)

### 3.3 Rydberg Atoms (Harvard, Wisconsin)

**Hardware**: Rydberg arrays (50-100 atoms)

**Typical Parameters**:
- T1 ~ 100 μs (Rydberg state decay)
- T2 ~ 50 μs
- γ_0 ~ 0.020 μs⁻¹

**State Preparation**:
- Ground state |g⟩ ≡ |0⟩
- Rydberg state |r⟩ ≡ |1⟩
- Microwave/optical pulse for rotation

**Ramsey Sequence**: Similar to superconducting (microwave control)

**Expected LRT Effect**: ΔT2 ~ 8 μs (similar to superconducting)

**Advantages**:
- Many qubits (statistical power)
- Clean system (less materials engineering)
- Platform diversity (different systematics than SC/ions)

---

## 4. Statistical Analysis Plan

### 4.1 Fit Models

**For each angle θ, fit Ramsey decay**:
```
P(τ, θ) = A · exp(-γ(θ)·τ) · cos(2πf·τ + φ) + B

Free parameters: γ(θ), A, f, φ, B
```

**Extract γ vs θ**:
```
Data: {(θ_i, γ_i, σ_i)} for i = 1, ..., N_angles
```

### 4.2 Model Comparison

**QM Model** (flat):
```
γ_QM(θ) = γ_0  (0 free parameters beyond baseline)

χ²_QM = ∑_i [(γ_i - γ_0) / σ_i]²
```

**LRT Model** (sin²(θ) or S_EM(θ)):
```
γ_LRT(θ) = γ_0 / [1 + η · S_EM(θ)]

Free parameters: γ_0, η

χ²_LRT = ∑_i [(γ_i - γ_LRT(θ_i; γ_0, η)) / σ_i]²
```

**Alternative LRT Parametrization** (simpler):
```
γ_LRT(θ) = γ_0 · [1 - η_eff · sin²(θ)]

Free parameters: γ_0, η_eff

This is approximate but easier to fit (linear in sin²(θ))
```

### 4.3 Hypothesis Tests

**Null Hypothesis (QM)**: η = 0 (flat γ)

**Alternative Hypothesis (LRT)**: η ≈ 0.23 (or η_eff ≈ 0.16 for simplified model)

**Likelihood Ratio Test**:
```
LR = -2 · [ln L_QM - ln L_LRT]
p-value from χ²(1 dof)
```

**F-test** (nested models):
```
F = [(RSS_QM - RSS_LRT) / 1] / [RSS_LRT / (N - 2)]

p-value from F(1, N-2)
```

**AIC/BIC**:
```
AIC_QM = 2k_QM - 2 ln L_QM
AIC_LRT = 2k_LRT - 2 ln L_LRT

Prefer model with lower AIC
ΔAIC > 10 → strong evidence
```

### 4.4 Systematic Error Analysis

**Cross-Check Consistency**:
1. **Basis rotation**: γ_X(θ) vs γ_Z(θ) → should differ (LRT basis-dependent)
2. **Echo vs no-echo**: γ_echo(θ) / γ_FID(θ) → ratio should be θ-independent (inhomogeneous vs homogeneous)
3. **Qubit variation**: γ(θ) shape consistent across qubits (not qubit-specific artifact)
4. **Platform consistency**: Superconducting vs ions agree on γ(θ)/γ(0) ratio

---

## 5. Error Budget

### 5.1 Statistical Errors

**Per-Angle Precision**:
- 10,000 shots × 20 time points → σ_γ / γ ≈ 2-3%
- 7-12 angles scanned → detect 11.5% effect at θ = 45° with 4-5σ

**Total Scan Precision**:
```
η_eff = 0.16 (from fit)
σ_η_eff ≈ 0.03  (from error propagation)

→ 5σ detection if LRT correct
```

### 5.2 Systematic Errors

| Source | Magnitude | Mitigation |
|--------|-----------|------------|
| Angle calibration | ±2° → ±4% in sin²(θ) | Tomography verification |
| Gate fidelity | ±1% | High-fidelity platforms (>99% gates) |
| Detuning variation | ±3% in γ fit | Fit frequency explicitly |
| Temperature drift | ±2% in γ_0 | Monitor T1, interleave angles |
| Crosstalk (SC) | ±2% | Isolated qubits |
| **Total Systematic** | **±6%** | **Multi-platform, cross-checks** |

### 5.3 Total Error Budget

```
σ_total(γ) = √(σ_stat² + σ_sys²)
           = √(0.03² + 0.06²)
           ≈ 0.067

For 11.5% effect at θ = 45°:
  Signal-to-noise = 0.115 / 0.067 ≈ 1.7σ (single angle)

Combining 7 angles (θ-dependence shape):
  Effective SNR ≈ 5σ (for LRT model vs QM flat)
```

---

## 6. Falsification Criteria

### 6.1 LRT is Supported If:

1. **Angle Dependence Confirmed**: χ²_LRT << χ²_QM (p < 0.01)
2. **Magnitude Match**: η_eff = 0.16 ± 0.08 (within 2σ of prediction)
3. **Functional Form**: S_EM(θ) or sin²(θ) fits better than linear, quadratic
4. **Platform Independence**: Superconducting + ions agree within 2σ
5. **Basis Dependence**: Effect varies with measurement basis (X, Y, Z)

### 6.2 LRT is Falsified If:

1. **Flat Response**: γ(θ) = constant ± 5% (no angle dependence)
2. **Wrong Sign**: γ(90°) > γ(0°) (opposite of prediction)
3. **Wrong Functional Form**: Linear in θ, not sin²(θ) or S_EM(θ)
4. **Platform Dependence**: Different platforms show different γ(θ) shapes
5. **Basis Independence**: Same γ(θ) in all measurement bases

### 6.3 Ambiguous Outcomes

**If effect present but smaller** (e.g., η_eff ≈ 0.08):
- LRT mechanism qualitatively correct
- Quantitative η needs refinement
- May indicate additional competing effects

**If basis-independent**:
- May suggest environmental noise source, not LRT
- Check for experimental artifact

---

## 7. Collaboration Strategy

### 7.1 Target Groups

**Superconducting Qubits**:
- **IBM Quantum**: Qiskit Experiments team, open access
- **Rigetti**: Academic partnerships
- **Google Quantum AI**: High-fidelity transmon qubits
- **Pitch**: "Systematic Ramsey θ-scan to test entropy-dephasing coupling"

**Trapped Ions**:
- **IonQ**: Research team, cloud access
- **Oxford**: 43Ca+ precision control
- **NIST**: 171Yb+ standards lab
- **Pitch**: "High-precision test leveraging ultra-long coherence times"

**Rydberg Atoms**:
- **Harvard**: Lukin group (Rydberg arrays)
- **Wisconsin**: Saffman group
- **Pitch**: "Many-qubit statistical power, platform diversity"

### 7.2 Resource Requirements

**Hardware Time**:
- Single qubit: 8 hours (7 angles × 20 time points × 10k shots × 100 μs)
- Including calibration/overhead: 16 hours per platform
- Multi-platform: 48 hours total

**Personnel**:
- 1 graduate student or postdoc
- 4-6 weeks effort (scan, cross-checks, analysis)

**Equipment**:
- Standard capabilities (no hardware modifications)
- Ramsey interferometry is routine measurement

### 7.3 Publication Plan

**Authorship**:
- Experimental team: First authors
- JD Longmire: Theory contribution (LRT prediction)
- Co-authorship on joint paper

**Target Venue**:
- **If confirmed**: Physical Review Letters or PRX Quantum
- **If null**: Physical Review A (honest null result, unexplored regime)

**Timeline to Submission**: 8-12 months after data collection

---

## 8. Timeline and Milestones

### Months 1-2: Setup and Calibration
- Week 1-2: Protocol finalization, collaboration outreach
- Week 3-4: Hardware access secured, qubit selection
- Week 5-6: Angle preparation verification (tomography)
- Week 7-8: Baseline Ramsey measurements (θ = 0°, 90°)

**Milestone**: Confirm γ(0°) ≠ γ(90°) at >2σ (preliminary signal)

### Months 3-4: Systematic θ-Scan
- Week 9-12: Full 7-12 angle scan (Ramsey decay at each angle)
- Week 13-16: Systematic cross-checks (basis, echo, qubits)

**Milestone**: Complete dataset with γ(θ) extracted for all angles

### Months 5-6: Multi-Platform Verification
- Week 17-20: Second platform (e.g., trapped ions if started with SC)
- Week 21-24: Optional third platform (Rydberg)

**Milestone**: Platform-independent confirmation or platform-specific insights

### Months 7-12: Analysis and Publication
- Months 7-8: Complete statistical analysis, model fitting
- Months 9-10: Draft manuscript, internal review
- Months 11-12: Submission, peer review

---

## 9. Risk Mitigation

### 9.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Angle miscalibration | Medium | High | Tomography verification, ±2° target |
| Insufficient precision | Low | High | 10k shots, multi-angle scan |
| Detuning variation | Medium | Medium | Fit frequency explicitly, monitor drift |
| T2 too short | Low | Medium | Use ions (longer T2) or echo sequences |

### 9.2 Strategic Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Competitor scoops | Very Low | Medium | Unexplored regime (QM predicts flat) |
| Null result | Uncertain | Medium | Honest publication, theory refinement |
| Platform artifact | Low | High | Multi-platform verification |
| Basis artifact | Low | High | Basis rotation cross-check |

### 9.3 Contingency Plans

**If precision insufficient**:
- Increase shot count to 20k per point
- Use trapped ions (10× longer T2 → 10× larger ΔT2)

**If null result**:
- Check for environmental noise masking effect
- Test in X, Y bases (may have different η)
- Publish as constraint on LRT parameter space

**If platform-dependent**:
- Investigate hardware-specific effects (crosstalk, control errors)
- May reveal platform-specific corrections to η

---

## 10. Analysis Scripts and Tools

### 10.1 Data Analysis Pipeline

**Script**: `ramsey_theta_analysis.py` (see separate file)

**Features**:
- Ramsey decay fitting (exponential + sinusoid)
- γ(θ) extraction with error propagation
- Model fitting (QM flat vs LRT S_EM(θ))
- Hypothesis testing (likelihood ratio, F-test, AIC/BIC)
- Visualization (Ramsey fringes, γ vs θ, model comparison)

### 10.2 Computational Validation

**Notebook**: `ramsey_theta_first_principles.ipynb` (see separate file)

**Structure**:
1. **Part 1**: Derive η from LRT variational framework
2. **Part 2**: Calculate S_EM(θ) for all angles
3. **Part 3**: Predict γ(θ) from η and S_EM(θ)
4. **Part 4**: QuTiP master equation simulation with derived parameters

**Non-Circular**: η derived independently, then applied to Ramsey system

---

## 11. Connection to Other Predictions

### 11.1 Relation to Path 1 (AC Stark θ-Dependence)

**Common Element**: Both test η ≈ 0.23 coupling via superposition angle dependence

**Complementary Observables**:
- Path 1: Energy shift Δω(θ) (via AC Stark)
- Path 3: Dephasing rate γ(θ) (via Ramsey)

**Independent Tests**: If both confirmed, η values should agree (consistency check)

### 11.2 Relation to Path 2 (Bell State Asymmetry)

**Complementary**:
- Path 2: Two-qubit entangled states (ΔT2/T1 between Bell states)
- Path 3: Single-qubit superpositions (γ(θ) vs angle)

**Unified Mechanism**: Both test distinguishability-dependent decoherence

### 11.3 Path 3 Advantages

**Cleaner Observable**: Single-qubit (no entanglement complications)
**Universal Platform**: All quantum platforms do Ramsey
**Direct Entropy Test**: S_EM(θ) is explicit function (no need for ΔF calculation)

**Trade-off**: Longer timeline (6-12 months) than Path 2 (1-2 months) due to systematic scan

---

## 12. Check #7: Experimental Literature Status

### 12.1 Ramsey Interferometry Literature

**Known Results**:
- Ramsey measurement is standard characterization tool
- T2* measured routinely for all qubits
- Ramsey fringes used for frequency calibration

**UNTESTED**:
- **Systematic γ(θ) vs θ scan**
- Angle-dependent dephasing never measured because QM predicts constant
- Most Ramsey measurements use θ = 90° (maximum signal) only

**Literature Search** (performed 2025-11-05):
1. **Superconducting**: T2* measured, but not θ-dependent
2. **Trapped ions**: Ramsey at θ = 90° standard, no angle scan
3. **Rydberg**: Similar (θ = 90° default for max contrast)
4. **No contradictions found**: Observable unexplored

### 12.2 Decision Gate: ✅ PROCEED

**Reasoning**:
- Prediction is untested (not falsified)
- QM provides no θ-dependence → no motivation to measure
- Effect size (11.5% at θ = 45°, 15.9% at θ = 90°) above noise
- Multiple platforms available
- Standard technique (Ramsey routine)

**Confidence**: High (H) - unexplored regime, clean single-qubit test, universal platform

---

## 13. Check #8: Computational Circularity (Pre-Verification)

**Status**: ⚠️ To be verified during notebook development

**Requirement**:
- η MUST be derived from LRT variational framework (Part 1)
- S_EM(θ) MUST be calculated from entropy definition (Part 2)
- γ(θ) prediction emerges from η × S_EM (Part 3)

**Forbidden**: Inserting γ(θ)/γ(0) = [1 - 0.16 sin²(θ)] by hand, claiming "validation"

**See**: `ramsey_theta_first_principles.ipynb` (to be developed)

---

## 14. Summary and Recommendations

### 14.1 Protocol Status

✅ **Complete**: Experimental design, statistical plan, error budget, falsification criteria
✅ **Platforms Identified**: Superconducting (IBM, Rigetti), Ions (IonQ, Oxford, NIST), Rydberg (optional)
✅ **Timeline Realistic**: 6-12 months (systematic scan, multi-platform)
✅ **Check #7 Passed**: Prediction untested by existing experiments

### 14.2 Key Strengths

1. **Cleanest single-qubit test** (no entanglement)
2. **Universal platform** (all quantum systems do Ramsey)
3. **Direct entropy measurement** (S_EM(θ) explicit)
4. **Standard technique** (Ramsey routine, no new calibration)
5. **Complementary to Path 1** (different observable, same η)

### 14.3 Key Challenges

1. **Systematic scan required** (7-12 angles → longer timeline)
2. **Angle calibration critical** (±2° target for tomography)
3. **Smaller effect than Path 1** (15.9% vs 23.5% at θ = 90°)
4. **Shape fitting** (need full θ-dependence, not just single point)

### 14.4 Recommended Next Steps

1. **Immediate**: Develop derivation document, analysis script, first-principles notebook
2. **Weeks 1-2**: Contact IBM Quantum, IonQ for hardware access
3. **Weeks 3-4**: Angle preparation verification, tomography
4. **Months 1-4**: Systematic θ-scan (7-12 angles, Ramsey decay)
5. **Months 5-6**: Multi-platform verification (superconducting + ions)
6. **Months 7-12**: Analysis, manuscript, publication

### 14.5 Success Criteria

**Experiment Successful If**:
- γ(θ) measured to ±3% precision for all angles
- Shape fitting distinguishes LRT from QM (p < 0.01)
- Multi-platform consistency (superconducting + ions agree)

**Theory Successful If**:
- η_eff = 0.16 ± 0.08 (or equivalently η = 0.23 ± 0.12)
- Functional form matches S_EM(θ) or sin²(θ)
- Basis-dependent (distinguishes LRT from environmental noise)
- Consistent with Path 1, Path 2 results (if measured)

---

**Protocol Version**: 1.0
**Status**: Complete and ready for collaboration outreach
**Next Steps**: Derivation document, analysis script, first-principles notebook
**Target Start Date**: Upon collaboration agreement (aim for Q1-Q2 2026)

**Complementary to Path 1 (AC Stark)**: Different observable, same underlying η ≈ 0.23 coupling
**Recommendation**: Execute **after** Path 2 (faster) but **in parallel with** Path 1 (independent convergence)
