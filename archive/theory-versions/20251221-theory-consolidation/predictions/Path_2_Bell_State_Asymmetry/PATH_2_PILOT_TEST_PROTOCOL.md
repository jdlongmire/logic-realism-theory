# Path 2 Pilot Test Protocol: Bell State Asymmetry (ΔT2/T1)

**Version**: 1.0
**Date**: November 5, 2025
**Author**: James D. Longmire
**Status**: DRAFT (Task 3.1 - Session 12.0)

---

## Executive Summary

**Objective**: Experimentally test LRT prediction that Bell states |Φ+⟩ and |Ψ+⟩ exhibit different T2/T1 ratios due to Fisher information asymmetry.

**Prediction**: ΔT2/T1 = (T2/T1)|Ψ+⟩ - (T2/T1)|Φ+⟩ ≈ 0.19 ± 0.05

**Timeline**: 1-2 months (pilot test)

**SNR**: 12σ (highest among all 4 prediction paths)

**Platform**: IBM Quantum (primary), IonQ (validation)

**Resource Requirements**:
- IBM Quantum Premium access (or academic collaboration)
- 2-qubit system with T1 > 100 μs, T2 > 50 μs
- State tomography capability
- ~100-200 circuit shots per measurement

---

## 1. Experimental Design

### 1.1 Three-Point Measurement Strategy

**Objective**: Measure ΔT2/T1 with sufficient confidence to distinguish LRT from QM predictions

#### **Point 1: Baseline Measurement (IBM Quantum)**

**Protocol**:
1. Prepare |Φ+⟩ = (|00⟩ + |11⟩)/√2 (even parity Bell state)
2. Measure T1 via population decay (variable delay, Z-basis measurement)
3. Measure T2 via coherence decay (Ramsey-type sequence, X-basis measurement)
4. Calculate (T2/T1)|Φ+⟩

5. Prepare |Ψ+⟩ = (|01⟩ + |10⟩)/√2 (odd parity Bell state)
6. Measure T1 via population decay
7. Measure T2 via coherence decay
8. Calculate (T2/T1)|Ψ+⟩

9. Calculate ΔT2/T1 = (T2/T1)|Ψ+⟩ - (T2/T1)|Φ+⟩

**Expected Results**:
- **LRT**: ΔT2/T1 ≈ 0.19 (38% enhancement for |Ψ+⟩)
- **QM**: ΔT2/T1 ≈ 0.00 (no asymmetry predicted)

**Shots**: 200 per delay point × 20 delay points × 2 states = 8,000 shots total

**Duration**: ~2 hours (including calibration)

---

#### **Point 2: Validation Measurement (IonQ)**

**Objective**: Verify result is platform-independent (not IBM-specific artifact)

**Protocol**: Identical to Point 1, adapted for trapped-ion platform

**Why IonQ**:
- Different noise model (trapped ions vs superconducting qubits)
- Different two-qubit gate implementation (Mølmer-Sørensen vs iSWAP/CZ)
- Rules out platform-specific systematic errors

**Duration**: ~2 hours (pending IonQ access)

---

#### **Point 3: Null Test (Control Measurement)**

**Objective**: Rule out systematic errors unrelated to Bell state parity

**Protocol**:
1. Prepare product states |00⟩ and |01⟩ (NOT entangled)
2. Measure T1, T2 for both states
3. Calculate ΔT2/T1 for product states

**Expected Results**:
- **LRT**: ΔT2/T1 ≈ 0.00 (no entanglement → no Fisher information asymmetry)
- **QM**: ΔT2/T1 ≈ 0.00 (agrees with LRT for product states)

**Interpretation**:
- If Point 1 shows ΔT2/T1 > 0 BUT Point 3 also shows ΔT2/T1 > 0 → systematic error (not LRT effect)
- If Point 1 shows ΔT2/T1 > 0 AND Point 3 shows ΔT2/T1 ≈ 0 → consistent with LRT

**Duration**: ~1 hour

---

### 1.2 Decision Tree Protocol

**After Point 1 (Baseline Measurement)**:

```
Measure ΔT2/T1 on IBM Quantum
         |
         ├─→ ΔT2/T1 > 0.15 (within 20% of prediction)
         |   └─→ ✅ PROCEED to Point 2 (IonQ validation)
         |       └─→ If IonQ confirms: Full study (100+ circuits)
         |       └─→ If IonQ differs: Investigate platform dependence
         |
         ├─→ 0.05 < ΔT2/T1 < 0.15 (weak signal, 25-75% of prediction)
         |   └─→ ⚠️ INVESTIGATE T1 asymmetry assumption
         |       └─→ Measure T1(|Φ+⟩) vs T1(|Ψ+⟩) independently
         |       └─→ If T1 asymmetry confirmed: Revise prediction model
         |       └─→ If T1 symmetric: Check T2 measurement methodology
         |
         └─→ ΔT2/T1 < 0.05 (no signal, <25% of prediction)
             └─→ ❌ PATH 2 FALSIFIED
                 └─→ PIVOT to Path 1 (AC Stark θ) or Path 3 (Ramsey θ)
                 └─→ Document null result (valuable for LRT falsification)
```

---

## 2. Measurement Procedures

### 2.1 Bell State Preparation

**|Φ+⟩ Preparation** (even parity):
```
Circuit:
|0⟩ ─H─●─────
|0⟩ ───X─────
     |Φ+⟩
```

**|Ψ+⟩ Preparation** (odd parity):
```
Circuit:
|0⟩ ─H─●─X───
|0⟩ ───X─────
     |Ψ+⟩
```

**Verification**: State tomography (Pauli basis measurements) to confirm fidelity > 0.95

---

### 2.2 T1 Measurement (Population Decay)

**Sequence**:
```
Prepare Bell state → Delay (τ) → Z-basis measurement
```

**Delay Points**: τ = [0, 10, 20, 30, ..., 200] μs (20 points, 0 to ~1.5×T1)

**Observable**: Bell state population P(|Bell⟩, τ) = ⟨ψ|ρ(τ)|ψ⟩

**Fit**: P(τ) = A × exp(-τ/T1) + B (exponential decay)

**Output**: T1 ± σ_T1 (error from fit uncertainty)

---

### 2.3 T2 Measurement (Coherence Decay)

**Sequence** (Ramsey-type):
```
Prepare Bell state → Delay (τ) → Coherence revival pulse → X-basis measurement
```

**Delay Points**: τ = [0, 5, 10, 15, ..., 100] μs (20 points, 0 to ~1.5×T2)

**Observable**: Off-diagonal density matrix elements (coherence)

**Fit**: C(τ) = A × exp(-τ/T2) (exponential decay)

**Output**: T2 ± σ_T2 (error from fit uncertainty)

**Note**: T2* (free induction decay) vs T2 (spin echo) - use appropriate sequence for platform

---

### 2.4 Error Propagation

**ΔT2/T1 Calculation**:
```
ΔT2/T1 = (T2/T1)|Ψ+⟩ - (T2/T1)|Φ+⟩
```

**Error Propagation**:
```
σ_ΔT2/T1 = sqrt[(σ_T2_Psi/T1_Psi)² + (T2_Psi × σ_T1_Psi / T1_Psi²)²
                + (σ_T2_Phi/T1_Phi)² + (T2_Phi × σ_T1_Phi / T1_Phi²)²]
```

**Target Precision**: σ_ΔT2/T1 < 0.05 (to distinguish ΔT2/T1 = 0.19 from 0.00 at >3σ)

---

## 3. Resource Requirements

### 3.1 IBM Quantum Access

**Preferred Systems**:
- **ibm_kyiv** (127 qubits, T1 ~150 μs, T2 ~100 μs)
- **ibm_sherbrooke** (127 qubits, T1 ~180 μs, T2 ~120 μs)
- **ibm_brisbane** (127 qubits, high-fidelity 2-qubit gates)

**Access Level**:
- **Option A**: IBM Quantum Premium ($$$, immediate access)
- **Option B**: Academic collaboration (MIT, Yale, IBM Research)
- **Option C**: IBM Quantum Network (via university partnership)

**Qubit Pair Selection**:
- High connectivity (direct 2-qubit gate)
- T1 > 100 μs (minimum for 20-point measurement)
- T2 > 50 μs (minimum for coherence measurement)
- Low crosstalk (< 1% gate error on neighboring qubits)

---

### 3.2 IonQ Access (Validation)

**Preferred Systems**:
- **IonQ Aria** (25 qubits, T1 ~1 sec, T2 ~1 sec, #AQ 23)
- **IonQ Forte** (32 qubits, improved fidelity)

**Access**: AWS Braket, Azure Quantum, or direct IonQ collaboration

**Why Trapped Ions**:
- Very long coherence times (T1, T2 ~ seconds)
- Different gate set (Mølmer-Sørensen vs IBM's echoed cross-resonance)
- Different noise sources (motional heating vs flux noise)

---

### 3.3 Timeline

**Week 1-2: Platform Access + Calibration**
- Secure IBM Quantum access (Premium or collaboration)
- Identify optimal qubit pair (T1, T2, gate fidelity)
- Calibrate Bell state preparation (fidelity > 0.95)
- Test T1/T2 measurement sequences

**Week 3-4: Baseline Measurement (Point 1)**
- Execute 8,000-shot measurement on IBM Quantum
- Analyze T1, T2 for |Φ+⟩ and |Ψ+⟩
- Calculate ΔT2/T1 ± σ
- Apply decision tree

**Week 5-6: Validation + Null Test (Points 2-3)**
- If Point 1 successful: Replicate on IonQ (Point 2)
- Execute null test with product states (Point 3)
- Cross-platform analysis

**Week 7-8: Analysis + Reporting**
- Error analysis and uncertainty quantification
- Compare to LRT prediction (ΔT2/T1 = 0.19 ± 0.05)
- Prepare results for publication/preprint

**Total Duration**: 1-2 months (depending on platform access speed)

---

## 4. Success Criteria

### 4.1 Pilot Test Success (GO to Full Study)

**Conditions**:
1. ΔT2/T1 > 0.15 on IBM Quantum (Point 1) ✅
2. ΔT2/T1 > 0.15 on IonQ (Point 2) ✅
3. ΔT2/T1 ≈ 0.00 for product states (Point 3) ✅
4. Statistical significance: |ΔT2/T1| / σ_ΔT2/T1 > 3 (>3σ detection) ✅

**Next Steps**:
- Full study: 100+ circuit variations (θ-dependence, different Bell states)
- Preprint submission (arXiv)
- Peer-reviewed publication (PRL, PRX Quantum, Nature Physics)

---

### 4.2 Partial Success (Revise Model)

**Conditions**:
- 0.05 < ΔT2/T1 < 0.15 (weak signal)

**Interpretation**:
- T1 asymmetry assumption may be incorrect (15% → 0-5%)
- Revisit Fisher information calculation
- Check for unmodeled platform-specific effects

**Next Steps**:
- Detailed T1 asymmetry measurement (separate experiment)
- Refine LRT prediction model
- Re-run pilot test with updated parameters

---

### 4.3 Null Result (Path 2 Falsified)

**Conditions**:
- ΔT2/T1 < 0.05 (no signal, <25% of prediction)

**Interpretation**:
- LRT Bell state asymmetry prediction is incorrect
- Fisher information coupling mechanism does not apply
- OR systematic error in prediction derivation

**Next Steps**:
- Document null result (valuable for LRT development)
- Pivot to Path 1 (AC Stark θ) or Path 3 (Ramsey θ)
- Investigate theoretical assumptions (Fisher info, η coupling)

---

## 5. Risk Mitigation

### 5.1 Platform Access Delays

**Risk**: IBM Quantum Premium too expensive, collaboration takes months

**Mitigation**:
- **Option A**: Apply for IBM Quantum Researchers program (free access for academics)
- **Option B**: Partner with university with existing IBM Quantum Network access
- **Option C**: Start with IBM Quantum Open Plan (limited but free) for initial calibration

---

### 5.2 Low Signal-to-Noise Ratio

**Risk**: ΔT2/T1 signal buried in measurement noise

**Mitigation**:
- Increase shot count (200 → 500 shots per point if needed)
- Use dynamical decoupling to extend T2 (improves SNR)
- Select highest-coherence qubit pairs (T1 > 150 μs)
- Apply Bayesian inference for tighter uncertainty bounds

---

### 5.3 Systematic Errors

**Risk**: Platform-specific effects mimic LRT signal

**Mitigation**:
- **Point 3** (null test with product states) explicitly checks this
- Cross-platform validation (IonQ) rules out IBM-specific artifacts
- Randomize qubit pair selection (measure on 3+ pairs, average results)
- Blind analysis (don't look at ΔT2/T1 until all systematics checked)

---

## 6. Collaboration Outreach Strategy

### 6.1 Target Groups

**IBM Quantum Research**:
- **Contact**: Dr. Jay Gambetta (VP, IBM Quantum), Dr. Antonio Córcoles (experimental lead)
- **Pitch**: "Novel test of quantum measurement theory using Bell state decoherence asymmetry"
- **Value Prop**: Publishable result (PRL-quality), uses existing IBM hardware, 1-2 month timeline

**Academic Collaborations**:
- **MIT**: Prof. Isaac Chuang, Prof. William Oliver (superconducting qubits)
- **Yale**: Prof. Robert Schoelkopf (circuit QED)
- **UC Berkeley**: Prof. Irfan Siddiqi (quantum error correction)
- **Pitch**: "First experimental test of LRT prediction, high SNR (12σ), fast timeline"

**IonQ**:
- **Contact**: Dr. Chris Monroe (Chief Scientist), Dr. Jungsang Kim (CTO)
- **Pitch**: "Cross-platform validation experiment, complements IBM superconducting qubit results"

---

### 6.2 Pitch Materials

**Required**:
1. ✅ **Path 2 notebook** (bell_asymmetry_first_principles.ipynb) - demonstrates prediction
2. ✅ **This protocol** (PATH_2_PILOT_TEST_PROTOCOL.md) - shows experimental feasibility
3. **1-page summary** (non-technical overview for PIs)
4. **2-page technical summary** (detailed for experimentalists)
5. **Collaboration timeline** (Gantt chart showing 8-week plan)
6. **Resource ask** (qubit hours, platform access level)

**Status**:
- Items 1-2: ✅ COMPLETE (Session 12.0)
- Items 3-6: Pending (Task 3.5 - Collaboration pitch materials, Week 4)

---

## 7. Next Steps (Post-Protocol)

### 7.1 Immediate (Week 1)

- [ ] Finalize this protocol (peer review with AI/collaborators)
- [ ] Create 1-page summary for experimentalist outreach
- [ ] Identify 3-5 target collaborators (IBM, MIT, Yale, IonQ)
- [ ] Draft email template for cold outreach

### 7.2 Short-Term (Week 2-4)

- [ ] Send outreach emails to target groups
- [ ] Follow up on responses
- [ ] Schedule Zoom calls with interested parties
- [ ] Refine protocol based on experimentalist feedback

### 7.3 Medium-Term (Month 2-3)

- [ ] Secure platform access (IBM Quantum Premium or collaboration)
- [ ] Execute pilot test (Points 1-3)
- [ ] Analyze results and apply decision tree
- [ ] Prepare preprint (if successful)

---

## 8. Appendix: Technical Details

### 8.1 Qubit Pair Selection Criteria

**Connectivity**:
- Direct coupling (avoid SWAP gates that add decoherence)
- Preferably edge qubits (lower crosstalk from neighbors)

**Coherence Times** (minimum):
- T1 > 100 μs (for 20-point measurement with max delay ~200 μs)
- T2 > 50 μs (for coherence measurement)
- T2/T1 > 0.4 (avoid pure dephasing regime)

**Gate Fidelity**:
- Single-qubit gate error < 0.1% (X, H, Z gates)
- Two-qubit gate error < 1% (CNOT or CZ)
- Readout fidelity > 95% (for both qubits)

**Example Qubits** (IBM Quantum systems):
- ibm_kyiv: Qubits (0, 1), (5, 6), (10, 11) - check current calibration
- ibm_sherbrooke: Qubits (15, 16), (30, 31) - high T1/T2 regions

---

### 8.2 Circuit Depth Budget

**Bell State Preparation**:
- H gate: 1 layer
- CNOT gate: 1 layer
- (Optional) X gate for |Ψ+⟩: 1 layer
- **Total**: 2-3 layers

**T1 Measurement**:
- Delay: variable (0-200 μs)
- Z-basis measurement: 1 layer
- **Total**: 3-4 layers

**T2 Measurement**:
- Delay: variable (0-100 μs)
- Coherence revival: 1-2 layers (platform-dependent)
- X-basis measurement: 1 layer
- **Total**: 4-6 layers

**Circuit Depth**: 4-6 layers (shallow enough for current NISQ devices)

---

### 8.3 Data Analysis Pipeline

**Software**:
- Python 3.10+ (data processing)
- Qiskit 1.0+ (circuit construction, IBM Quantum interface)
- QuTiP 5.0+ (theoretical predictions, cross-validation)
- NumPy, SciPy (fitting, error propagation)
- Matplotlib (visualization)

**Analysis Steps**:
1. Raw counts → Probability distributions
2. Exponential fits (T1, T2 extraction)
3. Error propagation (bootstrap + analytical)
4. ΔT2/T1 calculation with uncertainties
5. Statistical significance test (t-test, Bayesian)
6. Comparison to LRT prediction (ΔT2/T1 = 0.19 ± 0.05)

**Validation**:
- Cross-check with bell_asymmetry_analysis.py (from Sprint 16 Plan)
- Compare to QuTiP simulation results (from notebook)
- Blind analysis protocol (don't peek at ΔT2/T1 until systematics cleared)

---

## 9. Document History

**Version 1.0** (Nov 5, 2025):
- Initial draft created (Task 3.1, Session 12.0)
- 3-point measurement design
- Decision tree protocol
- Resource requirements (IBM Quantum, IonQ)
- 8-week timeline
- Collaboration outreach strategy

**Status**: DRAFT - pending peer review and experimentalist feedback

---

**Contact**: James D. Longmire (jdlongmire@example.com)
**GitHub**: logic-realism-theory/theory/predictions/Path_2_Bell_State_Asymmetry/
**License**: MIT
