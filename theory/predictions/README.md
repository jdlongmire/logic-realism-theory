# LRT Experimental Predictions

This folder contains all work related to testing LRT's falsifiable predictions.

**Last Updated**: 2025-11-05
**Current Focus**: Pivot to Bell Ceiling prediction (cleaner falsifiability)

---

## Folder Organization (Updated 2025-11-05)

### Active Prediction Paths

**Bell_Ceiling/** - **PRIMARY FOCUS** (NEW)
- **Prediction**: CHSH ≤ 2.790 (below Tsirelson bound 2.828)
- **Status**: α derivation needed (in progress)
- **Advantage**: Violates QM's fundamental bound (clean falsifiability)
- **See**: `Bell_Ceiling/README.md`

**T2-T1/** - **SECONDARY** (needs correction)
- **Prediction**: T2/T1 ≈ 0.81
- **Status**: Baseline error identified, correction in progress
- **Issue**: Falls within QM's allowed range (0 < T2/T1 ≤ 2)
- **See**: `T2-T1/README.md` and `T2-T1/LESSONS_LEARNED_T2_T1_PREDICTION.md`

---

## Path 3: T1 vs T2 Comparison (Moved to T2-T1/)

**Status**: Simulation-validated, **baseline correction needed** (2025-11-05)

**Core Documents** (now in `T2-T1/`):
- **[`T2-T1/T1_vs_T2_Protocol.md`](T2-T1/T1_vs_T2_Protocol.md)** - Complete experimental protocol (v1.2)
- **[`T2-T1/T1_vs_T2_Error_Budget.md`](T2-T1/T1_vs_T2_Error_Budget.md)** - Comprehensive error analysis
- **[`T2-T1/LESSONS_LEARNED_T2_T1_PREDICTION.md`](T2-T1/LESSONS_LEARNED_T2_T1_PREDICTION.md)** - **Error analysis** (2025-11-05)
- **[`Quantitative_Predictions_Derivation.md`](Quantitative_Predictions_Derivation.md)** - First-principles derivation (needs correction)

**QuTiP Validation**:
- **[`../../notebooks/Path3_T1_vs_T2_QuTiP_Validation.ipynb`](../../notebooks/Path3_T1_vs_T2_QuTiP_Validation.ipynb)** - Simulation validation

**Implementation Scripts**:
- **[`../../scripts/path3_t1_vs_t2/`](../../scripts/path3_t1_vs_t2/)** - Circuit generation scripts

**Key Hypothesis** ⚠️ **CORRECTION NEEDED**:
- **LRT**: T2/T1 ≈ 0.81 (from η ≈ 0.23)
- **QM** (CORRECTED 2025-11-05): T2/T1 = 2.0 (clean limit), range 0-2 (with noise)
- **Previous claim** (INCORRECT): "QM predicts T2/T1 ≈ 1.0"
- **Issue**: LRT's 0.81 is **within** QM's allowed range (not outside it)
- **See**: `T2-T1/LESSONS_LEARNED_T2_T1_PREDICTION.md` for complete analysis

**Quantitative Predictions** (from first principles):
- T2/T1 ≈ 0.8 (best estimate, 20% effect)
- T2/T1 ≈ 0.9 (conservative, 10% effect)
- T2/T1 ≈ 0.7 (lower bound, 30% effect)

**Validation Results** (Session 3.6):
- Error budget: ±2.8% on T2/T1 ratio
- Signal-to-noise: 3.6-10.7σ (highly significant)
- Statistical power: >95% with 40,000 shots per point
- QuTiP simulation: LRT effect detectable at >4σ significance

**Multi-LLM Review** (Session 3.6):
- Team scores: Grok 0.805, Gemini 0.62, ChatGPT 0.595 (avg: 0.673)
- Decision: NO-GO (below 0.70 threshold) but very close
- Critical gaps identified and addressed:
  - ✅ Error budget created
  - ✅ QuTiP simulation completed
  - ✅ Statistical power justified
  - ✅ Quantitative predictions emphasized
- **Next**: Re-submit for review with expected quality >0.75

**Resource Requirements**:
- 450 hours total quantum time (3 backends, including T2_echo)
- 40,000 shots per point (justified by power analysis)
- Enhanced IBM Quantum access recommended

### Path 5: Hamiltonian Frequency Shift (Planned)

**Status**: Protocol drafted, awaiting Path 3 completion

**Core Documents**:
- **[`Hamiltonian_Frequency_Shift_Protocol.md`](Hamiltonian_Frequency_Shift_Protocol.md)** - Frequency shift test protocol (v1.1)

**Key Hypothesis**:
- **LRT**: ω(|+⟩) ≠ ω(|0⟩) with δω/ω ≈ 10⁻⁴ - 10⁻³
- **QM**: ω(|+⟩) = ω(|0⟩) (no state-dependent frequency)

**Temperature-Dependence Signature**:
- **LRT**: δω ∝ T (linear scaling)
- **AC Stark**: δω independent of T
- **Distinguishing Test**: Temperature sweep (10-100 mK)

---

## Master Planning Documents

- **[`Prediction_Paths_Master.md`](Prediction_Paths_Master.md)** - Overview of all 8 prediction paths
- **[`Quantitative_Predictions_Derivation.md`](Quantitative_Predictions_Derivation.md)** - First-principles derivations

---

## Historical Test Designs (Learning Archive)

### Logical State-Dependent Error Test (Superseded by Path 3)

- **[`Logical_State_Dependent_Error_Test_Design.md`](Logical_State_Dependent_Error_Test_Design.md)** - Initial design (Phase 3 complete)
- **Status**: Superseded by Path 3 (T1 vs T2) protocol
- **Lessons**: VIF diagnostics essential, avoid A/B circuit comparison

### No Actualized Contradictions Test (Abandoned)

- **[`No_Actualized_Contradictions_Test_Design.md`](No_Actualized_Contradictions_Test_Design.md)** - Design iteration 1 (abandoned)
- **[`Contradiction_Test_Consultation_Analysis.md`](Contradiction_Test_Consultation_Analysis.md)** - Consultation results
- **Fatal Flaw**: Doesn't differentiate LRT from QM
- **Lesson**: Avoid A/B circuit comparisons (multicollinearity)

### Section 4 QEC Entropy-Error Test (Deferred)

- **[`Section_4_Revisions_Session_2.5.md`](Section_4_Revisions_Session_2.5.md)** - QEC analysis
- **Result**: Fundamental challenges identified, 2-5 year timeline
- **Status**: Deferred to future funded work

---

## Key Lessons Learned

1. **Avoid A/B Circuit Comparison**: Causes multicollinearity (VIF = ∞)
2. **Use Residual Analysis**: Compare measurement vs QM baseline prediction
3. **Design-First Methodology**: Validate with multi-LLM before coding
4. **VIF Diagnostics Mandatory**: Confirm VIF = 1.0 in protocol design
5. **Quantitative Predictions Essential**: Derive from first principles, not assumptions
6. **Error Budget Critical**: Must quantify all error sources before execution
7. **Simulation De-Risks**: QuTiP validation catches design flaws before expensive hardware runs

---

## Development Timeline

- **Session 2.4-2.5**: Initial contradiction test designs (abandoned after multi-LLM review)
- **Session 3.1-3.4**: Path 3 protocol development and multi-LLM review
- **Session 3.5**: Quantitative predictions derived from first principles
- **Session 3.6**: QuTiP validation + error budget created, all gaps addressed

---

## Related Documentation

- **Foundational Theory**: [`../Logic-realism-theory-foundational.md`](../Logic-realism-theory-foundational.md)
- **Session History**: [`../../Session_Log/`](../../Session_Log/)
  - [Session 3.6](../../Session_Log/Session_3.6.md) - Multi-LLM review + gap remediation
- **QuTiP Validation**: [`../../notebooks/Path3_T1_vs_T2_QuTiP_Validation.ipynb`](../../notebooks/Path3_T1_vs_T2_QuTiP_Validation.ipynb)
- **Implementation**: [`../../scripts/path3_t1_vs_t2/`](../../scripts/path3_t1_vs_t2/)
- **Multi-LLM Review**: [`../../multi_LLM/consultation/path3_t1_vs_t2_review_20251027.txt`](../../multi_LLM/consultation/path3_t1_vs_t2_review_20251027.txt)

---

## Next Steps

**Immediate** (Session 3.7):
1. Update Path 3 protocol to v1.3 (reference new validation documents)
2. Re-submit to multi-LLM team (expected quality >0.75)
3. Mark protocol as validated if team approves

**Future**:
4. Implement Path 5 (frequency shift) using same rigorous methodology
5. Consider additional paths once Path 3 is validated/executed

---

**Last Updated**: 2025-10-27 (Session 3.6)
**Primary Focus**: Path 3 T1 vs T2 protocol
**Status**: Simulation-validated, ready for team re-review
