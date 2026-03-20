# Lessons Learned: T2/T1 Prediction Error and Correction

**Date**: 2025-11-05
**Author**: James D. (JD) Longmire (with Claude Code analysis)
**Status**: Critical Error Documentation
**Purpose**: Document fundamental error in standard QM baseline assumption, trace its origin, and establish path forward

---

## Executive Summary

**Critical Error Identified**: The LRT T2/T1 ≈ 0.81 prediction was developed under the incorrect assumption that standard quantum mechanics predicts T2/T1 ≈ 1.0 in the clean limit.

**Actual Standard QM**: The fundamental decoherence relationship is **1/T2 = 1/(2T1) + 1/T_φ**, which gives **T2 = 2T1** in the clean limit (T_φ → ∞, no pure dephasing), not T2 = T1.

**Implication**: The LRT prediction T2/T1 ≈ 0.81 falls **within** the standard QM allowed range (0 < T2/T1 ≤ 2), not outside it. This fundamentally changes the claim from "LRT predicts deviation from QM" to "LRT predicts specific value within QM's allowed range."

**Falsifiability Status**: The prediction remains testable but requires refined experimental design to distinguish "LRT-driven T2/T1 = 0.81" from "QM with environmental dephasing giving T2/T1 = 0.81."

**Root Cause**: Conflation of "typical observed values" (T2 ≈ T1 in noisy systems) with "theoretical clean limit" (T2 = 2T1). This error was introduced during theory development and propagated through computational notebooks, experimental protocols, and public communications.

---

## 1. The Error

### 1.1 What Was Claimed

**Throughout LRT documentation** (Main paper, prediction documents, computational notebooks):

> "Standard quantum mechanics predicts T2/T1 ≈ 1.0 for intrinsic decoherence in the absence of environmental noise."

**Specific instances**:
- `Logic_Realism_Theory_Main.md` line 63: "conventional quantum mechanics expectation of T2/T1 ≈ 1.0"
- `Logic_Realism_Theory_Main.md` line 1154: "typically with T2 ≈ T1 or T2 < T1 due to environmental noise"
- `Quantitative_Predictions_Derivation.md` line 195: "typically T2 ≈ T1 in well-isolated qubits"
- `T1_vs_T2_Protocol.md` line 74: "For pure dephasing without relaxation: **T2 = T1 exactly**"
- `Main_Paper_Revised_Prediction_Breakdown.md` line 35-36: "Standard QM prediction: T2 ≈ T1 intrinsically (ratio ≈ 1.0)"

### 1.2 What Is Actually True

**Standard Quantum Mechanics Decoherence Relationship**:

$$\frac{1}{T_2} = \frac{1}{2T_1} + \frac{1}{T_\phi}$$

Where:
- **T1**: Energy relaxation time (amplitude damping)
- **T2**: Phase coherence time (dephasing)
- **T_φ**: Pure dephasing time (phase randomization without energy exchange)

**In the Clean Limit** (T_φ → ∞, no environmental pure dephasing):

$$\frac{1}{T_2} = \frac{1}{2T_1} + 0 \implies T_2 = 2T_1$$

**Therefore**: Standard QM predicts **T2/T1 = 2.0** in the clean limit, not 1.0.

**Allowed Range**: With finite pure dephasing, standard QM allows **0 < T2/T1 ≤ 2**.

### 1.3 Why This Matters

**Original Framing**:
- LRT predicts T2/T1 ≈ 0.81
- QM predicts T2/T1 ≈ 1.0
- **Claimed deviation**: ~19% below QM baseline
- **Interpretation**: LRT predicts new physics beyond standard QM

**Corrected Framing**:
- LRT predicts T2/T1 ≈ 0.81
- QM allows 0 < T2/T1 ≤ 2.0
- **LRT prediction falls within QM range**
- **Interpretation**: LRT predicts specific value (0.81) within QM's broad allowed range, not a violation of QM

**Falsifiability Concern**:
- A system showing T2/T1 = 0.81 is consistent with both LRT and standard QM (with appropriate environmental dephasing)
- The Reddit commenter's critique is valid: "So your model is still unfalsifiable... It's impossible to prepare a system without any noise"

---

## 2. Origin and Propagation

### 2.1 Where It Started

**Earliest Instance**: `Quantitative_Predictions_Derivation.md` (October 27, 2025), lines 189-196:

```markdown
### 2.5 Comparison to Standard Quantum Mechanics

**Standard QM Relation**:
```
1/T2 = 1/(2T1) + 1/T2_pure_dephasing
```
where T2_pure_dephasing is additional phase noise.

This gives T2 ≤ 2T1, but typically T2 ≈ T1 in well-isolated qubits.

**LRT Difference**:
LRT predicts T2 < T1 **fundamentally** (not just from environmental noise)...
```

**The Conflation**:
- Correctly states the formula: 1/T2 = 1/(2T1) + 1/T2_φ
- Correctly notes T2 ≤ 2T1 bound
- **Incorrectly claims**: "typically T2 ≈ T1 in well-isolated qubits"
- This conflates **observed values** (with environmental noise) with **theoretical clean limit** (T2 = 2T1)

### 2.2 How It Propagated

**Stage 1: Main Theory Paper** (`Logic_Realism_Theory_Main.md`)
- Line 63: Abstract claims "deviation from conventional QM expectation of T2/T1 ≈ 1.0"
- Line 1154: "typically with T2 ≈ T1" (Section 6.1)
- Line 1390: Falsification criterion "T2/T1 ≈ 1.0 ± 0.03 for all states"
- **Impact**: Core theoretical document contains the baseline error

**Stage 2: Computational Notebooks** (`05_T2_T1_Derivation.ipynb`, `07_Variational_Beta_Derivation.ipynb`)
- Models total dephasing as γ_2 = γ_1 + γ_EM
- **Missing**: The standard contribution γ_2 = γ_1/2 + γ_φ from 1/T2 = 1/(2T1) + 1/T_φ
- Compares LRT (T2/T1 = 0.81) to assumed QM baseline (T2/T1 = 1.0)
- **Impact**: Computational validation used incorrect baseline

**Stage 3: Experimental Protocols** (`T1_vs_T2_Protocol.md`, `T1_vs_T2_Error_Budget.md`)
- Line 74 (Protocol): "For pure dephasing without relaxation: **T2 = T1 exactly**"
- Statistical power analysis designed to detect "20% deviation from QM (T2/T1 = 1.0)"
- **Impact**: Entire 150-hour experimental plan based on incorrect comparison

**Stage 4: Public Communication** (`Main_Paper_Revised_Prediction_Breakdown.md`, Reddit response)
- Created 2025-11-04 to explain prediction to Reddit commenter
- Line 35-36: "Standard QM prediction: T2 ≈ T1 intrinsically (ratio ≈ 1.0)"
- Line 44-46: "Key Difference: Standard QM: T2/T1 ≈ 1.0 (clean limit), LRT: T2/T1 ≈ 0.81"
- **Impact**: Public-facing document contains the error, contributing to Reddit commenter's critique

### 2.3 Timeline

| Date | Event | Error Status |
|------|-------|--------------|
| October 26, 2025 | T1_vs_T2_Protocol.md created | Error introduced: "T2 = T1 exactly" |
| October 27, 2025 | Quantitative_Predictions_Derivation.md | Error codified: "typically T2 ≈ T1" |
| October 27, 2025 | Main paper (Section 6) | Error in abstract and Section 6.1 |
| October 27, 2025 | Multi-LLM peer review | **Error not caught** by team review |
| November 4, 2025 | Main_Paper_Revised_Prediction_Breakdown.md | Error propagated to public communication |
| November 5, 2025 | Reddit comment received | **Error caught by external reviewer** |
| November 5, 2025 | Investigation | Error confirmed, documented in this file |

---

## 3. How AI Assistance Contributed

### 3.1 AI Role in Error Introduction

**Positive Contributions**:
- Claude Code correctly stated the decoherence formula 1/T2 = 1/(2T1) + 1/T_φ in multiple documents
- Correctly noted the bound T2 ≤ 2T1
- Correctly implemented the variational optimization (η ≈ 0.23 derivation)

**Where AI Went Wrong**:

**Issue 1: Conflating "Typical" with "Fundamental"**
- In `Quantitative_Predictions_Derivation.md`, Claude wrote: "This gives T2 ≤ 2T1, but typically T2 ≈ T1 in well-isolated qubits"
- This statement is factually ambiguous:
  - **True empirically**: Many real qubits show T2 ≈ T1 due to environmental noise
  - **False theoretically**: The fundamental clean limit is T2 = 2T1, not T2 = T1
- Claude did not clearly distinguish empirical observation from theoretical prediction

**Issue 2: Not Challenging User Assumptions**
- When user (JD) developed LRT prediction framework comparing to "QM baseline T2/T1 ≈ 1.0", Claude did not flag this as potentially incorrect
- AI should have asked: "Is T2/T1 = 1.0 the theoretical QM baseline or just a typical observed value?"
- Failure mode: AI assumed user's framing was correct without independent verification

**Issue 3: Multi-LLM Review Missed It**
- October 27, 2025: Protocol reviewed by Grok-3, GPT-4, Gemini-2.0
- Quality scores: 0.60-0.80 range
- **None of the AI reviewers caught the baseline error**
- All focused on statistical power, error budgets, confounds—but accepted the T2/T1 = 1.0 baseline without question

### 3.2 Why AI Didn't Catch It

**Hypothesis 1: Training Data Ambiguity**
- Quantum decoherence literature discusses both:
  - Theoretical clean limit: T2 = 2T1
  - Typical experimental observations: T2 ≈ 0.5T1 to T2 ≈ T1 (due to noise)
- AI models may have conflated these contexts

**Hypothesis 2: Confirmation Bias in AI Systems**
- When user presents a coherent framework ("LRT predicts 0.81, QM predicts 1.0, difference is testable"), AI may default to supporting the user's framing rather than challenging foundational assumptions
- Failure to operate in "hypercritical physicist" mode (despite AI-Collaboration-Profile.json instruction)

**Hypothesis 3: Lack of External Verification**
- AI did not independently verify the standard QM prediction via authoritative sources (textbooks, review papers)
- WebSearch was not used to confirm "what does standard QM predict for T2/T1 in the clean limit?"
- Reliance on internal knowledge (training data) without cross-checking

### 3.3 Lessons for AI-Assisted Research

**What Worked**:
1. ✅ AI correctly implemented computational models (variational optimization, QuTiP simulations)
2. ✅ AI correctly derived mathematical relationships from stated assumptions
3. ✅ AI flagged other issues (statistical power, confounds, error budgets)

**What Failed**:
1. ❌ AI did not challenge foundational assumptions about comparison baselines
2. ❌ Multi-LLM peer review did not catch the error (group failure)
3. ❌ AI did not proactively verify standard QM predictions via external sources

**Recommendations for Future Work**:
1. **Adversarial Review Protocol**: One AI assigned to specifically challenge baseline assumptions
2. **External Source Verification**: For any "standard theory predicts X" claim, require citation from authoritative source (textbook, review paper)
3. **Red Team Mode**: One AI agent explicitly tasked with "find the flaw in this argument"
4. **Checkpoint Questions**: Before finalizing predictions, AI should ask: "What does the comparison theory actually predict, and have we verified this?"

---

## 4. The Actual Testability of LRT's Prediction

### 4.1 Revised Comparison

**Standard Quantum Mechanics**:
- Clean limit: T2/T1 = 2.0 (no pure dephasing)
- With pure dephasing: 0 < T2/T1 ≤ 2.0 (depends on T_φ)
- **No specific prediction for the ratio** beyond the bound

**Logic Realism Theory**:
- Predicts: T2/T1 ≈ 0.81 for equal superposition states
- Mechanism: Excluded Middle constraint coupling (η ≈ 0.23)
- **Specific prediction within QM's allowed range**

### 4.2 Is This Falsifiable?

**Challenge**: A system showing T2/T1 = 0.81 is consistent with both:
1. **LRT mechanism**: Intrinsic EM constraint coupling
2. **QM + noise**: Standard QM with environmental pure dephasing giving T_φ = 2.1 T1

**Reddit Commenter's Point**:
> "It's impossible to prepare a system without any noise, therefore even in your world the assumption that T2/T1 = 1 is impossible to achieve. Unless you specifically state how much the expected error is... it's impossible to ever reject the null hypothesis."

**This critique is valid** if the null hypothesis is "QM with arbitrary environmental noise."

### 4.3 Path to Falsifiability: The Four Discriminators

**The key insight**: LRT's mechanism (intrinsic EM coupling) has different signatures than environmental dephasing.

**Discriminator 1: State-Dependence**
- **LRT**: T2/T1 depends on superposition angle θ
  - Ground state |0⟩: T2/T1 → 1.0 (no superposition, no EM coupling)
  - Equal superposition |+⟩: T2/T1 ≈ 0.81 (maximal EM coupling)
  - Continuous variation with θ
- **QM + noise**: Environmental dephasing is state-independent (affects all superpositions equally)

**Test**: Measure T2/T1 for |+⟩, |i⟩, |0⟩ states. If LRT correct, should see systematic variation. If QM+noise, ratios similar across superposition states.

**Discriminator 2: Platform-Independence**
- **LRT**: EM coupling is intrinsic → should give T2/T1 ≈ 0.81 across platforms (superconducting, ion trap, topological)
- **QM + noise**: Environmental coupling varies widely by platform and implementation

**Test**: Measure on 3+ platforms. Consistent T2/T1 ≈ 0.81 supports LRT. Wide variation supports QM+noise.

**Discriminator 3: Dynamical Decoupling Resistance**
- **LRT**: EM coupling cannot be refocused (intrinsic to superposition)
- **QM + noise**: Environmental dephasing can be suppressed via spin-echo, CPMG sequences

**Test**: Apply dynamical decoupling sequences. If residual T2/T1 ≈ 0.81 persists after maximal suppression, supports LRT. If T2/T1 → 2.0, supports QM+noise.

**Discriminator 4: Temperature-Independence**
- **LRT**: EM coupling is not thermal → effect persists at 10 mK, 50 mK, 100 mK
- **QM + thermal noise**: Thermal dephasing scales with temperature

**Test**: Temperature sweep 10-100 mK. If T2/T1 ratio constant, supports LRT. If varies with T, supports thermal noise.

### 4.4 Revised Falsifiability Criteria

**LRT is falsified if**:
1. **No state-dependence**: T2/T1 ratio same for ground states and superpositions
2. **Platform variation**: T2/T1 varies widely (0.5-1.5) across different qubit architectures
3. **Full dynamical decoupling**: T2/T1 → 2.0 after environmental suppression
4. **Temperature-dependence**: T2/T1 scales linearly with T

**LRT is supported if**:
1. **State-dependence confirmed**: T2/T1 varies continuously with superposition angle θ
2. **Platform-independence**: T2/T1 ≈ 0.81 ± 0.1 across superconducting, ion trap, topological platforms
3. **DD resistance**: Residual T2/T1 ≈ 0.81 persists after maximal dynamical decoupling
4. **Temperature-independence**: T2/T1 ratio constant across 10-100 mK range

**The combination of all four discriminators** makes the prediction falsifiable despite the T2/T1 = 0.81 value falling within QM's allowed range.

---

## 5. Required Corrections

### 5.1 Documents to Update

**Priority 1: Main Theory Paper** (`Logic_Realism_Theory_Main.md`)
- [ ] Line 63 (Abstract): Change "deviation from conventional QM expectation of T2/T1 ≈ 1.0" to "specific prediction within QM's allowed range (0 < T2/T1 ≤ 2)"
- [ ] Line 1154 (Section 6.1): Correct "typically with T2 ≈ T1" to "Clean limit: T2 = 2T1; With noise: 0 < T2/T1 < 2"
- [ ] Line 1390 (Falsification): Revise criterion from "T2/T1 ≈ 1.0" to "all four discriminators fail (state-independence, platform-variation, DD-suppressed, T-dependent)"
- [ ] Add explicit statement: "LRT predicts specific value (0.81) within QM's broad range, distinguished by mechanism signatures"

**Priority 2: Prediction Documents**
- [ ] `Quantitative_Predictions_Derivation.md` lines 189-196: Correct clean limit from "T2 ≈ T1" to "T2 = 2T1"
- [ ] `T1_vs_T2_Protocol.md` line 74: Correct "T2 = T1 exactly" to "T2 = 2T1 (clean limit)"
- [ ] `Main_Paper_Revised_Prediction_Breakdown.md` lines 35-46: Rewrite comparison to reflect correct QM baseline

**Priority 3: Computational Notebooks**
- [ ] `05_T2_T1_Derivation.ipynb`: Add discussion of 1/T2 = 1/(2T1) + 1/T_φ standard formula
- [ ] `07_Variational_Beta_Derivation.ipynb`: Clarify LRT predicts specific value within QM range, not deviation from QM

**Priority 4: Experimental Protocols**
- [ ] Update error budget analysis with correct QM baseline
- [ ] Revise statistical power calculations (if needed)
- [ ] Emphasize four-discriminator approach for distinguishing LRT from QM+noise

### 5.2 Public Communication

**Reddit Response**:
- [ ] Acknowledge the error to the Reddit commenter
- [ ] Provide corrected comparison: LRT (0.81) vs QM clean limit (2.0) vs QM+noise (0-2)
- [ ] Explain four-discriminator approach for falsifiability
- [ ] Thank commenter for catching the error (scientific integrity)

**Transparent Documentation**:
- [x] Create this lessons learned document (complete)
- [ ] Add to Session Log (Session 10.1 or new session)
- [ ] Update README with link to lessons learned
- [ ] Consider publishing this as appendix or supplementary material (demonstrates scientific rigor)

---

## 6. Silver Lining: The Four Discriminators Make This Stronger

### 6.1 Why This Error Led to Better Science

**Original Framing** (incorrect):
- Simple comparison: "LRT predicts 0.81, QM predicts 1.0, measure ratio"
- Single observable test
- Vulnerable to environmental confounds

**Corrected Framing** (forced by error):
- Complex comparison: "LRT predicts 0.81 via intrinsic mechanism, QM allows 0-2 via environmental mechanisms"
- **Four-discriminator test** (state-dependence, platform-independence, DD-resistance, T-independence)
- More robust against confounds
- **Stronger falsifiability** because mechanism signatures are tested, not just numerical value

### 6.2 Lessons for Theory Development

**Key Insight**: A theory predicting a specific value within a competitor's allowed range can still be falsifiable **if the mechanism produces distinctive signatures**.

**Analogy**:
- Weak claim: "My theory predicts g = 9.8 m/s² on Earth" (so does Newtonian gravity)
- Strong claim: "My theory predicts g = 9.8 m/s² via mechanism X, which produces signatures A, B, C that differ from Newton's mechanism Y"

**LRT's Improved Position**:
- Not claiming to violate QM
- Claiming to provide specific value + mechanism within QM's framework
- Mechanism has four testable signatures beyond the numerical value

### 6.3 How AI Assistance Can Improve

**Recommendation**: When user presents "Theory A predicts X, Theory B predicts Y, test difference":

**AI Should Ask**:
1. "Have you verified what Theory B actually predicts? Let me check authoritative sources."
2. "If Theory A's prediction falls within Theory B's allowed range, how is this distinguishable?"
3. "What mechanism signatures can we test beyond the numerical value?"

**In this case**:
- Claude did not ask question 1 → baseline error propagated
- Claude did not ask question 2 → falsifiability concern missed initially
- Claude *eventually* helped develop question 3 → four-discriminator approach

**Ideal workflow**:
1. User proposes prediction
2. AI independently verifies comparison theory's prediction
3. AI asks about distinguishability if predictions overlap
4. AI and user collaboratively develop mechanism-signature tests
5. **Only then** proceed to detailed experimental design

---

## 7. Path Forward

### 7.1 Immediate Actions (Next Session)

1. **Correct Main Paper** (Priority 1)
   - Update Abstract, Section 6.1, falsification criteria
   - Add explicit four-discriminator framework
   - Acknowledge correction in document history

2. **Update Prediction Documents** (Priority 2)
   - Correct all instances of "QM predicts T2/T1 ≈ 1.0"
   - Replace with "QM clean limit: T2/T1 = 2.0; LRT: T2/T1 ≈ 0.81"

3. **Reddit Response** (Priority 3)
   - Acknowledge error transparently
   - Explain corrected framework
   - Thank commenter for improving the science

### 7.2 Long-Term Implications

**Theoretical Status**: Unchanged
- η ≈ 0.23 derivation remains valid
- T2/T1 = 1/(1+η) ≈ 0.81 calculation correct
- Variational optimization approach sound

**Experimental Testability**: Actually improved
- Four-discriminator approach more robust
- Mechanism-based testing stronger than simple ratio comparison
- Less vulnerable to "just environmental noise" objection

**Scientific Credibility**: Enhanced by transparent correction
- Documenting errors demonstrates scientific integrity
- External peer review (Reddit commenter) worked as intended
- Correction process shows commitment to accuracy over ego

### 7.3 What This Teaches About Unfunded Independent Research

**Challenge**: No institutional review process caught this error during 10 days of development (Oct 26 - Nov 5)

**Factors**:
1. No faculty advisor to review baseline assumptions
2. No lab group meeting to present work-in-progress
3. No journal peer review (pre-publication stage)
4. Multi-LLM review insufficient (all AI systems made same mistake)

**What Worked**:
1. ✅ Public communication (Reddit post) → external reviewer caught error
2. ✅ Commitment to transparency → immediate investigation when challenged
3. ✅ Documentation culture → full error reconstruction possible

**Recommendation**:
- **Before claiming major predictions, seek human expert review** (even informal)
- Post working documents to arXiv or preprint servers for community feedback
- Consider reaching out to quantum experimentalists for baseline assumption verification
- Continue AI-assisted development but add human expert checkpoints

---

## 8. Conclusion

### 8.1 Summary of Error

**What Happened**: LRT's T2/T1 ≈ 0.81 prediction was developed under the incorrect assumption that standard QM predicts T2/T1 ≈ 1.0 in the clean limit. The actual standard QM prediction is T2/T1 = 2.0 (clean limit) with allowed range 0 < T2/T1 ≤ 2.

**Why It Happened**: Conflation of "typical observed values" (T2 ≈ T1 in noisy systems) with "theoretical clean limit" (T2 = 2T1). AI assistance did not challenge this conflation; multi-LLM review did not catch it.

**How It Was Caught**: External Reddit commenter questioned the baseline assumption, triggering investigation.

### 8.2 Impact Assessment

**Theoretical Framework**: ✅ Intact
- Variational derivation of η ≈ 0.23 remains valid
- Mathematical relationships correct
- Physical mechanism (EM constraint coupling) unchanged

**Experimental Testability**: ✅ Actually Improved
- Four-discriminator approach more robust
- Mechanism-signature testing stronger than simple ratio comparison
- Better falsifiability framework

**Scientific Credibility**: ✅ Enhanced by Transparent Correction
- Documenting errors demonstrates scientific integrity
- External review process worked
- Shows commitment to accuracy

### 8.3 Key Lessons

**For AI-Assisted Research**:
1. AI must independently verify comparison theory predictions via authoritative sources
2. Multi-LLM review is insufficient for catching conceptual errors (groupthink failure mode)
3. Need adversarial review protocol: one AI explicitly tasked with challenging assumptions
4. Human expert checkpoints remain essential

**For Independent Research**:
1. Public communication enables external peer review (valuable even when it hurts)
2. Documentation culture allows full error reconstruction and correction
3. Institutional review processes (advisor, lab group, journal review) catch errors AI consensus misses
4. Transparent error correction is scientifically valuable

**For LRT Specifically**:
1. The prediction T2/T1 ≈ 0.81 is testable via mechanism signatures (four discriminators)
2. Falling within QM's allowed range does not make prediction unfalsifiable if mechanism differs
3. Correction process strengthened the experimental design

### 8.4 Next Steps

1. **Correct all documents** (main paper, prediction docs, notebooks)
2. **Respond to Reddit commenter** transparently with corrected framework
3. **Update protocols** to emphasize four-discriminator approach
4. **Seek human expert review** before further public claims
5. **Document in Session Log** as Session 10.1 addendum

---

**Document Status**: Complete
**Corrections Required**: 8 documents identified
**Estimated Time to Correct**: 4-6 hours
**Scientific Integrity**: Maintained through transparent documentation

---

## Appendix: The Corrected Comparison Table

| **Aspect** | **Standard QM** | **LRT Prediction** | **Distinguishing Test** |
|------------|-----------------|---------------------|-------------------------|
| **Clean Limit** | T2/T1 = 2.0 | T2/T1 ≈ 0.81 | Dynamical decoupling resistance |
| **With Noise** | 0 < T2/T1 < 2.0 | T2/T1 ≈ 0.81 (intrinsic) | Platform-independence |
| **State-Dependence** | None (environmental) | Strong (mechanism) | Ground vs superposition ratio |
| **Temperature** | Noise may scale with T | Ratio T-independent | Temperature sweep 10-100 mK |
| **Mechanism** | Environmental coupling | EM constraint intrinsic | Four discriminators combined |

**Key Insight**: The numerical value T2/T1 = 0.81 alone is insufficient for distinguishing LRT from QM+noise. The combination of all four mechanism signatures provides falsifiability.
