# The Tsirelson Bound as Interface Stability Limit in Logic Realism Theory

**James D. Longmire**
ORCID: 0009-0009-1383-7698

---

## Abstract

We examine Logic Realism Theory's interpretation of the Tsirelson bound (CHSH ≤ 2√2) as a structural consequence of the Infinite Information Space (IIS)–Boolean actuality interface. LRT proposes that superquantum correlations (e.g., PR-boxes reaching the algebraic maximum of 4) would destabilize the interface by permitting surplus ontological structure forbidden by Global Parsimony. However, we emphasize that this is an *interpretive* contribution, not an independent derivation: the bound itself emerges from the complex Hilbert space structure, which LRT inherits via local tomography. Existing explanations—information causality (Pawłowski et al. 2009), conservation per NPRF, and operational reconstructions—already derive the bound without LRT's framework. All approaches make identical experimental predictions: CHSH ≤ 2√2 exactly. Current experiments (S = 2.73 ± 0.02, Weihs 1998; S = 2.38 ± 0.14, Hensen 2015) approach but never exceed the bound, consistent with all theories. We identify what LRT adds to the explanatory landscape and what distinguishing tests, if any, could separate LRT's interpretation from alternatives.

---

## 1. Introduction

### 1.1 The Tsirelson Bound

The CHSH inequality bounds classical correlations:

$$S = |E(a,b) - E(a,b') + E(a',b) + E(a',b')| \leq 2$$

Quantum mechanics violates this bound, but only up to:

$$S_{QM} \leq 2\sqrt{2} \approx 2.828$$

This is the **Tsirelson bound** (Cirel'son 1980). The no-signaling algebraic maximum is 4, achievable by hypothetical Popescu-Rohrlich (PR) boxes.

**The foundational question:** Why does nature stop at 2√2, rather than permitting stronger non-signaling correlations?

### 1.2 Existing Explanations

Several approaches derive or explain the Tsirelson bound:

| Approach | Key Principle | Status |
|----------|--------------|--------|
| **Information Causality** (Pawłowski 2009) | Bob's info access ≤ bits received | Derives bound without Hilbert space |
| **Macroscopic Locality** | Classical limit consistency | Partial derivation |
| **Conservation per NPRF** | Angular momentum conservation | Spacetime constraint |
| **Local Tomography + Continuity** | Selects complex Hilbert space | Mathematical consequence |
| **Trivial Communication Complexity** | No computational speedup | Alternative principle |

Each has been criticized: Information Causality's foundational motivation is considered insufficient; local tomography assumes compositional structure; conservation per NPRF is a physical postulate.

### 1.3 The LRT Proposal

LRT proposes that the Tsirelson bound reflects **interface stability**—the constraint that the IIS-to-Boolean actualization process remain logically consistent under composition.

**Scope of this paper:** We assess what LRT contributes to understanding the bound, identify what hard data exists, and provide an honest assessment of LRT's explanatory vs. derivational power.

---

## 2. Experimental Data

### 2.1 High-Precision Bell Tests

| Experiment | Year | S Value | Precision | Notes |
|------------|------|---------|-----------|-------|
| Aspect et al. | 1982 | 2.70 ± 0.05 | 14σ from classical | First strong violation |
| Weihs et al. | 1998 | 2.73 ± 0.02 | 30σ from classical | Best precision, locality loophole closed |
| Hensen et al. (Delft) | 2015 | 2.38 ± 0.14 | Loophole-free | First loophole-free |
| Giustina et al. (Vienna) | 2015 | ~2.4 | Loophole-free | Photonic |
| Shalm et al. (Boulder) | 2015 | ~2.4 | Loophole-free | Photonic |
| Storz et al. (ETH) | 2023 | ~2.6 | Loophole-free, SC | Superconducting qubits |

**Key observations:**
- Best precision measurement: S = 2.73 ± 0.02 (Weihs 1998)
- Loophole-free measurements: S ~ 2.38-2.6 (lower due to experimental imperfections)
- Tsirelson bound: 2√2 ≈ 2.828
- **No violation of Tsirelson bound has ever been observed**

### 2.2 Why Experiments Don't Saturate the Bound

The gap between measured S and 2√2 reflects:
- Detector inefficiencies
- Imperfect state preparation
- Decoherence and noise
- Non-ideal measurement settings

This is NOT evidence for sub-Tsirelson physics—it's experimental limitation. Quantum mechanics predicts S = 2√2 for ideal measurements on maximally entangled states.

### 2.3 Tests for Beyond-Quantum Correlations

**No experiment has found S > 2√2.** Any such finding would revolutionize physics.

**Current precision limits:** To test whether S could exceed 2√2 by amount ε requires:
- Precision δS < ε
- Currently: δS ~ 10⁻² (best case)
- Ruling out ε = 10⁻³ would require ~10⁴ high-fidelity measurements

**Status:** No experiment has been designed specifically to test whether superquantum correlations exist. All experiments assume QM as correct.

---

## 3. The LRT Interpretation

### 3.1 Interface Stability Argument

In LRT, entanglement represents global constraints in non-Boolean IIS, actualized locally into Boolean outcomes. The interface must satisfy:

1. **Local Tomography** — Global states determined uniquely from local measurements
2. **No-Signaling** — Preserves locality of actualization
3. **Global Parsimony** — No surplus ontological structure
4. **Consistency Bridging Principle** — Information preservation across category transition

### 3.2 Why Superquantum Correlations Would Be Problematic

LRT proposes that correlations exceeding 2√2 would introduce instability:

**Signaling equivalence:** PR-boxes enable communication protocols exceeding quantum limits. Under composition, this creates functional signaling that the interface cannot mediate consistently.

**Ontological surplus:** Multiple distinct global configurations yield identical local marginals. This violates Global Parsimony—surplus structure exists with no distinguishable consequences.

**Constraint overload:** Excessive correlation strength propagates constraints faster than local actualization can resolve, risking logical contradictions in the actualized (Boolean) domain.

### 3.3 The Role of Complex Hilbert Space

LRT, via local tomography, selects complex Hilbert space as the unique structure satisfying compositional constraints. The Tsirelson bound is then a mathematical consequence:

**Derivation chain:**
```
3FLL → Distinguishability → Local Tomography → Complex Hilbert Space → 2√2
```

The bound emerges from the Cauchy-Schwarz inequality on quantum observables:
$$S = \langle A_0 B_0 \rangle + \langle A_0 B_1 \rangle + \langle A_1 B_0 \rangle - \langle A_1 B_1 \rangle$$

For ±1-valued observables in Hilbert space, this is bounded by 2√2.

---

## 4. Honest Assessment: What LRT Provides

### 4.1 What LRT Derives

| Component | Status | Notes |
|-----------|--------|-------|
| Complex Hilbert space | Derived (via local tomography) | From Hardy/Masanes-Müller reconstruction |
| Tsirelson bound value | Consequence | Mathematical result of Hilbert space |
| No-signaling | Derived | From interface locality |

### 4.2 What LRT Does NOT Derive

| Component | Status | Notes |
|-----------|--------|-------|
| Independent derivation of 2√2 | **Not provided** | Bound comes from Hilbert space structure |
| Prediction different from QM | **None** | Same S ≤ 2√2 as standard QM |
| Quantitative test vs. other interpretations | **None** | All predict exactly 2√2 |

### 4.3 Comparison with Information Causality

| Aspect | LRT | Information Causality |
|--------|-----|----------------------|
| Derives bound without Hilbert space | No | **Yes** |
| Provides physical motivation | Interface stability | Information access limit |
| Applies to general theories | Via parsimony | Operational, theory-independent |
| Foundational status | Claimed fundamental | "Not sufficiently motivated" (critics) |

**Critical point:** Information Causality derives the Tsirelson bound *without* assuming Hilbert space structure. LRT's derivation chain goes through Hilbert space, making it less fundamental in this specific sense.

### 4.4 The Interpretive Contribution

LRT's contribution is primarily **interpretive**:

- **Standard QM:** The bound is 2√2 because that's what the math gives.
- **Information Causality:** The bound is 2√2 because stronger correlations allow superluminal information access under composition.
- **LRT:** The bound is 2√2 because stronger correlations would destabilize the IIS-Boolean interface, violating Global Parsimony.

All three make the same prediction. The difference is explanatory framing, not empirical content.

---

## 5. Distinguishing Predictions?

### 5.1 What All Approaches Predict

All approaches predict:
- S ≤ 2√2 exactly
- No superquantum correlations
- Standard quantum mechanics

### 5.2 Could LRT Make Distinct Predictions?

LRT's framework *could* make additional predictions if interface stability constrains more than just the Tsirelson bound:

**Potential distinctive claims:**

| Prediction | LRT Claim | Status |
|------------|-----------|--------|
| No superquantum correlations in any scenario | Yes | Same as QM |
| No violations in causal inequality tests | Yes | 2025 experiments consistent |
| Bound holds for macroscopic entanglement | Yes | Same as QM |
| Bound robust under gravitational effects | Unclear | Not tested |

**Honest assessment:** No experiment currently distinguishes LRT's interpretation from standard QM or Information Causality.

### 5.3 The "Why This Bound" Question

| Approach | Answer to "Why 2√2?" | Satisfying? |
|----------|---------------------|-------------|
| Mathematical (Tsirelson) | Cauchy-Schwarz on Hilbert space | Technically correct but not explanatory |
| Information Causality | Information access constraint | Operational but foundationally unclear |
| Conservation per NPRF | Spacetime symmetry | Physical but assumes QM |
| LRT | Interface stability + Parsimony | Interpretive but not independent |

All answers are partial. The foundational question remains open.

---

## 6. Falsification Conditions

### 6.1 What Would Falsify LRT's Interpretation?

**LRT interpretation falsified if:**

1. Reliable S > 2√2 observed without signaling (superquantum correlations exist)
2. Bound exceeded in regime where interface should be stable
3. Alternative theories (real or quaternionic QM) reproduce S > 2√2 without parsimony violation

**Note:** These would also falsify standard QM and Information Causality. There is no LRT-specific falsifier for the Tsirelson bound prediction.

### 6.2 What Would Support LRT's Interpretation?

LRT interpretation supported (but not uniquely) if:

1. All experiments saturate but never exceed 2√2
2. Causal inequality bounds consistent with quantum limits
3. No superquantum correlations in any experimental configuration

**Honest assessment:** These outcomes also support QM and Information Causality. Support is shared.

---

## 7. Discussion

### 7.1 The Interpretive vs. Derivational Distinction

LRT's treatment of the Tsirelson bound illustrates a general pattern:

| LRT Contribution | Type |
|-----------------|------|
| Complex Hilbert space selection | Derivational (via reconstruction) |
| Tsirelson bound value | Consequential (from Hilbert space) |
| "Why not higher?" explanation | Interpretive (interface stability) |

LRT does not provide an independent derivation of 2√2 from 3FLL. It provides an interpretation of why the mathematically-derived bound is physically necessary.

### 7.2 Relation to Other LRT Predictions

The Tsirelson bound interpretation differs from other LRT predictions:

| Prediction | LRT-Specific? | Experimentally Distinguishable? |
|------------|--------------|--------------------------------|
| Collapse rate formula | Yes (no free parameters) | Yes (vs. GRW) |
| No anomalous heating | Yes (logical actualization) | Yes (vs. physical collapse) |
| Frame-independence | Shared with MWI | Partially (vs. Bohmian) |
| Tsirelson bound | Shared with all | **No** |

The Tsirelson bound is LRT's **weakest** distinctive prediction because all quantum interpretations share it.

### 7.3 The Value of Interpretive Contributions

Even without distinct predictions, interpretive contributions have value:

1. **Explanatory unification:** Connects the bound to Global Parsimony and interface stability
2. **Conceptual clarity:** Explains *why* superquantum correlations are impossible, not just that they're excluded
3. **Framework coherence:** Integrates with LRT's other claims (collapse, non-locality)

However, interpretive contributions cannot be experimentally validated directly.

---

## 8. Conclusion

LRT interprets the Tsirelson bound as a structural consequence of interface stability: correlations exceeding 2√2 would introduce surplus ontological structure forbidden by Global Parsimony. This provides a coherent explanation within LRT's framework.

**Key findings:**

1. **Hard data:** No Tsirelson bound violation observed. Best precision: S = 2.73 ± 0.02 (Weihs 1998). Gap from 2√2 reflects experimental imperfection, not physics.

2. **LRT's contribution:** Interpretive, not derivational. The bound is a mathematical consequence of complex Hilbert space, which LRT selects via local tomography but does not independently derive from 3FLL.

3. **Comparison with alternatives:** Information Causality derives the bound without Hilbert space formalism. LRT's derivation chain goes through Hilbert space, making it less foundationally independent.

4. **Distinguishing predictions:** None. All interpretations predict S ≤ 2√2 exactly. No experiment distinguishes LRT from standard QM or Information Causality for this prediction.

5. **Value:** LRT provides explanatory unification by connecting the bound to its broader framework (Global Parsimony, interface stability), even without unique predictions.

The Tsirelson bound illustrates LRT's interpretive scope: explaining *why* quantum mechanics has certain features, rather than deriving quantitatively distinct predictions.

---

## References

- Cirel'son, B.S. (1980). "Quantum generalizations of Bell's inequality." Lett. Math. Phys. 4, 93.
- Clauser, J.F., Horne, M.A., Shimony, A., Holt, R.A. (1969). "Proposed experiment to test local hidden-variable theories." Phys. Rev. Lett. 23, 880.
- Hensen, B. et al. (2015). "Loophole-free Bell inequality violation using electron spins separated by 1.3 kilometres." Nature 526, 682.
- Masanes, L., Müller, M.P. (2011). "A derivation of quantum theory from physical requirements." New J. Phys. 13, 063001.
- Pawłowski, M. et al. (2009). "Information causality as a physical principle." Nature 461, 1101.
- Popescu, S., Rohrlich, D. (1994). "Quantum nonlocality as an axiom." Found. Phys. 24, 379.
- Silman, J., Chailloux, A., Aharon, N., Kerenidis, I., Pironio, S., Massar, S. (2013). "Fully distrustful quantum bit commitment and coin flipping." Phys. Rev. Lett. 106, 220501.
- Storz, S. et al. (2023). "Loophole-free Bell inequality violation with superconducting circuits." Nature 617, 265.
- Stucki, D. et al. (2020). "Why the Tsirelson Bound? Bub's Question and Fuchs' Desideratum." Entropy 22, 1015.
- Weihs, G. et al. (1998). "Violation of Bell's inequality under strict Einstein locality conditions." Phys. Rev. Lett. 81, 5039.
