# ISSUE 001: Grounding Axiom 3 (Physical Constraints)

**Status:** IN PROGRESS
**Priority:** CRITICAL
**Created:** 2025-11-26
**Updated:** 2025-11-27
**Source:** External peer-review (Gemini, Grok, GPT synthesis)

---

## 1. Executive Summary (Final Verdict — 2025)

Axiom 3 in LRT introduces three physical constraints:

* **3a — Continuity**
* **3b — Reversibility**
* **3c — Local Tomography**

After extensive internal analysis, multi-LLM consultation, and circularity checks, the conclusions are:

| Sub-Axiom | Derivable from Logical Primitives Alone? | Final Status (2025) |
|-----------|------------------------------------------|---------------------|
| **3b Reversibility** | **No** — unless a bridging principle is added | **DERIVED**, conditional on CBP |
| **3a Continuity** | **No** | Motivated only (no derivation) |
| **3c Local Tomography** | **No — and almost certainly impossible** | Independent physical axiom |

**Key Result:**
LRT reduces the physical input required for Hilbert-space quantum mechanics down to **two** assumptions (continuity and local tomography), plus one weak bridging principle (CBP). Reversibility is genuinely *derived* once CBP is adopted.

---

## 2. Problem Statement

LRT's goal is to derive quantum mechanics from:

* the three Fundamental Laws of Logic (3FLL),
* the Infinite Information Space (IIS),
* pairwise distinguishability,
* and Boolean actuality at the interface.

However, Axiom 3 introduces the following physical constraints:

* **(3a) Continuity:** every two pure states are connected by a continuous reversible path.
* **(3b) Reversibility:** fundamental transformations are invertible (unitary).
* **(3c) Local Tomography:** composite states are fixed by statistics of local measurements.

External reviewers pointed out that these assumptions are **identical** to the postulates used in standard operational reconstructions (Hardy; Masanes–Müller; Chiribella–D'Ariano–Perinotti) and are **not derived** from logic, IIS, or distinguishability.

> **Grok:** "Logic alone does not demand continuous transformations or local tomography."
> **Gemini:** "Hilbert space comes *only* after you insert Axiom 3; these parts remain physical, not logical."

Thus, ISSUE 001 asks:

> **Can 3a–3c be derived from LRT's logical and informational primitives, or must they remain irreducible physical postulates?**

---

## 3. Existing LRT Commitments

Any attempted derivation may use:

* **3FLL** (Identity, Non-Contradiction, Excluded Middle)
* **IIS** (maximal distinguishability field)
* **Axiom 2:** pairwise distinguishability
* **Initial state s₀**
* **CCP (Constitutive Closure Principle):** the constitutive package generates all fundamental structure
* **Parsimony Theorem (16.10):** no surplus grounded propositions exist in Boolean actuality

**No additional physical axioms may be assumed unless declared explicitly.**

---

## 4. Summary of Derivation Attempts

### Approach A — Information Preservation

* Motivates reversibility.
* Does not force continuity.
* Does not touch local tomography.

**Outcome:** Partial only.

---

### Approach B — Distinguishability-Induced Metric

* Distinguishability defines a distance.
* Distance-preserving maps can still be discontinuous or discrete.

**Outcome:** No derivation.

---

### Approach C — Compositional Distinguishability

* Tried to derive local tomography from pairwise distinguishability.
* Key step ("global pairwise distinguishability reduces to local pairs") is unsupported.

**Outcome:** No derivation; identified decomposability gap.

---

### Approach D — Constructor Theory

* Promising reframing in terms of possible/impossible tasks.
* Not developed enough to yield a derivation.

**Outcome:** Open.

---

### Approach E/F — Logical Time (Resolution Ordering)

* Time = ordering of IIS → Boolean transitions.
* Reversibility: partial success (injectivity).
* Continuity: no derivation.
* Local tomography: circular arguments.

**Outcome:** Philosophically helpful, mathematically insufficient.

---

## 5. Parsimony Bridge and the Scope Gap

Parsimony constrains *Boolean actuality* (the domain of truth-valued propositions).
But we need constraints on *IIS dynamics* (pre-Boolean).

This mismatch creates the **scope gap**:

| Domain | What Parsimony Governs | What Axiom 3 Governs |
|--------|------------------------|----------------------|
| Actuality | Truthmakers, grounded propositions | – |
| IIS Dynamics | – | Transformations on modal states |

Thus, **Parsimony alone cannot constrain IIS dynamics**.
A bridging principle is necessary.

---

## 6. CBP — Consistency Bridging Principle (NEW)

**CBP (Consistency Bridging Principle):**

> **Admissible transformations on IIS are only those for which all reachable states can, in principle, participate in a consistent resolution to Boolean actuality, without generating ungroundable propositions.**

CBP does **not** claim "only what is actual exists."
It simply requires that modal dynamics never produce states incompatible with any possible Boolean history.

With CBP, the scope gap is closed, and reversibility can be derived.

---

## 7. Final Derivation Status (After CBP)

### (3b) Reversibility — YES (Derived with CBP)

**Argument:**

1. Irreversible maps require mechanisms for information destruction.
2. Such mechanisms require extra structure not contained in the constitutive package.
3. By CCP + Parsimony, surplus structure cannot exist at the fundamental level.
4. Irreversible dynamics produce states incompatible with any consistent Boolean history ⇒ violates CBP.
5. Therefore fundamental IIS dynamics must be reversible (unitary).

**Status:** **DERIVED**, conditional on CBP.

---

### (3a) Continuity — NO (Motivated Only)

Continuity would require showing discontinuous maps inevitably introduce surplus specification (e.g., jump sets, exception tables).
This is plausible but **not proven**; formal specification-complexity arguments are missing.

**Status:** Motivated but not derived.

---

### (3c) Local Tomography — NO (Almost Certainly Independent)

Local tomography demands that global states be reconstructible from local data.
No argument from 3FLL, distinguishability, IIS maximality, CCP, Parsimony, or CBP forces this.

The decomposability gap remains:

* Ruling out "surplus" global structure does **not** imply local reconstructibility.
* Reconstruction literature treats local tomography as irreducible.

**Status:** Independent physical axiom; likely irreducible.

---

## 8. Implications for LRT

LRT's reconstruction hierarchy becomes:

### Tier 0 — Pure Logical/Informational Foundations

3FLL, IIS, distinguishability, Boolean actuality, Parsimony theorem

### Tier 1 — One Minimal Bridging Principle

CBP → **Reversibility** (derived)

### Tier 2 — Two Irreducible Physical Axioms

**Continuity** + **Local Tomography** → Hilbert space

### Tier 3 — Theorems

Hilbert space → Born rule (Gleason) → QM structure

This is the strongest derivation currently compatible with the structure of quantum theory as understood in operational reconstructions.

---

## 9. Required Paper Revisions

This issue mandates:

### (1) Add a new subsection

**"Remaining Physical Input: Continuity and Local Tomography"**
explaining precisely what is and is not derived.

### (2) Add CBP to Section 16

as the sole bridging principle between IIS dynamics and Boolean actuality.

### (3) Promote Reversibility (3b) to a theorem

derived from Parsimony + CBP + CCP.

### (4) Explicitly mark continuity and local tomography as independent postulates

with clear justification aligned with reconstruction literature.

### (5) Update the derivation chain diagrams

to reflect Tier 0 → Tier 1 → Tier 2 → Hilbert space.

---

## 10. Close Conditions for ISSUE 001

ISSUE 001 can be closed once the following are completed:

- [ ] CBP added to the manuscript
- [ ] Reversibility theorem written and cross-referenced
- [ ] Continuity marked as conjectural, not derived
- [ ] Local tomography explicitly identified as irreducible
- [ ] Reconstruction chain updated
- [ ] Section 16 revision merged

---

## Supporting Documents

- `DERIVATION_ATTEMPT_LocalTomography.md` (7 approaches tested)
- `DERIVATION_ATTEMPT_Continuity_Reversibility.md` (5 approaches each)
- `DERIVATION_ATTEMPT_LogicalTime.md` (Approach F)
- `DERIVATION_ATTEMPT_ParsimonyBridge.md` (scope gap analysis)
- `CIRCULARITY_CHECK_Axiom3_Derivations.md` (circularity verification)
- `multi_LLM/consultation/parsimony_scope_gap_20251127.md` (multi-LLM consultation)

---

## References

- Masanes, L. and Müller, M. P. (2011). "A derivation of quantum theory from physical requirements."
- Hardy, L. (2001). "Quantum theory from five reasonable axioms."
- Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). "Informational derivation of quantum theory."
- Deutsch, D. and Marletto, C. (2015). "Constructor theory of information."

---

**End of ISSUE 001**
