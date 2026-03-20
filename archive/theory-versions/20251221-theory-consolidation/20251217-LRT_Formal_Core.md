# Logic Realism Theory: Formal Core

**Version:** 1.0
**Date:** 2025-12-17
**Author:** James D. Longmire (ORCID: 0009-0009-1383-7698)

---

## 1. The Central Claim

**Logic Realism Theory (LRT)** holds that physical reality is co-constituted by logical constraint operating on information space:

```
𝔄 = 𝔏(𝔍)
```

Where:
- **𝔍** (Information Space): The set of all total assignments of truth values to a σ-algebra of propositions about physical measurement outcomes
- **𝔏** (Logic Constraint): The operator that filters 𝔍 to those assignments satisfying the Three Fundamental Laws of Logic (3FLL)
- **𝔄** (Actualization): The set of physically realizable histories

---

## 2. The Three Fundamental Laws of Logic (3FLL)

| Law | Statement | Role |
|-----|-----------|------|
| **L₁** (Identity) | ∀A: A = A | States are self-identical |
| **L₂** (Non-Contradiction) | ∀A: ¬(A ∧ ¬A) | No state is both P and ¬P |
| **L₃** (Excluded Middle) | ∀A: A ∨ ¬A | Every state is either P or ¬P |

**Status:** Self-grounding. Denial presupposes what it denies.

---

## 3. Formal Definitions

**Definition 3.1 (Information Space):**
```
𝔍 := { s | s is a total truth-value assignment to σ-algebra P
       of physical measurement outcome propositions }
```

**Definition 3.2 (Logic Constraint Operator):**
```
𝔏(𝔍) := { s ∈ 𝔍 | s satisfies L₁, L₂, L₃ on all propositions in P }
```

**Definition 3.3 (Actualization Set):**
```
𝔄 := { s ∈ 𝔍 | s is physically realizable given Tier 1–3 axioms }
```

---

## 4. The Theorem-Conjecture Decomposition

### Theorem 4.1 (3FLL Constraint on Actualization)

*Given Tier 1 axioms and the empirical fact that no completed measurement record or physical observation violates 3FLL:*

```
𝔄 ⊆ 𝔏(𝔍)
```

**Proof sketch:** Any s ∈ 𝔄 encodes outcomes in a physically realizable history. No such outcome is both P and ¬P, neither P nor ¬P, or self-non-identical. Therefore s ∈ 𝔏(𝔍). ∎

**Status:** Empirically supported. No violation ever observed.

### Conjecture 4.1 (LRT Completeness)

*For any s ∈ 𝔏(𝔍), there exists a physically realizable history whose outcome pattern is s:*

```
𝔏(𝔍) ⊆ 𝔄
```

**Status:** Open. The ambitious heart of the research program.

### Corollary (Full Thesis)

If Conjecture 4.1 holds:
```
𝔄 = 𝔏(𝔍)
```

---

## 5. The Co-Constitutive Thesis

Neither 𝔏 nor 𝔍 alone constitutes physical reality:

| Component | Role |
|-----------|------|
| **𝔍** | Substrate — the space of possible information configurations |
| **𝔏** | Structure — the constraint filtering coherent from incoherent |
| **𝔄** | Emergence — physical reality as information-structured-by-logic |

**Key point:** This is NOT "logic alone generates reality" (strong idealism). It is the claim that 𝔏 and 𝔍 are **co-constitutive** of physical actualization.

**Resolution of over-generation:** If physical reality IS 𝔏(𝔍), there is no external standpoint from which 𝔏(𝔍) could be "too large." The completeness conjecture becomes definitional, not contingent.

---

## 6. The Tier System

### Tier 1: Structural Assumptions for 3FLL Application

| Axiom | Statement | Justification |
|-------|-----------|---------------|
| **(I)** | ∃D: D ≠ ∅ | 3FLL require a domain |
| **(I∞)** | ∀n ∈ ℕ: \|D\| > n | Continuous refinement requires unboundedness |
| **(I_pars)** | Select minimal specification | Required for L₁ to be verifiable |

### Tier 2: Established Mathematical Tools

Reconstruction theorems with tracked presuppositions:
- Stone's theorem (strongly continuous unitary groups)
- Gleason's theorem (probability measures on Hilbert spaces)
- Masanes-Müller reconstruction (operational axioms → quantum theory)

### Tier 3: Physical Principles

Empirically motivated inputs:
- Stability constraints (d ≤ 3)
- Symmetry principles
- Conservation laws

---

## 7. Empirical Status

### Falsifiability

LRT forbids:
1. A completed measurement recording P ∧ ¬P
2. A completed measurement failing to record P or ¬P (genuine gap)
3. A physical state failing self-identity across observation

### Current Evidence

**No violation has ever been observed.** All detector records across all domains of physics are Boolean at the outcome level.

### What Would Refute LRT

A reproducible experiment yielding contradictory outcomes in a completed measurement.

---

## 8. Scope Limitations

LRT concerns **physical reality** only:
- Measurement outcomes
- Actualized physical states
- What physics describes

LRT is **agnostic** about:
- Mathematical reality (abstract objects)
- Ontological status of 3FLL themselves
- Domains of reality beyond physics

---

## 9. Contrast with Alternatives

| Framework | Problem | LRT Solution |
|-----------|---------|--------------|
| **MWI** | Over-generation (all branches exist) | Only 𝔏(𝔍) exists |
| **Paraconsistent physics** | No distinct empirical predictions | All outcomes Boolean |
| **QBism** | Outcomes agent-centric | Intersubjectivity grounds realism |

---

## 10. Summary

| Statement | Status |
|-----------|--------|
| 𝔄 ⊆ 𝔏(𝔍) | **Theorem** — empirically established |
| 𝔏(𝔍) ⊆ 𝔄 | **Conjecture** — open research problem |
| 𝔄 = 𝔏(𝔍) | **Full thesis** — conditional on completeness |
| Co-constitution | 𝔏 and 𝔍 jointly constitute physical reality |
| Scope | Physical reality only |
| Falsifiability | Clear conditions; none violated |

---

## References

- Masanes, L. and Müller, M.P. (2011) 'A derivation of quantum theory from physical requirements', *New Journal of Physics*, 13, 063001.
- Stone, M.H. (1932) 'On One-Parameter Unitary Groups in Hilbert Space', *Annals of Mathematics*, 33(3), pp. 643-648.
- Gleason, A.M. (1957) 'Measures on the Closed Subspaces of a Hilbert Space', *Journal of Mathematics and Mechanics*, 6(6), pp. 885-893.

---

*This document presents the formal core of Logic Realism Theory in its tightest framing. For philosophical context, comparisons with existing traditions, and detailed derivations, see the full paper: `2025-12-17_logic_realism_philosophy_of_science.md`.*
