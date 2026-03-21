# Issue #38: Derive or justify `spectral_correspondence`

**Status:** OPEN
**Priority:** MEDIUM
**Blocked by:** None
**Blocks:** #39 (implicitly validates)
**Project:** #51

---

## Current Form

```lean
axiom spectral_correspondence [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (O : H →L[ℂ] H) (ev : ℂ) :
  (∃ ψ : H, ψ ≠ 0 ∧ OutcomePossible O ψ ev) ↔ O.hasEigenvalue ev
```

**Location:** `Step5/EigenvalueOutcome.lean:103`

---

## Issue

This is the standard quantum mechanical claim that "measurement outcomes = eigenvalues." The question is whether this is:

1. An axiom of QM (physical postulate)
2. A theorem derivable from LRT primitives

---

## Analysis

The correspondence follows from:
1. Spectral theorem: self-adjoint operators have real eigenvalues
2. Measurement interpretation: outcomes are eigenvalues

In LRT's framework, this should follow from Boolean actualization + spectral theory:
- A resolves events to {actual, nonActual}
- Sharp events correspond to projection operators
- Projection eigenvalues are {0, 1}
- General observables are sums of projections

---

## Path to Resolution

**Option A: Derive from Step4b Boolean chain**
- Boolean actualization → projection structure → spectral correspondence
- Requires wiring Step4b to Step5

**Option B: Reclassify as interpretation axiom**
- This is how we interpret the mathematical formalism physically
- Honest to mark as INTERPRETATION rather than REMAINING

**Option C: Prove from representation theory**
- Stone representation → projection lattice → spectral structure

---

## Recommendation

Assess whether the Boolean chain from Step4b provides sufficient infrastructure. If not, consider reclassifying as INTERPRETATION (not EXTERNAL, since it's not a mathematical theorem but a physical interpretation).
