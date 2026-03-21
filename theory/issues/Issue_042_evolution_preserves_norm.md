# Issue #42: Derive `evolution_preserves_norm`

**Status:** OPEN
**Priority:** MEDIUM
**Blocked by:** #41 (depends on evolution family)
**Blocks:** `step7_unitarity` theorem
**Project:** #51

---

## Current Form

```lean
axiom evolution_preserves_norm [InnerProductSpace ℂ H] (t : ℝ) :
  PreservesNorm (time_evolution_family t)
```

**Location:** `Step7_Unitarity.lean:135`

---

## Issue

This is derivable if we switch to Hamiltonian-based approach.

---

## Analysis

With Hamiltonian H (self-adjoint), define:
```
U(t) = exp(-i H t)
```

Then U(t) is unitary because:
1. H is self-adjoint: H† = H
2. Therefore (iH)† = -iH
3. U(t)† = exp(iHt) = U(-t)
4. U(t) U(t)† = exp(-iHt) exp(iHt) = exp(0) = I

Unitary operators preserve norm:
```
‖U(t)ψ‖² = ⟨U(t)ψ, U(t)ψ⟩ = ⟨ψ, U(t)†U(t)ψ⟩ = ⟨ψ, ψ⟩ = ‖ψ‖²
```

---

## Path to Resolution

1. Introduce `hamiltonian` and `hamiltonian_isSelfAdjoint` as new axioms
2. Define `time_evolution_family t := exp((-t * Complex.I) • hamiltonian)`
3. Use Mathlib's `exp` properties:
   - `NormedSpace.exp_add` for composition
   - `exp_zero` for identity
4. Prove `evolution_preserves_norm` from self-adjointness

---

## Mathlib Infrastructure Needed

- `exp_add_of_commute`: `exp(A + B) = exp(A) * exp(B)` when `[A,B] = 0`
- `exp_zero`: `exp(0) = 1`
- Properties of exp for self-adjoint operators

---

## Difficulty

MEDIUM — Mathematically straightforward. Requires setting up Hamiltonian-based definitions first (#41).

---

## Coupled With

This should be done together with #43 and #44 as a single "Step 7 consolidation" commit.
