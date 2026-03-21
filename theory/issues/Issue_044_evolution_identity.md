# Issue #44: Derive `evolution_identity`

**Status:** OPEN
**Priority:** HIGH (trivial)
**Blocked by:** #41 (depends on evolution family)
**Blocks:** None
**Project:** #51

---

## Current Form

```lean
axiom evolution_identity [InnerProductSpace ℂ H] :
  time_evolution_family 0 = ContinuousLinearMap.id ℂ H
```

**Location:** `Step7_Unitarity.lean:146`

---

## Issue

This is trivially derivable from `exp_zero`.

---

## Analysis

With Hamiltonian H, define:
```
U(t) = exp(-i H t)
```

Then:
```
U(0) = exp(-iH * 0) = exp(0) = I
```

---

## Path to Resolution

```lean
theorem evolution_identity : time_evolution_family 0 = ContinuousLinearMap.id ℂ H := by
  simp only [time_evolution_family_def, mul_zero, zero_smul, NormedSpace.exp_zero]
```

---

## Mathlib Infrastructure

- `NormedSpace.exp_zero : exp 0 = 1`
- Basic simp lemmas

---

## Difficulty

TRIVIAL — One-liner once Hamiltonian infrastructure is in place.

---

## Quick Win

This is a quick win that can be done immediately after #41 introduces the Hamiltonian definition.
