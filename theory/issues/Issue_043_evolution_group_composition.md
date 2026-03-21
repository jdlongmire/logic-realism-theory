# Issue #43: Derive `evolution_group_composition`

**Status:** OPEN
**Priority:** MEDIUM
**Blocked by:** #41 (depends on evolution family)
**Blocks:** #47 (redundant with this)
**Project:** #51

---

## Current Form

```lean
axiom evolution_group_composition [InnerProductSpace ℂ H] (s t : ℝ) :
  time_evolution_family (s + t) = time_evolution_family s * time_evolution_family t
```

**Location:** `Step7_Unitarity.lean:140`

---

## Issue

This is derivable if we switch to Hamiltonian-based approach.

---

## Analysis

With Hamiltonian H, define:
```
U(t) = exp(-i H t)
```

Then:
```
U(s+t) = exp(-iH(s+t)) = exp(-iHs - iHt)
       = exp(-iHs) * exp(-iHt)    (since -iHs and -iHt commute)
       = U(s) * U(t)
```

The key is that `-iHs` and `-iHt` commute (both are scalar multiples of the same H).

---

## Path to Resolution

Use Mathlib's `exp_add_of_commute`:
```lean
theorem exp_add_of_commute (hAB : Commute A B) :
  exp (A + B) = exp A * exp B
```

We need to show:
```lean
Commute ((-s * Complex.I) • H) ((-t * Complex.I) • H)
```

This follows from `smul_comm` since both are scalar multiples of H.

---

## Mathlib Infrastructure

- `exp_add_of_commute`
- `Commute` for scalar multiples

---

## Difficulty

MEDIUM — Once #41 sets up Hamiltonian infrastructure, this follows directly.

---

## Coupled With

- #42 (evolution_preserves_norm)
- #44 (evolution_identity)
- #47 is REDUNDANT with this (same group law, different notation)
