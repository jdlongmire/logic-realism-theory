# Issue #47: Remove `evolution_matches_actualization` (redundant)

**Status:** OPEN
**Priority:** HIGH (redundant)
**Blocked by:** #43 (same content)
**Blocks:** None
**Project:** #51

---

## Current Form

```lean
axiom evolution_matches_actualization [InnerProductSpace ℂ H]
  (e₁ e₂ : ActualizationEvent) (h : e₁ < e₂) :
  time_evolution_family (time_embedding e₂) =
    time_evolution_family (time_embedding e₂ - time_embedding e₁) *
    time_evolution_family (time_embedding e₁)
```

**Location:** `Step8_TemporalEmergence.lean:151`

---

## Issue

This is the group composition law restated in terms of actualization events. It's redundant with #43 (`evolution_group_composition`).

---

## Analysis

`evolution_group_composition` says:
```
U(s + t) = U(s) * U(t)
```

Setting `s = t₂ - t₁` and `t = t₁`:
```
U((t₂ - t₁) + t₁) = U(t₂ - t₁) * U(t₁)
U(t₂) = U(t₂ - t₁) * U(t₁)
```

This is exactly `evolution_matches_actualization`.

---

## Proposed Fix

Remove axiom; replace with theorem:

```lean
theorem evolution_matches_actualization (e₁ e₂ : ActualizationEvent) (h : e₁ < e₂) :
  time_evolution_family (time_embedding e₂) =
    time_evolution_family (time_embedding e₂ - time_embedding e₁) *
    time_evolution_family (time_embedding e₁) := by
  have := evolution_group_composition (time_embedding e₂ - time_embedding e₁) (time_embedding e₁)
  simp only [sub_add_cancel] at this
  exact this
```

---

## Difficulty

TRIVIAL — Direct consequence of group law.

---

## Impact

Removes one axiom. Should be done after or together with #43.
