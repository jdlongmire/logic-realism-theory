# Issue #46: Derive `time_embedding_strict_mono`

**Status:** OPEN
**Priority:** HIGH (derivable from #45)
**Blocked by:** #45 (time_embedding definition)
**Blocks:** None
**Project:** #51

---

## Current Form

```lean
axiom time_embedding_strict_mono : StrictMono time_embedding
```

**Location:** `Step8_TemporalEmergence.lean:101`

---

## Issue

This is derivable once #45 defines `time_embedding` as the natural cast.

---

## Analysis

With `time_embedding e := (e.id : ℝ)`:

```
StrictMono time_embedding
↔ ∀ e₁ e₂, e₁ < e₂ → time_embedding e₁ < time_embedding e₂
↔ ∀ e₁ e₂, e₁.id < e₂.id → (e₁.id : ℝ) < (e₂.id : ℝ)
```

This follows from `Nat.cast_strictMono`.

---

## Proposed Fix

```lean
theorem time_embedding_strict_mono : StrictMono time_embedding := by
  intro e₁ e₂ h
  simp only [time_embedding]
  exact Nat.cast_lt.mpr h
```

---

## Mathlib Infrastructure

- `Nat.cast_lt : (n : ℝ) < (m : ℝ) ↔ n < m`
- `Nat.cast_strictMono`

---

## Difficulty

TRIVIAL — Three-line proof once #45 is done.

---

## Order

Do immediately after #45.
