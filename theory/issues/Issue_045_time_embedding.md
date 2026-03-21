# Issue #45: Convert `time_embedding` from axiom to definition

**Status:** OPEN
**Priority:** HIGH (zero-cost)
**Blocked by:** None
**Blocks:** #46
**Project:** #51

---

## Current Form

```lean
axiom time_embedding : ActualizationEvent → ℝ
```

**Location:** `Step8_TemporalEmergence.lean:90`

---

## Issue

This can be trivially defined rather than axiomatized.

---

## Analysis

`ActualizationEvent` has an `id : ℕ` field. The time embedding is just the natural cast to ℝ.

---

## Proposed Fix

```lean
/-- Time embedding maps actualization events to real-valued time coordinates.
    Since events are ℕ-indexed, this is just the natural cast. -/
def time_embedding (e : ActualizationEvent) : ℝ := e.id
```

---

## Mathlib Infrastructure

- `Nat.cast` coercion to ℝ

---

## Difficulty

TRIVIAL — One-line definition replacement.

---

## Impact

- Removes one axiom
- #46 (`time_embedding_strict_mono`) becomes derivable from this definition
