# Issue #41: Assess `time_evolution_family` as root axiom

**Status:** OPEN
**Priority:** MEDIUM
**Blocked by:** None
**Blocks:** #42, #43, #44
**Project:** #51

---

## Current Form

```lean
axiom time_evolution_family [InnerProductSpace ℂ H] : ℝ → (H →L[ℂ] H)
```

**Location:** `Step7_Unitarity.lean:129`

---

## Issue

This is a ROOT axiom — it asserts that evolution operators exist. The question is whether this should be:

1. Kept as a primitive physical input
2. Derived from more fundamental LRT structures
3. Replaced with Hamiltonian-based formulation

---

## Analysis

**Option A: Keep as primitive**
- "Evolution exists" is a physical input
- LRT doesn't derive dynamics from pure logic
- Honest to mark as ROOT

**Option B: Replace with Hamiltonian**
- Define `hamiltonian : H →L[ℂ] H` (bounded approximation)
- Add `hamiltonian_isSelfAdjoint`
- Define `time_evolution_family t := exp((-t * Complex.I) • hamiltonian)`
- Derive #42, #43, #44 as theorems

**Option C: Derive from actualization structure**
- States evolve because actualizations occur in sequence
- Unitarity from information preservation
- More philosophically grounded but technically harder

---

## Recommendation

**Option B** is most practical:
- Reduces 4 axioms to 2
- Well-understood mathematics
- Preserves physical content

However, this introduces bounded Hamiltonian (physical Hamiltonians are unbounded). For LRT's purposes, this is acceptable since we already import Stone's theorem as EXTERNAL.

---

## Dependencies

- If replaced with Hamiltonian approach:
  - #42, #43, #44 become derivable
  - Need `NormedSpace.exp` properties from Mathlib
