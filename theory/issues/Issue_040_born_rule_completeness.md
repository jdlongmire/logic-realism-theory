# Issue #40: Derive `born_rule_completeness`

**Status:** OPEN
**Priority:** MEDIUM
**Blocked by:** #39 (requires spectral structure)
**Blocks:** None
**Project:** #51

---

## Current Form

```lean
axiom born_rule_completeness [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (P : ι → H →L[ℂ] H) (ψ : H) (hψ : ‖ψ‖ = 1)
  (hP : PartitionOfUnity P) :
  ∑ i, ‖P i ψ‖^2 = 1
```

**Location:** `Step6_BornRule.lean:431`

---

## Issue

This is Parseval's identity for orthonormal decomposition. It should be derivable from spectral theory.

---

## Analysis

Given:
- `PartitionOfUnity P`: `∑ᵢ Pᵢ = I` and each `Pᵢ` is a projection
- Projections are orthogonal: `Pᵢ * Pⱼ = 0` for `i ≠ j`
- `‖ψ‖ = 1`

Then:
```
‖ψ‖² = ⟨ψ, ψ⟩ = ⟨ψ, I ψ⟩ = ⟨ψ, (∑ᵢ Pᵢ) ψ⟩ = ∑ᵢ ⟨ψ, Pᵢ ψ⟩
     = ∑ᵢ ⟨Pᵢ ψ, Pᵢ ψ⟩  (since Pᵢ is self-adjoint and idempotent)
     = ∑ᵢ ‖Pᵢ ψ‖²
```

So: `1 = ∑ᵢ ‖Pᵢ ψ‖²`

---

## Path to Resolution

1. Use Mathlib's `OrthogonalFamily` or `DirectSum` infrastructure
2. May require `FiniteDimensional` instance for finite summation
3. Key lemmas needed:
   - Self-adjoint: `⟨Pψ, φ⟩ = ⟨ψ, Pφ⟩`
   - Idempotent: `P² = P`
   - Therefore: `⟨ψ, Pψ⟩ = ⟨Pψ, Pψ⟩ = ‖Pψ‖²`

---

## Difficulty

MEDIUM — Standard spectral theory. The proof is straightforward mathematically; the question is whether Mathlib has the right infrastructure exposed.

---

## Dependencies

- Requires proper `PartitionOfUnity` structure with orthogonality
- Benefits from #39 being fixed (ensures projections are properly typed)
