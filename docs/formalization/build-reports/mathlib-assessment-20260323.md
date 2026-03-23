# Mathlib Assessment: HARD Axioms

**Date:** 2026-03-23
**Purpose:** Assess whether remaining HARD axioms can be reduced using Mathlib

## HARD Axioms Under Review

| Axiom | Location | Description |
|-------|----------|-------------|
| `hamiltonian_generates_unitary` | Step10 | `exp(-i·H·t)` is unitary |
| `hamiltonian_generates_group_mul` | Step10 | `exp(-i·H·(s+t)) = exp(-i·H·s) · exp(-i·H·t)` |
| `schrodinger_from_stone` | Step10 | Stone's theorem connection |
| `step4_hilbert_space` | Step4 | (Now removed — see CPH001) |

## Mathlib Findings

### 1. Self-Adjoint → Unitary Exponential

**File:** `Mathlib/Analysis/CStarAlgebra/Exponential.lean`

**Available:**
```lean
-- exp(i·a) is unitary when a is self-adjoint
noncomputable def selfAdjoint.expUnitary (a : selfAdjoint A) : unitary A

-- exp(0) = 1
lemma selfAdjoint.expUnitary_zero : expUnitary (0 : selfAdjoint A) = 1

-- exp(a+b) = exp(a)·exp(b) when a,b commute
theorem Commute.expUnitary_add {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    expUnitary (a + b) = expUnitary a * expUnitary b
```

**Assessment:**
- `hamiltonian_generates_unitary`: **POTENTIALLY DERIVABLE**
  - Mathlib proves `exp(I·a)` is unitary for self-adjoint `a` in C*-algebras
  - Requires: formalize Hamiltonian as `selfAdjoint (H →L[ℂ] H)`
  - Gap: LRT uses bounded operators `H →L[ℂ] H`; Mathlib C*-algebra is more general

- `hamiltonian_generates_group_mul`: **POTENTIALLY DERIVABLE**
  - `Commute.expUnitary_add` gives: `exp(a+b) = exp(a)·exp(b)` when commute
  - For `t·H`, we have `(s·H) * (t·H) = (t·H) * (s·H)` (scalar multiples commute)
  - Should be derivable via: `exp((s+t)·H) = exp(s·H + t·H) = exp(s·H)·exp(t·H)`

### 2. Stone's Theorem

**Status:** NOT IN MATHLIB

Stone's theorem (one-parameter unitary groups have self-adjoint generators) requires:
- Unbounded operator theory (not in Mathlib)
- Spectral theory for unbounded operators (not in Mathlib)
- Domain considerations (not in Mathlib)

Mathlib's spectral theory is limited to:
- Bounded operators on Hilbert spaces
- C*-algebras (abstract, not concrete operators)

**Assessment:**
- `schrodinger_from_stone`: **NOT DERIVABLE** — Mathlib lacks unbounded operator theory
- `stones_theorem`: **EXTERNAL** — must remain axiom

### 3. Hilbert Space from CPH

**Status:** RESOLVED (this session)

`QuantumStateSpace.ofCPH` now derived via:
- `Module.Finite ℂ H` → `FiniteDimensional ℂ H`
- `FiniteDimensional.proper ℂ H` → `ProperSpace H`
- `complete_of_proper` → `CompleteSpace H`

**Axiom removed:** `step4_hilbert_space` (22 → 21 axioms)

## Summary

| Axiom | Status | Action |
|-------|--------|--------|
| `step4_hilbert_space` | ✅ **REMOVED** | Derived from Mathlib |
| `hamiltonian_generates_unitary` | ⚠️ **POTENTIALLY DERIVABLE** | Requires refactoring to use C*-algebra `selfAdjoint.expUnitary` |
| `hamiltonian_generates_group_mul` | ⚠️ **POTENTIALLY DERIVABLE** | Via `Commute.expUnitary_add` |
| `schrodinger_from_stone` | ❌ **NOT DERIVABLE** | Mathlib lacks unbounded operators |
| `stones_theorem` | ❌ **EXTERNAL** | Retain as Tier-2 import |

## Recommendations

1. **Immediate:** Mark `schrodinger_from_stone` and `stones_theorem` as EXTERNAL (Tier-2)
   - These are established mathematical results, not LRT axioms
   - Mathlib will likely not support them soon (unbounded operator theory is hard)

2. **Medium-term:** Attempt derivation of unitary generation axioms
   - Refactor `hamiltonian` to use `selfAdjoint` subtype
   - Apply `selfAdjoint.expUnitary` and `Commute.expUnitary_add`
   - May reduce axiom count by 2

3. **Low priority:** Monitor Mathlib development
   - Stone's theorem is a known gap
   - May be added in future Mathlib versions

## Axiom Count Projection

| Phase | Count | Notes |
|-------|-------|-------|
| Current | 21 | After CPH001 |
| After EXTERNAL reclassification | 21 | (no change, just labeling) |
| After unitary derivation | 19 | If successful |

**Realistic target:** 19-21 axioms (3 PRIMITIVE, 12-14 EXTERNAL, 4-6 REMAINING)
