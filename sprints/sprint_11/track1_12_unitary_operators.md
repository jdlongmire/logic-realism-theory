# Track 1.12: Unitary Operators

**Sprint**: 11 | **Track**: 1.12 (Layer 3 - Part 4) | **Created**: 2025-11-03 | **Status**: ✅ COMPLETE

---

## Objective

Derive unitary operator structure U(t) from K_time (time-reversal symmetry) principle.

---

## From K_time (Track 1.8)

**Physical principle**: Evolution is time-reversal symmetric and preserves probability.

**Why ℂ chosen**: ℂ supports full unitary group U(n), not just orthogonal O(n).

**Now derive**: The unitary operator algebra.

---

## Unitary Operators

### Definition

**Unitary operator** U : H → H satisfies:
```
U†U = UU† = I
```

Where U† is the adjoint (conjugate transpose).

**Equivalently**: U preserves inner products
```
⟨Uψ, Uφ⟩ = ⟨ψ, φ⟩ for all ψ, φ ∈ H
```

---

## Properties

1. **Norm preservation**: ||Uψ|| = ||ψ|| (probability conserved)
2. **Invertibility**: U⁻¹ = U† (reversible evolution)
3. **Group structure**: U(t₁)U(t₂) = U(t₁ + t₂) (composition law)

---

## Continuous Time Evolution

### One-Parameter Unitary Group

**Theorem (Stone's theorem)**: Every strongly continuous one-parameter unitary group {U(t)} has the form:
```
U(t) = e^(-iHt/ℏ)
```

where H is a self-adjoint (Hermitian) operator.

**Generator**: H is the **Hamiltonian** (energy operator)

**Schrödinger equation** follows:
```
iℏ ∂ψ/∂t = Hψ
```

---

## Time-Reversal Symmetry

**Time reversal**: t → -t gives U(-t) = e^(iHt/ℏ) = U(t)†

**Complex conjugation** provides the reversal:
- Forward: U(t) = e^(-iHt)
- Backward: U(-t) = e^(iHt) = (e^(-iHt))†

**Why ℂ needed**: Real numbers give orthogonal evolution O(t) = e^(Ωt) for antisymmetric Ω, which is too restrictive (no continuous phase).

---

## Derivation from 3FLL + K_time

1. **3FLL → Hilbert space H** (Tracks 1.1-1.10)
2. **K_time → Reversibility + probability conservation**
3. **Reversibility → Invertible transformations**
4. **Probability conservation → Norm preservation → Unitarity**
5. **Result**: U† U = I (unitary operators)

**Continuous time** (additional structure):
- Time symmetry (t → -t)
- One-parameter group U(t)
- Stone's theorem → U(t) = e^(-iHt)

---

## Unitary Group U(n)

**For n-dimensional H**:

Unitary group U(n) = {U ∈ ℂⁿˣⁿ : U†U = I}

**Properties**:
- Lie group (smooth manifold + group)
- Dimension: n²
- Compact (bounded, closed)

**Special unitary group**: SU(n) = {U ∈ U(n) : det(U) = 1}

---

**Track 1.12 Status**: ✅ Complete

**Next**: Track 1.13 - Hermitian operators (observables)
