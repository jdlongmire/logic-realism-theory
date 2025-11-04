# Track 2.5: Von Neumann Entropy Definition

**Sprint**: 11 (Non-Circular Foundations)
**Track**: 2.5 (Born Rule - Phase 2)
**Created**: 2025-11-03 (Session 8.2)
**Status**: 🟢 IN PROGRESS

---

## Overview

**Objective**: Define von Neumann entropy S(ρ) = -Tr(ρ ln ρ) on density operators (not on state vectors), providing foundation for Maximum Entropy Principle.

**Key Point**: Entropy defined on ρ (density operators from Phase 1), NOT on |ψ⟩ with presupposed probabilities.

**Non-circularity**: We're defining entropy on the probability structure we DERIVED (ρ from Gleason), not on assumed probabilities.

---

## 1. Von Neumann Entropy Definition

### Formula

**For density operator ρ**:
```
S(ρ) = -Tr(ρ ln ρ)
```

**In terms of eigenvalues**: If ρ = ∑ᵢ λᵢ|ψᵢ⟩⟨ψᵢ| (spectral decomposition):
```
S(ρ) = -∑ᵢ λᵢ ln λᵢ
```
(with convention 0 ln 0 = 0)

**Units**: Often written as S(ρ) = -k_B Tr(ρ ln ρ) where k_B is Boltzmann constant. For information theory, use nats or bits (k_B = 1).

### Why This Form?

**Shannon entropy generalization**:
Classical Shannon entropy: H(p) = -∑ᵢ pᵢ ln pᵢ

For quantum system with classical probabilities:
- ρ = ∑ᵢ pᵢ|ψᵢ⟩⟨ψᵢ| (diagonal in some basis)
- S(ρ) = -∑ᵢ pᵢ ln pᵢ = H(p) ✓

**Quantum extension**: von Neumann (1932) extended to non-diagonal ρ using S = -Tr(ρ ln ρ)

**Uniqueness**: Can be proven that S(ρ) = -Tr(ρ ln ρ) is the UNIQUE entropy functional satisfying natural axioms (continuity, additivity, etc.)

### Properties

**1. Non-negativity**: S(ρ) ≥ 0 for all ρ
- Proof: λᵢ ∈ [0,1], so -λᵢ ln λᵢ ≥ 0

**2. Minimum for pure states**: S(ρ) = 0 ⟺ ρ = |ψ⟩⟨ψ| (pure)
- Proof: ρ pure → single λ = 1 → -1·ln 1 = 0
- Converse: S = 0 → all λᵢ = 0 or 1, ∑λᵢ = 1 → single λ = 1 → pure

**3. Maximum for maximally mixed**: S(ρ) ≤ ln dim(ℋ), with equality for ρ = I/dim(ℋ)
- Proof: Maximum of -∑λᵢ ln λᵢ subject to ∑λᵢ = 1 is at λᵢ = 1/n (all equal)

**4. Concavity**: For convex combination ρ_λ = λρ₁ + (1-λ)ρ₂:
```
S(ρ_λ) ≥ λS(ρ₁) + (1-λ)S(ρ₂)
```
(Mixing increases entropy)

**5. Subadditivity**: For composite system ρ_{AB} on ℋ_A ⊗ ℋ_B:
```
S(ρ_{AB}) ≤ S(ρ_A) + S(ρ_B)
```
where ρ_A = Tr_B(ρ_{AB}) (partial trace)

**6. Invariance under unitaries**: S(UρU†) = S(ρ) for unitary U
- Physical: Entropy unchanged by reversible evolution

---

## 2. Connection to Information Theory

### Shannon Entropy

**Classical random variable X** with probabilities {p₁, ..., pₙ}:
```
H(X) = -∑ᵢ pᵢ log₂ pᵢ (bits)
```

**Interpretation**: Average information content / uncertainty

### Von Neumann as Quantum Shannon

**Quantum state ρ** on ℋ:
```
S(ρ) = -Tr(ρ ln ρ) (nats)
```

**Interpretation**: Quantum information content / uncertainty

**For diagonal ρ**: S(ρ) = H(eigenvalues) (classical Shannon entropy)

**For non-diagonal ρ**: Captures quantum coherences (off-diagonal terms)

### Quantum vs Classical Entropy

**Key difference**:
- Classical: H(p) depends only on probabilities {pᵢ}
- Quantum: S(ρ) depends on full ρ (eigenvalues + eigenvectors + phases)

**Example** (qubit):
```
ρ₁ = 0.5|0⟩⟨0| + 0.5|1⟩⟨1| (diagonal)
ρ₂ = 0.5|+⟩⟨+| + 0.5|-⟩⟨-| (diagonal in different basis)
```

Both have same eigenvalues {0.5, 0.5} → same S(ρ) = ln 2

But ρ₁ ≠ ρ₂ physically (different coherences in standard basis)

---

## 3. Physical Interpretation

### Entropy as Uncertainty

**Pure state** ρ = |ψ⟩⟨ψ|: S = 0
- No uncertainty (definite state)
- Maximum information

**Maximally mixed** ρ = I/dim(ℋ): S = ln dim(ℋ)
- Maximum uncertainty (no information)
- Minimum information

**Mixed state**: 0 < S < ln dim(ℋ)
- Partial uncertainty
- Partial information

### Entropy in Measurement

**Before measurement**: System in state ρ with entropy S(ρ)

**Measurement of observable A**: Projects to eigenstate |a⟩ with probability p(a) = Tr(ρ|a⟩⟨a|)

**After measurement**: State is ρ' = |a⟩⟨a| with S(ρ') = 0

**Information gained**: ΔI = S(ρ) - S(ρ') = S(ρ) - 0 = S(ρ)

**Entropy as information deficit**: S(ρ) = how much information measurement will provide

### Thermodynamic Connection

**Thermodynamic entropy**: S_therm = k_B ln Ω (Boltzmann)
- Ω = number of microstates

**Quantum thermal state**: ρ_β = Z⁻¹ e^(-βH)
- Z = Tr(e^(-βH)) (partition function)
- β = 1/(k_B T)

**Von Neumann entropy**:
```
S(ρ_β) = k_B (ln Z + β⟨H⟩)
```

**Connection to thermodynamics**:
- S(ρ_β) = S_therm at equilibrium
- Quantum entropy generalizes thermodynamic entropy

---

## 4. Maximum Entropy Principle

### Setup

**Problem**: Given constraints on system, which density operator ρ best represents our state?

**Constraints**:
- Expectation values: ⟨Aᵢ⟩ = Tr(ρAᵢ) = aᵢ (known)
- Normalization: Tr(ρ) = 1

**MaxEnt Principle** (Jaynes 1957): Choose ρ that maximizes S(ρ) subject to constraints

**Justification**: Maximum entropy = minimum assumptions = least biased estimate

### Mathematical Formulation

**Optimization problem**:
```
maximize: S(ρ) = -Tr(ρ ln ρ)
subject to:
  Tr(ρAᵢ) = aᵢ  (i = 1, ..., n)
  Tr(ρ) = 1
  ρ ≥ 0
```

**Lagrange multipliers**:
```
ℒ = -Tr(ρ ln ρ) - λ₀(Tr(ρ) - 1) - ∑ᵢ λᵢ(Tr(ρAᵢ) - aᵢ)
```

**Variational derivative**: δℒ/δρ = 0

**Solution**:
```
ρ_MaxEnt = Z⁻¹ exp(-∑ᵢ λᵢAᵢ)
```
where Z = Tr(exp(-∑ᵢ λᵢAᵢ)), and λᵢ determined by constraints

### Special Cases

**No constraints** (no information):
```
ρ_MaxEnt = I/dim(ℋ)  (maximally mixed)
S(ρ) = ln dim(ℋ)  (maximum entropy)
```

**Energy constraint** ⟨H⟩ = E:
```
ρ_MaxEnt = Z⁻¹ e^(-βH)  (canonical ensemble)
where β determined by E
```

**Complete information** (pure state):
```
ρ_MaxEnt = |ψ⟩⟨ψ|  (pure state projector)
S(ρ) = 0  (minimum entropy)
```

---

## 5. MaxEnt and Born Rule

### The Strategy

**Phase 1 (Tracks 2.1-2.4)**: Derived that probabilities have form:
```
p(measurement P) = Tr(ρP)
```
for some density operator ρ (from Gleason + 3FLL)

**Phase 2 (NOW)**: Use MaxEnt to determine WHICH ρ

**Question**: For a "definite quantum state", which ρ represents it?

**Answer** (Track 2.6-2.7): MaxEnt with "state is pure" constraint gives:
```
ρ = |ψ⟩⟨ψ|
```

Then Born rule follows:
```
p(outcome x) = Tr(ρ|x⟩⟨x|) = ⟨x|ψ⟩⟨ψ|x⟩ = |⟨x|ψ⟩|²
```

**Key**: |⟨x|ψ⟩|² emerges as OUTPUT, not INPUT!

### Non-Circularity Check

**Not circular because**:
1. ✅ Entropy S(ρ) defined on density operators (from Gleason, Track 2.3)
2. ✅ Density operators derived from frame functions (from 3FLL, Track 2.2)
3. ✅ MaxEnt is principle (maximize uncertainty given constraints)
4. ✅ Born rule will be DERIVED from MaxEnt + purity constraint

**Circular would be**:
- ❌ Starting with S = -∑ pᵢ ln pᵢ where pᵢ = |⟨i|ψ⟩|² (presupposing Born rule)
- ❌ Defining entropy on |ψ⟩ directly

**Our approach**:
- ✓ S(ρ) defined on operators ρ (derived from Gleason)
- ✓ Eigenvalues λᵢ of ρ are the probabilities (not presupposed)
- ✓ Born rule emerges from MaxEnt (Track 2.7)

---

## 6. Formal Properties for Lean

### Type Definitions

```lean
-- Von Neumann entropy
def von_neumann_entropy (ρ : DensityOperator ℋ) : ℝ :=
  -Tr(ρ.ρ * matrix_log ρ.ρ)

-- Alternative: via eigenvalues
def entropy_from_eigenvalues (λ : Fin n → ℝ) (h : ∀ i, 0 ≤ λ i ∧ λ i ≤ 1) : ℝ :=
  -∑ i, (λ i) * Real.log (λ i)
```

### Key Theorems

```lean
-- Non-negativity
theorem entropy_nonneg (ρ : DensityOperator ℋ) :
  0 ≤ von_neumann_entropy ρ

-- Pure state has zero entropy
theorem pure_iff_zero_entropy (ρ : DensityOperator ℋ) :
  IsPure ρ ↔ von_neumann_entropy ρ = 0

-- Maximally mixed has maximum entropy
theorem max_entropy_mixed (ρ : DensityOperator ℋ) :
  von_neumann_entropy ρ ≤ Real.log (finrank ℂ ℋ)
  ∧ (von_neumann_entropy ρ = Real.log (finrank ℂ ℋ) ↔ ρ = (1 / finrank ℂ ℋ) • I)

-- Concavity
theorem entropy_concave (ρ₁ ρ₂ : DensityOperator ℋ) (λ : ℝ) (h : 0 ≤ λ ∧ λ ≤ 1) :
  von_neumann_entropy (λ • ρ₁ + (1-λ) • ρ₂) ≥
    λ * von_neumann_entropy ρ₁ + (1-λ) * von_neumann_entropy ρ₂

-- Unitary invariance
theorem entropy_unitary_invariant (ρ : DensityOperator ℋ) (U : UnitaryOperator ℋ) :
  von_neumann_entropy (U * ρ * U†) = von_neumann_entropy ρ
```

### MaxEnt Principle

```lean
-- MaxEnt optimization problem
structure MaxEntProblem (ℋ : Type*) [InnerProductSpace ℂ ℋ] where
  constraints : List (Observable ℋ × ℝ)  -- (Aᵢ, aᵢ) pairs

-- MaxEnt solution
def maxent_density (problem : MaxEntProblem ℋ) : DensityOperator ℋ :=
  -- Solve: maximize S(ρ) subject to Tr(ρAᵢ) = aᵢ
  sorry  -- Full proof requires optimization theory

-- MaxEnt characterization
axiom maxent_exponential (problem : MaxEntProblem ℋ) :
  ∃ (λ : List ℝ) (Z : ℝ),
    (maxent_density problem).ρ = Z⁻¹ • exp(-∑ᵢ λᵢ * (problem.constraints.get i).1)
```

---

## 7. Examples

### Example 1: No Information (Maximally Mixed)

**Constraints**: Only Tr(ρ) = 1 (normalization)

**MaxEnt solution**:
```
ρ = I/dim(ℋ)
```

**Entropy**:
```
S(ρ) = ln dim(ℋ)  (maximum)
```

**Physical interpretation**: Complete ignorance → uniform distribution

### Example 2: Known Energy (Thermal State)

**Constraints**:
- Tr(ρ) = 1
- ⟨H⟩ = Tr(ρH) = E (known energy)

**MaxEnt solution**:
```
ρ_β = Z⁻¹ e^(-βH)  (canonical ensemble)
where β = 1/(k_B T) determined by E
```

**Entropy**:
```
S(ρ_β) = k_B(ln Z + β E)
```

**Physical interpretation**: Thermodynamic equilibrium at temperature T

### Example 3: Pure State Constraint

**Constraints**:
- Tr(ρ) = 1
- Tr(ρ²) = 1 (purity)

**MaxEnt solution**:
```
ρ = |ψ⟩⟨ψ|  (pure state projector)
```

**Entropy**:
```
S(ρ) = 0  (minimum)
```

**Physical interpretation**: Definite quantum state (maximum information)

**This is the key for Born rule!** (Track 2.6-2.7)

---

## 8. Track 2.5 Summary

### What We Defined

**Von Neumann entropy**: S(ρ) = -Tr(ρ ln ρ)
- On density operators (from Phase 1)
- NOT on state vectors with presupposed probabilities
- Generalizes Shannon entropy to quantum case

**Properties**:
- S ≥ 0 (non-negative)
- S = 0 ⟺ pure state
- S = ln dim(ℋ) for maximally mixed
- Concave, unitary-invariant

**MaxEnt Principle**: Choose ρ maximizing S given constraints

### Non-Circularity Maintained ✓

**Entropy defined on**:
- ρ (density operators from Gleason, Track 2.3)
- Gleason from frame functions (Track 2.2)
- Frame functions from 3FLL (Track 2.2)

**Not presupposing**: |⟨x|ψ⟩|² form (that's output of Track 2.7)

**Next**: Apply MaxEnt to derive Born rule

### Phase 2 Status

**Completed**:
- ✅ Track 2.5: Entropy definition

**Remaining**:
- Track 2.6: MaxEnt with constraints
- Track 2.7: Derive Born rule p(x) = |⟨x|ψ⟩|²

**Then**: Phase 3 (Lean formalization + validation)

---

## References

**Von Neumann Entropy**:
- von Neumann, J. (1932). "Mathematical Foundations of Quantum Mechanics."
- Nielsen, M. A., & Chuang, I. L. (2000). "Quantum Computation and Quantum Information." Cambridge University Press.

**Maximum Entropy**:
- Jaynes, E. T. (1957). "Information Theory and Statistical Mechanics." Physical Review, 106(4), 620.
- Jaynes, E. T. (1957). "Information Theory and Statistical Mechanics. II." Physical Review, 108(2), 171.

**Quantum Information Theory**:
- Wilde, M. M. (2013). "Quantum Information Theory." Cambridge University Press.
- Wehrl, A. (1978). "General properties of entropy." Reviews of Modern Physics, 50(2), 221.

---

**Track 2.5 Created**: 2025-11-03
**Status**: ✅ COMPLETE
**Next**: Track 2.6 - MaxEnt application with constraints
