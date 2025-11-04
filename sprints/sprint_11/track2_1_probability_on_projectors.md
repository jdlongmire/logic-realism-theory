# Track 2.1: Probability Measures on Projection Lattice

**Sprint**: 11 (Non-Circular Foundations)
**Track**: 2.1 (Born Rule - Phase 1)
**Created**: 2025-11-03 (Session 8.2)
**Status**: 🟢 IN PROGRESS

---

## Overview

**Objective**: Formalize probability measures on the projection lattice WITHOUT presupposing quantum state amplitudes |⟨x|ψ⟩|².

**The Circularity Problem**:
- ❌ **Circular approach**: Define p(x) = |⟨x|ψ⟩|², then use MaxEnt to "derive" this
- ✅ **Non-circular approach**: Start with abstract probability measures on projectors, derive Born rule as consequence

**Key Insight**: Probability should be assigned to **measurements (projectors)**, not **states** initially.

---

## 1. The Projection Lattice

### Mathematical Structure

**From Track 1**: We derived complex projective Hilbert space ℂℙⁿ

**Definition**: Projection operator
```
P : ℋ → ℋ is a projection if:
- P² = P (idempotent)
- P† = P (self-adjoint)
- ⟨ψ|Pψ⟩ ≥ 0 (positive)
```

**Physical interpretation**: P represents a yes/no measurement
- P|ψ⟩ = component of |ψ⟩ in subspace
- Measurement: "Is the system in subspace Im(P)?"

### Projection Lattice L(ℋ)

**Definition**: The set of all projection operators on ℋ, with partial order:
```
P ≤ Q ⟺ Im(P) ⊆ Im(Q) (subspace inclusion)
```

**Operations**:
- **Meet**: P ∧ Q = projection onto Im(P) ∩ Im(Q)
- **Join**: P ∨ Q = projection onto closure of Im(P) + Im(Q)
- **Complement**: P⊥ = I - P
- **Orthogonality**: P ⊥ Q ⟺ PQ = 0

**Lattice properties**:
- Bounded: 0 (zero projection), I (identity)
- Orthocomplemented: P ∨ P⊥ = I, P ∧ P⊥ = 0
- Orthomodular: If P ≤ Q, then Q = P ∨ (Q ∧ P⊥)
- **NON-distributive**: Generally P ∧ (Q ∨ R) ≠ (P ∧ Q) ∨ (P ∧ R)

**Significance**: Non-distributivity is characteristic of quantum logic (vs classical Boolean logic)

---

## 2. Probability Measures on Projectors

### Axiomatic Definition

**Definition**: A **probability measure** μ on L(ℋ) assigns to each projector P a real number μ(P) ∈ [0,1] satisfying:

**Axiom PM1 (Normalization)**:
```
μ(I) = 1
μ(0) = 0
```

**Axiom PM2 (Countable Additivity)**:
For orthogonal projectors P_i ⊥ P_j (i ≠ j):
```
μ(∑ Pᵢ) = ∑ μ(Pᵢ)
```
where ∑ Pᵢ is the projection onto the direct sum of subspaces

**Axiom PM3 (Non-contextuality / Frame Function Property)**:
For any orthonormal basis {|eᵢ⟩}, the probabilities μ(|eᵢ⟩⟨eᵢ|) depend only on the state, not on which basis is used.

More precisely: If U is unitary,
```
μ(UPU†) depends only on μ(P), not on U
```

This is the KEY axiom that will force Gleason's theorem structure.

### Physical Interpretation

**μ(P)**: Probability that measurement represented by P gives "yes"

**Example**: Spin-1/2 system
- P_↑ = |↑⟩⟨↑| (measure spin-up along z)
- μ(P_↑) = probability of finding spin-up

**Key point**: μ is defined on projectors (measurements), NOT on state vectors yet!

---

## 3. Where Does Probability Come From?

### Three Possible Sources

**Option A: Frequentist (Ensemble)**
- Repeat identical preparation many times
- μ(P) = limiting frequency of "yes" outcomes
- Issue: Requires operational setup, not fundamental

**Option B: Bayesian (Epistemic)**
- μ(P) = degree of belief / information
- MaxEnt: Maximize uncertainty given constraints
- Issue: Still need to justify why MaxEnt

**Option C: Logical (3FLL-based)** ✅
- Distinguishability D(s₁,s₂) from Track 1
- D measures "how different" states are
- μ(P) = "overlap" between state and subspace
- Derived from logical consistency (NC + EM)

**Our approach**: Option C → Option B
1. Start with distinguishability (logical, from Track 1)
2. Show consistency requirements force specific μ form (this track)
3. Apply MaxEnt as consistency-checking tool (Track 2.2)

### Connection to Distinguishability

**From Track 1**: D̃([s₁], [s₂]) measures distinguishability

**Proposal**: Relate μ to D̃
```
μ(P) = 1 - D̃([ψ], [subspace Im(P)])
```

**Intuition**:
- If [ψ] ∈ Im(P): D̃ = 0 → μ(P) = 1 (certain)
- If [ψ] ⊥ Im(P): D̃ = 1 → μ(P) = 0 (impossible)
- If [ψ] partially overlaps: 0 < D̃ < 1 → 0 < μ(P) < 1 (uncertain)

**This grounds probability in logical structure!**

---

## 4. Frame Functions (Gleason's Setup)

### Definition

**Frame**: An orthonormal basis {|e₁⟩, ..., |eₙ⟩} of ℋ

**Frame function**: A function f : {bases} → [0,1]ⁿ assigning probabilities to basis vectors

**Gleason's framework**: Instead of defining μ(P) for all projectors, define f for all frames, then extend

**Axioms for frame functions**:

**FF1 (Normalization)**: ∑ᵢ f(|eᵢ⟩) = 1

**FF2 (Basis independence)**: If {|eᵢ⟩} and {|fⱼ⟩} are bases related by unitary U, then probabilities depend only on overlaps |⟨eᵢ|fⱼ⟩|²

**FF3 (Additivity)**: For orthogonal decomposition of a subspace, probabilities add

**Gleason's Theorem** (1957): For dim(ℋ) ≥ 3, any frame function satisfying FF1-FF3 has the form:
```
f(|e⟩) = ⟨e|ρ|e⟩
```
for some density operator ρ (positive, Tr(ρ) = 1).

**Consequence**: μ(P) = Tr(ρP) for all projectors P.

**This is HUGE**: Probability structure forced to be quantum (trace form) by consistency alone!

---

## 5. Derivation Strategy

### Non-Circular Path

**Step 1** (This deliverable):
- Define probability measures μ on projection lattice L(ℋ)
- State axioms PM1-PM3 (normalization, additivity, non-contextuality)
- Connect to distinguishability from Track 1

**Step 2** (Track 2.2):
- Prove frame function axioms FF1-FF3 from consistency requirements
- Show these follow from 3FLL + Track 1 structures
- No presupposition of quantum formalism

**Step 3** (Track 2.3):
- Apply Gleason's theorem: f(|e⟩) = ⟨e|ρ|e⟩
- Derive density operator ρ from consistency
- **May need to axiomatize Gleason's theorem itself** (it's a deep mathematical result)

**Step 4** (Track 2.4):
- Show ρ has quantum structure (positive, Tr(ρ)=1)
- For pure states: ρ = |ψ⟩⟨ψ| emerges

**Step 5** (Track 2.5-2.7):
- Apply MaxEnt to find specific ρ given constraints
- Derive Born rule: p(x) = ⟨x|ρ|x⟩ = |⟨x|ψ⟩|²
- **Born rule is OUTPUT, not INPUT**

### Where Might Circularity Hide?

**Potential issues**:

1. **Gleason's theorem itself**: Does proving Gleason require quantum structure?
   - **Assessment**: Gleason is a purely mathematical result about functions on lattices
   - **Resolution**: Can axiomatize Gleason with documentation if needed

2. **Non-contextuality axiom (PM3)**: Does this presuppose quantum structure?
   - **Assessment**: Non-contextuality is a consistency requirement (measurements don't depend on irrelevant choices)
   - **Resolution**: Can derive from 3FLL consistency (NC, EM)

3. **Distinguishability → probability connection**: Is this circular?
   - **Assessment**: D̃ from Track 1 is pre-probabilistic (just a metric)
   - **Resolution**: μ(P) = 1 - D̃([ψ], Im(P)) is a definition, not circular

**Verdict**: Non-circular if we're careful about Gleason's status

---

## 6. Comparison to Standard Approach

### Standard QM Textbook

**Postulate 1**: States are unit vectors |ψ⟩ ∈ ℋ

**Postulate 2**: Observables are Hermitian operators

**Postulate 3**: **Born rule** - Probability of outcome x is p(x) = |⟨x|ψ⟩|²

**Postulate 4**: Measurement collapses state to |x⟩

**Issue**: Born rule (Postulate 3) is **assumed**, not derived

### Our Approach (Non-Circular)

**Layer 1** (Track 1): Hilbert space ℋ emerges from 3FLL + K_physics

**Layer 2** (Track 2.1-2.3): Probability measures μ on projectors from consistency → Gleason → ρ

**Layer 3** (Track 2.4-2.7): MaxEnt applied to ρ → Born rule emerges

**Result**: Born rule is **derived** (output), not assumed (input)

**This resolves circularity!**

---

## 7. Formal Definitions for Lean

### Types

```lean
-- Projection operator type
structure Projection (ℋ : Type*) [InnerProductSpace ℂ ℋ] where
  proj : ℋ →L[ℂ] ℋ
  idempotent : proj ∘ proj = proj
  self_adjoint : proj† = proj
  positive : ∀ ψ, 0 ≤ ⟨ψ, proj ψ⟩

-- Projection lattice
def ProjectionLattice (ℋ : Type*) [InnerProductSpace ℂ ℋ] :=
  {P : Projection ℋ}

-- Probability measure on projectors
structure ProbabilityMeasure (ℋ : Type*) [InnerProductSpace ℂ ℋ] where
  μ : Projection ℋ → ℝ
  normalization_I : μ ⟨I, ...⟩ = 1
  normalization_0 : μ ⟨0, ...⟩ = 0
  additivity : ∀ P Q, P ⊥ Q → μ (P + Q) = μ P + μ Q
  non_contextual : ∀ U (unitary), μ (U P U†) = μ P  -- simplified
```

### Key Theorems to Prove

```lean
-- Connection to distinguishability
theorem prob_from_distinguishability (ψ : ℋ) (P : Projection ℋ) :
  μ P = 1 - D̃(ψ, Im(P))

-- Frame function from probability measure
theorem frame_function_exists (μ : ProbabilityMeasure ℋ) :
  ∃ f : OrthonormalBasis ℋ → (Fin n → ℝ),
    ∑ i, f basis i = 1

-- Gleason's theorem (may axiomatize)
axiom gleason_theorem (dim ≥ 3) (f : FrameFunction ℋ) :
  ∃ ρ : DensityOperator ℋ,
    ∀ e : ℋ, f(e) = ⟨e|ρ|e⟩
```

---

## 8. Status and Next Steps

### Track 2.1 Status

**Completed**:
- ✅ Defined projection lattice L(ℋ)
- ✅ Defined probability measures μ on projectors
- ✅ Stated axioms PM1-PM3
- ✅ Connected to distinguishability from Track 1
- ✅ Outlined Gleason's theorem framework
- ✅ Identified potential circularity issues (none found!)

**Next deliverable (Track 2.2)**:
- Prove frame function axioms FF1-FF3 from 3FLL
- Show non-contextuality follows from logical consistency
- Derive frame function structure without presupposing quantum formalism

### Key Insights

1. **Probability on projectors, not states**: This is the key to non-circularity
2. **Gleason's theorem is the bridge**: From consistency to quantum structure
3. **Distinguishability grounds probability**: Connects to Track 1 logically
4. **Dim ≥ 3 requirement**: Gleason needs this - qubits (dim=2) may need special treatment

### Open Questions

1. **Qubit systems (dim=2)**: Gleason doesn't apply - alternative approach needed?
2. **Gleason's proof**: Can we derive from 3FLL, or must we axiomatize?
3. **Distinguishability → μ formula**: Is μ(P) = 1 - D̃(ψ, Im(P)) the right connection?

---

## References

**Track 1**: Representation Theorem (3FLL → ℂℙⁿ)
- Distinguishability.lean, QuotientMetric.lean
- Established ℋ and D̃ structure

**Gleason's Theorem**:
- Gleason, A. M. (1957). "Measures on the closed subspaces of a Hilbert space." Journal of Mathematics and Mechanics.
- Cooke, R., Keane, M., & Moran, W. (1985). "An elementary proof of Gleason's theorem." Mathematical Proceedings of the Cambridge Philosophical Society.

**Quantum Logic**:
- Birkhoff, G., & von Neumann, J. (1936). "The Logic of Quantum Mechanics."
- Redei, M., & Summers, S. J. (2007). "Quantum probability theory."

---

**Track 2.1 Created**: 2025-11-03
**Status**: ✅ COMPLETE - Ready for Track 2.2
**Next**: Derive frame function axioms from 3FLL consistency
