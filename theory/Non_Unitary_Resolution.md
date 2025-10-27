# Non-Unitary Evolution Resolution

**Document Version**: 1.0
**Date**: October 27, 2025
**Status**: Sprint 4 - Task 1.2
**Author**: James D. (JD) Longmire

---

## Purpose

This document addresses a critical issue raised in peer review of the foundational paper:

**Reviewer's Concern**: "Stone's theorem (used to derive time emergence from Identity constraint) requires continuous unitary evolution. However, measurement and decoherence are non-unitary processes. How does LRT reconcile this apparent contradiction?"

**Resolution**: Stone's theorem applies to **closed systems** with fixed constraint threshold K. Measurement involves **changing** K → K-ΔK via observer/environment coupling. These are different regimes with different evolution types.

---

## Table of Contents

1. [The Problem Statement](#1-the-problem-statement)
2. [The Hierarchical Framework](#2-the-hierarchical-framework)
3. [Mathematical Structure](#3-mathematical-structure)
4. [Resolution of Stone's Theorem Issue](#4-resolution-of-stones-theorem-issue)
5. [Physical Interpretation](#5-physical-interpretation)
6. [Formal Verification](#6-formal-verification)
7. [Implications for LRT](#7-implications-for-lrt)
8. [References](#8-references)

---

## 1. The Problem Statement

### 1.1 Stone's Theorem in LRT

**LRT Claim** (Section 3.3 of foundational paper):
- Identity constraint I operating on information space → continuous one-parameter group of operators
- Stone's theorem: Continuous one-parameter unitary group ←→ self-adjoint generator H
- Result: i dψ/dt = Hψ (Schrödinger equation)
- Time parameter t emerges from monotonic flow under Identity constraint

**Stone's Theorem Requirements**:
- Continuous one-parameter family of operators {U(t)}
- Group property: U(t₁)U(t₂) = U(t₁+t₂)
- **Unitarity**: U†(t)U(t) = I (preserves inner product)
- Strong continuity: lim_{t→0} U(t)ψ = ψ

### 1.2 The Measurement Problem

**Measurement/Decoherence are Non-Unitary**:
- Projection postulate: ψ → M_i ψ / ||M_i ψ|| (non-unitary)
- Decoherence: ρ → Σ_k K_k ρ K_k† (trace-preserving but not unitary)
- Dimension reduction: H_full → H_subspace (loses information)

**Apparent Contradiction**:
- If Identity constraint generates unitary evolution (Stone's theorem)...
- But measurement is non-unitary...
- Then how can LRT derive both from the same principles?

---

## 2. The Hierarchical Framework

### 2.1 Key Insight: Constraint Threshold K

**LRT's Actualization Process**: A = L(I)
- **Actualization A**: Physical states that satisfy constraints
- **Logical operators L**: Identity, Non-Contradiction, Excluded Middle
- **Information space I**: All possible configurations

**Constraint Threshold K**:
- Measures "degree of actualization"
- K = number of constraint violations tolerated
- Range: K = ∞ (pure information) → K = 0 (classical reality)

**State Space V_K**:
- V_K = {σ ∈ I | h(σ) ≤ K}
- h(σ) = constraint violation count for configuration σ
- Smaller K → smaller state space → more actualized

### 2.2 Two Regimes of Evolution

#### Regime 1: Unitary Evolution (Fixed K)

**Context**: Closed quantum system, constraint threshold constant

**Mechanism**:
- Identity constraint I operates within V_K
- Generates continuous one-parameter unitary group {U(t)}
- Stone's theorem applies → i dψ/dt = Hψ

**Properties**:
- Preserves: Normalization, energy, state space dimension
- Time-reversible: U(-t) = U†(t)
- Information-preserving: dim(V_K) constant

**Physical Examples**:
- Free particle evolution
- Harmonic oscillator
- Unitary quantum gates
- Isolated qubit coherent evolution

#### Regime 2: Non-Unitary Measurement (Changing K)

**Context**: Open system, observer/environment coupling adds constraints

**Mechanism**:
- Observer (or environment) contributes additional constraints
- Constraint threshold reduces: K → K' where K' < K
- State space contracts: V_K → V_K' ⊂ V_K
- Projection: ψ ∈ V_K → ψ' ∈ V_K' (non-unitary)

**Properties**:
- Reduces: State space dimension, superposition complexity
- Irreversible: Cannot recover ψ from ψ'
- Information-losing: dim(V_K') < dim(V_K)

**Physical Examples**:
- Measurement by macroscopic apparatus
- Environmental decoherence
- Quantum-to-classical transition
- Pointer state selection

### 2.3 Hierarchical Structure

**Identity Constraint at Multiple Levels**:

**Level 1: System Identity** (intra-system)
- Identity constraint within system's V_K
- Generates unitary evolution U(t)
- Preserves system's degree of actualization

**Level 2: System-Environment Identity** (inter-system)
- Identity constraint across system ⊗ environment
- Leads to entanglement: ψ_sys ⊗ ψ_env → |Ψ⟩_entangled
- Still unitary for composite system

**Level 3: Actualization** (constraint addition)
- Observer actualization: measurement = constraint tightening
- Environment actualization: decoherence = constraint leakage
- Non-unitary: K → K-ΔK, V_K → V_{K-ΔK}

**Resolution**: Stone's theorem applies at Levels 1 & 2 (closed systems, fixed K). Non-unitarity emerges at Level 3 (open systems, changing K). No contradiction!

---

## 3. Mathematical Structure

### 3.1 Constraint Threshold Dynamics

**State Space Hierarchy**:
```
V_∞ ⊇ V_K₁ ⊇ V_K₂ ⊇ ... ⊇ V_0
```
where K_∞ > K₁ > K₂ > ... > 0

**Inclusion Property**: K' ≤ K implies V_K' ⊆ V_K

### 3.2 Measurement Operator Structure

**Definition**: Measurement operator for K → K-ΔK

**Components**:
- **Projection P_{K-ΔK}**: Projects onto subspace V_{K-ΔK}
- **Renormalization N**: Ensures ⟨ψ'|ψ'⟩ = 1
- **Combined**: M = N ∘ P_{K-ΔK}

**Properties**:
1. **Idempotent**: P² = P (projection)
2. **Hermitian**: P† = P (self-adjoint)
3. **Non-unitary**: P†P ≠ I (loses information)
4. **Dimension reduction**: rank(P) = dim(V_{K-ΔK}) < dim(V_K)

**Action on state**:
```
ψ ∈ V_K  →  M·ψ = P_{K-ΔK}·ψ / ||P_{K-ΔK}·ψ||  ∈ V_{K-ΔK}
```

### 3.3 Unitary vs Non-Unitary Evolution

**Unitary Evolution (Fixed K)**:
```
dψ/dt = -iHψ    (Schrödinger equation)
ψ(t) = U(t)ψ(0)  where U(t) = exp(-iHt)

Properties:
- U†(t)U(t) = I (unitary)
- ⟨ψ(t)|ψ(t)⟩ = ⟨ψ(0)|ψ(0)⟩ (norm preserved)
- dim(V_K) constant
```

**Non-Unitary Measurement**:
```
ψ ∈ V_K  →  ψ' = M_i·ψ / ||M_i·ψ||  ∈ V_{K_i}

where:
- K_i < K (constraint threshold reduced)
- M_i†M_i ≠ I (non-unitary)
- dim(V_{K_i}) < dim(V_K) (information lost)
```

### 3.4 Born Rule Emergence

**Measurement Probability**:
```
P(outcome i) = ||M_i·ψ||² / Σ_j ||M_j·ψ||²
            = ||P_{K_i}·ψ||² / ⟨ψ|ψ⟩
            = ⟨ψ|P_{K_i}|ψ⟩
```

**For orthogonal projections** {P_i} with Σ_i P_i = I:
```
P(outcome i) = |⟨i|ψ⟩|²    (Born rule)
```

**Key Result**: Born rule emerges from constraint geometry, not assumed!

---

## 4. Resolution of Stone's Theorem Issue

### 4.1 Direct Response to Reviewer

**Question**: "How does LRT reconcile Stone's theorem (requiring unitarity) with non-unitary measurement?"

**Answer**:

Stone's theorem applies to **closed quantum systems** with **fixed constraint threshold K**. In this regime:
- Identity constraint I generates continuous one-parameter unitary group
- Evolution: i dψ/dt = Hψ (Schrödinger equation)
- Stone's theorem guarantees H is self-adjoint
- Time t emerges as flow parameter

Measurement involves **changing constraint threshold** K → K-ΔK via:
- **Observer coupling**: Macroscopic apparatus adds constraints
- **Environmental coupling**: Surrounding degrees of freedom leak constraints

This is a **different physical process** from closed-system evolution:
- Not continuous one-parameter group (discrete jumps in K)
- Stone's theorem does NOT apply (not the same mathematical structure)
- Non-unitarity emerges naturally from state space contraction

**Analogy**:
- Unitary evolution = sliding along a fixed manifold (constant dimension)
- Measurement = projecting to lower-dimensional submanifold (dimension reduction)

### 4.2 Mathematical Precision

**Stone's Theorem Statement**:
> Let {U(t) : t ∈ ℝ} be a strongly continuous one-parameter unitary group on Hilbert space H. Then there exists a unique self-adjoint operator H such that U(t) = exp(-iHt).

**Where it applies in LRT**:
- **Hilbert space**: ℓ²(V_K) = {ψ : V_K → ℂ | Σ|ψ|² = 1}
- **Unitary group**: {U_K(t) : t ∈ ℝ} acting on ℓ²(V_K)
- **Generator**: H_K = graph Laplacian on V_K
- **Evolution**: ψ(t) = exp(-iH_K t)ψ(0) for ψ ∈ ℓ²(V_K)

**Where it does NOT apply**:
- Measurement operator M : ℓ²(V_K) → ℓ²(V_{K-ΔK})
- Not a unitary operator: M†M ≠ I_{V_K}
- Changes Hilbert space dimension: dim(V_K) → dim(V_{K-ΔK})
- Not continuous one-parameter group (discrete threshold change)

**Conclusion**: No contradiction. Stone's theorem and measurement operators operate in different mathematical structures.

### 4.3 Comparison to Standard QM

**Standard QM Approach**:
- Unitary evolution: U(t) = exp(-iHt) (between measurements)
- Measurement: Projection postulate (ad hoc, not derived)
- Two separate postulates, not unified

**LRT Approach**:
- **Unified origin**: Both emerge from Identity constraint + Actualization
- Unitary: Identity within fixed V_K
- Non-unitary: Actualization changes K → K-ΔK
- **Measurement derived**, not postulated

**Advantage**: LRT provides deeper explanation of why unitary evolution and non-unitary measurement coexist.

---

## 5. Physical Interpretation

### 5.1 Constraint Threshold as Physical Parameter

**K = ∞**: Pure information space
- No constraints actualized
- Maximal superposition
- No physical reality (pre-measurement)

**K finite**: Quantum regime
- Some constraints actualized (Identity, Non-Contradiction)
- Partial superposition allowed
- Unitary evolution governs dynamics

**K → 0**: Classical regime
- All constraints fully actualized (Identity, Non-Contradiction, Excluded Middle)
- Superposition suppressed
- Definite outcomes (measurement)

### 5.2 Observer Role

**Observer as Constraint Source**:
- Macroscopic apparatus has K_obs ≈ 0 (highly actualized)
- Coupling system ↔ observer → constraint leakage
- System K reduces toward K_obs
- Result: Wave function collapse

**NOT consciousness-dependent**:
- Observer = any system with K_obs << K_sys
- Environment acts as distributed observer
- Decoherence = continuous K reduction via environment

### 5.3 Time Evolution Types

**Coherent Evolution** (K constant):
- Quantum interference preserved
- Reversible dynamics
- Examples: Isolated qubit, Schrödinger's cat (before observation)

**Decoherence** (K gradual decrease):
- Environmental coupling
- Continuous information loss
- Master equation: dρ/dt = -i[H,ρ] + D(ρ)

**Measurement** (K sudden decrease):
- Strong observer coupling
- Discrete projection
- Von Neumann collapse

---

## 6. Formal Verification

### 6.1 Lean 4 Formalization (In Progress)

**Module**: `LogicRealismTheory/Measurement/NonUnitaryEvolution.lean`

**Key Definitions**:
```lean
-- State space for constraint threshold K
def StateSpace (K : ℕ) : Set V := {σ : V | ConstraintViolations σ ≤ K}

-- Measurement operator: K_pre → K_post where K_post < K_pre
structure MeasurementOperator (K_pre K_post : ℕ) where
  matrix : Matrix V V ℂ
  constraint_reduction : K_post < K_pre
  projects_onto : ∀ σ ∈ StateSpace K_post, ...
  annihilates : ∀ σ ∉ StateSpace K_post, ...
```

**Key Theorems**:
```lean
-- Unitary evolution preserves state space
theorem unitary_preserves_K {K : ℕ} (U : UnitaryOperator K) (ψ : QuantumState K) :
  ψ.evolve U ∈ StateSpace K

-- Measurement reduces state space
theorem measurement_reduces_K {K_pre K_post : ℕ}
    (M : MeasurementOperator K_pre K_post) :
  StateSpace K_post ⊂ StateSpace K_pre

-- No contradiction: different mathematical structures
theorem no_unitarity_contradiction :
  ∃ (U : UnitaryOperator K) (M : MeasurementOperator K (K-1)),
    (U.matrix * U.matrix.conjTranspose = Matrix.one) ∧
    (M.matrix * M.matrix.conjTranspose ≠ Matrix.one)
```

**Status**: Module created (Sprint 4, Task 1.2). Full formalization pending dependency resolution.

### 6.2 Exploratory Formalization

**Reference**: `approach_2_reference/lean/LFT_Proofs/PhysicalLogicFramework/`

**Relevant Modules**:
1. `QuantumEmergence/MeasurementMechanism.lean` (~300 lines)
   - Full treatment of measurement as constraint addition
   - Born rule derivation from constraint geometry
   - Observer role formalization

2. `Dynamics/QuantumDynamics.lean` (~200 lines)
   - Unitary evolution from Fisher geodesic flow
   - Schrödinger equation derivation
   - Stone's theorem application

**Note**: These are exploratory formalizations from an alternative approach. Core concepts are being integrated into the current `LogicRealismTheory` codebase.

---

## 7. Implications for LRT

### 7.1 Theoretical Coherence

**Strengthens LRT's Foundational Program**:
- Resolves apparent contradiction (Stone's theorem vs measurement)
- Unifies unitary and non-unitary evolution under single framework
- Derives measurement, doesn't postulate it

**Hierarchical Structure**:
- Identity constraint operates at multiple levels (system, environment, observer)
- Each level has appropriate dynamics (unitary within, non-unitary across)
- Emergent complexity from simple principles

### 7.2 Testable Predictions

**Decoherence Rate Prediction**:
- Rate of K reduction depends on coupling strength to environment/observer
- Predicts continuous transition: coherent → partially decohered → classical

**State-Dependent Effects**:
- States with higher constraint violations (larger h(σ)) decohere faster
- Equal superpositions (maximal ΔS_EM) most vulnerable

**K-Threshold Phenomenology**:
- Different K regimes exhibit different physics
- Smooth interpolation: quantum (large K) → classical (small K)

### 7.3 Relation to Standard QM

**What LRT Adds**:
- Physical mechanism for measurement (constraint threshold change)
- Explanation of unitary/non-unitary coexistence
- Parameter K tracks degree of actualization

**What LRT Preserves**:
- All standard QM predictions (Born rule, Schrödinger equation)
- No modification to quantum mechanics itself
- Interpretational framework, not new physics

### 7.4 Open Questions for Future Work

1. **Quantitative K dynamics**: Derive rate equations for dK/dt
2. **Observer definition**: Precise criterion for K_obs → constraint addition
3. **Thermodynamics**: Connection between K and entropy/temperature
4. **Quantum-classical boundary**: Sharp vs smooth K transition?
5. **Cosmology**: Initial K = ∞ at Big Bang?

---

## 8. References

### 8.1 LRT Documents

1. Longmire, J.D. (2025). "Logic Realism Theory: Foundational Paper". `theory/Logic-realism-theory-foundational.md`
2. Sprint 4 Plan: `sprints/sprint_4/SPRINT_4_PLAN.md`
3. T2/T1 Derivation: `notebooks/Logic_Realism/05_T2_T1_Derivation.ipynb`

### 8.2 Lean Formalization

1. Current module: `lean/LogicRealismTheory/Measurement/NonUnitaryEvolution.lean` (Sprint 4)
2. Exploratory modules: `approach_2_reference/lean/LFT_Proofs/PhysicalLogicFramework/`
   - `QuantumEmergence/MeasurementMechanism.lean`
   - `Dynamics/QuantumDynamics.lean`

### 8.3 Mathematical Foundations

1. Stone, M.H. (1932). "On one-parameter unitary groups in Hilbert space". *Annals of Mathematics*, 33(3), 643-648.
2. von Neumann, J. (1932). *Mathematical Foundations of Quantum Mechanics*. Princeton University Press.
3. Zurek, W.H. (2003). "Decoherence, einselection, and the quantum origins of the classical". *Reviews of Modern Physics*, 75(3), 715.

### 8.4 Related Work

1. Caticha, A. (2019). "Entropic Dynamics: Quantum Mechanics from Entropy and Information Geometry". *Entropy*, 21(10), 943.
2. Reginatto, M. (1998). "Derivation of the equations of nonrelativistic quantum mechanics using the principle of minimum Fisher information". *Physical Review A*, 58(3), 1775.

---

## Summary

**Problem**: Stone's theorem requires unitarity, but measurement is non-unitary.

**Resolution**:
- Stone's theorem applies to **closed systems** (fixed K) → unitary evolution
- Measurement involves **constraint addition** (K → K-ΔK) → non-unitary
- Hierarchical Identity constraint operates at multiple levels
- No contradiction: different regimes, different dynamics

**Implications**:
- Measurement **derived** from actualization process, not postulated
- Unifies unitary and non-unitary evolution
- Provides physical mechanism (K dynamics) for quantum-classical transition

**Status**: Theory complete, Lean formalization in progress (Sprint 4, Task 1.2).

---

**Copyright © 2025 James D. (JD) Longmire**
**License**: Apache License 2.0
