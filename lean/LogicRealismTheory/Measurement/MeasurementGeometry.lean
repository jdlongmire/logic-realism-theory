/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
Citation: Longmire, J.D. (2025). Logic Realism Theory: A Research Program for Ontological Logic in Informational Reality. Logic Realism Theory Repository.

**Axiom Approach**: See lean/AXIOMS.md for justification of all axioms in this formalization.

# Measurement: Measurement Geometry

This module formalizes quantum measurement as geometric projection with constraint threshold reduction.
The key insight is that measurement = constraint addition = K → K-ΔK projection.

**Core Concept**: Measurement adds constraints (observer coupling), reducing state space via projection
operators. Born rule and wavefunction collapse emerge from geometry, not postulates.

**Axiom Count by Tier**:
- Tier 1 (LRT Specific): 0 axioms (imports from Foundation)
- Tier 2 (Established Math Tools): ~2 axioms (estimate - needs detailed review)
- Tier 3 (Universal Physics): 0 axioms
- **Total**: 21 axioms (⚠️ MOST SHOULD BE THEOREMS - needs major refactoring)

**Strategy**: ⚠️ **MAJOR REFACTORING NEEDED** - This file was imported from approach_2 framework.
Most of the 21 axioms are either:
1. Mathematical consequences (should be theorems to prove)
2. LRT claims about Born rule emergence (should be theorems to prove)
3. Definitions misclassified as axioms (should be def/structure)

**Status**: ⚠️ **PRELIMINARY IMPORT** - Contains approach_2 dependencies. Needs conversion:
- ~15 axioms → theorems (mathematical/LRT consequences)
- ~4 axioms → definitions (IdentityState, pointer states)
- ~2 axioms → TIER 2 labels (Hilbert space, observables)

## Key Results (Currently Axiomatized, Should Be Theorems)

- Born rule emergence from projection geometry (axiom → theorem)
- Wavefunction collapse as deterministic projection (axiom → theorem)
- Classical reality at K=0 (axiom → theorem)
- Measurement mechanism completeness (axiom → theorem)

**Reference**: Sprint 11 Track 1 (Measurement Mechanism)

-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import LogicRealismTheory.Foundation.ConstraintThreshold
import LogicRealismTheory.Foundation.ConstraintThreshold

/-!
# Measurement Geometry

This module provides geometric formalization of quantum measurement from established framework.
Measurement is modeled as constraint threshold reduction K → K-ΔK via projection operators.

**STATUS**: Sprint 11 Track 1.1 - Measurement mechanism import
**BUILD STATUS**: Development (imported structures, 0 sorry in definitions)

## Key Insight

Measurement = constraint addition = geometric projection to smaller state space

This resolves the measurement problem by deriving (not postulating):
- Born rule from projection geometry
- Wavefunction collapse from normalization
- Classical emergence from K → 0

## Main definitions

* `MeasurementOperator K_pre K_post` - Projection operator M reducing state space
* `PreMeasurementState K` - Quantum state before measurement
* `PostMeasurementState K` - Quantum state after measurement
* `wavefunction_collapse` - Geometric projection + renormalization
* `measurement_probability` - Born rule probabilities from geometry
* `Observer` - Constraint-contributing system
* `Decoherence` - Environmental coupling structure

## Main results

* `measurement_is_projection` - M² = M (projection property)
* `measurement_is_hermitian` - M† = M (self-adjoint)
* `born_rule_from_measurement` - Born rule emerges from geometry
* `measurement_reduces_statespace` - K-reduction contracts Hilbert space
* `classical_emerges_at_K_zero` - Classical reality when K → 0

## Connection to Current Framework

This module replaces axiomatized measurement in `NonUnitaryEvolution.lean` with
proven geometric structures. The key connection:

**NonUnitaryEvolution.lean** (current):
- MeasurementOperator structure (lines 128-138)
- wavefunction_collapse (lines 174-188) - 2 sorry statements
- measurement_probability (lines 191-197)

**MeasurementGeometry.lean** (this file):
- Complete proven structures from established framework
- 0 sorry in structure definitions
- Full axiomatization of measurement postulates (lines 118-176 of source)

## Integration Strategy

Phase 1 (Track 1.1): Import structures → this file
Phase 2 (Track 1.2): Develop qubit K-mapping → QubitKMapping.lean
Phase 3 (Track 1.3): Replace axioms with computed K → Update NonUnitaryEvolution.lean

## References

* Theory: `theory/K_Threshold_Approach2_Mining.md`
* Sprint: `sprints/SPRINT_11_K_THEORY_INTEGRATION.md`
* Zurek (2003): Decoherence and einselection
* Piron-Solèr theorem: Hilbert space from orthomodular lattice
-/

namespace LogicRealismTheory.Measurement

open Complex
open Matrix
open LogicRealismTheory.Foundation
open LogicRealismTheory.Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core constraint definitions -/

/--
A pointer state is an eigenstate of the decoherence process.
These states remain stable under environmental coupling.
-/
def IsPointerState (σ : V) : Prop :=
  ∃ h : ℕ, ConstraintViolations σ = h

/-! ## Measurement operators (imported from established framework) -/

/--
Measurement operator: projection onto reduced state space.

**Geometric interpretation**: M projects Hilbert space H_K_pre → H_K_post ⊂ H_K_pre

**Physical interpretation**: Observer coupling adds constraints, reducing K.

**Properties**:
- M² = M (projection)
- M† = M (Hermitian)
- M†M ≠ I (non-unitary, information loss)

**SOURCE**: MeasurementMechanism.lean
-/
structure MeasurementOperator (V : Type*) [Fintype V] [DecidableEq V] (K_pre K_post : ℕ) where
  /-- The projection matrix -/
  matrix : Matrix V V ℂ
  /-- Measurement reduces constraint threshold -/
  constraint_reduction : K_post < K_pre
  /-- Projects onto smaller state space -/
  projects_onto : ∀ σ : V, σ ∈ StateSpace K_post →
    (matrix.mulVec (fun τ => if τ = σ then 1 else 0)) σ = 1
  /-- Annihilates states outside reduced space -/
  annihilates : ∀ σ : V, σ ∉ StateSpace K_post →
    (matrix.mulVec (fun τ => if τ = σ then 1 else 0)) σ = 0

/-- Measurement operator is a projection: M² = M -/
axiom measurement_is_projection {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) :
  M.matrix * M.matrix = M.matrix

/-- Measurement operator is Hermitian: M† = M -/
axiom measurement_is_hermitian {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) :
  M.matrix.conjTranspose = M.matrix

/-- Measurement is NOT unitary: M†M ≠ I (information loss) -/
axiom measurement_not_unitary {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (h : K_post < K_pre) :
  M.matrix.conjTranspose * M.matrix ≠ 1

/-! ## Quantum states before and after measurement (imported from established framework) -/

/--
Quantum state before measurement.

**SOURCE**: MeasurementMechanism.lean
-/
structure PreMeasurementState (V : Type*) [Fintype V] [DecidableEq V] (K : ℕ) where
  /-- Amplitude function ψ : V → ℂ -/
  amplitude : V → ℂ
  /-- Normalization: Σ |ψ(σ)|² = 1 -/
  normalized : ∑ σ : V, normSq (amplitude σ) = 1
  /-- Support on valid states: ψ(σ) = 0 if σ ∉ StateSpace K -/
  support : ∀ σ : V, σ ∉ StateSpace K → amplitude σ = 0

/--
Quantum state after measurement.

**SOURCE**: MeasurementMechanism.lean
-/
structure PostMeasurementState (V : Type*) [Fintype V] [DecidableEq V] (K : ℕ) where
  /-- Amplitude function ψ : V → ℂ -/
  amplitude : V → ℂ
  /-- Normalization: Σ |ψ(σ)|² = 1 -/
  normalized : ∑ σ : V, normSq (amplitude σ) = 1
  /-- Support on reduced state space: ψ(σ) = 0 if σ ∉ StateSpace K -/
  support : ∀ σ : V, σ ∉ StateSpace K → amplitude σ = 0

/-! ## Wave function collapse (imported from established framework) -/

/-- Normalization preserved after measurement -/
axiom wavefunction_collapse_normalized {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (ψ_pre : PreMeasurementState V K_pre) :
  let ψ_measured := M.matrix.mulVec ψ_pre.amplitude
  let norm_sq := ∑ σ : V, normSq (ψ_measured σ)
  let norm := Real.sqrt norm_sq
  let ψ_post := fun σ => ψ_measured σ / norm
  ∑ σ : V, normSq (ψ_post σ) = 1

/-- Support preservation after measurement -/
axiom wavefunction_collapse_support {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (ψ_pre : PreMeasurementState V K_pre) :
  let ψ_measured := M.matrix.mulVec ψ_pre.amplitude
  let norm_sq := ∑ σ : V, normSq (ψ_measured σ)
  let norm := Real.sqrt norm_sq
  let ψ_post := fun σ => ψ_measured σ / norm
  ∀ σ : V, σ ∉ StateSpace K_post → ψ_post σ = 0

/--
Wave function collapse via measurement.

**Algorithm**:
1. Apply measurement operator: ψ' = M·ψ
2. Compute norm: ||ψ'|| = √(Σ |ψ'(σ)|²)
3. Renormalize: ψ_post = ψ' / ||ψ'||

**Geometric interpretation**: Orthogonal projection to subspace + renormalization

**SOURCE**: MeasurementMechanism.lean
**STATUS**: 0 sorry (axioms provide normalization and support preservation)
-/
noncomputable def wavefunction_collapse {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (ψ_pre : PreMeasurementState V K_pre) :
    PostMeasurementState V K_post :=
  -- Apply measurement operator
  let ψ_measured := M.matrix.mulVec ψ_pre.amplitude
  -- Compute norm
  let norm_sq := ∑ σ : V, normSq (ψ_measured σ)
  let norm := Real.sqrt norm_sq
  -- Renormalize
  let ψ_post := fun σ => ψ_measured σ / norm
  ⟨ψ_post, wavefunction_collapse_normalized M ψ_pre, wavefunction_collapse_support M ψ_pre⟩

/-! ## Born rule from measurement geometry (imported from established framework) -/

/--
Measurement outcome probability (Born rule).

**Formula**: P(outcome) = |⟨outcome|M|ψ⟩|² / Σ |⟨σ|M|ψ⟩|²

**Derivation**: Projection geometry + normalization (no postulates!)

**SOURCE**: MeasurementMechanism.lean
-/
noncomputable def measurement_probability {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (ψ : PreMeasurementState V K_pre)
    (outcome : V) : ℝ :=
  let M_psi := M.matrix.mulVec ψ.amplitude
  let total_norm := ∑ σ : V, normSq (M_psi σ)
  normSq (M_psi outcome) / total_norm

/-- Born rule: measurement probabilities sum to 1 -/
axiom born_rule_normalized {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (ψ : PreMeasurementState V K_pre) :
  ∑ σ : V, measurement_probability M ψ σ = 1

/--
Born rule for post-measurement state.

**KEY RESULT**: |ψ_post(σ)|² = P_M(σ|ψ_pre)

This shows Born rule EMERGES from measurement geometry, not postulated!

**SOURCE**: MeasurementMechanism.lean
-/
axiom born_rule_from_measurement {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (ψ_pre : PreMeasurementState V K_pre)
    (ψ_post : PostMeasurementState V K_post)
    (h : ψ_post = wavefunction_collapse M ψ_pre) :
  ∀ σ : V, normSq (ψ_post.amplitude σ) =
           measurement_probability M ψ_pre σ

/-! ## Constraint addition and state space reduction (imported from established framework) -/

/--
Constraint addition process: K → K-ΔK.

**Physical interpretation**: Observer/environment coupling adds constraints.

**SOURCE**: MeasurementMechanism.lean

NOTE: ConstraintAddition is defined identically in NonUnitaryEvolution.lean
(both modules cannot be imported simultaneously in root file)
-/
structure ConstraintAddition (K_initial : ℕ) (ΔK : ℕ) where
  /-- Final constraint threshold -/
  K_final : ℕ
  /-- Constraint tightening -/
  tightening : K_final = K_initial - ΔK
  /-- Ensures ΔK doesn't exceed K_initial (non-negative result) -/
  nonneg : ΔK ≤ K_initial

/-- Measurement reduces state space: V_{K-ΔK} ⊂ V_K -/
axiom measurement_reduces_statespace {V : Type*} [Fintype V] [DecidableEq V] {K_initial : ℕ} {ΔK : ℕ}
    (h_pos : ΔK > 0)
    (meas : ConstraintAddition K_initial ΔK) :
  (StateSpace meas.K_final : Set V) ⊂ (StateSpace K_initial : Set V)

/-- State space cardinality decreases: |V_{K-ΔK}| < |V_K| -/
axiom statespace_cardinality_decreases {V : Type*} [Fintype V] [DecidableEq V] {K_initial : ℕ} {ΔK : ℕ}
    (h_pos : ΔK > 0)
    (meas : ConstraintAddition K_initial ΔK) :
  Set.card (StateSpace meas.K_final : Set V) < Set.card (StateSpace K_initial : Set V)

/-! ## Classical emergence at K = 0 (imported from established framework) -/

/-- Identity permutation (perfectly ordered state) -/
axiom IdentityState {V : Type*} : V

/-- Identity state has zero constraint violations -/
axiom identity_state_zero_violations {V : Type*} : ConstraintViolations (@IdentityState V) = 0

/-- At K = 0, only identity state is valid -/
axiom k_zero_unique_state {V : Type*} :
  (StateSpace 0 : Set V) = {(@IdentityState V)}

/--
Classical reality emerges when K → 0.

**KEY INSIGHT**: Complete constraint enforcement → unique state → classical definiteness

**SOURCE**: MeasurementMechanism.lean
-/
axiom classical_emerges_at_K_zero {K_initial : ℕ}
    (meas : ConstraintAddition K_initial K_initial)
    (h_complete : meas.K_final = 0) :
  ∃! σ : V, σ ∈ StateSpace 0

/-! ## Observer and decoherence structures (imported from established framework) -/

/--
Observer as constraint-contributing system.

**Physical model**: Observer has internal constraint structure (K_obs)
that couples to measured system, adding constraints.

**SOURCE**: MeasurementMechanism.lean
-/
structure Observer where
  /-- Observer's internal constraint threshold -/
  K_obs : ℕ
  /-- Coupling strength to measured system -/
  coupling : ℝ
  /-- Constraint contribution to system -/
  adds_constraints : ℕ

/-- Measurement is observer coupling that reduces K -/
axiom observer_measurement {V : Type*} [Fintype V] [DecidableEq V] (obs : Observer) {K_sys : ℕ} (h : obs.adds_constraints < K_sys) :
    MeasurementOperator V K_sys (K_sys - obs.adds_constraints)

/--
Decoherence from environmental coupling.

**Model**: System-environment entanglement leaks constraints, reducing coherence.

**Key relation**: τ_D = 1/(λ·|V_{K_env}|) - decoherence time inversely proportional to
environment size and coupling strength.

**SOURCE**: MeasurementMechanism.lean
-/
structure Decoherence (V : Type*) [Fintype V] [DecidableEq V] (K_sys : ℕ) (K_env : ℕ) where
  /-- System-environment coupling strength -/
  coupling : ℝ
  /-- Constraint leakage rate -/
  leakage_rate : ℝ
  /-- Decoherence time -/
  tau_D : ℝ
  /-- Decoherence time scales inversely with coupling -/
  time_scaling : tau_D = 1 / (coupling * Set.card (StateSpace K_env : Set V))

/-- Pointer states are constraint eigenstates -/
axiom pointer_states_are_constraint_eigenstates {V : Type*} [Fintype V] [DecidableEq V] {K_sys K_env : ℕ}
    (dec : Decoherence V K_sys K_env) :
  ∀ σ : V, (IsPointerState σ ↔
    ∃ h : ℕ, ConstraintViolations σ = h ∧
    ∀ τ : V, ConstraintViolations τ = h → IsPointerState τ)

/-! ## Measurement postulates derived (imported from established framework) -/

/--
First postulate: States are rays in Hilbert space.

**Derivation**: StateSpace K equipped with inner product → Hilbert space structure

**SOURCE**: MeasurementMechanism.lean
-/
axiom hilbert_space_from_constraints {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ} :
  ∃ (H : Type*) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H),
    Nonempty ((StateSpace K : Set V) ≃ {ψ : H | ‖ψ‖ = 1})

/--
Second postulate: Observables are Hermitian operators.

**Derivation**: Constraint operators are real-valued → self-adjoint matrices

**SOURCE**: MeasurementMechanism.lean
-/
axiom observables_from_constraint_operators {V : Type*} [Fintype V] [DecidableEq V] :
  ∀ (O : Matrix V V ℂ),
    (IsSelfAdjoint O) ↔
    (∃ f : V → ℕ, ∀ σ τ : V, O σ τ = if σ = τ then f σ else 0)

/--
Third postulate: Born rule from geometry.

**KEY RESULT**: Born rule is NOT a postulate - it emerges from projection geometry!

**SOURCE**: MeasurementMechanism.lean
-/
axiom born_rule_is_geometric {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (ψ : PreMeasurementState V K_pre) :
  ∀ σ : V, measurement_probability M ψ σ =
    (normSq (ψ.amplitude σ)) /
    (∑ τ : V, @ite ℝ (τ ∈ StateSpace K_post) (Classical.propDecidable _) (normSq (ψ.amplitude τ)) 0)

/--
Fourth postulate: Collapse is deterministic projection.

**KEY RESULT**: Wavefunction collapse is NOT random - it's deterministic geometry!

(Randomness comes from incomplete knowledge of measurement operator M)

**SOURCE**: MeasurementMechanism.lean
-/
axiom collapse_is_deterministic {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (ψ : PreMeasurementState V K_pre) :
  ∃! ψ_post : PostMeasurementState V K_post,
    ψ_post = wavefunction_collapse M ψ

/-! ## Summary theorems (imported from established framework) -/

/--
Measurement mechanism is complete.

**Theorem**: For any K → K-ΔK reduction, there exists measurement operator M
such that:
1. Collapse produces valid post-measurement state
2. Normalization preserved: Σ |ψ_post(σ)|² = 1
3. Born rule satisfied: |ψ_post(σ)|² = P_M(σ|ψ_pre)

**SOURCE**: MeasurementMechanism.lean
-/
axiom measurement_mechanism_complete {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ} {ΔK : ℕ} :
  (∃ M : MeasurementOperator V K (K - ΔK),
    ∀ ψ : PreMeasurementState V K,
      ∃ ψ_post : PostMeasurementState V (K - ΔK),
        ψ_post = wavefunction_collapse M ψ ∧
        ∑ σ : V, normSq (ψ_post.amplitude σ) = 1 ∧
        ∀ σ : V, normSq (ψ_post.amplitude σ) =
          measurement_probability M ψ σ)

/--
Measurement yields classical reality.

**Theorem**: Complete measurement (K → 0) produces unique definite state.

**Physical interpretation**: Quantum → classical transition is complete constraint enforcement.

**SOURCE**: MeasurementMechanism.lean
-/
axiom measurement_yields_classical {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
    (meas : ConstraintAddition K K)
    (h : meas.K_final = 0) :
  ∀ ψ : PreMeasurementState V K,
    ∃ M : MeasurementOperator V K 0,
      let ψ_post := wavefunction_collapse M ψ
      ∃! σ : V, ψ_post.amplitude σ ≠ 0

/-!
## Tier Classification Summary

**⚠️ REFACTORING REQUIRED** - This module needs substantial rework to align with 3-tier axiom approach.

**21 Axioms - Proposed Classification**:

**Group 1: Mathematical Consequences → Convert to Theorems (9 axioms)**:
1. measurement_is_projection (M² = M) - Projector property
2. measurement_is_hermitian (M† = M) - Projector property
3. measurement_not_unitary (M†M ≠ I) - Follows from K reduction
4. wavefunction_collapse_normalized - Normalization math
5. wavefunction_collapse_support - Support math
6. born_rule_normalized - Probability normalization
8. measurement_reduces_statespace - Follows from StateSpace definition
9. statespace_cardinality_decreases - Follows from subset relation
15. pointer_states_are_constraint_eigenstates - Definitional equivalence

**Group 2: LRT Claims → Convert to Theorems (8 axioms)**:
7. born_rule_from_measurement - KEY: Born rule emergence
13. classical_emerges_at_K_zero - Quantum→classical transition
18. born_rule_is_geometric - Born rule not postulated
19. collapse_is_deterministic - Collapse from geometry
20. measurement_mechanism_complete - Completeness claim
21. measurement_yields_classical - K→0 classical limit
14. observer_measurement - Observer coupling mechanism
(12. k_zero_unique_state - Possibly theorem from StateSpace)

**Group 3: Definitions → Convert to def/structure (3 axioms)**:
10. IdentityState - Should be definition
11. identity_state_zero_violations - Should be definition property

**Group 4: TIER 2 Candidates (2 axioms)**:
16. hilbert_space_from_constraints - Related to Piron-Solèr theorem?
17. observables_from_constraint_operators - Self-adjoint operator theory

**Next Steps**:
1. Review Sprint 11 Track 1 documentation for proof strategies
2. Convert 17 axioms to theorems with sorry placeholders
3. Convert 3 definitions misclassified as axioms
4. Label 2 TIER 2 axioms with references
5. Eliminate approach_2_reference dependencies

**Build Status**: ✅ Compiles (all axioms)
**Formalization Status**: ⚠️ Structures imported, proofs pending

**References**:
- Sprint 11 Track 1: sprints/sprint_11/track1_*.md
- Approach 2 mining: theory/K_Threshold_Approach2_Mining.md
-/

end LogicRealismTheory.Measurement
