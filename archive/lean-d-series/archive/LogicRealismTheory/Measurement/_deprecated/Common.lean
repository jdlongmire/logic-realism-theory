/-
Copyright (c) 2025 James D. (JD) Longmire. All rights reserved.
Released under Apache 2.0 license.
Authors: James D. (JD) Longmire

**Axiom Approach**: See lean/AXIOMS.md for justification of all axioms in this formalization.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Measurement Common Definitions

This module contains shared measurement structures and axioms used by both
MeasurementGeometry.lean and NonUnitaryEvolution.lean.

**PURPOSE**: Avoid code duplication and enable simultaneous import of both modules.

## Main definitions

* `StateSpace K` - Valid configurations with at most K constraint violations
* `MeasurementOperator K_pre K_post` - Projection operator reducing K_pre → K_post
* `ConstraintAddition` - Constraint threshold reduction structure K → K-ΔK
* `wavefunction_collapse` - Measurement-induced state collapse
* `measurement_probability` - Born rule probability

## Main axioms

* `measurement_is_projection` - M is a projection operator
* `measurement_is_hermitian` - M is Hermitian
* `measurement_not_unitary` - M is not unitary (when K reduces)
* `wavefunction_collapse_normalized` - Collapsed state is normalized
* `wavefunction_collapse_support` - Collapsed state support in StateSpace K_post

**REFACTORED**: Session 11.2 - extracted from duplicated definitions
-/

namespace LogicRealismTheory.Measurement

open Complex Matrix

-- ═══════════════════════════════════════════════════════════════════════════
-- FUNDAMENTAL AXIOMS AND DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════════

-- Axiomatize Set cardinality (not available in current Mathlib)
axiom Set.card {α : Type*} : Set α → ℕ

/--
Number of constraint violations for a configuration.

**AXIOMATIZED**: This is a foundational structure in LRT measurement theory.
The specific constraints depend on the physical system being modeled.
-/
axiom ConstraintViolations {V : Type*} : V → ℕ

/-- State space at constraint threshold K: all configurations with ≤ K violations -/
def StateSpace {V : Type*} (K : ℕ) : Set V := {σ : V | ConstraintViolations σ ≤ K}

/-- Monotonicity: Lower thresholds yield smaller state spaces -/
axiom statespace_monotone {V : Type*} {K K' : ℕ} (h : K' ≤ K) :
  (StateSpace K' : Set V) ⊆ (StateSpace K : Set V)

-- ═══════════════════════════════════════════════════════════════════════════
-- MEASUREMENT OPERATOR
-- ═══════════════════════════════════════════════════════════════════════════

/--
Measurement operator: Projects from K_pre to K_post constraint threshold.

**Physical Interpretation**: Measurement adds constraints via observer interaction,
reducing the allowed state space from V_K_pre to V_K_post where K_post < K_pre.
-/
structure MeasurementOperator (V : Type*) [Fintype V] [DecidableEq V] (K_pre K_post : ℕ) where
  /-- The measurement operator matrix -/
  matrix : Matrix V V ℂ
  /-- Constraint reduction: measurement tightens threshold -/
  constraint_reduction : K_post < K_pre
  /-- Projects onto post-measurement space -/
  projects_onto : ∀ σ : V, σ ∈ StateSpace K_post →
    (matrix.mulVec (fun τ => if τ = σ then 1 else 0)) σ ≠ 0
  /-- Annihilates states outside post-measurement space -/
  annihilates : ∀ σ : V, σ ∉ StateSpace K_post →
    (matrix.mulVec (fun τ => if τ = σ then 1 else 0)) σ = 0

/-- Measurement operators are projections: M² = M -/
axiom measurement_is_projection {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) :
  M.matrix * M.matrix = M.matrix

/-- Measurement operators are Hermitian: M† = M -/
axiom measurement_is_hermitian {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) :
  M.matrix.conjTranspose = M.matrix

/-- Measurement operators are non-unitary when K reduces -/
axiom measurement_not_unitary {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) (h : K_post < K_pre) :
  M.matrix.conjTranspose * M.matrix ≠ 1

-- ═══════════════════════════════════════════════════════════════════════════
-- WAVEFUNCTION COLLAPSE
-- ═══════════════════════════════════════════════════════════════════════════

/-- The collapsed wavefunction is normalized -/
axiom wavefunction_collapse_normalized {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) (amplitude : V → ℂ) :
  let ψ_measured := M.matrix.mulVec amplitude
  let norm_sq := ∑ σ : V, normSq (ψ_measured σ)
  let norm := Real.sqrt norm_sq
  let ψ_post := fun σ => ψ_measured σ / norm
  ∑ σ : V, normSq (ψ_post σ) = 1

/-- The collapsed wavefunction has support only in StateSpace K_post -/
axiom wavefunction_collapse_support {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) (amplitude : V → ℂ) :
  let ψ_measured := M.matrix.mulVec amplitude
  let norm_sq := ∑ σ : V, normSq (ψ_measured σ)
  let norm := Real.sqrt norm_sq
  let ψ_post := fun σ => ψ_measured σ / norm
  ∀ σ : V, σ ∉ StateSpace K_post → ψ_post σ = 0

/--
Wavefunction collapse: Apply measurement operator and renormalize.

**Returns**: Collapsed wavefunction amplitude after measurement.
-/
noncomputable def wavefunction_collapse {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) (amplitude : V → ℂ) : V → ℂ :=
  let ψ_measured := M.matrix.mulVec amplitude
  let norm_sq := ∑ σ : V, normSq (ψ_measured σ)
  let norm := Real.sqrt norm_sq
  fun σ => ψ_measured σ / norm

/--
Measurement probability (Born rule): Probability of measuring outcome σ.

**Formula**: P(σ) = |M|ψ⟩(σ)|² / ∑_τ |M|ψ⟩(τ)|²
-/
noncomputable def measurement_probability {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) (amplitude : V → ℂ) (outcome : V) : ℝ :=
  let M_psi := M.matrix.mulVec amplitude
  let total_norm := ∑ σ : V, normSq (M_psi σ)
  normSq (M_psi outcome) / total_norm

-- ═══════════════════════════════════════════════════════════════════════════
-- CONSTRAINT ADDITION
-- ═══════════════════════════════════════════════════════════════════════════

/--
Constraint addition structure: K_initial → K_final = K_initial - ΔK.

**Physical Interpretation**: Observer/environment coupling adds constraints,
tightening the allowed state space.
-/
structure ConstraintAddition (K_initial : ℕ) (ΔK : ℕ) where
  /-- Final constraint threshold -/
  K_final : ℕ
  /-- Constraint tightening -/
  tightening : K_final = K_initial - ΔK
  /-- Ensures ΔK doesn't exceed K_initial (non-negative result) -/
  nonneg : ΔK ≤ K_initial

end LogicRealismTheory.Measurement
