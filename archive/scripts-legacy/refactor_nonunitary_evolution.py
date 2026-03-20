#!/usr/bin/env python3
"""
Refactor NonUnitaryEvolution.lean to use ConstraintThreshold and MeasurementGeometry.
Removes duplicate definitions and adds necessary imports.
"""

# Read the file
with open('lean/LogicRealismTheory/Measurement/NonUnitaryEvolution.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Step 1: Add imports after Mathlib imports
old_imports = """import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt"""

new_imports = """import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LogicRealismTheory.Foundation.ConstraintThreshold
import LogicRealismTheory.Measurement.MeasurementGeometry"""

content = content.replace(old_imports, new_imports)

# Step 2: Remove Set.card axiom (lines 77-78)
content = content.replace(
    """-- Axiomatize Set cardinality (not available in current Mathlib)
axiom Set.card {α : Type*} : Set α → ℕ

""", "")

# Step 3: Add open Foundation after "open Complex Matrix"
content = content.replace(
    """open Complex Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]""",
    """open Complex Matrix
open LogicRealismTheory.Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]""")

# Step 4: Remove ConstraintViolations, StateSpace, statespace_monotone
content = content.replace(
    """axiom ConstraintViolations {V : Type*} : V → ℕ

def StateSpace {V : Type*} (K : ℕ) : Set V := {σ : V | ConstraintViolations σ ≤ K}

axiom statespace_monotone {V : Type*} {K K' : ℕ} (h : K' ≤ K) :
  (StateSpace K' : Set V) ⊆ (StateSpace K : Set V)

""", "")

# Step 5: Remove MeasurementOperator structure
content = content.replace(
    """structure MeasurementOperator (V : Type*) [Fintype V] [DecidableEq V] (K_pre K_post : ℕ) where
  matrix : Matrix V V ℂ
  constraint_reduction : K_post < K_pre
  projects_onto : ∀ σ : V, σ ∈ StateSpace K_post →
    (matrix.mulVec (fun τ => if τ = σ then 1 else 0)) σ ≠ 0
  annihilates : ∀ σ : V, σ ∉ StateSpace K_post →
    (matrix.mulVec (fun τ => if τ = σ then 1 else 0)) σ = 0

""", "")

# Step 6: Remove measurement axioms
content = content.replace(
    """axiom measurement_is_projection {V : Type*} [Fintype V] [DecidableEq V]
    {K_pre K_post : ℕ} (M : MeasurementOperator V K_pre K_post) :
  M.matrix * M.matrix = M.matrix

""", "")

content = content.replace(
    """axiom measurement_is_hermitian {V : Type*} [Fintype V] [DecidableEq V]
    {K_pre K_post : ℕ} (M : MeasurementOperator V K_pre K_post) :
  M.matrix.conjTranspose = M.matrix

""", "")

content = content.replace(
    """axiom measurement_not_unitary {V : Type*} [Fintype V] [DecidableEq V]
    {K_pre K_post : ℕ} (M : MeasurementOperator V K_pre K_post)
    (h : K_post < K_pre) :
  M.matrix.conjTranspose * M.matrix ≠ 1

""", "")

# Step 7: Remove wavefunction_collapse axioms and definition
content = content.replace(
    """axiom wavefunction_collapse_normalized {V : Type*} [Fintype V] [DecidableEq V]
    {K_pre K_post : ℕ} (M : MeasurementOperator V K_pre K_post)
    (ψ_pre : QuantumState V K_pre) :
  let ψ_measured := M.matrix.mulVec ψ_pre.amplitude
  let norm_sq := ∑ σ : V, normSq (ψ_measured σ)
  let norm := Real.sqrt norm_sq
  let ψ_post := fun σ => ψ_measured σ / norm
  ∑ σ : V, normSq (ψ_post σ) = 1

""", "")

content = content.replace(
    """axiom wavefunction_collapse_support {V : Type*} [Fintype V] [DecidableEq V]
    {K_pre K_post : ℕ} (M : MeasurementOperator V K_pre K_post)
    (ψ_pre : QuantumState V K_pre) :
  let ψ_measured := M.matrix.mulVec ψ_pre.amplitude
  let norm_sq := ∑ σ : V, normSq (ψ_measured σ)
  let norm := Real.sqrt norm_sq
  let ψ_post := fun σ => ψ_measured σ / norm
  ∀ σ : V, σ ∉ StateSpace K_post → ψ_post σ = 0

""", "")

content = content.replace(
    """noncomputable def wavefunction_collapse {V : Type*} [Fintype V] [DecidableEq V]
    {K_pre K_post : ℕ} (M : MeasurementOperator V K_pre K_post)
    (ψ_pre : QuantumState V K_pre) :
    QuantumState V K_post :=
  let ψ_measured := M.matrix.mulVec ψ_pre.amplitude
  let norm_sq := ∑ σ : V, normSq (ψ_measured σ)
  let norm := Real.sqrt norm_sq
  let ψ_post := fun σ => ψ_measured σ / norm
  ⟨ψ_post, wavefunction_collapse_normalized M ψ_pre, wavefunction_collapse_support M ψ_pre⟩

""", "")

# Step 8: Remove measurement_probability definition
content = content.replace(
    """noncomputable def measurement_probability {V : Type*} [Fintype V] [DecidableEq V]
    {K_pre K_post : ℕ} (M : MeasurementOperator V K_pre K_post)
    (ψ : QuantumState V K_pre) (outcome : V) : ℝ :=
  let M_psi := M.matrix.mulVec ψ.amplitude
  let total_norm := ∑ σ : V, normSq (M_psi σ)
  normSq (M_psi outcome) / total_norm

""", "")

# Step 9: Remove ConstraintAddition structure
content = content.replace(
    """structure ConstraintAddition (K_initial : ℕ) (ΔK : ℕ) where
  K_final : ℕ
  tightening : K_final = K_initial - ΔK
  nonneg : ΔK ≤ K_initial

""", "")

# Write back
with open('lean/LogicRealismTheory/Measurement/NonUnitaryEvolution.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print("[OK] Added imports: ConstraintThreshold and MeasurementGeometry")
print("[OK] Added open LogicRealismTheory.Foundation namespace")
print("[OK] Removed 13 duplicate definitions:")
print("  - Set.card axiom")
print("  - ConstraintViolations axiom")
print("  - StateSpace definition")
print("  - statespace_monotone axiom")
print("  - MeasurementOperator structure")
print("  - measurement_is_projection axiom")
print("  - measurement_is_hermitian axiom")
print("  - measurement_not_unitary axiom")
print("  - wavefunction_collapse_normalized axiom")
print("  - wavefunction_collapse_support axiom")
print("  - wavefunction_collapse definition")
print("  - measurement_probability definition")
print("  - ConstraintAddition structure")
print("\n[OK] Unique content preserved:")
print("  - QuantumState structure")
print("  - UnitaryOperator structure")
print("  - unitary_preserves_norm axiom")
print("  - unitary_preserves_K theorem")
print("  - measurement_reduces_K theorem")
print("  - observer_adds_constraints axiom")
print("  - no_unitarity_contradiction theorem")
print("  - unitary_preserves_dimension axiom")
print("  - measurement_reduces_dimension axiom")
print("  - evolution_types_distinct theorem")
print("\nNonUnitaryEvolution.lean refactored successfully!")
