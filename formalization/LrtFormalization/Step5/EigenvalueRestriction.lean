/-
  Logic Realism Theory — Step 5: Eigenvalue Restriction Lemma

  Proves: Self-adjoint operators with spectrum ⊆ {0,1} are projections (P² = P)

  Author: James D. Longmire
  Date: 2026-03-13
  Status: Theorem (v3, 2026-03-20) — spectral_idempotent_of_bool_spectrum converted from axiom
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace LRT.Step5

open scoped InnerProductSpace
open LinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Part I: Basic Definitions -/

def HasBooleanSpectrum (T : H →L[ℂ] H) : Prop := spectrum ℂ T ⊆ {0, 1}

def IsSelfAdjoint' (T : H →L[ℂ] H) : Prop :=
  ∀ x y : H, @inner ℂ H _ (T x) y = @inner ℂ H _ x (T y)

def IsIdempotent (T : H →L[ℂ] H) : Prop := T * T = T

structure IsOrthogonalProjection (P : H →L[ℂ] H) : Prop where
  self_adjoint : IsSelfAdjoint' P
  idempotent : IsIdempotent P

/-! ## Part II: Eigenvector-Level Arguments -/

lemma bool_eigenvalue_idempotent (μ : ℂ) (h : μ ∈ ({0, 1} : Set ℂ)) : μ^2 = μ := by
  rcases h with rfl | rfl <;> ring

lemma eigenvector_idempotent
    (T : H →L[ℂ] H) (v : H) (μ : ℂ)
    (h_eigen : T v = μ • v) (h_bool : μ ∈ ({0, 1} : Set ℂ)) :
    (T * T) v = T v := by
  calc (T * T) v = T (T v) := rfl
    _ = T (μ • v) := by rw [h_eigen]
    _ = μ • (T v) := ContinuousLinearMap.map_smul T μ v
    _ = μ • (μ • v) := by rw [h_eigen]
    _ = μ^2 • v := by rw [smul_smul]; ring_nf
    _ = μ • v := by rw [bool_eigenvalue_idempotent μ h_bool]
    _ = T v := by rw [← h_eigen]

/-! ## Part III: Polynomial Facts -/

noncomputable def idempotencePolynomial : Polynomial ℂ := Polynomial.X^2 - Polynomial.X

lemma zero_is_root : Polynomial.IsRoot idempotencePolynomial 0 := by
  simp [idempotencePolynomial, Polynomial.IsRoot]

lemma one_is_root : Polynomial.IsRoot idempotencePolynomial 1 := by
  simp [idempotencePolynomial, Polynomial.IsRoot]

lemma idempotence_poly_roots :
    ∀ μ : ℂ, Polynomial.IsRoot idempotencePolynomial μ ↔ μ ∈ ({0, 1} : Set ℂ) := by
  intro μ
  simp only [idempotencePolynomial, Polynomial.IsRoot, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have : μ^2 - μ = μ * (μ - 1) := by ring
    rw [this] at h
    rcases mul_eq_zero.mp h with h0 | h1
    · left; exact h0
    · right; exact sub_eq_zero.mp h1
  · intro h; rcases h with rfl | rfl <;> ring

/-! ## Part IV: Finite-Dimensional Spectral Theorem -/

section FiniteDimensional

variable [FiniteDimensional ℂ H]

lemma agrees_on_eigenspaces
    (T : H →ₗ[ℂ] H) (_hT : T.IsSymmetric)
    (h_bool : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → μ ∈ ({0, 1} : Set ℂ)) :
    ∀ μ : ℂ, ∀ v ∈ Module.End.eigenspace T μ, T (T v) = T v := by
  intro μ v hv
  rw [Module.End.mem_eigenspace_iff] at hv
  by_cases h : Module.End.HasEigenvalue T μ
  · have h_in : μ ∈ ({0, 1} : Set ℂ) := h_bool μ h
    calc T (T v) = T (μ • v) := by rw [hv]
      _ = μ • T v := LinearMap.map_smul T μ v
      _ = μ • (μ • v) := by rw [hv]
      _ = μ^2 • v := by rw [smul_smul]; ring_nf
      _ = μ • v := by rw [bool_eigenvalue_idempotent μ h_in]
      _ = T v := by rw [← hv]
  · by_cases hv0 : v = 0
    · simp [hv0]
    · exfalso; apply h
      rw [Module.End.hasEigenvalue_iff]; intro h_bot
      have hmem := Module.End.mem_eigenspace_iff.mpr hv
      rw [h_bot] at hmem
      exact hv0 ((Submodule.mem_bot ℂ).mp hmem)

theorem fin_dim_spectral_idempotent
    (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (h_bool : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → μ ∈ ({0, 1} : Set ℂ)) :
    T * T = T := by
  have h_agree := agrees_on_eigenspaces T hT h_bool
  haveI : Fact T.IsSymmetric := ⟨hT⟩
  ext v
  have hv_decomp := (LinearIsometryEquiv.symm_apply_apply hT.diagonalization v).symm
  rw [hv_decomp]
  simp only [hT.diagonalization_symm_apply, map_sum]
  congr 1; funext μ
  exact h_agree μ.val ↑(hT.diagonalization v μ) (hT.diagonalization v μ).property

lemma isSelfAdjoint'_toLinearMap_isSymmetric (T : H →L[ℂ] H) (h_sa : IsSelfAdjoint' T) :
    (T : H →ₗ[ℂ] H).IsSymmetric := fun x y => h_sa x y

lemma hasBooleanSpectrum_implies_bool_eigenvalues
    (T : H →L[ℂ] H) (h_bool : HasBooleanSpectrum T) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (T : H →ₗ[ℂ] H) μ → μ ∈ ({0, 1} : Set ℂ) := by
  intro μ h_eigen
  apply h_bool
  rw [spectrum.mem_iff]; intro h_inv
  rw [Module.End.hasEigenvalue_iff] at h_eigen; apply h_eigen
  rw [Submodule.eq_bot_iff]; intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv
  obtain ⟨u, hu⟩ := h_inv
  have hv_ker : ((algebraMap ℂ (H →L[ℂ] H)) μ - T) v = 0 := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.algebraMap_apply]
    have : T v = μ • v := hv
    rw [this]
    exact sub_self _
  have h_eq : (↑u : H →L[ℂ] H) v = 0 := by rw [hu]; exact hv_ker
  -- Show v = u⁻¹ (u v) = u⁻¹ 0 = 0
  have h_inv_mul : (↑u⁻¹ : H →L[ℂ] H) * (↑u : H →L[ℂ] H) = 1 := by
    have := Units.inv_mul u
    simp only [← Units.val_mul, this, Units.val_one]
  have key : v = (↑u⁻¹ : H →L[ℂ] H) ((↑u : H →L[ℂ] H) v) := by
    calc v = (1 : H →L[ℂ] H) v := by simp
      _ = ((↑u⁻¹ : H →L[ℂ] H) * (↑u : H →L[ℂ] H)) v := by rw [h_inv_mul]
      _ = (↑u⁻¹ : H →L[ℂ] H) ((↑u : H →L[ℂ] H) v) := rfl
  rw [key, h_eq]; simp

end FiniteDimensional

/-! ## Part V: Main Theorem -/

section SpectralIdempotentTheorem

variable [FiniteDimensional ℂ H]

/-- **THEOREM (2026-03-20):** Self-adjoint operators with Boolean spectrum are idempotent.
    Previously axiom, now proven for finite dimensions. -/
theorem spectral_idempotent_of_bool_spectrum
    (T : H →L[ℂ] H) (h_sa : IsSelfAdjoint' T) (h_bool : HasBooleanSpectrum T) :
    IsIdempotent T := by
  unfold IsIdempotent
  have h_sym := isSelfAdjoint'_toLinearMap_isSymmetric T h_sa
  have h_bool_eigen := hasBooleanSpectrum_implies_bool_eigenvalues T h_bool
  have h_lin_idem := fin_dim_spectral_idempotent (T : H →ₗ[ℂ] H) h_sym h_bool_eigen
  ext v
  calc ((T * T) : H →ₗ[ℂ] H) v
      = ((T : H →ₗ[ℂ] H) * (T : H →ₗ[ℂ] H)) v := rfl
    _ = (T : H →ₗ[ℂ] H) v := by rw [h_lin_idem]

theorem step5_eigenvalue_restriction
    (T : H →L[ℂ] H) (h_sa : IsSelfAdjoint' T) (h_bool : HasBooleanSpectrum T) :
    IsOrthogonalProjection T :=
  ⟨h_sa, spectral_idempotent_of_bool_spectrum T h_sa h_bool⟩

end SpectralIdempotentTheorem

/-! ## Part VI: Event Operators Bridge (to Step4/Boolean.lean)

The original axiom `event_operator_has_bool_spectrum (E : H →L[ℂ] H) (h_event : True)`
was a placeholder with trivial predicate. It has been replaced by:

- `Step4.Boolean.EventRepresentation`: Structure bundling an Event with its
  Hilbert space operator, self-adjointness, and Boolean spectrum property
- `Step4.Boolean.event_operator_boolean_spectrum`: Extracts HasBooleanSpectrum from EventRepresentation
- `Step4.Boolean.event_operator_is_projection`: Derives IsOrthogonalProjection from EventRepresentation

The derivation chain is:
  L₃ (excluded middle) → Event.l3_decidable (sharp events)
    → EventRepresentation.boolean_spectrum → HasBooleanSpectrum
    → step5_eigenvalue_restriction → IsOrthogonalProjection

See Step4/Boolean.lean for the complete bridge from LRT ontology to projection structure.
-/

end LRT.Step5
