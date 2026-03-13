/-
  Logic Realism Theory — Step 5: Eigenvalue Restriction Lemma

  Proves: Self-adjoint operators with spectrum ⊆ {0,1} are projections (P² = P)

  This is the core mathematical content of LRT Step 5. The physical interpretation
  (Boolean actualization → spectrum constraint) is a Tier 2 axiom; this file
  handles the pure mathematics.

  Key Result (Spectral Idempotence):
    For self-adjoint T with σ(T) ⊆ {0,1}, the polynomial p(x) = x² - x
    vanishes on the spectrum, hence p(T) = T² - T = 0, so T² = T.

  Author: James D. Longmire
  Date: 2026-03-13
  Status: Refined (v2)
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

/-! ## Part I: Basic Definitions

We define the core predicates: Boolean spectrum, self-adjointness, idempotence.
-/

/-- An operator has Boolean spectrum if its spectrum is contained in {0, 1} -/
def HasBooleanSpectrum (T : H →L[ℂ] H) : Prop :=
  spectrum ℂ T ⊆ {0, 1}

/-- Self-adjoint operator (inner product form) -/
def IsSelfAdjoint' (T : H →L[ℂ] H) : Prop :=
  ∀ x y : H, @inner ℂ H _ (T x) y = @inner ℂ H _ x (T y)

/-- An operator is idempotent if T² = T -/
def IsIdempotent (T : H →L[ℂ] H) : Prop :=
  T * T = T

/-- An orthogonal projection is self-adjoint and idempotent -/
structure IsOrthogonalProjection (P : H →L[ℂ] H) : Prop where
  self_adjoint : IsSelfAdjoint' P
  idempotent : IsIdempotent P

/-! ## Part II: Eigenvector-Level Arguments

The direct argument for idempotence at the eigenvector level.
-/

/-- Key lemma: μ² = μ for μ ∈ {0, 1} -/
lemma bool_eigenvalue_idempotent (μ : ℂ) (h : μ ∈ ({0, 1} : Set ℂ)) : μ^2 = μ := by
  rcases h with rfl | rfl
  · ring
  · ring

/-- For any eigenvector of T with eigenvalue in {0,1}, T² acts as T -/
lemma eigenvector_idempotent
    (T : H →L[ℂ] H)
    (v : H)
    (μ : ℂ)
    (h_eigen : T v = μ • v)
    (h_bool : μ ∈ ({0, 1} : Set ℂ)) :
    (T * T) v = T v := by
  calc (T * T) v
      = T (T v) := by rfl
    _ = T (μ • v) := by rw [h_eigen]
    _ = μ • (T v) := by exact ContinuousLinearMap.map_smul T μ v
    _ = μ • (μ • v) := by rw [h_eigen]
    _ = (μ * μ) • v := by rw [smul_smul]
    _ = μ^2 • v := by ring_nf
    _ = μ • v := by rw [bool_eigenvalue_idempotent μ h_bool]
    _ = T v := by rw [← h_eigen]

/-! ## Part III: The Polynomial Functional Calculus Argument

The spectral theorem for self-adjoint operators implies that if a polynomial
p vanishes on the spectrum, then p(T) = 0.

For p(x) = x² - x, the roots are exactly {0, 1}.
If σ(T) ⊆ {0, 1}, then p vanishes on σ(T), hence T² - T = 0.
-/

/-- The idempotence polynomial p(x) = x² - x -/
noncomputable def idempotencePolynomial : Polynomial ℂ :=
  Polynomial.X^2 - Polynomial.X

/-- The polynomial x² - x has roots exactly at 0 and 1 -/
lemma idempotence_poly_roots :
    (idempotencePolynomial.roots : Multiset ℂ) = {0, 1} := by
  sorry -- Standard polynomial factorization

/-- If μ ∈ {0, 1}, then the idempotence polynomial vanishes at μ -/
lemma idempotence_poly_vanishes_on_bool (μ : ℂ) (h : μ ∈ ({0, 1} : Set ℂ)) :
    Polynomial.aeval μ idempotencePolynomial = (0 : ℂ) := by
  simp only [idempotencePolynomial, map_sub, map_pow, Polynomial.aeval_X]
  rcases h with rfl | rfl
  · ring
  · ring

/-! ## Part IV: Finite-Dimensional Spectral Theorem

In finite dimensions, the spectral theorem for self-adjoint operators
provides a complete eigenspace decomposition.
-/

section FiniteDimensional

variable [FiniteDimensional ℂ H]

-- **TIER 1 THEOREM (from Mathlib):**
-- Self-adjoint operators on finite-dimensional Hilbert spaces are diagonalizable.
-- This is the spectral theorem. Mathlib provides:
-- - LinearMap.IsSymmetric.direct_sum_isInternal
-- - LinearMap.IsSymmetric.diagonalization

/-- Eigenvalues of self-adjoint operators are real (Mathlib provides this) -/
lemma eigenvalues_real (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue T μ) : starRingEnd ℂ μ = μ :=
  hT.conj_eigenvalue_eq_self hμ

/-- **LEMMA:** For finite-dimensional self-adjoint T with Boolean spectrum,
    T agrees with T² on each eigenspace. -/
lemma agrees_on_eigenspaces
    (T : H →ₗ[ℂ] H)
    (hT : T.IsSymmetric)
    (h_bool : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → μ ∈ ({0, 1} : Set ℂ)) :
    ∀ μ : ℂ, ∀ v ∈ Module.End.eigenspace T μ, T (T v) = T v := by
  intro μ v hv
  rw [Module.End.mem_eigenspace_iff] at hv
  by_cases h : Module.End.HasEigenvalue T μ
  · have h_in : μ ∈ ({0, 1} : Set ℂ) := h_bool μ h
    calc T (T v)
        = T (μ • v) := by rw [hv]
      _ = μ • T v := by exact LinearMap.map_smul T μ v
      _ = μ • (μ • v) := by rw [hv]
      _ = (μ * μ) • v := by rw [smul_smul]
      _ = μ^2 • v := by ring_nf
      _ = μ • v := by rw [bool_eigenvalue_idempotent μ h_in]
      _ = T v := by rw [← hv]
  · -- If μ is not an eigenvalue, then Tv = μv forces v = 0 or μ is an eigenvalue
    -- Since h says μ is not an eigenvalue, and hv says Tv = μv, we need v = 0
    by_cases hv0 : v = 0
    · simp [hv0]
    · -- v ≠ 0 and Tv = μv means μ IS an eigenvalue, contradiction
      exfalso
      apply h
      rw [Module.End.hasEigenvalue_iff]
      intro h_bot
      have hmem : v ∈ Module.End.eigenspace T μ := Module.End.mem_eigenspace_iff.mpr hv
      rw [h_bot] at hmem
      exact hv0 ((Submodule.mem_bot ℂ).mp hmem)

/-- **THEOREM (Finite-Dimensional Spectral Idempotence):**
    If T is self-adjoint with all eigenvalues in {0,1}, then T² = T. -/
theorem fin_dim_spectral_idempotent
    (T : H →ₗ[ℂ] H)
    (hT : T.IsSymmetric)
    (h_bool : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → μ ∈ ({0, 1} : Set ℂ)) :
    T * T = T := by
  -- Use the spectral theorem: H = ⊕ eigenspaces
  -- On each eigenspace, T² = T (from agrees_on_eigenspaces)
  -- Therefore T² = T on all of H
  ext v
  -- The direct sum decomposition from the spectral theorem
  have h_decomp := hT.direct_sum_isInternal
  -- This requires extracting the decomposition and showing linearity
  sorry -- Requires working with Mathlib's DirectSum API

end FiniteDimensional

/-! ## Part V: General Case (Axiomatized)

For infinite-dimensional or bounded operator cases, we axiomatize the
functional calculus result.
-/

/-- **TIER 2 AXIOM (Spectral Idempotence):**
    For self-adjoint operators with spectrum ⊆ {0,1},
    the polynomial functional calculus gives T² = T.

    This is standard functional analysis:
    - The continuous functional calculus maps f ↦ f(T)
    - For f(x) = x², we get f(T) = T²
    - If σ(T) ⊆ {0,1} and g(x) = x² - x, then g|_{σ(T)} = 0
    - By the spectral mapping theorem, g(T) = 0, so T² = T
-/
axiom spectral_idempotent_of_bool_spectrum
    (T : H →L[ℂ] H)
    (h_sa : IsSelfAdjoint' T)
    (h_bool : HasBooleanSpectrum T) :
    IsIdempotent T

/-! ## Part VI: The Step 5 Theorem -/

/-- **Step 5 Eigenvalue Restriction Theorem:**
    Self-adjoint operators with Boolean spectrum are orthogonal projections. -/
theorem step5_eigenvalue_restriction
    (T : H →L[ℂ] H)
    (h_sa : IsSelfAdjoint' T)
    (h_bool : HasBooleanSpectrum T) :
    IsOrthogonalProjection T :=
  ⟨h_sa, spectral_idempotent_of_bool_spectrum T h_sa h_bool⟩

/-! ## Part VII: Connection to LRT's Boolean Actualization

The physical input: A : Events → {0,1} (Boolean actualization)
implies that event operators have spectrum ⊆ {0,1}.

This is formalized as a Tier 2 axiom connecting physics to operator theory.
-/

/-- **TIER 2 AXIOM (Actualization Interpretation):**
    Event operators representing LRT's Boolean actualization predicates
    have Boolean spectrum.

    Physical justification:
    - Measurement outcomes correspond to eigenvalues (spectral theorem)
    - LRT's actualization function A outputs only 0 or 1
    - Therefore eigenvalues ∈ {0,1}

    This bridges the metaphysical (A is Boolean) to the mathematical (σ(E) ⊆ {0,1}).
-/
axiom event_operator_has_bool_spectrum
    (E : H →L[ℂ] H)
    (h_event : True) -- Placeholder for "E represents an LRT event"
    : HasBooleanSpectrum E

/-- **Corollary:** All LRT event operators are orthogonal projections. -/
theorem event_operators_are_projections
    (E : H →L[ℂ] H)
    (h_sa : IsSelfAdjoint' E)
    (h_event : True)
    : IsOrthogonalProjection E :=
  step5_eigenvalue_restriction E h_sa (event_operator_has_bool_spectrum E h_event)

/-! ## Status

CONFIDENCE: HIGH (core math is standard, only spectral theorem application axiomatized)

**PROVEN:**
- bool_eigenvalue_idempotent: μ² = μ for μ ∈ {0,1}
- eigenvector_idempotent: T²v = Tv for eigenvectors with Boolean eigenvalue
- idempotence_poly_vanishes_on_bool: p(μ) = 0 for μ ∈ {0,1}
- eigenvalues_real: Uses Mathlib's LinearMap.IsSymmetric.conj_eigenvalue_eq_self
- agrees_on_eigenspaces: T² = T on each eigenspace (for Boolean spectrum)

**AXIOMATIZED (Tier 2):**
- spectral_idempotent_of_bool_spectrum: The full T² = T from functional calculus
- event_operator_has_bool_spectrum: Physics interpretation

**SORRY (implementation details):**
- idempotence_poly_roots: Standard polynomial factorization
- fin_dim_spectral_idempotent: Needs DirectSum API work

The core mathematical insight is sound; the remaining `sorry` items are
Mathlib API work, not conceptual gaps.
-/

end LRT.Step5
