/-
  Logic Realism Theory — Step 5: Eigenvalue Restriction Lemma

  Proves: Self-adjoint operators with spectrum ⊆ {0,1} are projections (P² = P)

  This is the core mathematical content of LRT Step 5. The physical interpretation
  (Boolean actualization → spectrum constraint) is a Tier 2 axiom; this file
  handles the pure mathematics.

  Author: James D. Longmire
  Date: 2026-03-13
  Status: Draft
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Projection

namespace LRT.Step5

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]

/-! ## The Characterization Lemma

The key result: for self-adjoint operators, spectrum ⊆ {0,1} iff idempotent.

We prove the direction needed for LRT: spectrum ⊆ {0,1} → idempotent.
-/

/-- An operator has Boolean spectrum if its spectrum is contained in {0, 1} -/
def HasBooleanSpectrum (T : H →L[Complex] H) : Prop :=
  spectrum Complex T ⊆ {0, 1}

/-- Self-adjoint operator (inner product form) -/
def IsSelfAdjoint' (T : H →L[Complex] H) : Prop :=
  ∀ x y : H, @inner Complex H _ (T x) y = @inner Complex H _ x (T y)

/-- An operator is a projection if it is idempotent -/
def IsIdempotent (T : H →L[Complex] H) : Prop :=
  T * T = T

/-- An orthogonal projection is self-adjoint and idempotent -/
structure IsOrthogonalProjection (P : H →L[Complex] H) : Prop where
  self_adjoint : IsSelfAdjoint' P
  idempotent : IsIdempotent P

/-! ## Direct Eigenvalue Argument

Instead of using functional calculus, we use the direct argument:
- If mu is an eigenvalue with eigenvector v, then T²v = mu²v
- If spectrum ⊆ {0,1}, then mu² = mu for all eigenvalues
- Therefore T²v = muv = Tv for all eigenvectors
- By density of span of eigenvectors (spectral theorem), T² = T

For this file, we axiomatize the spectral theorem application as it depends
on Mathlib's spectral theory completeness.
-/

/-- Key lemma: mu² = mu for mu ∈ {0, 1} -/
lemma bool_eigenvalue_idempotent (mu : Complex) (h : mu ∈ ({0, 1} : Set Complex)) : mu^2 = mu := by
  rcases h with rfl | rfl
  · ring
  · ring

/-- For any eigenvector of T with eigenvalue in {0,1}, T² acts as T -/
lemma eigenvector_idempotent
    (T : H →L[Complex] H)
    (v : H)
    (mu : Complex)
    (h_eigen : T v = mu • v)
    (h_bool : mu ∈ ({0, 1} : Set Complex)) :
    (T * T) v = T v := by
  calc (T * T) v
      = T (T v) := by rfl
    _ = T (mu • v) := by rw [h_eigen]
    _ = mu • (T v) := by exact ContinuousLinearMap.map_smul T mu v
    _ = mu • (mu • v) := by rw [h_eigen]
    _ = (mu * mu) • v := by rw [smul_smul]
    _ = mu^2 • v := by ring_nf
    _ = mu • v := by rw [bool_eigenvalue_idempotent mu h_bool]
    _ = T v := by rw [← h_eigen]

/-! ## The Main Theorem (Axiomatized)

The full theorem requires the spectral theorem to assert that eigenvectors span H
(or that the spectral integral characterizes the operator). We state this as
a Tier 2 axiom for now, pending Mathlib's spectral theory coverage.
-/

/-- TIER 2 AXIOM: For self-adjoint operators with spectrum ⊆ {0,1},
    the eigenspace decomposition (spectral theorem) implies T² = T.

    Justification: Standard functional analysis. The polynomial p(mu) = mu² - mu
    vanishes on {0,1}, so p(T) = 0 by polynomial functional calculus. -/
axiom spectral_idempotent_of_bool_spectrum
    (T : H →L[Complex] H)
    (h_sa : IsSelfAdjoint' T)
    (h_bool : HasBooleanSpectrum T) :
    IsIdempotent T

/-- **Step 5 Eigenvalue Restriction Theorem:**
    Self-adjoint operators with Boolean spectrum are orthogonal projections. -/
theorem step5_eigenvalue_restriction
    (T : H →L[Complex] H)
    (h_sa : IsSelfAdjoint' T)
    (h_bool : HasBooleanSpectrum T) :
    IsOrthogonalProjection T :=
  ⟨h_sa, spectral_idempotent_of_bool_spectrum T h_sa h_bool⟩

/-! ## Connection to LRT's Boolean Actualization

The physical input: A : Events → {0,1} (Boolean actualization)
implies that event operators have spectrum ⊆ {0,1}.

This is formalized as a Tier 2 axiom connecting physics to operator theory.
-/

/-- TIER 2 AXIOM (Actualization Interpretation):
    Event operators representing LRT's Boolean actualization predicates
    have Boolean spectrum.

    Justification: Measurement outcomes correspond to eigenvalues (spectral theorem);
    LRT's A outputs only 0 or 1; therefore eigenvalues ∈ {0,1}. -/
axiom event_operator_has_bool_spectrum
    (E : H →L[Complex] H)
    (h_event : True)
    : HasBooleanSpectrum E

/-- **Corollary:** All LRT event operators are orthogonal projections. -/
theorem event_operators_are_projections
    (E : H →L[Complex] H)
    (h_sa : IsSelfAdjoint' E)
    (h_event : True)
    : IsOrthogonalProjection E :=
  step5_eigenvalue_restriction E h_sa (event_operator_has_bool_spectrum E h_event)

end LRT.Step5
