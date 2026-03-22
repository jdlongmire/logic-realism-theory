/-
  Logic Realism Theory — Step 7: Unitarity

  Proves: Time evolution preserves inner products: ⟨U(t)ψ|U(t)φ⟩ = ⟨ψ|φ⟩

  Unitarity emerges from:
  1. Probability conservation (Born rule normalization preserved)
  2. Distinguishability preservation (L₃ constraint)
  3. Linearity of quantum mechanics (from local tomography)

  The key insight: the only linear maps preserving norms are unitary operators.

  Author: James D. Longmire
  Date: 2026-03-13
  Status: Foundation
  Epistemic Status: ESTABLISHED (conditional on Steps 4-6)
-/

import LrtFormalization.Step6_BornRule
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace LRT.Step7

open scoped InnerProductSpace
open LRT.Step5 LRT.Step6

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Part I: Norm Preservation

Evolution must preserve norms to maintain probability normalization.
-/

/-- A linear map preserves norms -/
def PreservesNorm (U : H →L[ℂ] H) : Prop :=
  ∀ ψ : H, ‖U ψ‖ = ‖ψ‖

/-- Norm preservation implies normalization preservation -/
theorem preserves_normalization (U : H →L[ℂ] H) (h : PreservesNorm U) :
    ∀ ψ : H, IsNormalized ψ → IsNormalized (U ψ) := by
  intro ψ h_norm
  unfold IsNormalized at *
  rw [h ψ, h_norm]

/-! ## Part II: Inner Product Preservation

Unitarity is equivalent to inner product preservation.
-/

/-- A linear map preserves inner products -/
def PreservesInner (U : H →L[ℂ] H) : Prop :=
  ∀ ψ φ : H, @inner ℂ H _ (U ψ) (U φ) = @inner ℂ H _ ψ φ

/-- Inner product preservation implies norm preservation -/
theorem inner_implies_norm (U : H →L[ℂ] H) (h : PreservesInner U) :
    PreservesNorm U := by
  intro ψ
  have h1 : ‖U ψ‖^2 = ‖ψ‖^2 := by
    have hU := h ψ ψ
    -- ‖x‖² = Re⟨x,x⟩ for complex inner product spaces
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re hU
  nlinarith [norm_nonneg (U ψ), norm_nonneg ψ, sq_nonneg ‖U ψ‖, sq_nonneg ‖ψ‖]

/-! ## Part III: Unitary Operators

Definition and characterization of unitary operators.
-/

/-- An operator is unitary if it preserves inner products -/
structure IsUnitary (U : H →L[ℂ] H) : Prop where
  preserves_inner : PreservesInner U

/-- Unitary operators are isometries -/
theorem unitary_is_isometry (U : H →L[ℂ] H) (h : IsUnitary U) :
    PreservesNorm U :=
  inner_implies_norm U h.preserves_inner

/-- Unitary operators preserve probability distributions (Born rule)
    Note: Full statement uses adjoint U†; here we use a simplified version. -/
theorem unitary_preserves_probability
    (U : H →L[ℂ] H)
    (h_unitary : IsUnitary U)
    (ψ : H)
    (h_norm : IsNormalized ψ) :
    IsNormalized (U ψ) := by
  -- Unitarity preserves norms, hence normalization
  exact preserves_normalization U (inner_implies_norm U h_unitary.preserves_inner) ψ h_norm

/-! ## Part IV: LRT Derivation of Unitarity

The LRT argument: if evolution preserves:
1. Normalization (probability conservation)
2. Distinguishability (L₃ constraint)
3. Linearity (from local tomography)

Then evolution must be unitary.
-/

/-- **THEOREM (from mathlib):** Wigner's theorem — norm-preserving linear maps preserve inner products.

    Derived from mathlib's `LinearMap.norm_map_iff_inner_map_map`: norm preservation
    is equivalent to inner product preservation for linear maps on inner product spaces.
    This is the content of Wigner's theorem for linear (not anti-linear) maps.

    Note: Bijectivity is not required for linear maps (unlike the general Wigner theorem
    which considers anti-linear maps). The mathlib theorem handles the linear case directly. -/
theorem wigner_theorem
    (U : H →L[ℂ] H)
    (h_norm : PreservesNorm U) :
    IsUnitary U := by
  constructor
  intro ψ φ
  -- Use mathlib's LinearMap.norm_map_iff_inner_map_map
  have h := (LinearMap.norm_map_iff_inner_map_map U.toLinearMap).mp h_norm
  exact h ψ φ

/-! ## Part IV-A: Hamiltonian-Based Time Evolution (Issues #41, #42, #43)

The Hamiltonian approach reduces 4 axioms to 2 root axioms:
- hamiltonian: The generator of time evolution
- hamiltonian_isSelfAdjoint: H† = H (ensures unitarity)

From these, we derive:
- time_evolution_family: U(t) = exp(-iHt)
- evolution_preserves_norm: Follows from self-adjointness
- evolution_group_composition: Follows from exponential properties
- evolution_identity: U(0) = I

**Axiom Reduction (2026-03-21):** 4 axioms → 2 axioms
-/

/-- **TIER 2 AXIOM (ROOT 1/2):** The Hamiltonian operator exists.

    H : H →L[ℂ] H is the generator of time evolution.
    In physics, the Schrödinger equation is i∂ψ/∂t = Hψ.

    This is a physical input: systems have energy observables. -/
axiom hamiltonian : H →L[ℂ] H

/-- **TIER 2 AXIOM (ROOT 2/2):** The Hamiltonian is self-adjoint.

    H† = H ensures:
    1. Real eigenvalues (energy is real)
    2. Unitary evolution (U(t)†U(t) = I)
    3. Probability conservation

    This is the key constraint that makes quantum evolution reversible. -/
axiom hamiltonian_isSelfAdjoint : ContinuousLinearMap.adjoint (hamiltonian (H := H)) = hamiltonian

/-- **DEFINITION:** Time evolution family U(t) = exp(-iHt).

    The generator is -iH (skew-adjoint when H is self-adjoint).
    Note: We use ℏ = 1 units. -/
noncomputable def time_evolution_family (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ((-Complex.I * t) • hamiltonian)

/-- **THEOREM (was axiom):** Time evolution preserves normalization.

    **Derivation:** Since H is self-adjoint, -iH is skew-adjoint.
    For skew-adjoint generators, exp(tA) is unitary, hence norm-preserving.

    U(t)†U(t) = exp(iHt)exp(-iHt) = exp(0) = I

    **Status:** THEOREM (2026-03-21) - derived from hamiltonian_isSelfAdjoint

    **Technical Note (2026-03-21):** The mathematical derivation is:
    1. H is self-adjoint (axiom hamiltonian_isSelfAdjoint)
    2. Therefore -iH is skew-adjoint: star(-iH) = iH† = iH = -(-iH)
    3. exp of skew-adjoint is unitary (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint)
    4. Unitary operators preserve norms

    Uses NormedAlgebra.restrictScalars ℚ ℂ to obtain the required NormedAlgebra ℚ instance
    from the existing NormedAlgebra ℂ instance on H →L[ℂ] H. -/
theorem evolution_preserves_norm (t : ℝ) : PreservesNorm (time_evolution_family (H := H) t) := by
  intro ψ
  -- Provide NormedAlgebra ℚ instance by restricting scalars from ℂ
  let _ : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  -- The generator -iH is skew-adjoint when H is self-adjoint
  -- First show the generator is skew-adjoint
  have h_skew : ((-Complex.I * t) • hamiltonian (H := H)) ∈ skewAdjoint (H →L[ℂ] H) := by
    rw [SetLike.mem_coe, skewAdjoint.mem_iff]
    simp only [ContinuousLinearMap.star_smul, star_mul', Complex.star_def, Complex.conj_neg_I]
    rw [hamiltonian_isSelfAdjoint]
    simp only [Complex.ofReal_re, Complex.ofReal_im, neg_zero, Complex.conj_ofReal]
    ring_nf
    simp only [neg_smul, smul_neg]
  -- exp of skew-adjoint is unitary
  have h_unitary := NormedSpace.exp_mem_unitary_of_mem_skewAdjoint h_skew
  -- Unitary operators are isometries, hence preserve norms
  have h_isometry := unitary.isometry ⟨time_evolution_family t, h_unitary⟩
  exact h_isometry.norm_map ψ

/-- **THEOREM (was axiom):** Time evolution satisfies the group composition law.

    **Derivation:** exp(-iH(s+t)) = exp(-iHs)exp(-iHt) because -iH commutes with itself.

    Mathematical justification:
    - U(s+t) = exp(-iH(s+t)) = exp(-iHs - iHt)
    - Since -iHs and -iHt are scalar multiples of the same operator H, they commute
    - By exp_add_of_commute: exp(A + B) = exp(A) * exp(B) when [A, B] = 0
    - Therefore U(s+t) = U(s) * U(t)

    **Status:** THEOREM (2026-03-21) - derived from exponential properties -/
theorem evolution_group_composition (s t : ℝ) :
    time_evolution_family (H := H) (s + t) = time_evolution_family s * time_evolution_family t := by
  unfold time_evolution_family
  -- Provide NormedAlgebra ℚ instance by restricting scalars from ℂ
  let _ : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  -- Scalar multiples of the same operator commute
  have h_comm : Commute ((-Complex.I * s) • hamiltonian (H := H)) ((-Complex.I * t) • hamiltonian) := by
    unfold Commute SemiconjBy
    simp only [smul_mul_smul, mul_comm]
  -- Use exp_add_of_commute: exp(A + B) = exp(A) * exp(B) when A and B commute
  have h_add : ((-Complex.I * (s + t)) • hamiltonian (H := H)) =
      ((-Complex.I * s) • hamiltonian) + ((-Complex.I * t) • hamiltonian) := by
    simp only [mul_add, add_smul]
  rw [Complex.ofReal_add, h_add]
  exact NormedSpace.exp_add_of_commute h_comm

/-- **THEOREM (was axiom):** U(0) is the identity.

    **Derivation:** U(0) = exp((-i*0)H) = exp(0) = I.

    Mathematical justification:
    - U(0) = exp((-i * 0) • H) = exp(0 • H) = exp(0) = 1 = id

    Uses `NormedSpace.exp_zero` from Mathlib.

    **Status:** THEOREM (2026-03-21) - derived from definition -/
theorem evolution_identity : time_evolution_family (H := H) 0 = ContinuousLinearMap.id ℂ H := by
  unfold time_evolution_family
  -- -i * 0 = 0, and 0 • H = 0, exp(0) = 1 = id
  have h1 : (-Complex.I * (0 : ℂ)) = 0 := by ring
  have h2 : (0 : ℂ) • hamiltonian (H := H) = 0 := zero_smul ℂ _
  simp only [Complex.ofReal_zero, h1, h2, NormedSpace.exp_zero]
  rfl

/-- **Step 7 Theorem:** Time evolution at any time t is unitary.

    From L₃ (distinguishability) + probability conservation → unitarity.

    **Derivation:** Wigner's theorem (mathlib) shows that norm-preserving linear maps
    preserve inner products. This holds for all linear maps without requiring bijectivity. -/
theorem step7_unitarity (t : ℝ) : IsUnitary (time_evolution_family (H := H) t) :=
  wigner_theorem (time_evolution_family t) (evolution_preserves_norm t)

/-- **THEOREM (was axiom):** Time evolution preserves distinguishability.

    This follows from unitarity: unitary operators preserve inner products,
    so orthogonal states remain orthogonal.

    **Derivation:**
    - step7_unitarity proves U(t) is unitary (IsUnitary (time_evolution_family t))
    - IsUnitary.preserves_inner: ⟨U(t)ψ|U(t)φ⟩ = ⟨ψ|φ⟩
    - If ⟨ψ|φ⟩ = 0 (orthogonal), then ⟨U(t)ψ|U(t)φ⟩ = 0

    **Status:** THEOREM (2026-03-19) - converted from axiom -/
theorem evolution_preserves_distinguishability
    (t : ℝ)
    (ψ φ : H)
    (h_orth : @inner ℂ H _ ψ φ = 0) :
    @inner ℂ H _ (time_evolution_family (H := H) t ψ) (time_evolution_family t φ) = 0 := by
  -- U(t) is unitary by step7_unitarity
  have h_unitary : IsUnitary (time_evolution_family (H := H) t) := step7_unitarity t
  -- Unitary operators preserve inner products
  have h_inner : @inner ℂ H _ (time_evolution_family (H := H) t ψ) (time_evolution_family t φ) =
      @inner ℂ H _ ψ φ := h_unitary.preserves_inner ψ φ
  -- Since ⟨ψ|φ⟩ = 0, we have ⟨U(t)ψ|U(t)φ⟩ = 0
  rw [h_inner, h_orth]

/-! ## Part V: One-Parameter Groups

Time evolution forms a continuous one-parameter group.
-/

/-- A one-parameter group of unitaries -/
structure UnitaryGroup where
  /-- The unitary at time t -/
  U : ℝ → (H →L[ℂ] H)
  /-- Each U(t) is unitary -/
  unitary : ∀ t, IsUnitary (U t)
  /-- Group property: U(s+t) = U(s) ∘ U(t) -/
  group_mul : ∀ s t, U (s + t) = U s * U t
  /-- Identity: U(0) = I -/
  group_id : U 0 = ContinuousLinearMap.id ℂ H

/-- **THEOREM (was axiom, 2026-03-20):** Time evolution forms a one-parameter unitary group.

    **Derivation:**
    - time_evolution_family: the family of operators U(t)
    - step7_unitarity: each U(t) is unitary (from evolution_preserves_norm + Wigner)
    - evolution_group_composition: U(s+t) = U(s) * U(t)
    - evolution_identity: U(0) = I

    This was previously axiomatized directly. Now derived from the more primitive
    axioms: time_evolution_family, evolution_preserves_norm, evolution_group_composition,
    and evolution_identity.

    **Status:** THEOREM (2026-03-20) - converted from axiom -/
noncomputable def time_evolution_group : UnitaryGroup (H := H) where
  U := time_evolution_family
  unitary := step7_unitarity
  group_mul := evolution_group_composition
  group_id := evolution_identity

/-! ## Status

CONFIDENCE: HIGH (conditional on Steps 4-6)

**Definitions:**
- PreservesNorm, PreservesInner: Defined
- IsUnitary: Defined
- UnitaryGroup: Defined
- time_evolution_family: Defined as exp(-iHt)

**Tier 2 Axioms (2 total):**
- hamiltonian: The Hamiltonian operator H : H →L[ℂ] H
- hamiltonian_isSelfAdjoint: H† = H (self-adjointness)

**Derived Theorems:**
- inner_implies_norm: Inner preservation → norm preservation
- wigner_theorem: Norm-preserving linear maps preserve inner products
- **evolution_preserves_norm: THEOREM (was axiom)** - from hamiltonian_isSelfAdjoint
- **evolution_group_composition: THEOREM (was axiom)** - from exp_add_of_commute
- **evolution_identity: THEOREM (was axiom)** - from exp_zero
- step7_unitarity: Each U(t) is unitary (from evolution_preserves_norm + Wigner)
- evolution_preserves_distinguishability: Orthogonal states remain orthogonal
- **time_evolution_group: THEOREM (was axiom)** - constructed from derived theorems

**Axiom Reduction History:**
- 2026-03-20: time_evolution_group axiom replaced by four primitive axioms
- 2026-03-21: evolution_identity derived from evolution_has_generator + exp_zero (Issue #44)
- 2026-03-21: **Hamiltonian refactor (Issues #41, #42, #43): 4 axioms → 2 axioms**
  - Replaced: time_evolution_family, evolution_preserves_norm, evolution_group_composition, evolution_has_generator
  - Added: hamiltonian, hamiltonian_isSelfAdjoint
  - Derived: time_evolution_family (as definition), evolution_preserves_norm, evolution_group_composition, evolution_identity

The Hamiltonian approach identifies the true physical primitives:
1. Existence of energy observable (hamiltonian)
2. Reality of energy eigenvalues (hamiltonian_isSelfAdjoint)

Everything else follows: unitary evolution, group structure, probability conservation.

Unitarity is now established. Step 8 will derive temporal emergence.
-/

end LRT.Step7
