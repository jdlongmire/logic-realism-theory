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

/-! ## Part IV-A: Time Evolution Axioms

These axioms define the structure of time evolution, from which we derive UnitaryGroup.
-/

/-- **TIER 2 AXIOM (LRT):** There exists a family of operators indexed by time.

    This is the fundamental existence axiom: time evolution gives us operators U(t). -/
axiom time_evolution_family : ℝ → (H →L[ℂ] H)

/-- **TIER 2 AXIOM (LRT):** Time evolution preserves normalization.

    This is probability conservation: total probability = 1 at all times.
    Applies to each U(t) in the time evolution family. -/
axiom evolution_preserves_norm (t : ℝ) : PreservesNorm (time_evolution_family (H := H) t)

/-- **TIER 2 AXIOM (Physical):** Time evolution satisfies the group composition law.

    U(s + t) = U(s) ∘ U(t) encodes time-translation symmetry. -/
axiom evolution_group_composition (s t : ℝ) :
    time_evolution_family (H := H) (s + t) = time_evolution_family s * time_evolution_family t

/-- **TIER 2 AXIOM (Physical):** U(0) is the identity.

    At t = 0, no evolution has occurred. -/
axiom evolution_identity : time_evolution_family (H := H) 0 = ContinuousLinearMap.id ℂ H

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

**Tier 2 Axioms:**
- time_evolution_family: Family of operators U(t) indexed by time
- evolution_preserves_norm: Probability conservation at all times
- evolution_group_composition: U(s+t) = U(s) * U(t) (time-translation symmetry)
- evolution_identity: U(0) = I

**Derived Theorems:**
- inner_implies_norm: Inner preservation → norm preservation
- wigner_theorem: Norm-preserving linear maps preserve inner products
- step7_unitarity: Each U(t) is unitary (from evolution_preserves_norm + Wigner)
- evolution_preserves_distinguishability: Orthogonal states remain orthogonal
- **time_evolution_group: THEOREM (was axiom, 2026-03-20)** - constructed from
  time_evolution_family + step7_unitarity + evolution_group_composition + evolution_identity

**Axiom Reduction (2026-03-20):**
The single `time_evolution_group` axiom has been replaced by four more primitive axioms:
1. time_evolution_family (existence of operator family)
2. evolution_preserves_norm (probability conservation)
3. evolution_group_composition (time-translation symmetry)
4. evolution_identity (identity at t=0)

This decomposition makes the physics clearer: probability conservation and time-translation
symmetry are the fundamental requirements; unitarity and group structure follow.

Unitarity is now established. Step 8 will derive temporal emergence.
-/

end LRT.Step7
