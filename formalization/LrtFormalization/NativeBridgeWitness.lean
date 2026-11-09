/-
  NativeBridgeWitness.lean

  Native Step0/Step1 witness for WP-LRT-ONTO-0001 (verification handoff,
  2026-11-08).

  The standalone countermodel in BridgeSelectionCountermodel.lean works over
  Nat with plain sets; it is not built from the native LRT primitives. This
  file constructs the corresponding witness natively, from the Step0
  primitives (`I`, `ActionPrimitive`, `X.standard`) and the Step1 definition
  of `A_Omega`, and records two facts:

  1. There is a native state `X` whose actualized set `A_Omega X` is
     nonempty AND proper (a singleton), while every configuration remains
     L3-admissible. Its nonemptiness is witnessed constructively; the proof
     does not use `bridge_principle` (see the `#print axioms` audit in the
     verification report).

  2. There is also a native state whose actualized set is empty. So the
     universal nonemptiness asserted by `bridge_principle` is a substantive
     postulate over the Step0/Step1 definitions, not a definitional
     consequence of them.

  Scope note: these are models of the native Step0/Step1 assumptions. They
  are not models of the full LRT physics programme (Steps 2+ impose further
  structure), and nothing here decides the physical eligibility question.
-/

import LrtFormalization.Step1_Constitution

namespace LRT.NativeBridgeWitness

open LRT.Step0 LRT.Step1

attribute [local instance] Classical.propDecidable

/-- The action that actualizes exactly one configuration `a₀`. -/
noncomputable def singletonAction (a₀ : I) : ActionPrimitive :=
  ActionPrimitive.mk_default fun c =>
    if c = a₀ then ActualityValue.actual else ActualityValue.nonActual

/-- The native state carrying the singleton action. -/
noncomputable def singletonX (a₀ : I) : X :=
  X.standard (singletonAction a₀)

theorem singletonX_action (a₀ : I) :
    (singletonX a₀).action = singletonAction a₀ :=
  rfl

theorem singletonAction_apply (a₀ c : I) :
    (singletonAction a₀).A c =
      (if c = a₀ then ActualityValue.actual else ActualityValue.nonActual) :=
  rfl

theorem aOmega_singletonX (a₀ : I) : A_Omega (singletonX a₀) = {a₀} := by
  ext c
  simp only [A_Omega, Set.mem_setOf_eq, Set.mem_singleton_iff,
    singletonX_action, singletonAction_apply]
  constructor
  · intro h
    by_cases hca : c = a₀
    · exact hca
    · simp [hca] at h
  · intro h
    simp [h]

/-- Native witness: a nonempty, proper actualized subset of the admissible
    configurations, with every configuration admissible. Nonemptiness here is
    constructive and does not depend on `bridge_principle`. -/
theorem exists_native_proper_nonempty_actual :
    ∃ X₀ : X, Nonempty (A_Omega X₀) ∧ A_Omega X₀ ≠ Set.univ ∧
      ∀ c : I, Admissible c := by
  obtain ⟨a₀, b, hab⟩ := exists_distinct_configurations
  refine ⟨singletonX a₀, ⟨a₀, ?_⟩, ?_, all_configs_admissible⟩
  · rw [aOmega_singletonX]
    exact Set.mem_singleton a₀
  · rw [aOmega_singletonX]
    intro h
    have hb : b ∈ ({a₀} : Set I) := h ▸ Set.mem_univ b
    have hba : b = a₀ := by simpa using hb
    exact hab hba.symm

/-- The action that actualizes nothing. -/
noncomputable def noneAction : ActionPrimitive :=
  ActionPrimitive.mk_default fun _ => ActualityValue.nonActual

theorem noneX_action_apply (c : I) :
    (X.standard noneAction).action.A c = ActualityValue.nonActual :=
  rfl

theorem aOmega_noneX : A_Omega (X.standard noneAction) = ∅ := by
  ext c
  simp only [A_Omega, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rw [noneX_action_apply]
  simp

end LRT.NativeBridgeWitness
