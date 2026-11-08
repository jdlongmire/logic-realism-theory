/-!
# Bridge selection countermodel (WP-LRT-ONTO-0001)

This countermodel has an infinite admissible configuration domain and a
nonempty proper actualized subset. It is a semantic counterexample to
the assertion that actualized configurations must equal all admissible
configurations. It does not refute the LRT grounding ontology.

No additional axioms or sorry are introduced.
-/
import Mathlib.Data.Set.Basic

namespace LRT.BridgeSelectionCountermodel

def admissible : Set Nat := Set.univ
def actual : Set Nat := {n | n = 0}

theorem zero_actual : 0 ∈ actual := by
  simp [actual]

theorem one_admissible : 1 ∈ admissible := by
  simp [admissible]

theorem one_not_actual : 1 ∉ actual := by
  simp [actual]

theorem actual_subset_admissible : actual ⊆ admissible := by
  intro n hn
  simp [admissible]

theorem actual_ne_admissible : actual ≠ admissible := by
  intro h
  have hmem : 1 ∈ actual := by
    rw [h]
    exact one_admissible
  exact one_not_actual hmem

theorem actual_nonempty : actual.Nonempty := by
  exact ⟨0, zero_actual⟩

end LRT.BridgeSelectionCountermodel
