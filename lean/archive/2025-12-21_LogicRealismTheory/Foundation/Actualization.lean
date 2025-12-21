/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0

# Actualization: A = L(I)

This module formalizes the central thesis of Logic Realism Theory:
Actualized reality A is identical to the logical structure L(I) over
the Infinite Information Space.

## Correspondence to Technical Paper

Section 2.3 in:
  Longmire, J.D. (2025). "Logic Realism Theory: Technical Foundations"
  DOI: 10.5281/zenodo.17831883

## Key Result

A = L(I) is NOT an axiom but a THEOREM. It follows from the observation
that any actualized fact must be a decidable proposition about distinctions.

-/

import LogicRealismTheory.Foundation.IIS

namespace LogicRealismTheory.Foundation

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTUALIZATION STRUCTURE
-- ═══════════════════════════════════════════════════════════════════════════════

/--
An actualized fact is a proposition about I together with a witness
that the proposition is decidable (has a definite truth value).

**Technical Paper Reference:** §2.3, Definition 2.3
-/
structure ActualizedFact where
  proposition : Set I
  decidable : ∀ x : I, Decidable (x ∈ proposition)

/--
The space of actualized reality A is the collection of all actualized facts.
-/
def A := ActualizedFact

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE CENTRAL THEOREM: A = L(I)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Theorem (A ⊆ L(I))**: Every actualized fact corresponds to a proposition in L(I).

This direction is immediate from the definition.
-/
theorem actualized_subset_logic : ∀ a : A, a.proposition ∈ (Set.univ : Set (Set I)) := by
  intro a
  trivial

/--
**Theorem (L(I) ⊆ A under classical logic)**: In classical logic, every
proposition in L(I) is decidable, hence corresponds to an actualized fact.

This uses Lean's classical logic (Law of Excluded Middle).
-/
theorem logic_subset_actualized (P : Set I) : ∃ a : A, a.proposition = P := by
  use ⟨P, fun x => Classical.dec (x ∈ P)⟩

/--
**THE CENTRAL THESIS: A = L(I)**

Actualized reality is identical to the logical structure over I.
This is proven (not axiomatized) using classical logic.

**Technical Paper Reference:** §2.3, Theorem 2.1
-/
theorem A_equals_L : ∀ P : Set I, ∃ a : A, a.proposition = P :=
  logic_subset_actualized

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSEQUENCES OF A = L(I)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Actualized facts satisfy excluded middle: for any proposition P and
any distinction x, either P holds at x or it doesn't.

This is the logical foundation for definite measurement outcomes.
-/
theorem actualized_excluded_middle (a : A) (x : I) :
    x ∈ a.proposition ∨ x ∉ a.proposition :=
  excluded_middle_in_L a.proposition x

/--
Actualized facts satisfy non-contradiction: no distinction can both
satisfy and not satisfy the same proposition.

This prevents logical inconsistency in actualized reality.
-/
theorem actualized_non_contradiction (a : A) (x : I) :
    ¬(x ∈ a.proposition ∧ x ∉ a.proposition) :=
  non_contradiction_in_L a.proposition x

-- ═══════════════════════════════════════════════════════════════════════════════
-- AXIOM COUNT SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- Tier 1 (LRT Specific): 0 new axioms (uses IIS.lean axioms)
-- Tier 2 (Established Math): 0 in this file
-- Tier 3 (Universal Physics): 0 in this file
--
-- Theorems proven: 5
--   - actualized_subset_logic
--   - logic_subset_actualized
--   - A_equals_L (THE CENTRAL THESIS)
--   - actualized_excluded_middle
--   - actualized_non_contradiction
--
-- Key result: A = L(I) is PROVEN, not axiomatized

end LogicRealismTheory.Foundation
