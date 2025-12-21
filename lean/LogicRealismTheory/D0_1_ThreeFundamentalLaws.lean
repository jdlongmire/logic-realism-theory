/-
D0.1: Three Fundamental Laws of Logic

LRT Tier: 0 (Primitive, Self-Grounding)
Stage: Lean (from Notebook)
Status: Complete
Depends On: None (primitive)

This module formalizes the Three Fundamental Laws of Logic (L₃) as they appear
in Logic Realism Theory. In Lean 4 (based on classical logic), these laws are
foundational—they are built into the system itself.

The formalization serves to:
1. Make the laws explicit and named for LRT documentation
2. Demonstrate they hold in the formal system
3. Provide a foundation for subsequent derivations

Note: These are not "proven" from simpler principles—they ARE the simplest
principles. In classical Lean, they are axiomatic/definitional.

## Interpretation Boundary

This file formalizes logical constraints at the level of propositions.
Ontological interpretation (that reality obeys these laws) is external to
the formal system. Lean proves structural relations; LRT claims ontological
significance in the theory documents.

## Classical Dependency

| Law | Intuitionistically Valid | Classical Required |
|-----|--------------------------|-------------------|
| L₁ (Identity) | ✓ Yes | No |
| L₂ (Non-Contradiction) | ✓ Yes | No |
| L₃ (Excluded Middle) | No | ✓ Yes |

Excluded Middle requires `Classical.em` in Lean. This is intentional—LRT
claims L₃ applies to actualized reality, which is classical.
-/

import Mathlib.Logic.Basic

namespace LRT.D0_1

/-!
## The Three Fundamental Laws of Logic (L₃)

These laws are ontologically constitutive in LRT: they constrain what can be
actual, not merely what can be known or represented.
-/

section Definitions

/-- L₁: Law of Identity - Every thing is identical to itself -/
theorem law_of_identity (A : α) : A = A := rfl

/-- L₂: Law of Non-Contradiction - No proposition is both true and false -/
theorem law_of_non_contradiction (P : Prop) : ¬(P ∧ ¬P) := fun ⟨hp, hnp⟩ => hnp hp

/-- L₃: Law of Excluded Middle - Every proposition is either true or false -/
theorem law_of_excluded_middle (P : Prop) : P ∨ ¬P := Classical.em P

end Definitions

/-!
## Named Forms for LRT Reference

Standard naming conventions for cross-referencing with theory documents.
-/

section NamedForms

/-- L₁ in LRT notation -/
abbrev L₁ := @law_of_identity

/-- L₂ in LRT notation -/
abbrev L₂ := @law_of_non_contradiction

/-- L₃ in LRT notation -/
abbrev L₃ := @law_of_excluded_middle

end NamedForms

/-!
## Self-Grounding Property

The self-grounding nature of L₃ cannot be fully captured in a formal system
(Lean assumes classical logic). However, we can demonstrate key consequences.
-/

section SelfGrounding

/-- Any denial of L₁ presupposes identity (demonstrated by type structure) -/
example (A : α) : A = A := rfl

/-- Contradiction leads to anything (explosion principle) -/
theorem explosion (P Q : Prop) (h : P ∧ ¬P) : Q := absurd h.1 h.2

/-- L₂ is equivalent to: contradiction implies false -/
theorem non_contradiction_equiv (P : Prop) : ¬(P ∧ ¬P) ↔ (P ∧ ¬P → False) :=
  Iff.rfl

/-- L₃ enables decidability of propositions (in classical logic) -/
noncomputable def excluded_middle_enables_decidability (P : Prop) : Decidable P :=
  Classical.dec P

end SelfGrounding

/-!
## Key Consequences

Theorems that follow immediately from L₃.
-/

section Consequences

/-- Double negation elimination (classical) -/
theorem double_negation_elim (P : Prop) : ¬¬P → P := Classical.byContradiction

/-- Proof by contradiction (classical) -/
theorem by_contradiction (P : Prop) : (¬P → False) → P := Classical.byContradiction

/-- De Morgan's laws -/
theorem de_morgan_and (P Q : Prop) : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := not_and_or

theorem de_morgan_or (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := not_or

/-- Law of non-contradiction in disjunctive form -/
theorem non_contradiction_disj (P : Prop) : ¬P ∨ ¬¬P := by
  cases Classical.em P with
  | inl hp => right; exact fun hnp => hnp hp
  | inr hnp => left; exact hnp

end Consequences

/-!
## Computational Verification

Simple computational demonstrations (mirrors notebook Python cells).
-/

section Verification

/-- Identity holds for natural numbers -/
example : (42 : ℕ) = 42 := rfl

/-- Identity holds for any type -/
example (x : α) : x = x := rfl

/-- Non-contradiction: True ∧ ¬True is False -/
example : ¬(True ∧ ¬True) := fun ⟨_, hf⟩ => hf trivial

/-- Excluded middle: True ∨ ¬True -/
example : True ∨ ¬True := Or.inl trivial

/-- Excluded middle: False ∨ ¬False -/
example : False ∨ ¬False := Or.inr id

end Verification

/-!
## Status

CONFIDENCE: HIGH
All theorems proven (no sorry statements).
L₃ are foundational in Lean's classical logic.

Quality Gates:
✓ No sorry statements
✓ No axiom declarations (uses Lean/Mathlib foundations)
✓ All theorems compile
✓ Mirrors D0.1 notebook structure
-/

end LRT.D0_1
