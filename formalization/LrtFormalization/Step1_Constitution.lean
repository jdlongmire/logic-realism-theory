/-
  Logic Realism Theory — Step 1: Transcendental Constitution

  Formalizes: X ⊣ A_Ω (X grounds the total actual structure)

  The Bridge Principle: X transcendentally constitutes A_Ω because
  - X is ontologically prior to A_Ω
  - A_Ω obtains in virtue of X
  - The grounding relation is non-causal and non-temporal

  Author: James D. Longmire
  Date: 2026-03-13
  Status: Foundation
  Epistemic Status: ESTABLISHED (within LRT framework, given Bridge Principle)
-/

import LrtFormalization.Step0_Primitives

namespace LRT.Step1

open LRT.Step0

/-! ## Part I: The Total Actual Structure A_Ω

A_Ω is the set of all configurations that survive the L₃ admissibility filter.
-/

/-! ### Admissibility

A configuration is admissible if it satisfies L₃.

NOTE: All configurations in I are type-level admissible.
L₃ operates at the propositional level, not configuration level.
Filtering is post-hoc via A: the actualization primitive selects
which admissible configurations become actual.

This is intentional: I∞ is the maximal distinguishability substrate,
while A performs ontological selection within that substrate.

The `Admissible` predicate is defined in Step0 via L3Admissible.
Here we confirm all configurations satisfy it.
-/

/-- All configurations in I are admissible (Step0.Admissible) -/
theorem all_configs_step1_admissible (c : I) : Step0.Admissible c :=
  Step0.all_configs_admissible c

/-- The total actual structure: all configurations marked actual by A -/
def A_Omega (X : Step0.X) : Set I :=
  { c : I | X.action.A c = ActualityValue.actual }

-- A_Ω is the structural expression of X at Level 2.
-- While X is the primitive ontic state (Level 1: *why* does actuality obtain?),
-- A_Ω is *what* actuality looks like.

/-! ## Part II: The Bridge Principle

The Bridge Principle is an explicit axiom connecting X to A_Ω.
It is not derivable within standard grounding frameworks alone.
-/

/-- The Bridge Principle: X grounds A_Ω.

This is a Tier 2 axiom. It states that the existence and structure of A_Ω
is constituted by X. In grounding-theoretic terms: A_Ω obtains in virtue of X.
-/
axiom bridge_principle (X : Step0.X) : Nonempty (A_Omega X)

/-- A_Ω is uniquely determined by X -/
theorem A_Omega_determined_by_X (X₁ X₂ : Step0.X)
    (h_same_action : X₁.action.A = X₂.action.A) :
    A_Omega X₁ = A_Omega X₂ := by
  unfold A_Omega
  ext c
  simp [h_same_action]

/-! ## Part III: Grounding Properties

Properties of the X ⊣ A_Ω relation (Fine/Schaffer grounding).

- X is ontologically prior to A_Ω: A_Ω is defined in terms of X, not vice versa.
- The grounding is non-causal: no temporal parameter at this level.
- The grounding is constitutive: A_Omega is a function of X.
-/

/-! ## Part IV: The Constitution Theorem

Step 1 of the derivation chain.
-/

/-- **Step 1 Constitution Theorem:**
    X transcendentally constitutes A_Ω.

    Given X, we can construct A_Ω, and A_Ω is non-empty (by Bridge Principle).
-/
theorem step1_constitution (X : Step0.X) :
    ∃ (AΩ : Set I), AΩ = A_Omega X ∧ Nonempty AΩ :=
  ⟨A_Omega X, rfl, bridge_principle X⟩

-- Note: A_Ω being non-empty doesn't mean it's infinite.
-- That depends on A. But the *potential* from I∞ is infinite.

/-- Every actual configuration comes from I∞ (type closure) -/
theorem actual_configs_in_I (X : Step0.X) (c : I) (_h : c ∈ A_Omega X) : c ∈ (Set.univ : Set I) :=
  Set.mem_univ c

/-- A_Ω is a subset of I (strengthened form) -/
theorem A_Omega_subset_I (X : Step0.X) : A_Omega X ⊆ Set.univ := Set.subset_univ _

/-- If A_Ω is empty, no configuration is actual -/
theorem empty_A_Omega_means_nothing_actual (X : Step0.X) (h : A_Omega X = ∅) :
    ∀ c : I, X.action.A c = ActualityValue.nonActual := by
  intro c
  have : c ∉ A_Omega X := by simp [h]
  unfold A_Omega at this
  simp at this
  cases X.action.determinate c with
  | inl h_act => exact absurd h_act this
  | inr h_non => exact h_non

/-! ## Part V: Bridge Principle Motivation

The Bridge Principle is axiomatic, but philosophically motivated:
- Empirical fact: something exists (actuality is non-empty)
- L₃ alone cannot force existence (logic doesn't entail ontology)
- A alone doesn't guarantee non-trivial selection
- The combination X = [L₃ : I∞ : A] is co-constitutive of actuality

Future work: Explore whether empty A_Ω leads to contradiction with
L₃ (distinguishability requires something to be distinguished).
See `empty_A_Omega_means_nothing_actual` above.
-/

/-! ## Status

CONFIDENCE: HIGH (Grok review: 75-85% sufficiency for downstream)
- A_Omega: Defined (set comprehension)
- Bridge Principle: Tier 2 axiom (necessary philosophical input)
- step1_constitution: Proven from definitions + axiom

The Bridge Principle is the key philosophical axiom of Step 1.
Without it, we cannot establish that A_Ω is non-empty.
-/

-- Axiom audit: uncomment to verify dependencies
-- #print axioms bridge_principle
-- #print axioms step1_constitution
-- #print axioms A_Omega_determined_by_X

end LRT.Step1
