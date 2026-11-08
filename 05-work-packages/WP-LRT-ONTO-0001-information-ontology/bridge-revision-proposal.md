# Bridge identity: controlled canonical wording proposal
Status: PROPOSED / NOT ADOPTED
Date: 2026-11-08

## Recommended semantic decision
Preserve the three primitives χ = [L3 : I∞ : A] and define logical admissibility separately from obtaining:
- C := {i ∈ I∞ | L3-admissible(i)}.
- AΩ := {i ∈ C | A(i) = actual}.
- Consequently AΩ ⊆ C, without asserting AΩ = C.

If I∞ is already typed as admissible configurations, C = I∞ in that formalization; that is a modeling choice, not a metaphysical theorem that every representable content is coherent. Physical eligibility P and its possible additional predicate K remain research questions and must not be silently added as a fourth primitive.

## Suggested README replacement (pending theory-owner acceptance)
Replace the literal equation AΩ = L3(I∞) and the sentence claiming actuality coincides with all logically admissible configurations with:

> Let C := L3(I∞) denote the logically admissible configurations. The actualized domain is AΩ := {i ∈ C | A(i) = actual}. Thus AΩ ⊆ C. L3 constrains admissibility; the irreducible primitive A determines which admissible configurations obtain. The grounding claim χ ⊢ AΩ remains an ontological commitment rather than a mathematical entailment from L3 alone.

This proposal preserves the selection semantics of [Lean Step1](../../formalization/LrtFormalization/Step1_Constitution.lean) and the necessary/non-sufficient distinction in [prephysics](../../theory/000-prephysics-conditions.md).

## Evidence and formal counterexample
[bridge-countermodel.lean](bridge-countermodel.lean) is a candidate Lean file representing two admissible configurations, only one actual. It is a finite semantic counterexample to unconditional extensional equality. It does not satisfy the infinite-I axiom in Step0 and therefore is not a full model of LRT. An infinite extension would require a separate proof/model.

The existing Lean [Step0](../../formalization/LrtFormalization/Step0_Primitives.lean) defines A as I → ActualityValue, while [Step1](../../formalization/LrtFormalization/Step1_Constitution.lean) defines A_Omega X as the selected subset and separately assumes nonemptiness via bridge_principle. The [entailment audit](../WP-LRT-ENT-0001-entailment-audit/entailment-matrix.md) must therefore distinguish definitional selection, nonempty-actuality axiom, and ontology-to-physics bridge premises.

## Validation and approval gate
- Lean compiler/build: NOT RUN. The model is proposed code, not a verified theorem.
- Canonical README/core physics: NOT CHANGED.
- Theory-owner acceptance required for any canonical revision.
- If approved, revise README, core physics §1.2, cross-references, and entailment step 0 together; check downstream Lean statements and run Lean build.
