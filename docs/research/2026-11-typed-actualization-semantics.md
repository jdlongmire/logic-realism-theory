# Typed actualization semantics: proposed bridge refinement
Status: PROPOSED FORMAL SPECIFICATION; NOT CANONICAL
Date: 2026-11-08
Decision under examination: distinguish logical eligibility from actualization (Option B of the [reconciliation audit](2026-11-bridge-identity-nlc-reconciliation-audit.md)).

## Problem and canonical evidence
The [prephysics argument](../../theory/000-prephysics-conditions.md) distinguishes admissibility, informational structure, and actualization, stating that consistency alone does not entail manifestation. [Core physics](../../theory/100-LRT-CORE-PHYSICS.md) specifies χ = [L3 : I∞ : A], and simultaneously writes AΩ := L3(I∞), describing AΩ as all L3-admissible configurations. A literal extensional reading would collapse coherent possibilities into actualities. The [README](../../README.md) repeats that reading. The [entailment matrix](../../05-work-packages/WP-LRT-ENT-0001-entailment-audit/entailment-matrix.md) labels the bridge ontological and conditional.

## Typed domains and predicates
Let U denote the set of representable informational descriptions, not assumed to be a physically realized set. A representation may be a consistent vehicle depicting inconsistent content.

Let C = {x in U | Coherent(x)} be coherent *represented configurations*, distinct from mere coherent encoding vehicles. L3 is a logical admissibility predicate applied to the represented configuration, with Coherent(x) iff L3(x) under the chosen classical interpretation.

Let P = {x in C | Eligible(x)} denote physically eligible configurations. Eligibility may depend on additional physical constraints K, not specified by L3 alone. K is an **unresolved primitive/derived target**, not a discovered law.

Let AΩ = {x in P | Obtains(x)} denote configurations obtaining in the actual world or history, indexed by a specified context if time and possible-world distinctions matter.

Therefore AΩ ⊆ P ⊆ C ⊆ U.

The action primitive A must distinguish **selection/obtaining** from **eligibility**. Proposed notation:
C := L3(U)
P := {x in C : K(x)}
AΩ := Act_A(P)
with Act_A(P) ⊆ P.
Here Act_A is a *typed selection/actualization operator*, not necessarily a deterministic or temporal algorithm. The subscript identifies the primitive and is not an extra independent axiom.

## Bridge proposal and its limits
Proposed replacement for literal equality:
χ = [L3 : U : A] ⊢ AΩ,
AΩ = Act_A(K(L3(U))) ⊆ L3(U).
This is a **proposed revision**, not an established derivation. If K is not independently grounded, the expression merely displays unresolved constraints. No assertion is made that every coherent possibility is physically eligible or that every eligible possibility obtains.

An alternative conservative reading keeps the historical expression AΩ := L3(I∞) as shorthand for a *constraint on the form of actuality*, not extensional equality. This requires an explicit notation convention and is not equivalent to the typed proposal.

## Minimal countermodel exposing the problem
Take U={u,v}, both L3-admissible; suppose only u obtains. Then C={u,v}, AΩ={u}. The prephysics principle is satisfied. The literal AΩ=L3(U) is false. The model shows the two statements are not jointly entailed without a further postulate that all coherent configurations obtain. It does **not** disprove the broader LRT ontology.

## Interaction with entanglement
The [existing entanglement treatment](../../theory/104-LRT-ENTANGLEMENT.md) places nonseparable configurations in I∞ and Boolean outcomes in AΩ. Under typed semantics, the quantum state belongs to an admissible/eligible domain and realized outcomes to an actualization domain. An entangled state can remain structurally nonseparable without implying superluminal causal influence. However, tensor products, the Born rule, no-signaling, and Tsirelson's bound remain independent derivation obligations. Distance-independent logical consistency (NLC-1) alone does not imply them.

## Dependency and acceptance checklist
- [ ] Decide whether I∞ means all representations, all coherent possibilities, or all physically eligible states; avoid silent redefinition.
- [ ] Specify how nonphysical informational substance relates to U and the vehicle/content distinction.
- [ ] Determine whether K is fundamental, emergent, or eliminable, with independent justification.
- [ ] Clarify whether Act_A applies to configurations, events, histories, or measurement outcomes.
- [ ] Reconcile existing README, core physics, prephysics, entanglement, and formalization bridge statements.
- [ ] Trace Lean theorem/axiom dependencies before modifying signatures or claimed entailments.
- [ ] Verify original primary literature and mark borrowed mathematical assumptions.
- [ ] Obtain explicit theory-owner acceptance of bridge semantics before changing canonical statements.

## Epistemic classification
Domain hierarchy: **proposed definitions**. Minimal countermodel: **valid relative to stipulated interpretation**. Actualization necessity: **argued metaphysical premise**. Quantum explanatory consequence: **not derived**.
