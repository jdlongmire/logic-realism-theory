# Ontology and actualization: baseline and claim matrix
Status: INITIAL AUDIT / 2026-11-08
Work package: WP-LRT-ONTO-0001
All file links are relative to this work package.

| ID | Proposition | Classification | Source | Finding |
|---|---|---|---|---|
| ONTO-01 | χ = [L3 : I∞ : A] is a three-primitive ontology | AXIOMATIC / ONTOLOGICAL | [README](../../README.md), [core physics](../../theory/100-LRT-CORE-PHYSICS.md) | Baseline retained; sufficiency requires separate argument |
| ONTO-02 | Logical admissibility and information do not suffice for manifestation | ARGUED | [prephysics](../../theory/000-prephysics-conditions.md), sections 5-6 | Supports irreducible actualization |
| ONTO-03 | AΩ = L3(I∞) as literal set equality | CONTESTED | [README](../../README.md), [core physics](../../theory/100-LRT-CORE-PHYSICS.md), §1.2 | Appears inconsistent with selecting only some admissible configurations |
| ONTO-04 | AΩ(X) = {c : I | X.action.A c = actual} | FORMAL DEFINITION | [Lean Step1](../../formalization/LrtFormalization/Step1_Constitution.lean) | Existing formalization implements selection semantics |
| ONTO-05 | All I configurations are admissible under current Lean predicate | FORMAL THEOREM | [Lean Step1](../../formalization/LrtFormalization/Step1_Constitution.lean) | Admissibility filter is not selective in this model |
| ONTO-06 | Nonempty actualized domain | IMPORTED AXIOM | [Lean Step1](../../formalization/LrtFormalization/Step1_Constitution.lean) | bridge_principle asserts Nonempty (A_Omega X); not independently derived |
| ONTO-07 | Every actual configuration has determinate identity | FORMAL THEOREM / WEAK EXPLANATORY NOVELTY | [Lean Step2](../../formalization/LrtFormalization/Step2_DeterminateIdentity.lean) | Stronger theorem all_configs_determinate holds without actualization premise |
| ONTO-08 | Coherence ⊇ physical eligibility ⊇ actuality | PROPOSED TAXONOMY | [typed proposal](../../docs/research/2026-11-typed-actualization-semantics.md) | Eligibility K not established by L3 |
| ONTO-09 | Entanglement follows from nonspatial logical unity | CONJECTURAL | [entanglement paper](../../theory/104-LRT-ENTANGLEMENT.md), [NLC note](../../docs/research/2026-11-information-ontology-and-nonlocal-coherence.md) | Must audit tensor/Hilbert imports and quantum correlation bound |
| ONTO-10 | Step0-2 constitute independent physical derivation | NOT ESTABLISHED | [Lean Step0](../../formalization/LrtFormalization/Step0_Primitives.lean), [Step1](../../formalization/LrtFormalization/Step1_Constitution.lean), [Step2](../../formalization/LrtFormalization/Step2_DeterminateIdentity.lean) | Definitions, classical logic and bridge axiom suffice for displayed results; physics inference remains argued |

## Minimal countermodel
Let I={u,v}; both satisfy the model's admissibility predicate. Let A(u)=actual and A(v)=nonActual. Then AΩ={u}, while L3(I)={u,v}. The Lean selection definition permits this; the literal bridge equality does not. An infinite information domain can extend the example by adding arbitrary nonactual configurations. This is a semantic countermodel, not a compiled Lean theorem.

## Dependencies and acceptance gate
Coordinate with [WP-LRT-ENT-0001](../WP-LRT-ENT-0001-entailment-audit/entailment-matrix.md). Resolve whether L3(I∞) denotes admissibility, selected actuality, or a constitutive characterization. No formal or prose rewrite is authorized by this matrix.
