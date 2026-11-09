# Actualization selection cannot by itself enforce local tomography

Status: RESEARCH / MODEL-THEORETIC INDEPENDENCE ARGUMENT
Date: 2026-11-08
Scope: no new primitive, axiom, Lean file, or canonical theorem label.

## Question

Can the binary actualization primitive A, whose only native Step0 structure is a configuration-to-actuality-value function, independently exclude the real-quantum J⊗J degree of freedom and thereby force local tomography?

## Result: no, given only the currently stated selection semantics

The corrected bridge is C=L3(I∞) and AΩ={i∈C | A(i)=actual}. Step0's action primitive supplies a binary valuation on configurations; Step1 defines AΩ by its preimage. The nonemptiness axiom `bridge_principle` does not constrain composite effects, tensor products, or product-effect separation.

**Independence argument.** Fix an admissible operational model M with a composite state space S_AB and a nonzero product-effect-invisible difference d=s−t. Enlarge the information configuration domain, if needed, to an infinite disjoint union of configurations representing M and unused configurations. Define A so that s and t are both actual, and choose at least one actual configuration. This satisfies binary selection and nonemptiness. The same local product effects remain unable to distinguish s and t. Thus no implication from binary selection plus nonemptiness to local tomography holds for the class of operational models admitting this embedding. The argument does not claim the enriched M is a model of every additional LRT physical axiom.

**Selection sensitivity.** One could instead select only s among the pair, making this particular witness disappear from the actual subset. That is a contingent selection choice, not a theorem that *all* allowed actual composites are locally tomographic. To guarantee tomography for every permitted A, the selection law must restrict which configurations can jointly obtain, or impose independent structure on the composite state/effect spaces.

## Concrete witness inherited from PR #104

For two rebits J=[[0,-1],[1,0]], K=J⊗J, and ρ±=(I₄±tK)/4, 0<t≤1. They are distinct legitimate global states with identical probabilities for every real-symmetric local product effect, yet the global effect (I₄+K)/2 separates them. Let A mark both as actual. All conditions on A listed above hold, while local tomography fails.

## Formal dependency boundary

Native Step0: `ActionPrimitive.A : I → ActualityValue`.
Native Step1: `A_Omega X := {c : I | X.action.A c = ActualityValue.actual}`; `bridge_principle X : Nonempty (A_Omega X)`.
Neither definition refers to `S_AB`, `E_A`, `E_B`, a tensor-product structure, or the product-effect span W. Therefore no proof of W's separation property follows *without* additional premises connecting the two languages.

This is a semantic independence argument, not a new Lean theorem. The separate Muse native Step0/Step1 formalization remains the authority for verified Lean dependency claims.

## What could change the result?

1. **Nontrivial selection dynamics:** A physical law for A forbidding jointly actual states with differences in the product-effect annihilator. This must be stated without presupposing W or tomography if the goal is foundational explanation.
2. **Compositional closure:** A theory of which subsystem and interaction configurations may actualize jointly. Derive a theorem excluding hidden composite degrees of freedom from this principle.
3. **Operational domain restriction:** Identify the physical-state domain with classes distinguished by product effects. This makes tomography true by construction, but is a quotient/definition and cannot establish why nature selects that domain.

## Falsification-oriented next experiment

Attempt a minimal compositional actualization axiom CA that refers to subsystem compatibility and composition, not measurement effects. Construct a countermodel with the two-rebit J⊗J sector satisfying CA. If it survives, CA is insufficient. If it is excluded, prove that exclusion and then test for other nonlocally tomographic GPT countermodels. Track every extra premise.

## Disposition

**NOT DERIVED:** binary actualization and nonempty actuality do not imply local tomography. Maintain the current `REQUIRES_NEW_PREMISE` classification. Do not amend the three-primitive ontology or assert that the 2011 Masanes–Müller reconstruction derives tomography: it explicitly assumes it.

References: `formalization/LrtFormalization/Step0_Primitives.lean`; `formalization/LrtFormalization/Step1_Constitution.lean`; `05-work-packages/WP-LRT-ONTO-0001-information-ontology/local-tomography-real-quantum-countermodel.md`; `05-work-packages/WP-LRT-ONTO-0001-information-ontology/compositional-interaction-separation-theorem.md`.
