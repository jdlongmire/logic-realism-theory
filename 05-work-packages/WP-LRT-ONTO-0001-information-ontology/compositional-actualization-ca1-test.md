# CA-1: compositional actualization and its real-quantum countermodel

Status: RESEARCH / CANDIDATE REJECTED AS SUFFICIENT FOR TOMOGRAPHY
Date: 2026-11-08
No canonical axiom, theorem label, or Lean proof is changed.

## Candidate CA-1 (product closure)

For physical systems A and B with admissible states S_A, S_B and actualization selections A_A, A_B, A_AB, assume a product embedding `⊗:S_A×S_B→S_AB`. The proposed compositional actualization principle is:

`CA1: (A_A(s)=actual ∧ A_B(t)=actual) ⇒ A_AB(s⊗t)=actual.`

It states that jointly actualizable subsystem states have an actualizable composite product. It refers to actualization and composition, not measurement effects. For clarity, the word *actualizable* is here represented by a binary selection predicate; if A marks only the single obtaining universe-history, CA1 would require a different modal formulation. This is a conceptual limitation of the proposal.

## Countermodel

Take finite-dimensional real quantum systems. A single rebit state is a 2×2 real symmetric positive semidefinite matrix of trace one. The composite of two rebits is the full space of 4×4 real symmetric positive semidefinite matrices of trace one. The product `s⊗t` is a legitimate composite state.

Let the actualization predicates mark **every** allowed state actual. Then CA1 holds immediately, product composition is well-defined, and the selection sets are nonempty. Yet the two distinct composite states
`ρ±=(I₄±u(J⊗J))/4`, `0<u≤1`, with `J=[[0,-1],[1,0]]`, agree on all product-effect probabilities. The composite is not locally tomographic.

Therefore CA1 does **not** imply local tomography. This is a countermodel to a universal mathematical implication from CA1 and ordinary real-quantum state/effect composition. It does not assert that marking every state actual is a metaphysically coherent interpretation of one realized history; it tests the formal weakness of the selection predicate as currently defined.

## Stronger candidate CA-2 (hereditary decomposition)

Every actual composite state is a convex mixture of product states:
`CA2: A_AB(ρ)=actual ⇒ ρ∈conv{ s⊗t : s∈S_A, t∈S_B }`.

This rules out entangled *actual* states. If the whole normalized composite state space is assumed to equal the convex hull of product states, and if local effects span the dual spaces of their respective subsystem state spaces, product-effect statistics separate composite states in the induced tensor-product vector space. The last conclusion relies on additional local effect-separation and composite representation hypotheses, not on CA2 alone.

CA2 is unattractive for LRT as a universal physical postulate because quantum entangled states are empirically important and are explicitly part of the intended reconstruction. A selection rule that excludes all entangled actual states would undermine the program's target.

## Stronger candidate CA-3 (compositional identity faithfulness)

Require every composite distinction to be witnessed by an actualizable interaction with separately accessible subsystem records. This could admit entanglement, but without a precise restriction on allowed interactions and records it risks paraphrasing local tomography. Global measurements that deposit local readouts do **not** suffice: a joint interaction can detect `J⊗J` while the original product-effect statistics still cannot.

A genuine CA-3 theorem must prove that accessible records can be generated without a prior nonlocal coupling or a measurement-completeness premise equivalent to tomography.

## Decision table

| Candidate | Independent of product-effect statistics? | Rebit obstruction excluded? | Suitable as established LRT law? |
|---|---|---|---|
| CA1 product closure | Yes | No | No |
| CA2 separable-only actualization | Yes as stated | Can exclude entangled sector only with extra spanning/representation assumptions | No: conflicts with target entanglement |
| CA3 accessible subsystem records | Not yet formally defined | Unknown | No |

## Next proof obligation

Seek a **non-circular, entanglement-compatible** compositional actualization principle. State its exact domain (actual versus possible states), prove it implies `(S_AB−S_AB)∩W^⊥={0}`, and test it against the real-quantum model and other GPTs. In particular, do not conflate 'global measurement with local readouts' with 'product-effect tomography'.

## Primary and internal sources

- Masanes and Müller (2011), *A derivation of quantum theory from physical requirements*, https://arxiv.org/abs/1004.1483 (local tomography is an independent requirement).
- `formalization/LrtFormalization/Step0_Primitives.lean`; `formalization/LrtFormalization/Step1_Constitution.lean`.
- `05-work-packages/WP-LRT-ONTO-0001-information-ontology/actualization-tomography-independence.md`.
- `05-work-packages/WP-LRT-ONTO-0001-information-ontology/compositional-interaction-separation-theorem.md`.

## Validation

The countermodel follows from direct linear algebra: `Tr(JE)=0` for every symmetric 2×2 local effect, and `J⊗J` is symmetric. This document contains an analytic counterexample, not a Lean build or an independently run numerical computation. No change to canonical epistemic status is proposed without owner review.
