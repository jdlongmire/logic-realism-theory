# Logic-priority dependency protocol for LRT reconstruction

Status: RESEARCH METHODOLOGY / OWNER-CLARIFIED FOUNDATIONAL COMMITMENT
Date: 2026-11-08
Scope: ontology work package; no changes to canonical equations, axioms, Lean, or epistemic status.

## Foundational commitment

In LRT, the Three Fundamental Laws of Logic (3FLL: identity, non-contradiction, excluded middle) are logically and ontologically prior to the mathematical descriptions of physical reality. Mathematics is a representational language for admissible structure; a mathematical model must not silently become an ontological primitive. The primitive triad remains `χ=[L3:I∞:A]`, with A understood as the ontological operation making transitions possible.

**Three different dependency claims must not be conflated.**
1. Logical presupposition: ordinary classical mathematical proofs employ logical principles.
2. Ontological priority: LRT proposes that the applicable mathematical structures express constraints on actuality grounded in 3FLL and Action.
3. Formal entailment: a specific structure (natural numbers, real or complex fields, tensor products, Hilbert space, probability, dynamics) is a theorem from stated LRT premises.

The first does not prove the third. The second is a programmatic metaphysical commitment. A deductive reconstruction must explicitly establish the third.

## Dependency discipline

For every proposed reconstruction step, record:
- **Ontological inputs:** exactly which 3FLL/I∞/A concepts are used, and whether they are primitive or defined.
- **Logical rules:** classical logic, choice, quantification, equality, and any metalogic assumed by the proof assistant.
- **Structural imports:** sets/types, infinity, ordering, composition, topology, continuity, linearity, probability, inner products, and dynamics, each tagged as derived, independently postulated, or representational.
- **Claim strength:** definition, conditional theorem, model-theoretic counterexample, conjecture, or empirical claim.
- **Circularity test:** whether the intended conclusion is equivalent to or implied by an imported premise.
- **Countermodel test:** whether alternative models satisfy the explicit premises but violate the conclusion.
- **Operational interpretation:** whether a mathematical distinction is physically realizable or merely formal.

The existence of multiple models satisfying 3FLL is not a refutation of ontological priority. It is evidence that the principles alone underdetermine the particular mathematical structure unless further constraints are shown.

## Proposed reconstruction sequence (not an entailment theorem)

1. 3FLL as admissibility constraints.
2. I∞ as informational possibility and A as transition-enabling ontological operation.
3. Identity and distinction of admissible configurations; licensed and obtaining transitions.
4. Composition of Actions, compatibility, persistence, and emergent order.
5. Representational structures adequate to the derived relational laws.
6. Operational effects, probability, physical kinematics, and dynamics.

No arrow is currently certified as a theorem merely by inclusion in this sequence.

## Immediate methodological consequences

**Avoid imported Hilbert-space structure.** Do not assume complex amplitudes, inner products, reversible unitaries, or tensor-factor dimensions while claiming to derive them.

**Use GPTs and real quantum theory as adversarial models.** Their role is to test specific proposed logical entailments, not to define what Action ontologically must be. A countermodel is decisive only for premises that the model actually satisfies.

**Treat Lean as a formal audit, not an ontology oracle.** Lean's type theory, classical axioms, and imported mathlib structures are formal background. A proof depending on them must disclose those dependencies. The fact that Lean can express a structure does not show that 3FLL uniquely determines it.

**Respect the existing selection abstraction.** `Step0_Primitives.lean` and `Step1_Constitution.lean` currently encode binary actuality. They do not yet formalize the full ontological meaning of Action. Preserve them while developing a separately reviewed action-centered representation.

## First falsification target: identity and Action do not uniquely determine arithmetic

Take two distinct classical structures satisfying ordinary identity, non-contradiction, and excluded middle: a one-element domain and a two-element domain. Their cardinalities differ while both obey the 3FLL. Even when an infinite I∞ is required, an infinite set can support distinct orders and algebraic operations; logic and infinitude alone do not select a unique group law, field, topology, or probability calculus. A richer A may constrain this, but its compositional laws must be stated and tested.

This is a **non-uniqueness observation**, not a proof that mathematics cannot be ontologically downstream of logic.

## Research gates

G1: Specify Action, licensed transitions, and occurrence without assuming physical time.
G2: Define a minimal compositional algebra of Actions and identify every extra axiom.
G3: Prove any claimed emergence of order, measure, probability, or linear structure.
G4: Compare countermodels, especially real-quantum nonlocal tomography, using the exact derived premises.
G5: Only after successful independent proof, revise the canonical reconstruction chain and formalization.

## Traceability

- Owner clarification: mathematics downstream of 3FLL; Action is the ontological operation enabling state transitions.
- `action-ontological-operation-research-semantics.md`.
- `compositional-interaction-separation-theorem.md`.
- `formalization/LrtFormalization/Step0_Primitives.lean`, `Step1_Constitution.lean`.

Verification: conceptual dependency audit and elementary countermodel argument. No new Lean build, external peer review, or physical derivation is claimed.
