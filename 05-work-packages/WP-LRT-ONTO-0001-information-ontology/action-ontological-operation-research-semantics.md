# Action as ontological operation: corrected LRT research semantics

Status: RESEARCH / OWNER-CLARIFIED INTENT, MATHEMATICAL MODEL PROVISIONAL
Date: 2026-11-08
Scope: ontology work package only; no silent changes to canonical equations, Lean, or epistemic labels.

## 1. Owner clarification and the modeling error

The intended primitive **Action (A)** is *the ontological operation that makes a transition possible*. It is not adequately characterized by the present Lean selection map `ActionPrimitive.A : I → ActualityValue`. That map encodes a derived actual/nonactual predicate, without specifying a possible transition or the operation grounding its possibility. The prior local-tomography countermodels are valid against this selection abstraction; they are not decisive tests of a richer action ontology.

Preserve the three primitives `χ=[L3:I∞:A]` and the admissible/actual distinction. Do not simply replace A with an ordinary physical evolution operator or a clock-indexed function.

## 2. Levels and proposed minimal semantics

Let `C=L3(I∞)` denote admissible configurations, without presupposing a Hilbert space, spacetime, metric, probability, or time parameter.

- **Ontological primitive A:** grounds the possibility of actualization transitions. Primitive; its explanatory role is not reduced to a Boolean predicate.
- **Action-licensed relation R_A⊆C×C:** `R_A(x,y)` means a transition from x to y is permitted by A and logical constraints. This relation is a *representation* of consequences of A, not a definition that reduces A to R_A.
- **Obtaining events E⊆R_A:** which licensed transitions actually obtain. The distinction between permission and occurrence must be explicit. A further actuality/occurrence structure may be needed; do not silently add it as an independent fourth ontological primitive.
- **Actualized configurations:** states participating in obtaining events, or additionally a specified initial actuality boundary. Neither definition follows without a choice about beginnings, persistence, and whether actualization always entails change.

A provisional representation is `A ⊢ R_A(x,y)`, `Occ(x,y)`, with `Occ(x,y)⇒R_A(x,y)`. This does not assert `x≠y`; persistence/self-transition remains open. `R_A` need not be total, deterministic, transitive, symmetric, reversible, or serial.

## 3. Avoiding circular time

An ordered pair `(x,y)` records source/target roles, not elapsed time. A proposed causal/temporal precedence relation might arise from chains of obtaining transitions, but acyclicity, antisymmetry, nontriviality, and consistency with observed time are additional proof obligations. A directed cycle is mathematically possible under the minimal axioms; hence a partial order cannot be asserted yet.

## 4. Immediate independence test

**Proposition.** The bare existence of an action-licensed transition relation, together with the rule that obtaining transitions must be licensed, does not imply local tomography.

**Countermodel construction.** Let the composite state domain be the valid real two-rebit density matrices. Take `R_A=S_AB×S_AB` (every ordered transition is licensed), and take `Occ=R_A` or any nonempty subset. All obtaining transitions are licensed. Yet `ρ±=(I₄±u(J⊗J))/4`, `0<u≤1`, have identical local product-effect statistics and distinct global statistics. Thus the proposed action-relation representation alone cannot exclude the hidden composite direction.

A less permissive witness is `R_A={(s,s):s∈S_AB}∪{(ρ+,ρ−)}`, with `Occ={(ρ+,ρ−)}`. This contains an actual, nonidentity state change and still does not change the local measurement effect algebra. Even **nontrivial obtaining change** alone is insufficient.

The model tests a *minimal formal representation* of A, not the full intended metaphysical operation. It establishes which additional structural assumptions must be articulated before a tomography theorem can be claimed.

## 5. Independent research obligations

**A. Action and individuation.** Does physical identity depend on the total pattern of admissible interactions? Distinguish ontological difference from operationally accessible measurement effects.

**B. Action composition.** Define sequential composition and subsystem-parallel composition of licensed actions without assuming a preexisting clock or complex Hilbert space. Show whether composition is associative, whether identity/persistence actions exist, and whether a non-signalling or locality rule is independently motivated.

**C. Operational realization.** Derive an effect/record structure from actions. Explain what constitutes an observable distinction and why a global action could or could not be replaced by subsystem-local actions. Explicitly test the two-rebit `J⊗J` direction.

**D. Temporal emergence.** Derive, rather than assume, a physically meaningful precedence relation from obtaining transitions.

**E. Formalization discipline.** Maintain existing Step0/Step1 as a documented selection abstraction until a reviewed alternative exists. Develop a parallel Lean research namespace only after selecting precise types and assumptions. Any proof must distinguish what follows from the three primitives from what follows from newly posited composition laws.

## 6. Falsification and decision gates

A proposed Action axiom set is insufficient if a model satisfies it and admits distinct composite states with identical product-effect statistics. Test against real quantum theory, then additional GPT countermodels. If a theorem is obtained, audit whether a premise already entails `(S_AB−S_AB)∩W⊥={0}` by definition.

Decision gate 1: approve the action/permission/occurrence distinction and resolve whether actualization requires change.
Decision gate 2: choose a compositional operation with independently motivated laws.
Decision gate 3: attempt a formal derivation of operational separation and local tomography.
Do not promote speculative results to established canonical status.

## 7. Sources and traceability

- Owner clarification in the current research discussion: Action is the ontological operation making transitions possible.
- `formalization/LrtFormalization/Step0_Primitives.lean` and `Step1_Constitution.lean`: existing selection abstraction.
- `actualization-tomography-independence.md`, `compositional-actualization-ca1-test.md`, `ca3-global-interaction-local-record-counterexample.md`: earlier limits on selection/recordability.
- Masanes and Müller (2011), https://arxiv.org/abs/1004.1483 : local tomography is an independent reconstruction requirement.

Verification status: analytic countermodel and dependency analysis; no Lean build, experimental test, or claimed derivation of quantum theory.
