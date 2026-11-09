# Essential Action and Modal Dynamism: independence test

Status: RESEARCH / MODEL-THEORETIC ANALYSIS, NOT CANONICAL
Date: 2026-11-08
Work package: WP-LRT-ACT-0001

## Problem

The owner has stipulated that L₃, I∞ and A are inseparable co-primitives: none obtains independently. Fundamental A is the ontological condition for actuality and the possibility of state transitions, not a QFT operator, an earlier physical event, or merely a Boolean selection map. The question is whether this characterization **entails** that every actual physical structure admits a nonidentity transition.

A single primitive can have multiple constitutive roles without those roles being reducible to one another. “Action is essential to reality” and “every actual structure can change” are therefore distinct assertions unless an additional bridge is established.

## Typed analytical framework (imported mathematics)

The following many-sorted model is a *test representation*, not an ontological definition or derivation of the triad:

- `World` and `Structure` are sorts; `State(F)` is a nonempty set for each structure F.
- `Actual(w,F)` states that F obtains at w.
- `Triad(w)` is an indivisible primitive marker of co-constitution; no separate existence of L₃, I∞, or A is modeled.
- `Lic(w,F,s,t)` states that an A-grounded nontrivial transition from s to t is licensed, where s,t∈State(F).
- `Occ(w,F,s,t)` states that the transition occurs.
- `s≠t` is equality within a chosen representation, not automatically an ontic distinction; gauge-equivalent states require quotienting or a separate ontic-distinctness relation.

Minimal assumptions:

- **OIP-T:** `Actual(w,F) → Triad(w)`. The co-primitive inseparability is represented by the atomic marker, avoiding a fictional model of separately obtaining primitives.
- **EVENT:** `Occ(w,F,s,t) → Lic(w,F,s,t)`. Occurrence entails licensing. No converse.
- **COH:** Every modeled actual structure has a logically consistent state description. This does not specify Hilbert space, local tomography or a Hamiltonian.

Potential strengthening:

- **DF (dynamical fecundity):** `∀w,F,s, Actual(w,F) → ∃t, OnticallyDistinct_F(s,t) ∧ Lic(w,F,s,t)`.
- **DF∃ (weaker):** `∀w,F, Actual(w,F) → ∃s,t, OnticallyDistinct_F(s,t) ∧ Lic(w,F,s,t)`.
- **DF-context (relational):** `∀w,F, Actual(w,F) → ∃E,s,t, DistinctComposite((F,E),s,t) ∧ Lic(w,(F,E),s,t)`, for an admissible interaction context E.

DF is stronger than DF∃; DF-context does not imply intrinsic nonidentity transitions of F. All three require assumptions about ontic distinction, composability and admissible contexts not supplied by OIP.

## Finite countermodels (explicit valuations)

**C0, the inert singleton.** One world w; one actual F; `State(F)={s}`; `Triad(w)=true`; `Lic=Occ=∅`. COH, OIP-T, and EVENT hold. DF and DF∃ fail. Thus these assumptions do not entail any nonidentity change.

**C1, capacity without occurrence.** One world w; one actual F; `State(F)={s,t}` with distinct ontic states; `Lic={(s,t)}`; `Occ=∅`. OIP-T, EVENT and DF∃ hold, while DF fails at t. No transition occurs. This refutes the inference from *some* capacity to actual change.

**C2, universal capacity without occurrence.** One world w; one actual F; `State(F)={s,t}`; `Lic={(s,t),(t,s)}`; `Occ=∅`. OIP-T, EVENT, DF and DF∃ hold, but there is no occurring event. This refutes DF ⇒ continuous or any actual excitation.

**C3, relational capacity with intrinsic inertness.** Actual F and context E; F has one intrinsic state s; composite (F,E) has two ontically distinct configurations u,v and `Lic((F,E),u,v)`; no nonidentity `Lic` on F alone. OIP-T, EVENT and DF-context hold, DF∃ on F fails. A capacity to participate in interactions is not identical to intrinsic capacity to change.

**C4, merely representational difference.** A two-label description `s,t` with gauge equivalence `s∼t` has a syntactic `Lic(s,t)`, but no ontic distinction. Replacing `s≠t` by `OnticallyDistinct(s,t)` prevents a spurious proof of dynamical fecundity.

All models are finite, classical metamodels. They show logical nonimplication under stated premises; they do not prove that C0 or C3 is metaphysically permitted by the full intended meaning of A.

## Conditional implications

1. **DF ⇒ DF∃**, assuming each actual F has at least one state. Choose any s, then DF witnesses t.
2. **DF∃ ⇏ DF** by C1.
3. **DF ⇏ ∃Occ** by C2.
4. **OIP-T + EVENT + COH ⇏ DF∃** by C0.
5. **DF-context ⇏ DF∃ on isolated F** by C3.

The proofs are first-order witness/countermodel arguments. No theorem that OIP *alone* supplies DF is claimed.

## The conceptual fork

**Constitutive reading (A-C):** A is co-necessary for physical obtaining and underwrites the intelligibility of transitions, but not every actual object must possess an intrinsic nonidentity transition. This is compatible with C0 at the model level.

**Intrinsic-dynamical reading (A-D):** A's essential nature requires every actual structure to have a genuinely distinct possible successor. This excludes C0 by an added axiom DF and requires an ontic individuation criterion.

**Relational-dynamical reading (A-R):** Every actual structure can participate in some nontrivial Action-grounded interaction within a possible context, even if intrinsically stationary. This requires a context ontology and is weaker than A-D in one respect, stronger than A-C in another.

These are alternative proposals, not three derivations. Do not elevate any one to canonical theory without owner approval.

## QFT-facing caution

A stationary vacuum or energy eigenstate does not furnish evidence for an ontologically inert field: available interactions and nontrivial correlations can persist. Conversely, a mathematically trivial sector may be representationally inert. The existence of a mathematical transition operator is not proof that a physical event occurred. No preferred time parameter is assumed by these models; “successor” is a relation, not a preexisting clock.

## Recommended next test

Test A-R against the possibility of a physically actual but **absolutely isolated** sector. If the sector cannot couple to any possible context and admits no intrinsic state distinctions, is it still physically actual under LRT? A-C permits it at the model level; A-D and A-R exclude it by distinct principles. This question may discriminate the essential meaning of A without stipulating that excitations must continually occur.

Then assess whether the proposed exclusion follows from a pre-mathematical account of actual physical identity or merely imports dynamical fecundity as an axiom. Require an observable consequence before claiming an empirical distinction from QFT.

## Epistemic status

HIGH (conditional elementary logic): implications 1–5 and finite countermodels relative to the explicitly specified metamodel.
UNCERTAIN (ontology): which of A-C, A-D, A-R captures fundamental Action, and whether the finite countermodels are metaphysically admissible.
NOT ESTABLISHED: derivation of QFT dynamics, Hilbert space, local tomography, Born rule, or new testable predictions.

Related: `ontological-inseparability-inertness-test.md`, `global-coherence-coprimitive-action-qft-test.md`, and `action-identity-research-baseline.md`. No canonical equations, Lean files, published artifacts, or epistemic labels were changed.
