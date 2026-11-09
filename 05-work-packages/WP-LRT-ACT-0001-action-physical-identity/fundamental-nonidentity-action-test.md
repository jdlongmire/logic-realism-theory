# Fundamental Action as necessary non-identity change: coherence and independence tests

**Status:** RESEARCH / AXIOM PROPOSAL AND GAP ANALYSIS; NOT CANONICAL  
**Date:** 2026-11-09  
**Work package:** WP-LRT-ACT-0001  
**Related:** `constitutive-action-measurement-boundary.md`, `action-essentiality-modal-independence.md`, `ci1-noncircular-actuality-underdetermination.md`

## Owner clarification and change in research premises

The owner states: **Without fundamental state change (A), nothing actualizes or obtains; L₃ and I∞ are inert without A. A necessarily entails genuine non-identity change at the fundamental ontological level.** This is a proposed ontological axiom, not a consequence established from the three laws of logic.

The three co-primitives remain inseparable: `χ=[L₃:I∞:A]`. Calling L₃ and I∞ *inert* means they are not independently physically actualizing; it does **not** mean that they first exist without A and subsequently receive it. Nor does it entail that I∞ is a pre-existing inventory of actual worlds.

The prior minimal A-C interpretation allowed constitutive A with no non-identity change. **That interpretation is now incompatible with the owner's clarified premise.** Research must distinguish fundamental ontological non-identity change from changes detectable in an emergent or effective physical description.

## Typed candidate axiom

Use separate sorts `S` (actual constitutions), `D` (descriptions), `R` (formal change relata or aspects), and `Δ` (fundamental change instances). No member of R is thereby asserted to be an independently obtaining physical state.

Predicates: `Actualχ(s)`, `Constitutes(δ,s)`, `FundChange(δ)`, `From(δ,r)`, `To(δ,r')`, `OnticDistinct(r,r')`. Relations are semantic placeholders pending interpretation.

**A-NIC (owner axiom, formal research rendering):**

`∀s:S, Actualχ(s) → ∃δ:Δ, FundChange(δ) ∧ Constitutes(δ,s) ∧ ∃r r':R, From(δ,r) ∧ To(δ,r') ∧ OnticDistinct(r,r')`.

This asserts **necessary non-identity change** for every actual constitution. It does not assert that every conceivable transition is realized, that all constituents individually change, or that an ordered pair of independently actual states exists. A-NIC does not assert a first change or an initial condition.

**A-INERT (counterfactual dependence, research rendering):** no physical actuality is constituted under removal of A's role from χ. Formally, in a deliberately weakened comparison semantics `¬A-role → ¬∃s Actualχ(s)`. This is a modal comparison of descriptions, not a possible world where L₃ or I∞ independently obtains.

**A-CO (inseparability):** every actual constitution is jointly grounded in all three co-primitives, with no independently obtaining proper subset.

**A-COH:** actuality implies logical coherence.

**A-NONTRIV:** `OnticDistinct` must be grounded in an independently specified physical/ontic difference criterion, not simply `r ≠ r'` as syntactic labels. Otherwise A-NIC is satisfied by arbitrary relabeling and lacks physical content.

### Important semantic caveat

The quantified formula A-NIC is a **model schema**, not a literal metaphysical claim that change is an operation between independently actual states. The very use of `From` and `To` can smuggle in ordered transition ontology. An alternative event/contrast semantics might use `DifferenceWithin(δ,s)` as primitive and require an explicit nontriviality condition. This trades one unresolved term for another. Neither formalism yet derives change from L₃ or I∞.

## Finite separating tests

**T1: Inert actual singleton (excluded).** S={s}, Δ=∅, Actualχ(s). It can satisfy the earlier CC-1..5 by treating A as an uninterpreted tag. It **violates A-NIC**. The old E1 stationary-actuality model is excluded *when* it truly lacks fundamental non-identity change.

**T2: Fundamental two-aspect change, macroscopically stationary (admitted conditionally).** S={s}, R={r₀,r₁}, Δ={δ}, `OnticDistinct(r₀,r₁)`, `From(δ,r₀)`, `To(δ,r₁)`, `Constitutes(δ,s)`. An effective observable `M` maps both aspects to the same measured value. A-NIC holds despite `M(r₀)=M(r₁)`. This illustrates logical compatibility only: without an independently grounded ontic distinction, the construction could be pure gauge or representation change.

**T3: Distinct labels, no physical difference (excluded by A-NONTRIV).** R={u,v}, u≠v as symbols, but u and v are physically equivalent under the model's equivalence relation. Defining `OnticDistinct(u,v)` solely as `u≠v` would make A-NIC vacuous. A-NONTRIV rules out this witness.

**T4: Change without metric time (admitted conditionally).** A directed distinction `r₀→r₁` exists as a primitive logical/asymmetric relation, with no metric time function or duration. This shows a model of non-identity change need not *include* clock time. It does **not** prove a physically adequate account of change without temporal order: direction and asymmetry require their own justification.

**T5: Actual change with no initial physical state (underdetermined).** Consider a finite cycle of two ontically distinguishable aspects or a bi-infinite chain, each with a change relation and no privileged initial aspect. These avoid specifying a first event but do not solve the metaphysical grounding of the whole change structure. A cycle's orientation or a chain's ordering may still be primitive.

**T6: Non-identity dynamics underdetermination.** Two extensions share the same A-NIC, A-CO and A-COH structures, but one permits a single directed relation while the other permits additional transitions. Both satisfy A-NIC. Therefore A-NIC does **not** determine a unique law of motion, transition rate, conservation rule, Born probability, or measurement outcome.

**T7: Ontic change versus observational change.** An effective stationary state can be a coarse-graining of fundamentally distinct aspects, but only if those distinctions survive the theory's own physical equivalence criteria. No assumption that every quantum stationary state conceals unobserved physical motion is licensed by A-NIC.

## What follows, and what does not

**Conditional theorem (immediate from A-NIC):** `Actualχ(s) → ∃δ FundChange(δ)`. A-NIC entails that every actual constitution includes a fundamental non-identity-change witness.

**Conditional exclusion:** Any structure that is actual but admits no ontically non-identical change violates A-NIC. This excludes genuinely static-at-all-levels models as representations of actuality **if** the axiom is accepted.

**Not entailed:** metric time; an initial state; local motion; observable events; excitation; continuous trajectories; physical energy transfer; a quantum measurement; definite outcomes; stochastic probabilities; Hilbert-space structure; or the Born rule.

**Noncircularity not yet established:** A-NIC stipulates the change witness. Without a substantive identity/difference criterion and a reason why such change constitutes actuality, the proposal risks replacing an actuality label with a change label. The axiom adds logical strength but its explanatory sufficiency is open.

## Revised G-ACT obligations

**G-ACT-1, difference:** Specify ontic non-identity independently of syntactic inequality, gauge artifacts and mere observational differences.

**G-ACT-2, constitution:** Explain how genuine non-identity change is *constitutive of* an actual structure rather than a relation between already actual relata. Avoid a temporally prior pre-actual state.

**G-ACT-3, direction:** Establish whether change intrinsically involves asymmetry or ordering, and whether that ordering is logically primitive, ontologically derived, or emergent. Do not assume physical time.

**G-ACT-4, physical restriction:** Find a nontrivial constraint on admissible change from χ and explicitly inventory any additional axioms. Merely requiring at least one change does not determine dynamics.

**G-ACT-5, empirical discrimination:** Specify a test or restriction that could differentiate A-NIC from a competing ontology. A claim of hidden fundamental change compatible with every observation risks empirical insulation.

**G-ACT-6, downstream measurement:** Only after G-ACT-1..4, evaluate definite records, state update, and probability. No measurement solution is presently demonstrated.

## Countermodel audit of earlier notes

The old E1 model is now **rejected** if it truly has no fundamental change, but may survive as a *macroscopically stationary* model if a nontrivial fundamental witness exists. Other E2..E6 are not automatically invalidated; they must be checked for whether an A-NIC witness can be added without changing their intended distinction. Likewise C0..C4 cannot be declared universally compatible or incompatible without model-by-model inspection.

The earlier research statement “A is essential but need not entail a non-identity transition” was correct **relative to CC-1..5 alone**, but is no longer an adequate expression of the owner's stronger A-NIC premise.

## Research status and decision

- **HIGH (formal, conditional):** A-NIC excludes actuality without any fundamental non-identity-change witness; it does not imply a specific physical dynamics.
- **HIGH (methodological):** syntactic inequality and ontic distinction must not be conflated.
- **UNCERTAIN:** whether fundamental non-identity change can be specified without presupposing actuality, temporal order or an independent identity criterion.
- **NOT ESTABLISHED:** noncircular explanatory adequacy, empirical falsifier, dynamical law, measurement solution or Born-rule derivation.

**Recommendation:** retain A-NIC as an explicit *owner-proposed research axiom*, then tackle G-ACT-1 and G-ACT-2 before attempting to derive physics. Do not silently promote this note into canonical theory, Lean axioms, or published claims.

## Verification scope

Reasoned finite countermodels and syntactic entailments reviewed at research level. No machine-checked Lean proof or runtime physics simulation performed.
