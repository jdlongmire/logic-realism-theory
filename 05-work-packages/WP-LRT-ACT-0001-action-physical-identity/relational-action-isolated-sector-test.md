# Relational Action and Absolutely Isolated Sectors: identity and interaction test

Status: RESEARCH / COUNTERMODEL STUDY; NOT CANONICAL
Date: 2026-11-08
Work package: WP-LRT-ACT-0001

## Research question

If L₃, I∞ and A are inseparable co-primitives, must every physically actual structure admit a nontrivial possible interaction, at least in some admissible context? Does the absence of any such interaction make a structure physically unreal or merely inaccessible? This tests relational Action (A-R) from `action-essentiality-modal-independence.md`, without redefining the primitive A as a measurement or interaction operator.

## Distinctions and definitions

- **Absolute isolation (AIso):** A sector has no *nontrivial* licensed interactions with any admissible external context, including hypothetical contexts. This is stronger than practical or causal inaccessibility and stronger than no currently occurring interaction.
- **Intrinsic inertness (IInert):** No ontically distinct intrinsic transition is licensed for the sector.
- **Operational invisibility (OInv):** All tests in a specified permitted observation class give identical records whether the sector is present or absent.
- **Physical nonexistence:** The sector does not obtain. This does not follow from OInv without an independently justified observability principle.
- **Identity-only coupling:** A formal identity map or product composition does not count as a nontrivial interaction.
- **Co-primitive Action:** The ontological condition for actuality and possibility of transitions, not identical to any one nontrivial coupling.

These are explicitly model-relative notions. “All possible contexts” requires an independently specified admissibility criterion; otherwise A-R can be made true by declaring a hypothetical context admissible.

## Minimal model language (mathematics imported for testing)

Use structures F and environments E; possible composite descriptions `F⊗E` only where a composition relation `Comp(F,E)` is supplied. `Lic(F⊗E,u,v)` is a provisional licensed-transition relation. `Diff_F(u,v)` means a physically meaningful F-related distinction, after quotienting representational/gauge redundancy. Define:

`NontrivCoupling(F,E) := Comp(F,E) ∧ ∃u,v [Lic(F⊗E,u,v) ∧ Diff_F(u,v) ∧ ContextDependent(F,E,u,v)]`.

The last predicate means that a change attributable to the interaction is not just a pair of independently evolving states. This criterion is a **research placeholder**, not an ontologically prior definition; no Hilbert tensor product is assumed by the symbol `⊗`.

`A-R := ∀F [Actual(F) → ∃E NontrivCoupling(F,E)]`.

`AIso(F) := ¬∃E NontrivCoupling(F,E)`.

By elementary predicate logic, A-R entails `Actual(F) → ¬AIso(F)`. **This is definitional conditional exclusion**; it is not an independent derivation from OIP or from the meaning of A.

## Separating models

**R1: Obtaining isolated sector.** Two sectors F and E each have coherent states and obtain under the indivisible triad; no composite nontrivial coupling is licensed for F with any context, and F has only one intrinsic state. OIP and constitutive A-C are respected by stipulation; A-R is false. This shows OIP does not by itself eliminate isolated sectors.

**R2: Unobserved but interactable sector.** F has no coupling to currently accessible instruments, but there exists an admissible context E* with nontrivial coupling. F is OInv relative to actual instrumentation but not AIso. A-R holds; current non-detection cannot refute actuality.

**R3: Correlated yet noninteracting description.** F and E have a jointly specified correlated state, while all permitted transitions are independent local changes and no interaction can be licensed. Correlation by itself does not establish nontrivial coupling or A-R. If one defines interaction to include state preparation or common-cause history, additional temporal/causal premises are needed.

**R4: Distinct sectors with identical records.** Two ontically distinct sectors differ in allowed internal or contextual transitions but the permitted record maps erase the distinction. A-R can hold while operational separation fails. Thus A-R does not entail AI-1 or local tomography.

**R5: Superselection boundary.** A formal theory with superselection sectors can forbid certain coherent superpositions or inter-sector operations without making each sector ontologically nonexistent. A sector's inaccessibility under a restricted observable algebra is weaker than AIso. This is an illustrative theory structure, not a claim that all QFT superselection sectors are absolutely isolated.

**R6: Trivial context loophole.** If any F may be paired with a fabricated E whose only purpose is to stipulate `NontrivCoupling(F,E)`, A-R is satisfied vacuously. A valid reconstruction needs a noncircular admissibility rule for contexts grounded in the co-primitive ontology.

## Logical results

1. `OIP ⇏ A-R`: R1, given the explicit minimal OIP model.
2. `A-R ⇒ Actual(F) → ¬AIso(F)`: immediate from the definitions.
3. `OInv ⇏ AIso`: R2.
4. `A-R ⇏ operational separation`: R4.
5. `Global correlation ⇏ nontrivial coupling`: R3.
6. `A-R ⇏ continuously occurring interaction`: a model may license interaction with E* while `Occurs` is empty.

These results are conditional on the toy semantics. They do not demonstrate that the metaphysical co-primitive A entails A-R.

## Physical comparison and limitations

Algebraic QFT associates local observable algebras with spacetime regions; distinct representations and superselection structures may arise. This does not prove an ontological interaction requirement for every sector. Gauge-invariant observables, causal accessibility, and hypothetical coupling must be kept separate. A theory with an exactly decoupled hidden sector may be physically underdetermined by our observations, yet is not thereby inconsistent. The logical coherence of such a model is a challenge to any attempt to *derive* A-R without an extra premise.

## Decision analysis

Three possible research directions:

- **D1, retain minimal OIP:** Actuality requires co-primitive A, but absolutely isolated actual sectors are not ruled out. Most conservative; leaves physical individuation underdetermined.
- **D2, adopt A-R as an additional metaphysical axiom:** Excludes absolute isolation by stipulation. Requires independent justification and does not by itself yield a testable prediction.
- **D3, derive a weaker Action-relevance principle:** Seek a noncircular argument that every *physically individuated* structure has at least one possible distinguishing Action relation, while permitting unobservable and currently decoupled structures. Beware that defining physical identity by such relations makes the conclusion analytic.

**Recommendation:** pursue D3 as a candidate proof obligation while retaining D1 as the research baseline. Do not canonize D2 without owner authorization.

## Falsification and proof obligations

- **RA-1:** Give pre-mathematical criteria for an admissible context, without assuming a QFT coupling algebra.
- **RA-2:** Define nontrivial Action relevance without equating ontic identity with operational distinguishability.
- **RA-3:** Prove or refute `OnticallyDistinct(F,G) → DifferentActionPossibilities(F,G)` under independently stated axioms.
- **RA-4:** Test the isolated-sector countermodel against a stronger, owner-approved account of A rather than dismissing it by definition.
- **RA-5:** Distinguish predictions of A-R from ordinary hidden-sector models; otherwise report no empirical discrimination.
- **RA-6:** Reconcile global coherence with locality without assuming a preferred global time or deriving local tomography by fiat.

## Status

**HIGH** confidence in the explicit logical nonimplications relative to the stated models. **UNCERTAIN** whether relational Action is metaphysically essential. **NOT ESTABLISHED**: reconstruction of QFT, exclusion of hidden sectors, or derivation of observable signatures. No canonical theory, Lean axioms, or published text changed.

Traceability: `action-essentiality-modal-independence.md`, `ontological-inseparability-inertness-test.md`, `action-identity-research-baseline.md`, and `global-coherence-coprimitive-action-qft-test.md`.
