# LRT Entailment Audit Matrix

Status: INITIAL BASELINE
Date: 2026-09-14
Work package: WP-LRT-ENT-0001

## Governing test

For each reconstruction arrow, ask:

> If the consequent were unknown, would the antecedent independently force a competent investigator to discover it?

Classification vocabulary:

- LOGICAL: follows by valid logical consequence from stated premises.
- ONTOLOGICAL: follows from an explicit constitutive/grounding commitment of LRT.
- BRIDGE: connects ontology to operational or physical structure and therefore carries substantive extra argumentative burden.
- IMPORTED_THEOREM: follows by applying an established external mathematical theorem once its premises are supplied.
- EMPIRICAL_ASSUMPTION: depends on a premise warranted by observed physical regularity rather than LRT alone.

Disposition vocabulary:

- SURVIVES
- SURVIVES_CONDITIONALLY
- REQUIRES_NEW_PREMISE
- REDESCRIPTION
- FAILS

## Baseline chain

Canonical public summary:

`χ -> AΩ -> Determinate Identity -> Local Tomography -> C-Hilbert space -> PVM -> Born Rule -> Unique Next State -> t -> Schrödinger dynamics`

The active core physics document additionally identifies the Physical Proposition Criterion (PPC) as the governing ontology-to-operational bridge. The audit therefore makes PPC explicit even where abbreviated summaries omit it.

| # | Reconstruction step | Initial classification | Initial disposition | Audit focus |
|---|---|---|---|---|
| 0 | `X = [L3 : I∞ : A] -> AΩ = L3(I∞)` | ONTOLOGICAL | SURVIVES_CONDITIONALLY | Constitutive specification is internal to the ontology. Audit whether the notation is definition, grounding claim, or substantive entailment at each use. |
| 1 | `AΩ -> Determinate Identity` | ONTOLOGICAL / BRIDGE | SURVIVES_CONDITIONALLY | Determine whether determinate identity follows from L3 alone or from an additional interpretation of physical propositionhood. |
| 2 | `Determinate Identity -> PPC` | BRIDGE | SURVIVES_CONDITIONALLY | Central vulnerability. Separate logical distinctness, informational distinctness, and operational distinguishability. The active paper itself marks this bridge ARGUED rather than established. |
| 3 | `PPC -> Local Tomography` | BRIDGE | SURVIVES_CONDITIONALLY | Test whether local access to all identity-making relations actually follows, or whether composite-state reconstruction/local accessibility is an extra operational axiom. |
| 4 | `Local Tomography + reconstruction premises -> complex Hilbert space` | IMPORTED_THEOREM / BRIDGE | SURVIVES_CONDITIONALLY | Identify the full Masanes-Müller or related premise set. Determine which premises LRT independently grounds and which remain imported. |
| 5 | `complex Hilbert space + Boolean action/event structure -> PVM` | BRIDGE / IMPORTED_THEOREM | SURVIVES_CONDITIONALLY | Test whether Boolean actual/nonactual valuation forces projection-valued event structure or whether the quantum event algebra has already entered through representation assumptions. |
| 6 | `PVM + probability assumptions -> Born Rule` | IMPORTED_THEOREM / BRIDGE | SURVIVES_CONDITIONALLY | Audit Gleason premises, dimensional restrictions, noncontextuality/additivity assumptions, and whether any premise is equivalent to substantial Born-rule structure. |
| 7 | `actualization/determinate succession -> Unique Next State` | ONTOLOGICAL / BRIDGE | SURVIVES_CONDITIONALLY | Determine whether uniqueness is ontologically forced and whether determinism at the state-update level is being introduced beyond observed quantum statistics. |
| 8 | `Unique Next State -> ordered succession parameter t` | BRIDGE | SURVIVES_CONDITIONALLY | Distinguish an ordering parameter from physical time. Audit continuity, reversibility, homogeneity, and composition assumptions. |
| 9 | `t + continuous unitary group -> self-adjoint generator` | IMPORTED_THEOREM | SURVIVES_CONDITIONALLY | Stone's theorem is legitimate once strong continuity and unitary one-parameter group structure are established. Main burden lies in where those premises come from. |
| 10 | `self-adjoint generator -> Schrödinger equation` | IMPORTED_THEOREM | SURVIVES_CONDITIONALLY | Mathematical step is standard. The claim must be phrased as conditional on the prior unitary/continuity structure, not as derivation from L3 alone. |

## Immediate findings

1. The strongest current LRT claim is a grounding/reconstruction claim, not new mathematics. That is consistent with the active core paper's own statement of contribution.
2. The PPC is the principal ontology-to-physics bridge. Machine verification downstream cannot establish the independent truth of PPC or of any other encoded bridge premise.
3. The historical repository already contains an internal warning that "Deriving Schrödinger from 3FLL" is misleading when Stone's theorem and its premises are required. The current audit adopts that warning as a control.
4. Claims that LRT predicted complex quantum mechanics before experiments published in 2021 are historically impossible for a framework formulated later. Such claims must be relabeled as structural selection, reconstruction, or retrodiction according to the exact chronology.
5. A lack of novel empirical prediction does not by itself falsify LRT if LRT is scoped as a foundational ontology and reconstruction programme. It does prevent the reconstruction alone from being counted as corroborated novel physics.

## Next audit increment

The next pass will decompose Steps 2-4 in detail:

`L3 -> determinate content -> informational distinguishability -> operational distinguishability -> local tomography -> complex Hilbert-space selection`

For each sub-arrow, the audit will record exact canonical source text, formalized premise, external theorem dependency, counterexample class, and failure condition.
