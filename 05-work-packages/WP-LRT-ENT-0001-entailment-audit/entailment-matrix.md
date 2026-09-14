# LRT Entailment Audit Matrix

Status: ACTIVE
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

| # | Reconstruction step | Classification | Disposition | Audit finding |
|---|---|---|---|---|
| 0 | `X = [L3 : I∞ : A] -> AΩ = L3(I∞)` | ONTOLOGICAL | SURVIVES_CONDITIONALLY | Constitutive specification internal to the ontology. Must remain distinguished from a mathematical derivation. |
| 1 | `AΩ -> Determinate Identity` | ONTOLOGICAL | SURVIVES_CONDITIONALLY | Determinate identity is plausible as a constitutive consequence of Identity applied to actualized configurations. It does not by itself establish measurability or local accessibility. |
| 2 | `Determinate Identity -> PPC` | BRIDGE | REQUIRES_NEW_PREMISE | Strict entailment fails. Logical or informational distinctness does not by itself entail operational distinguishability. The active paper concedes the inference is defensible but not logically compelled. Operational Determinacy must be exposed as an explicit constitutive/operational principle rather than treated as forced by L3 alone. |
| 3 | `PPC -> Local Tomography` | BRIDGE | REQUIRES_NEW_PREMISE | Strict entailment fails. Even global operational distinguishability does not entail local tomographic accessibility. The historical H1->H2 bridge explicitly admits this gap and adds a locality/decomposability premise for relations. |
| 4 | `Local Tomography + reconstruction premises -> complex Hilbert space` | IMPORTED_THEOREM / BRIDGE | SURVIVES_CONDITIONALLY | Pending full Masanes-Müller premise audit. Local tomography alone is insufficient; all reconstruction premises must be enumerated and independently sourced. |
| 5 | `complex Hilbert space + Boolean action/event structure -> PVM` | BRIDGE / IMPORTED_THEOREM | SURVIVES_CONDITIONALLY | Pending audit of whether projection structure is genuinely forced by binary actualization or imported through operator/event representation. |
| 6 | `PVM + probability assumptions -> Born Rule` | IMPORTED_THEOREM / BRIDGE | SURVIVES_CONDITIONALLY | Pending Gleason-premise audit, including dimension, additivity/noncontextuality and whether probability structure is already substantially assumed. |
| 7 | `actualization/determinate succession -> Unique Next State` | ONTOLOGICAL / BRIDGE | SURVIVES_CONDITIONALLY | Pending. Must distinguish ontological actuality from deterministic state-update dynamics. |
| 8 | `Unique Next State -> ordered succession parameter t` | BRIDGE | SURVIVES_CONDITIONALLY | Pending. An ordering relation does not automatically yield physical time, continuity, reversibility or homogeneity. |
| 9 | `t + continuous unitary group -> self-adjoint generator` | IMPORTED_THEOREM | SURVIVES_CONDITIONALLY | Stone's theorem is legitimate once strong continuity and one-parameter unitarity are independently established. |
| 10 | `self-adjoint generator -> Schrödinger equation` | IMPORTED_THEOREM | SURVIVES_CONDITIONALLY | Standard conditional mathematical step. Must never be presented as deriving Schrödinger dynamics from L3 alone. |

## Step 2 finding: L3 to PPC

The active core paper decomposes the PPC into:

`L3-determinate content -> informational distinguishability -> operational distinguishability`.

The first arrow can be defended within the stipulated nature of `I∞`: if configurations are informational configurations, distinct configurations must differ informationally. The second arrow is substantive. An informational distinction may be ontically real without being measurable unless LRT adds the principle that physical standing requires some possible operational consequence.

The paper currently calls this Operational Determinacy and argues that an actualized informational difference with no physical consequence would make actualization vacuous. This is a coherent LRT commitment, but it is not forced by L3. It rules out ontologies containing physically real but in-principle operationally inaccessible distinctions.

Disposition: preserve Operational Determinacy, but elevate it to an explicit bridge/constitutive principle with its own failure condition. Do not describe it as a theorem of L3.

## Step 3 finding: PPC to local tomography

The repository's own H1->H2 bridge document states that metaphysical supervenience does not automatically produce operational local tomography and that global correlations may supervene on subsystem facts while failing local accessibility.

Even granting Operational Determinacy, the move to local tomography needs a further claim:

> Every identity-relevant relation in a composite system is distinguishable by a measurement protocol decomposable into local subsystem measurements and classical correlation of their outcomes.

Call this provisional principle **Local Operational Decomposability (LOD)**.

`PPC` establishes, at most, that a physically real difference has some possible operational signature. `LOD` says that for composites the signature is reconstructible from local operations. These are different claims.

Disposition: local tomography should be represented as conditional on `Operational Determinacy + LOD`, not as an entailment of Determinate Identity or L3 alone.

## Architectural redirect under evaluation

The reconstruction should provisionally be rewritten as:

`TRT/LRT ontology`
`-> Determinate Identity`
`+ Operational Determinacy`
`+ Local Operational Decomposability`
`-> Local Tomography`
`+ external reconstruction premises`
`-> quantum formal structure`.

This is weaker rhetorically and stronger methodologically. It exposes exactly where ontology ends and physics-facing bridge principles begin.

A further possibility remains open: Operational Determinacy and/or LOD may belong in a separate **physics interface layer** rather than in LRT's hard ontological core. If so, LRT becomes a foundational ontology with multiple possible physical realizations, and the present quantum reconstruction becomes one descendant model rather than the unique physical consequence of LRT.

## Immediate findings

1. The strongest current LRT contribution remains a grounding/reconstruction claim, not new mathematics.
2. PPC is not derivable from L3 alone. The current repository text already effectively concedes this.
3. Local tomography requires more than PPC. A locality/decomposability premise is currently hidden in the bridge argument.
4. Machine verification downstream cannot establish the independent truth of these bridge principles. Lean can prove consequences of encoded premises, not justify their ontological-to-physical interpretation.
5. The historical repository warning that "Deriving Schrödinger from 3FLL" is misleading is correct and now adopted as a governing control.
6. Claims that LRT predicted complex quantum mechanics before experiments published in 2021 are historically impossible for a later framework and require relabeling as reconstruction, structural selection, or retrodiction.
7. A lack of novel empirical prediction does not by itself falsify LRT as a foundational ontology. It prevents the reconstruction alone from being counted as corroborated novel physics.

## Next audit increment

Audit Step 4 in full. Enumerate every premise used to obtain complex Hilbert-space structure from local tomography and the selected reconstruction theorem(s). For each premise record whether it is:

- independently grounded by LRT,
- supplied by Operational Determinacy or LOD,
- empirically motivated,
- imported as a reconstruction axiom,
- or mathematically definitional.

The test remains: if complex quantum structure were unknown, would these premises independently force its discovery?