# Step 4 Audit: From Local Tomography to Complex Quantum Structure

Status: ACTIVE FINDING
Date: 2026-09-14
Work package: WP-LRT-ENT-0001

## Question

Does LRT's ontology plus local tomography independently force complex Hilbert-space quantum theory, or does the current reconstruction rely on a larger imported operational axiom set?

## Canonical LRT claim under audit

The active formalization document states, in effect:

`H1 + H2 + continuous reversible transformations -> projective Hilbert space over C`

and attributes this jointly to Hardy (2001), Chiribella-D'Ariano-Perinotti (2011), and Masanes-Muller (2011).

That statement is too compressed to function as a faithful imported theorem. These are distinct reconstruction programmes with materially different premise sets.

## Primary-source check

### Masanes and Muller 2011

Primary source: L. Masanes and M. P. Muller, *A derivation of quantum theory from physical requirements*, New Journal of Physics 13 (2011) 063001; arXiv:1004.1483.

The paper states five requirements, not merely local tomography plus continuous reversible transformations:

1. A one-bit system is characterized by a finite set of outcome probabilities.
2. The state of a composite is characterized by statistics of measurements on the individual components (tomographic locality/local tomography).
3. Systems carrying the same amount of information have equivalent state spaces.
4. Any pure state can be reversibly transformed into any other.
5. For a one-bit system, all mathematically well-defined measurements are physically allowed.

The work is embedded in the generalized probabilistic theory framework, which already assumes operational primitives including preparations, mixtures, measurements, outcome frequencies, convex state spaces, affine effects/transformations, and subsystem composition. The authors state that quantum theory and classical probability theory are the theories satisfying their requirements; strengthening reversible transformations with continuity rules out the classical case.

Disposition: LRT cannot cite Masanes-Muller as establishing

`local tomography + continuity -> complex Hilbert space`.

The full premise burden is materially larger.

### Hardy 2001

Primary source: L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012.

Hardy derives quantum theory from five axioms. His fifth axiom requires continuous reversible transformations between pure states; Hardy explicitly notes that dropping continuity returns classical probability theory. Hardy's result therefore does not support the compressed theorem form unless the other Hardy axioms are also independently supplied.

Disposition: Hardy is a reconstruction route, not a theorem allowing the rest of the premise set to be omitted.

### Chiribella, D'Ariano and Perinotti 2011

Primary source: G. Chiribella, G. M. D'Ariano and P. Perinotti, *Informational derivation of Quantum Theory*, Physical Review A 84, 012311 (2011); arXiv:1011.6451.

Their reconstruction uses five elementary axioms:

- causality,
- perfect distinguishability,
- ideal compression,
- local distinguishability,
- pure conditioning,

plus the purification postulate, which singles out quantum theory within the broader class.

Disposition: CDP cannot be treated as interchangeable with Hardy or Masanes-Muller, nor as support for `local tomography + continuity` alone.

## Finding

The current LRT Step 4 is not a single imported theorem with a small premise set. It is a **reconstruction-family junction**.

The current presentation collapses:

- Hardy's five-axiom route,
- Masanes-Muller's five-requirement GPT route,
- CDP's five axioms plus purification,

into one synthetic theorem. This creates an entailment illusion: premises supplied by the reconstruction literature disappear from view and the remaining LRT premises appear to do more work than they actually do.

## Revised classification

Current arrow:

`Local Tomography + reconstruction premises -> complex Hilbert space`

Classification: IMPORTED_THEOREM / BRIDGE / EMPIRICAL-OPERATIONAL PREMISES

Disposition: REQUIRES_NEW_PREMISE

Reason: local tomography is only one member of a larger reconstruction axiom set. Continuous reversibility is also insufficient by itself. A valid LRT reconstruction must select one reconstruction theorem, enumerate its full assumptions, and independently justify every assumption not supplied by established mathematics.

## Recommended redirect

Do not try to preserve a monolithic `L3 -> QM` chain.

Split the programme into layers:

### Layer 1: LRT Ontology

`X = [L3 : I_infinity : A]`

Grounds:

- logical admissibility,
- informational individuation,
- actuality/actualization,
- determinate identity.

### Layer 2: Physics Interface Principles

Candidate principles include:

- Operational Determinacy (OD),
- Local Operational Decomposability (LOD),
- convex operational state representation,
- composition rules,
- reversible-transformation assumptions,
- continuity assumptions,
- information-capacity/equivalence assumptions.

These must be explicit and individually challengeable.

### Layer 3: Reconstruction Descendant

Choose a specific operational reconstruction programme and ask:

`LRT ontology + explicit interface principles -> premises of reconstruction theorem?`

Only after all theorem premises are discharged should LRT claim recovery of quantum structure.

This architecture allows multiple descendant reconstructions. If two independent reconstruction routes can be grounded from the same small interface set, that becomes positive evidence for explanatory compression. If they require unrelated imported assumptions, LRT should say so.

## Severe test for explanatory derivation

For each selected reconstruction theorem:

1. List every premise exactly as required by the primary source.
2. Remove knowledge of quantum mechanics from consideration.
3. Ask whether LRT ontology plus independently stated interface principles would motivate that premise before knowing the target theory.
4. Mark any premise motivated only because it is known to recover QM as target-conditioned.
5. Count the irreducible physics-facing assumptions left after the audit.

LRT's explanatory gain should be measured by how much of the reconstruction premise set is genuinely grounded, not by whether a Lean theorem can connect already-encoded premises to the target formalism.

## Immediate consequence for current documentation

The statement equivalent to

`H1 ∧ H2 ∧ Continuity -> CPH_over_C`

must be treated as a placeholder abstraction, not as a faithful statement of Hardy, Masanes-Muller, or CDP.

No active prose should cite those three works collectively as though they prove that compressed implication.
