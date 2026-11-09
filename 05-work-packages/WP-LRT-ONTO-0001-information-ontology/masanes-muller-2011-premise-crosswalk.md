# Masanes–Müller 2011 primary-source premise crosswalk

Status: PRIMARY FULL-TEXT AUDIT / RESEARCH; no canonical theorem promotion
Date: 2026-11-08
Target: `theory/100-LRT-CORE-PHYSICS.md` §3.2
Primary source: Masanes, L. and Müller, M. P. (2011), *A derivation of quantum theory from physical requirements*, New Journal of Physics 13, 063001, DOI 10.1088/1367-2630/13/6/063001, full text https://arxiv.org/html/1004.1483v4 , especially §§II–III and introduction.
Related author exposition: Müller, M. P. and Masanes, L. (2012/2016), *Information-theoretic postulates for quantum theory*, https://arxiv.org/html/1203.4516v3 .

## Primary theorem's actual five requirements

| 2011 requirement | Primary §III statement | Current LRT entailment | Disposition |
|---|---|---|---|
| R1: Finiteness | A capacity-two state space has finite dimension | Not entailed by L3, I∞, A, or the selection bridge | OPEN PHYSICAL/OPERATIONAL PREMISE |
| R2: Local tomography | A composite state is characterized by statistics of local subsystem measurements; equivalent to (d_AB+1)=(d_A+1)(d_B+1) | LRT's PPC-to-tomography inference is disputed by its own entailment matrix; requires operational accessibility/decomposability | OPEN BRIDGE PREMISE |
| R3: Equivalence of subspaces | The zero-probability face of a capacity-c system, for a complete measurement, is equivalent to the capacity-(c−1) state space | Not established by the selection definition or L3; stronger than vague equivalence of equal-capacity systems | OPEN PHYSICAL PREMISE |
| R4: Symmetry | Every pair of pure states is related by an allowed reversible transformation | No LRT derivation established by this audit; the 2011 paper does **not** assume continuous reversibility here | OPEN DYNAMICAL PREMISE |
| R5: All measurements allowed | Every effect on a capacity-two state space corresponds to a possible measurement outcome | Neither logical determinacy nor actualization guarantees unrestricted effects | OPEN MEASUREMENT PREMISE |

The authors work in a generalized probabilistic theory (GPT) framework that already assumes operational preparation, mixture, transformation, measurement, frequencies/probabilities, convex state spaces, and composite-system conventions. These are **background operational assumptions**, not results of the LRT three primitives. Primary §II.1–II.4 and §III.

## Critical correction: quantum versus classical alternatives

The 2011 introduction states that **classical probability theory (CPT) and quantum theory (QT)** both satisfy the five requirements. It says that strengthening R4 to continuity of reversible transformations excludes CPT and selects QT. Thus the core manuscript's four-condition shorthand (local tomography, continuous reversible dynamics, existence of entangled states, unrestricted observables) is **not** the enumerated 2011 theorem hypothesis set, and its current attribution is inaccurate.

The 2012/2016 authors' exposition explicitly gives four information-theoretic postulates and omits much technical detail. Its four include local tomography, equivalence of systems of equal information capacity, pure-state reversible transitivity, and unrestricted positive-probability effects. It should not be conflated with the exact five 2011 requirements.

## Implications for the LRT reconstruction

1. The statement `local tomography + three additional axioms ⇒ complex Hilbert space` needs a theorem-specific source and exact hypothesis list. The current manuscript's cited 2011 paper does not establish that shorthand as written.
2. The inference `χ ⇒ local tomography ⇒ complex Hilbert space` has **at least** five distinct premise obligations (including GPT background), not merely a local tomography obligation.
3. R1 is finite-dimensionality of a capacity-two *operational state space*, not finiteness of the total information domain I∞. No immediate contradiction with an infinite information domain follows.
4. R3 is a face/subspace equivalence condition and cannot be discharged by ordinary logical identity alone.
5. R4's continuity strengthening must be separated from its transitivity formulation. Conflating them obscures why the classical branch survives the original five requirements.
6. This audit does not independently prove the source's reconstruction theorem, and does not decide whether LRT can eventually derive its assumptions.

## Proposed correction for §3.2 (requires owner review)

Replace the manuscript's four-condition 2011 attribution with:

> Masanes and Müller (2011) reconstruct classical probability theory and complex quantum theory within a generalized probabilistic framework using five requirements: finiteness for capacity-two systems, local tomography, equivalence of subspaces, reversible transitivity of pure states, and unrestricted measurements for capacity-two systems. Their paper notes that an additional continuity strengthening of reversible transformations excludes the classical alternative. LRT has not yet derived all these requirements from χ; their use is therefore a conditional imported reconstruction.

Status recommendation: `IMPORTED THEOREM / CONDITIONAL ON FULL GPT AND R1–R5 ASSUMPTIONS`. The paper's *own* theorem is established mathematics conditional on its hypotheses; the LRT-to-hypotheses bridge remains unproven.

## Source verification and limitations

HIGH confidence for all five R1–R5 definitions and the CPT/QT alternative: directly read the full primary 2011 HTML, Introduction, §§II–III (https://arxiv.org/html/1004.1483v4). HIGH confidence for the four-postulate summary in the authors' later primary exposition (https://arxiv.org/html/1203.4516v3). This audit did not run new Lean code, audit Gleason/Busch, or verify every technical lemma in the 2011 appendix.

Next: obtain owner review of the proposed §3.2 correction, then update the entailment matrix and canonical manuscript in a coordinated PR. Keep Muse's Step0/Step1 Lean task independent.
