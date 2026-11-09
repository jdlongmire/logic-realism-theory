# CA-3: globally generated local records do not entail local tomography

Status: RESEARCH / EXPLICIT COUNTEREXAMPLE TO WEAK CA-3
Date: 2026-11-08
Scope: independent of canonical axiom changes and Muse's Lean work.

## Candidate tested

**CA-3w (recordability):** For every pair of globally distinguishable composite states there is a physically allowed interaction that deposits the distinguishing outcome into a locally readable classical record.

CA-3w is compatible with entangled states and is phrased in terms of physical interactions and records rather than asserting product-effect completeness. It is therefore a natural, falsifiable candidate for LRT's intended operational-determinacy bridge.

## Constructive counterexample in real quantum theory

Let `J=[[0,-1],[1,0]]`, `K=J⊗J` and `ρ±=(I₄±tK)/4`, `0<t≤1`. The global two-outcome projective measurement has `P+=(I₄+K)/2` and `P−=(I₄−K)/2`. Its probabilities are

`Pr(+|ρ+)=(1+t)/2`, `Pr(+|ρ−)=(1−t)/2`.

Couple the *composite* to a real classical two-state pointer and encode the projective outcome in orthogonal pointer states `|0⟩,|1⟩`. The pointer is locally measurable after the global coupling. One concrete real isometric measurement dilation on system and initialized pointer is `V|ψ⟩=P+|ψ⟩⊗|0⟩+P−|ψ⟩⊗|1⟩`. Since `P+P−=0` and `P++P−=I`, `V†V=I`; finite-dimensional real isometries extend to real orthogonal transformations on a sufficiently large space. The measurement is therefore implementable by an allowed global interaction with a real pointer.

For `t>0`, pointer outcome statistics differ, so the distinguishing information is in a **locally readable record**. Nevertheless, for every real-symmetric pair of local effects E,F on the *original two subsystems*,

`Tr[(ρ+−ρ−)(E⊗F)] = (t/2)Tr(JE)Tr(JF)=0`.

Thus **CA-3w is true for this pair, but local tomography is false**. More generally, every globally distinguishable state pair in finite-dimensional real quantum theory can be measured by an appropriate global effect and its outcome written to a local classical pointer. The model therefore satisfies the recordability principle for globally distinguishable pairs.

## Why this matters

There are three different notions:

1. Product effects measured on A and B with no global coupling beforehand.
2. An entangling/global interaction on AB followed by a local pointer readout.
3. Full global tomography with arbitrary composite measurements.

(2) and (3) may be available when (1) is not. Treating the pointer as a new local subsystem *after* a global interaction does not establish that the **original** AB state was characterized by original A/B product-effect statistics.

A strengthened CA-3s requiring records from *strictly local instruments and classical communication only* is sufficient to separate all states only because it effectively asserts the injectivity of the local measurement map; it must receive an independent physical justification to avoid circularity.

## Consequence for LRT

- CA-3w, even when combined with binary actualization and global operational distinguishability, does **not** imply local tomography.
- Any non-circular alternative must restrict which global interactions count as ontologically primitive, or derive a structural relation between global and product effects from independent principles.
- This result does not exclude the logical possibility of a future successful LRT compositional theorem. It falsifies this precise weak recordability formulation.
- Do not promote CA-3w to a canonical axiom; retain `REQUIRES_NEW_PREMISE` for the determinacy-to-tomography step.

## Further research direction

Formulate a category of subsystem-local transformations and a monoidal composition rule without assuming tomography. Seek a separately motivated constraint on admissible transformations or state composition that forces the product-effect span to separate all physical states. Test the constraint against the two-rebit model and other nonlocally tomographic GPTs before attributing it to L3 or A.

## Validation and limits

The matrix probabilities and dilation isometry are elementary analytic identities and are reproducible directly. This document does not claim a Lean verification, a complete physical implementation, or a new derivation from LRT's three primitives. The finite-dimensional extension of an isometry to an orthogonal map is standard linear algebra. The use of a global measurement is essential to the counterexample.

Related internal files: `compositional-actualization-ca1-test.md`, `local-tomography-real-quantum-countermodel.md`, `compositional-interaction-separation-theorem.md`.
