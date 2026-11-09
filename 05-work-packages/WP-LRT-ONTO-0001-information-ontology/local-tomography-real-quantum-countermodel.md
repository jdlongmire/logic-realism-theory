# Operational determinacy versus local tomography: a real-quantum countermodel

Status: RESEARCH RESULT / CONDITIONAL BRIDGE; not a canonical theorem amendment
Date: 2026-11-08
Related: WP-LRT-ENT-0001; WP-LRT-ONTO-0001; core physics §3.1

## Exact question

Does the ontological actualization bridge `C=L3(I∞)`, `AΩ={i∈C | A(i)=actual}`, plus determinate identity and the existence of some distinguishing measurement for each pair of states, entail that **product effects of local measurements** separate every pair of composite states?

**Answer: no, without an additional local-accessibility/compositional premise.** The following explicit finite-dimensional real-quantum model separates the concepts.

## Constructive witness

Let each subsystem be a two-dimensional *real* quantum system. Define the real antisymmetric matrix
`J = [[0,-1],[1,0]]`. The tensor `K=J⊗J` is real symmetric, traceless, and obeys `K²=I₄`. For any `0<t≤1`, define two real symmetric normalized positive states on the composite:
`ρ₊=(I₄+tK)/4` and `ρ₋=(I₄−tK)/4`.
Their eigenvalues are `(1±t)/4`, hence both are positive semidefinite; `Tr ρ±=1`, and `ρ₊≠ρ₋`.

For any real symmetric local effects `E,F`, `Tr(JE)=Tr(JF)=0`, so
`Tr[(ρ₊−ρ₋)(E⊗F)] = (t/2)Tr(JE)Tr(JF)=0`.
Consequently **all local product-effect statistics agree** for these two distinct global states.

Nevertheless the globally admissible projective effect `P=(I₄+K)/2` distinguishes them:
`Tr[(ρ₊−ρ₋)P]=t` (nonzero for `t>0`).
Thus each state has determinate identity and a possible *global* distinguishing measurement, while the composite is not locally tomographic. At `t=1`, the states are orthogonal rank-two mixtures.

Actualization is independent of the obstruction: choose `A` to mark either or both of these admissible states actual. Mere membership in `AΩ` adds no constraint on the available effect algebra or the injectivity of the local statistics map. To use this example as a model of *all* LRT axioms would require checking any additional LRT restrictions on physical states and composites. It is a countermodel to the **specific inference** from determinacy/global operational distinguishability to local tomography, not a refutation of the full ontology.

## Distinguish three predicates

1. **Ontic identity:** `s≠t` is a determinate proposition.
2. **Global operational separation:** some admissible composite measurement `M` has `p(M|s)≠p(M|t)`.
3. **Local tomography:** some product effect `E⊗F` has `p(E⊗F|s)≠p(E⊗F|t)` for every distinct composite pair.

(3) implies (2), but (1) and (2) do not entail (3). Even requiring every identity-making relation to be measurable *somehow* does not establish that local product effects are jointly separating.

## The missing premise

Define **Local Product-Effect Separation (LPES)**:

For every composite AB and distinct admissible states `s,t∈S_AB`, there exist allowed local effects `e_A∈E_A`, `e_B∈E_B` such that `(e_A⊗e_B)(s)≠(e_A⊗e_B)(t)`.

LPES is extensionally equivalent to state local tomography in the finite-dimensional GPT setting with product-effect probabilities. Asserting LPES is therefore an explicit operational assumption, not a derivation. A non-circular LRT derivation must produce an independently motivated structural axiom implying LPES, with a proof that rules out real-quantum `J⊗J` degrees of freedom without presupposing the desired local statistics.

The original core physics §3.1 argues that accessible identity-making relations must be *locally* accessible. The real-quantum model pinpoints the unproved transition: **global accessibility of a relation does not imply access through product effects**. It also distinguishes local tomography from recovering a composite from the two reduced states alone: local tomography includes **correlations** of joint local measurement outcomes.

## Proposed research decision

- Keep `χ→AΩ` as the accepted constitutive bridge.
- Classify `Determinate Identity→Local Tomography` as `REQUIRES_NEW_PREMISE` until a non-circular LPES-deriving condition is demonstrated.
- Treat `Operational Determinacy` as an independently substantive operational bridge, even if it is intended as a constitutive explication.
- Do not claim that an experimentally disfavored real-Hilbert theory is *logically* inconsistent. Experimental exclusion and logical entailment are distinct.
- Leave canonical §3.1 epistemic labels unchanged pending owner review; use this document as a countermodel and dependency specification.

## Primary references

- Müller, M. P. and Masanes, L. (2012/2016), *Information-theoretic postulates for quantum theory*, https://arxiv.org/abs/1203.4516 . Authors discuss local tomography as a separate postulate.
- de la Torre, G., Masanes, L., Short, A. J. and Müller, M. P. (2012), *Deriving quantum theory from its local structure and reversibility*, Phys. Rev. Lett. 109, 090403, https://doi.org/10.1103/PhysRevLett.109.090403 .
- Renou, M.-O. et al. (2021), *Quantum theory based on real numbers can be experimentally falsified*, Nature 600, 625–629, https://www.nature.com/articles/s41586-021-04160-4 . Real versus complex quantum network predictions under specified compositional assumptions.
- Chiribella, G., D'Ariano, G. M. and Perinotti, P. (2012), *Quantum Theory, Namely the Pure and Reversible Theory of Information*, Entropy 14, 1877–1893, https://www.mdpi.com/1099-4300/14/10/1877 . Authors explicitly state local tomography as a principle.

## Validation and limits

The matrix identities above are direct algebraic calculations, not a Lean proof. No code or new axioms were introduced into the canonical formalization. The independent Muse Lean assignment is unaffected. Primary author papers were identified and cross-checked for their formulation of local tomography; the matrix witness is presented with all needed arithmetic so it can be independently reproduced.
