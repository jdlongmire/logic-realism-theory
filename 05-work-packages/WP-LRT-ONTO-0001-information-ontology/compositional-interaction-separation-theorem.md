# Compositional interaction and local tomography: finite-dimensional separation theorem

Status: RESEARCH / CONDITIONAL MATHEMATICAL RESULT
Date: 2026-11-08
Dependency: `local-tomography-real-quantum-countermodel.md` and `local-tomography-premise-candidates.md`.
Scope: operational distinguishability under product effects, classical adaptive local protocols, and ancillary resources. No new LRT primitive or canonical axiom.

## 1. Finite-dimensional linear separation criterion

Let `V_AB` be a finite-dimensional real ordered vector space of unnormalized composite states, `S_AB` its normalized state base, and `E_A`, `E_B` sets of allowed local effects. Define the accessible product-effect span
`W := span_R { e⊗f : e∈E_A, f∈E_B } ⊆ V_AB* `.
The map `T:S_AB→R^(E_A×E_B)` evaluates every product effect.

**Proposition (exact criterion).** `T` is injective on `S_AB` if and only if
`(S_AB−S_AB) ∩ W^⊥ = {0}`.
Here `W^⊥={v∈V_AB | w(v)=0 for every w∈W}`.

**Proof.** If `T(s)=T(t)`, every generating product effect annihilates `s−t`, hence `s−t∈W^⊥`. Conversely if `s−t∈W^⊥`, every product-effect statistic agrees. Thus injectivity is equivalent to absence of nonzero differences in that annihilator. QED.

**Corollary (sufficient, not always necessary).** If `W=V_AB*`, local tomography follows. If `S_AB` has nonempty relative interior in its normalized affine hyperplane and `W` contains the unit effect, local tomography is equivalent to `W=V_AB*`: a nonzero annihilator direction has zero normalization and admits sufficiently small positive and negative perturbations around an interior state.

The latter regularity conditions must be stated; one cannot infer full dual spanning merely from injectivity on a thin state subset.

## 2. Why adaptive LOCC without new resources does not repair the obstruction

Consider finite-round protocols whose branches consist only of **local instruments**, conditioning on prior classical outcomes, and classical communication, with no shared ancillary entanglement or nonlocal operations. For a fixed transcript, its outcome probability is an evaluation by a positive product effect `e_h⊗f_h`; a coarsened outcome is a sum of such effects. Consequently every transcript or coarse-grained effect belongs to `W`.

Therefore, if `s−t∈W^⊥`, **no such finite-round LOCC protocol distinguishes s from t**. The argument assumes standard bilinear composition of local instrument outcome probabilities, including the usual operational dual action of local updates. A generalized theory with a different instrument calculus must be checked separately.

The proposition does not claim that every separable effect is implementable by LOCC; it only uses the one-way containment `LOCC effects ⊆ span(product effects)`.

## 3. Concrete real-quantum obstruction

For real two-level systems set `J=[[0,-1],[1,0]]`, `K=J⊗J`, and `ρ±=(I₄±tK)/4` for `0<t≤1`. All real symmetric local effects `E,F` obey `Tr(JE)=Tr(JF)=0`; hence `Tr[(ρ+−ρ−)(E⊗F)]=0`. The globally allowed effect `P=(I₄+K)/2` separates them by `t`.

The real symmetric single-system operator space has dimension 3; its product span on two rebits has dimension 9, while the real symmetric four-dimensional composite operator space has dimension 10. The missing direction is `J⊗J`. Local adaptive protocols confined to the product-effect span cannot recover that direction.

**Independent numerical validation (NumPy, executed 2026-11-08):** at `t=0.6`, eigenvalues of each state are `[0.1,0.1,0.4,0.4]`; `Tr[(ρ+−ρ−)P]=0.6`; `Tr[(ρ+−ρ−)(|0><0|⊗|0><0|)]=0`. A basis of 3 real symmetric 2×2 matrices produces 9 linearly independent tensor products. These calculations check positivity, a global effect, one local effect, and the product-span rank. The all-effects claim follows analytically from trace factorization.

## 4. What an interaction-based derivation would need

A proposed independent LRT premise must either:

**Route I: constrain the admissible composite state space.** Demonstrate that the kernel `W^⊥` contains no difference of allowed physical states, without stipulating local tomography in disguised form. Specify a physical/ontological principle that forbids the `J⊗J` sector.

**Route II: expand the operational resources.** Specify ancillas, preparations, couplings, or interaction protocols that allow reconstruction of global state distinctions. Crucially, an ability to distinguish states by *global* protocols does **not** itself prove local tomography under the original subsystem product effects. One must prove that the new resources induce a separating family of *original local* product-effect statistics, or explicitly weaken/redefine the target property.

Shared entanglement, teleportation, or globally interacting ancillas can change what protocols can distinguish; using them as a derivation requires independently justifying the requisite state spaces, transformations, and resources. Importing full complex quantum information-processing assumptions would undermine a foundational reconstruction.

## 5. Decision for the LRT chain

- `Determinate Identity ⇒ global operational separation` remains an argued bridge.
- `Global operational separation ⇒ local tomography` is false in the stated finite-dimensional operational setting.
- `Finite-round LOCC without nonlocal resources ⇒ local tomography` is likewise insufficient.
- The next non-circular candidate is a **composite-state restriction** justified from a separately formulated interaction/actualization principle. No such principle is proven here.
- Preserve `Determinate Identity → Local Tomography` as `REQUIRES_NEW_PREMISE` and do not change canonical §3.1 labels without owner review.

## Verification and limits

This document supplies a self-contained linear-algebra proof and independently executed NumPy numerical checks. It is **not** a Lean formalization, a derivation from LRT's three primitives, or a claim that all generalized probabilistic theories have the assumed local instrument structure. Muse's separate native Step0/Step1 assignment is unaffected.

Primary context: Masanes and Müller (2011), https://arxiv.org/abs/1004.1483 ; Masanes and Müller (2012), https://arxiv.org/abs/1203.4516 .
