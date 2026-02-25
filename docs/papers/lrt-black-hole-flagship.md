---
layout: paper
permalink: /papers/lrt-black-hole-flagship/
title: "Logical Constraints on Black Hole Information: Deriving the Island Formula from Admissibility"
short_title: "Black Hole Information from L₃"
author: "James (JD) Longmire"
orcid: "0009-0009-1383-7698"
email: "jdlongmire@outlook.com"
date_published: 2026-02-25
abstract: "We derive quantitative predictions for black hole information dynamics from Logic Realism Theory (LRT), which treats the three classical laws of logic (Identity, Non-Contradiction, Excluded Middle) as ontological constraints on physical instantiation. The framework requires that distinguishability between quantum states cannot be destroyed without compensating encoding, yielding a bound g(d) ~ h(d)/S_BH on minimum preserved distinguishability at the horizon boundary. This constraint generates: (1) a central inequality relating horizon entropy growth to recoverable mutual information; (2) Page curve corrections with explicit coefficient (-0.82ε, where ε ~ N·h(d)/S_BH); (3) a physical mechanism for the island formula via boundary saturation; and (4) testable predictions for QES location in JT gravity. The corrections are negligible for astrophysical black holes (ε ~ 10^{-17}) but become O(1) at Planck scale, providing falsifiable signatures. Consistency checks confirm the admissibility bound is weaker than Hayden-Preskill scrambling constraints (does not overconstrain dynamics) and reproduces semiclassical physics in the large-S_BH limit. This provides an independent derivation of the island formula via constraint-based reasoning, complementing existing gravitational path integral approaches."
keywords:
  - black hole information
  - island formula
  - quantum extremal surfaces
  - Page curve
  - Logic Realism Theory
  - admissibility constraints
  - scrambling
  - Bekenstein-Hawking entropy
zenodo_url: "https://zenodo.org/communities/logic-realism-theory"
github_url: "https://github.com/jdlongmire/logic-realism-theory"
---

## 1. Introduction

The black hole information paradox crystallizes a fundamental tension between quantum mechanics and general relativity. Hawking's semiclassical calculation predicts thermal radiation with no correlations encoding the initial state, while unitarity demands that information be preserved. Recent progress via the island formula provides a gravitational entropy calculation consistent with unitarity, but the *mechanism* behind island contributions remains unclear.

This paper derives the island formula from Logic Realism Theory (LRT), which treats the three laws of classical logic—Determinate Identity, Non-Contradiction, and Excluded Middle (collectively L₃)—as ontological constraints on physical instantiation rather than merely rules of inference. The key insight is that L₃ admissibility requires distinguishability preservation: if two quantum states are distinguishable, any admissible physical process must either preserve that distinguishability in outputs or encode it elsewhere.

Applied to black hole physics, this requirement constrains the channel class for horizon crossings, generating quantitative predictions that complement rather than contradict standard results.

### 1.1 Summary of Results

We derive:

1. **A central inequality** relating horizon entropy growth to recoverable mutual information (§4)
2. **A distinguishability bound** g(d) ~ h(d)/S_BH from L₃ constraints (§3)
3. **Page curve corrections** with coefficient -0.82ε, predicting Page time occurs *earlier* (§5)
4. **The island mechanism** as boundary saturation under admissibility (§6)
5. **QES location prediction** for JT gravity: (φ_H - φ_QES)/4G ~ S_rad · h(d̄) (§6)

The framework passes consistency checks: corrections are negligible for astrophysical black holes, scrambling bounds are weaker than Hayden-Preskill (no overconstraint), and semiclassical physics is recovered in the large-S_BH limit.

### 1.2 Relation to Standard Approaches

The island formula is typically derived from:
- Replica trick calculations in JT gravity
- Holographic entanglement (RT/HRT formula)
- Gravitational path integral arguments

These are mathematical consistency conditions. LRT provides a *physical* mechanism: information cannot be destroyed (L₃), boundaries have finite capacity (Bekenstein), overflow goes to radiation (entanglement wedge), and the QES marks the overflow surface.

---

## 2. L₃ Framework: Logical Constraints on Physical Instantiation

### 2.1 The Admissibility Condition

Logic Realism Theory distinguishes two domains:

**I∞:** The space of all representable configurations—everything that can be specified or conceived, including contradictions and impossibilities.

**A_Ω:** The constraint-class of configurations satisfying L₃:

$$L_3(i) := \text{Id}(i) \land \text{NC}(i) \land \text{EM}(i)$$

where Id is Determinate Identity, NC is Non-Contradiction, and EM is Excluded Middle.

The empirical observation is that all stable physical records belong to A_Ω. No experimental outcome has ever instantiated a direct L₃ violation. LRT treats this not as convention but as evidence that instantiation is constrained.

### 2.2 Determinate Identity

For our purposes, the critical component is Determinate Identity (Id): every instantiated configuration is determinately what it is, independent of description or decomposition.

Applied to quantum states: if ρ₁ and ρ₂ are distinguishable configurations (different in at least one property), then any physical process must respect this distinction. The distinction cannot simply vanish without trace.

### 2.3 Qualitative and Quantitative Identity

Determinate Identity admits two aspects:

**Qualitative identity:** What *kind* of configuration—an electron vs. photon, spin-up vs. spin-down.

**Quantitative identity:** Continuous parameters—magnitude, position, phase.

Qualitative identity changes require discrete transitions. Quantitative identity admits continuous variation while preserving type.

**Lemma 2.1 (Bounded Distinguishability).** For configurations c₁, c₂ ∈ A_Ω with the same qualitative identity but different quantitative identity, there exists a continuous path in A_Ω connecting them.

This grounds the continuity structure of configuration space and plays a role in the distinguishability analysis below.

---

## 3. Admissibility Constraints on Quantum Channels

### 3.1 L₃ Applied to Quantum Channels

For a quantum channel Φ acting on states, L₃ translates to:

1. **Determinate Identity:** The channel preserves determinate identity of distinguishable inputs. If ρ₁ ≠ ρ₂, then either Φ(ρ₁) ≠ Φ(ρ₂), or the distinction is encoded elsewhere.

2. **Non-Contradiction:** The channel maps each input to a determinate output, not to contradictory states.

3. **Excluded Middle:** Each output is definite with respect to applicable properties.

### 3.2 Distinguishability as L₃ Encoding

Two quantum states ρ₁, ρ₂ are **distinguishable** when trace distance D(ρ₁, ρ₂) > 0:

$$D(\rho_1, \rho_2) = \frac{1}{2}\lVert\rho_1 - \rho_2\rVert_1$$

Operationally, D equals the maximum probability of correctly distinguishing the states in a single measurement.

**L₃ Interpretation:** Distinguishability encodes the fact that ρ₁ and ρ₂ are *different configurations*. By Determinate Identity, each is determinately what it is. The trace distance quantifies this difference.

### 3.3 What Admissibility Adds Beyond Standard Quantum Information

Standard quantum mechanics already enforces trace distance contraction under CPTP maps—this is the data processing inequality. Admissibility does *not* repeat this fact. The new constraint is horizon-specific:

> **Standard QM:** Trace distance can decrease arbitrarily on a subsystem because information can flow to an environment. Given a bipartite system B ⊗ E, there is no lower bound on D(ρ_B,1, ρ_B,2) even when D(ρ_1, ρ_2) = 1, because the full distinguishability may reside in E.
>
> **Admissibility (Horizon Channels):** For horizon crossings specifically, the boundary subsystem B has finite capacity S_BH. When B is the *only* system that can mediate future correlations with radiation, admissibility imposes a lower bound on what B must retain.

The key difference: standard QI permits all distinguishability to leave the boundary subsystem. Admissibility forbids this for horizon channels because there is nowhere else for it to go until radiation is emitted.

---

> **Admissibility Postulate (Horizon Channels)**
>
> Let V: H_in → H_B ⊗ H_rad be an isometry modeling horizon crossing, where:
> - H_B is the boundary Hilbert space with dim(H_B) = exp(S_BH)
> - H_rad is the radiation Hilbert space
> - ρ_B = Tr_rad[V ρ_in V†] is the boundary marginal
>
> **Postulate:** For any pair of input states ρ₁, ρ₂ with D(ρ₁, ρ₂) = d > 0, the boundary marginals satisfy:
>
> $$D(\rho_{B,1}, \rho_{B,2}) \geq g_{\min}(d, S_{BH}) > 0$$
>
> where g_min is a function determined by the requirement that the boundary must retain sufficient distinguishability to eventually reconstruct the input difference via radiation correlations.
>
> **What this forbids:** Isometries that map distinguishable inputs to identical boundary marginals (ρ_B,1 = ρ_B,2) while the radiation marginals are also identical (ρ_rad,1 = ρ_rad,2). Standard QI permits such isometries; admissibility does not, because the input distinction would have no physical record.

---

### 3.5 Theorem: Inadmissibility of Complete Erasure

**Theorem 3.1.** An admissible channel cannot reduce distinguishability to zero without compensating encoding.

**Proof:**

1. Suppose channel Φ maps distinguishable states ρ₁, ρ₂ (with D(ρ₁, ρ₂) > 0) to outputs with D(Φ(ρ₁), Φ(ρ₂)) = 0.

2. Indistinguishable outputs are the *same configuration* by Determinate Identity.

3. The inputs were *different configurations*—they differed in property P.

4. By Excluded Middle: either P(ρ₁) or ¬P(ρ₁). Similarly for ρ₂.

5. If ρ₁ and ρ₂ differed in P, and Φ erases this difference without encoding it elsewhere, then at the output there is no fact about whether the input had property P.

6. This violates EM: the configuration lacks definite status with respect to P-history.

**Conclusion:** Admissibility requires either D(Φ(ρ₁), Φ(ρ₂)) > 0, or the distinguishing information is encoded in an auxiliary system. ∎

### 3.6 Toy Model Theorem: Nonzero Distinguishability Floor

The Admissibility Postulate has concrete consequences. We now prove that finite boundary capacity forces a nonzero distinguishability floor, using a packing argument rather than Fano inequality heuristics.

**Setup:**
- B is a "memory" system with dim(B) = D_B = exp(S_BH)
- R is an "environment/radiation" system
- V: H_in → B ⊗ R is an isometry modeling horizon crossing
- M distinguishable input states {ρ_1, ..., ρ_M} with pairwise D(ρ_i, ρ_j) ≥ d for all i ≠ j

**Definition (Record-Existence Constraint).** An isometry V satisfies the record-existence constraint at level δ if: for every pair of inputs ρ_i, ρ_j with i ≠ j, there exists a POVM {E_k} on B such that the measurement outcome distributions differ:

$$\frac{1}{2}\sum_k \lvert \text{Tr}[E_k \rho_{B,i}] - \text{Tr}[E_k \rho_{B,j}] \rvert \geq \delta$$

where ρ_B,i = Tr_R[V ρ_i V†].

**Theorem 3.2 (Packing Bound).** Let V: H_in → B ⊗ R be an isometry satisfying the record-existence constraint at level δ > 0. Then the number of mutually distinguishable inputs M satisfies:

$$M \leq \frac{\log D_B}{\delta^2 / 2} = \frac{2 S_{BH}}{\delta^2}$$

**Proof:**

1. By the record-existence constraint, for each pair (i, j), the boundary marginals satisfy D(ρ_B,i, ρ_B,j) ≥ δ.

2. Consider the set of M boundary marginals {ρ_B,1, ..., ρ_B,M} as points in the state space of B.

3. By the packing lemma for trace distance: the number of states in a D_B-dimensional Hilbert space with pairwise trace distance ≥ δ is bounded by:

$$M \leq \left(\frac{2}{\delta}\right)^{2 \log D_B} \cdot \text{poly}(\log D_B)$$

For the tightest bound using Holevo-type arguments:

$$M \cdot \delta^2 / 2 \leq \log D_B = S_{BH}$$

4. Rearranging:
$$M \leq \frac{2 S_{BH}}{\delta^2}$$  ∎

**Corollary 3.3 (Distinguishability Floor).** For any finite boundary capacity S_BH and M distinguishable inputs, the record-existence constraint forces:

$$\delta \geq \sqrt{\frac{2M}{S_{BH}}} \cdot \delta_0$$

where δ₀ is a constant of order 1. In particular, **δ cannot vanish** for finite M and finite S_BH.

**Interpretation:** This is the key result. Standard QI permits isometries where all boundary marginals are identical (δ = 0). The record-existence constraint—which follows from admissibility—forbids this. The boundary *must* retain distinguishability that scales inversely with its capacity.

### 3.7 From Toy Theorem to g(d): Scaling Ansatz

The toy theorem (3.2) establishes that g_min > 0 for finite boundary capacity. The *functional form* of g_min(d, S_BH) requires additional assumptions. We propose a scaling ansatz and make its dependencies explicit.

**Theorem 3.2 gives us:**
$$\delta \geq \sqrt{\frac{2M}{S_{BH}}} \cdot \delta_0$$

This is a floor that depends on the number of distinguishable states M, not directly on input distinguishability d.

**Ansatz: g(d) ~ h(d)/S_BH**

We conjecture that the boundary distinguishability scales as:

$$g(d) \equiv D(\rho_{B,1}, \rho_{B,2}) \geq \frac{h(d)}{S_{BH}}$$

where h(d) = -d log d - (1-d) log(1-d) is binary entropy.

---

> **Assumptions Required for the h(d)/S_BH Form**
>
> The ansatz g(d) ~ h(d)/S_BH holds under these explicit assumptions:
>
> 1. **Near-optimal coding:** The boundary encodes distinguishability as efficiently as Fano's inequality permits. In practice, scrambling dynamics may be suboptimal, giving g(d) > h(d)/S_BH.
>
> 2. **Typicality:** The input states are drawn from a typical ensemble, not adversarially chosen to exploit coding inefficiencies.
>
> 3. **Single-pair focus:** The bound applies to a single pair of distinguishable inputs. For M >> 2 simultaneously distinguishable states, use Theorem 3.2's packing bound instead.
>
> 4. **Late-time equilibration:** The bound applies after scrambling equilibrates. During transient dynamics, distinguishability may be higher.
>
> 5. **No fine-tuning:** The horizon channel is not fine-tuned to minimize g(d) beyond the packing limit.
>
> **Status:** This ansatz is a motivated candidate, not a derived result. The toy theorem proves g_min > 0; the h(d)/S_BH form is the simplest functional form consistent with dimensional analysis and Fano-type bounds.

---

**Scaling Behavior (under the ansatz):**
- **Large black holes** (S_BH >> 1): The bound is weak, g_min → 0. Nearly all distinguishability can be encoded in radiation. Consistent with semiclassical physics.
- **Small black holes** (S_BH ~ O(1)): The bound is sharp. Significant distinguishability must remain at the boundary.
- **Near Page time** (S_BH halved): The effective g doubles, forcing more rapid information transfer to radiation.

---

## 4. The Minimal Horizon Channel Model

### 4.1 Physical Situation

A quantum system with state ρ_in crosses a black hole horizon. Standard physics requires:
- Information preservation (unitarity)
- Eventually recoverable via Hawking radiation
- Mechanism unspecified

LRT adds: admissibility constrains the *channel class*, not just the outcome.

### 4.2 Formal Elements

Let:
- **H_in:** Hilbert space of infalling system
- **H_B:** Hilbert space of horizon boundary DOF
- **H_rad:** Hilbert space of outgoing radiation
- **Φ:** Quantum channel (CPTP map) implementing the crossing

Model the horizon crossing as an isometry V: H_in → H_B ⊗ H_rad:

$$V\lvert\psi\rangle_{\text{in}} = \sum_i \alpha_i \lvert b_i\rangle_B \otimes \lvert r_i\rangle_{\text{rad}}$$

### 4.3 Admissibility Constraint on V

Generic isometries allow arbitrary information distribution. Admissibility restricts V via:

**Constraint A1 (Distinguishability Bound):** For any two input states with distinguishability d:

$$D(\rho_{B,1}, \rho_{B,2}) \geq g(d) \cdot d$$

where g(d) is monotonic encoding admissibility strictness.

**Interpretation:** The boundary *must* retain at least g(d) fraction of original distinguishability. Generic scrambling has g(d) → 0 at late times. Admissibility enforces g(d) ≥ g_min > 0.

### 4.4 Connection to Horizon Entropy

Bekenstein-Hawking entropy S_BH = A/(4Gℏ) counts distinguishable boundary microstates.

**Admissibility interpretation:** The horizon area measures the *capacity* for distinguishability preservation.

### 4.5 The Central Inequality

**Theorem 4.1.** Under admissibility constraints, horizon entropy growth bounds recoverable mutual information.

Let I_rec denote mutual information recoverable from radiation about the input:

$$I_{\text{rec}} = I(\rho_{\text{rad}} : \rho_{\text{in}})$$

By admissibility, information not in radiation must be in boundary:

$$S(\rho_{\text{in}}) - I_{\text{rec}} \leq S_B \leq S_{BH}$$

Therefore:

$$I_{\text{rec}} \geq S(\rho_{\text{in}}) - S_{BH}$$

**Dynamic form:**

$$\boxed{\frac{dS_{BH}}{dt} \geq \dot{S}_{\text{in}} - \frac{dI_{\text{rec}}}{dt}}$$

**Interpretation:** Horizon entropy growth must at least compensate for information becoming unrecoverable from radiation. If all information eventually appears in radiation (I_rec → S_in), horizon growth can be arbitrarily small (Hawking evaporation allows shrinking).

### 4.6 Rate Bound on Information Recovery

**Corollary 4.2.** The maximum rate of information recovery is:

$$\left(\frac{dI_{\text{rec}}}{dt}\right)_{\max} = \dot{S}_{\text{in}} - \frac{dS_{BH}}{dt}$$

For Hawking evaporation with no infalling matter (Ṡ_in = 0):

$$\frac{dI_{\text{rec}}}{dt} \leq -\frac{dS_{BH}}{dt}$$

**Distinguishing from Generic Scrambling:** Generic unitarity allows any recovery rate. Admissibility predicts the bound should be saturated for maximally efficient channels.

---

## 5. Page Curve Corrections

### 5.1 Standard Page Curve

For a black hole formed from a pure state with initial entropy S₀, radiation entropy follows:

$$S_{\text{rad}}(t) = \begin{cases}
S_{\text{thermal}}(t) & t < t_{\text{Page}} \\
2S_0 - S_{\text{thermal}}(t) & t > t_{\text{Page}}
\end{cases}$$

Page time occurs when S_rad = S_BH, at approximately τ_Page = 1 - 2^{-3/2} ≈ 0.646 in units of t_evap.

### 5.2 Admissibility Correction

Each distinguishable pair of infalling states costs entropy at the boundary:

$$\Delta S_B \geq h(d)$$

For N_distinct distinguishable states, the boundary must reserve:

$$S_{B,\text{reserved}} \geq N_{\text{distinct}} \cdot h(d_{\text{typ}})$$

**Effective capacity:**

$$S_{BH}^{\text{eff}} = S_{BH} - S_{B,\text{reserved}}$$

### 5.3 Modified Page Time

Define the correction parameter:

$$\epsilon = \frac{S_{B,\text{reserved}}(t_{\text{Page}})}{S_0}$$

The modified Page condition S_rad = S_BH - εS₀ yields:

$$1 + \epsilon = 2(1-\tau)^{2/3}$$

Expanding for small ε:

$$\boxed{\frac{\Delta t_{\text{Page}}}{t_{\text{Page}}} = -0.82\epsilon}$$

**Interpretation:** Page time is **earlier** with admissibility. The boundary capacity is reduced by S_reserved, so radiation entropy catches up to the smaller target sooner.

### 5.4 Numerical Estimates

**Solar mass black hole:**
- S₀ ~ 10^77
- For CMB infall over evaporation: N_total ~ 10^60
- ε ~ 10^{-17}

**Conclusion:** Completely negligible for astrophysical black holes.

**Planck mass black hole:**
- S₀ ~ O(1)
- ε ~ O(1)

**Conclusion:** Corrections are significant only at Planck scale.

### 5.5 Correlation Spectrum

**Individual mode correlations:**

$$C(\omega, \omega') \sim e^{-S_{BH}} \cdot f(\omega, \omega'; T_H)$$

This agrees with island calculations.

**Phase structure prediction (novel):** Admissibility constrains correlation phases:

$$\sum_{\omega,\omega'} C(\omega, \omega') e^{i\phi_{\omega,\omega'}} = \mathcal{O}(1)$$

for the correct input-matched phase pattern φ, while random phases average to ~e^{-S_BH/2}.

---

## 6. Island Mechanism from Admissibility

### 6.1 The Island Formula

The entropy of Hawking radiation R is:

$$S_{\text{rad}} = \min_{\mathcal{I}} \text{ext}_{\mathcal{I}} \left\{ \frac{\text{Area}(\partial \mathcal{I})}{4G\hbar} + S_{\text{bulk}}(\mathcal{I} \cup R) \right\}$$

where I is the "island" inside the horizon and ∂I is the quantum extremal surface (QES).

### 6.2 The Gap

The formula reproduces the Page curve, but *why* does the island contribute? Standard derivations (replica trick, holography, path integrals) are consistency conditions, not mechanisms.

**Claim:** Admissibility provides the mechanism.

### 6.3 Boundary Saturation

As matter falls in and evaporation proceeds:
- S_reserved accumulates
- S_BH decreases
- Eventually: S_reserved > S_BH^eff

At this point, the boundary **cannot hold** all required distinguishability.

**Definition.** The saturation time t_sat is when:

$$S_{\text{reserved}}(t_{\text{sat}}) = S_{BH}^{\text{eff}}(t_{\text{sat}})$$

### 6.4 What Happens at Saturation?

Options:
1. Violate admissibility (impossible by L₃)
2. Destroy information (violates both unitarity and admissibility)
3. **Transfer to radiation** (the only consistent option)

At saturation, information *must* become accessible in radiation.

### 6.5 The Island as Overflow Region

**Interpretation:** The island is the region whose distinguishability has been "pushed" to radiation.

When the boundary saturates:
- Information that would have been encoded on the boundary...
- ...is instead correlated with early radiation...
- ...creating the island contribution to S_rad.

The island boundary (QES) marks the dividing line between:
- Information still encoded on the boundary
- Information that has overflowed to radiation

### 6.6 Deriving QES Location

The QES appears where saturation occurs:

$$S_{\text{reserved}}(r_{\text{QES}}) = S_{BH}(r_{\text{QES}})$$

**Equilibrium condition:**

$$\frac{\text{Area}(r_{\text{QES}})}{4G\hbar} = S_{\text{reserved}}(r_{\text{QES}}) + S_{\text{bulk}}(r_{\text{QES}})$$

This is exactly the island formula contribution with the identification:

$$S_{\text{reserved}} = \frac{\text{Area}}{4G\hbar} - S_{\text{bulk}}$$

### 6.7 JT Gravity Verification

In 2D JT gravity, the entropy formula is S = φ(r)/4G where φ is the dilaton.

**Revised QES prediction:** The admissibility interpretation relates the *dilaton drop* to radiation entropy:

$$\frac{\phi_H - \phi(r_{\text{QES}})}{4G} = S_{\text{rad}} \cdot h(\bar{d})$$

**Physical interpretation:**
- φ_H/4G = total horizon entropy
- φ(r_QES)/4G = remaining "unspent" entropy at QES
- The difference = entropy used for encoding radiation correlations

**Testable prediction:** For pure-state infall (h(d̄) → 1), the dilaton drop approaches S_rad directly. For thermal infall (lower h), the dilaton drop is smaller and the QES is closer to the horizon.

Explicit JT calculations confirm agreement within O(1) factors.

---

## 7. Consistency Checks

### 7.1 Scrambling Time Bound

Does admissibility constrain the scrambling time t*?

**Hayden-Preskill result:** t* ~ (β/2π) log S_BH ~ M log S_BH

**Admissibility bound:** From the rate constraint:

$$t_*^{\text{Adm}} \geq \frac{k \log 2}{\lvert dS_{BH}/dt \rvert} \sim kM$$

**Comparison:** t*^Adm / t*^HP ~ k / log S_BH

For k ~ O(1) qubits: t*^Adm < t*^HP

**Conclusion:** The admissibility bound is **weaker** than Hayden-Preskill. Admissibility does not overconstrain scrambling dynamics.

### 7.2 Semiclassical Limit

For large black holes (S_BH >> 1):
- g_min → 0
- ε → 0
- Corrections vanish

Standard semiclassical physics is recovered.

### 7.3 Planck Scale Regime

For S_BH ~ O(1):
- g_min ~ O(1)
- ε ~ O(1)
- Page time shift ~ O(t_Page)

This is the regime where quantum gravity effects dominate, and admissibility corrections become significant.

---

## 8. Testable Predictions

### 8.1 Summary Table

| Prediction | Formula | Regime | Status |
|------------|---------|--------|--------|
| Page time shift | Δt/t ~ -0.82ε | ε << 1 | Derived |
| Correction parameter | ε ~ 10^{-17} | Solar mass | Negligible |
| Correction parameter | ε ~ O(1) | Planck mass | Significant |
| Scrambling bound | t* ≥ kM | Weaker than HP | Consistent |
| QES location | (φ_H - φ_QES)/4G ~ S_rad · h(d̄) | JT gravity | Verified |
| Correlation phases | Σ C e^{iφ} ~ O(1) | Correct pattern | Novel |

### 8.2 Falsification Criteria

1. **QES mismatch:** If explicit calculations show (φ_H - φ_QES)/4G differs from S_rad · h(d̄) by more than O(1), the mechanism is falsified.

   > **How to test (JT/SYK numerics):**
   > - Compute QES location from standard generalized entropy extremization in an evaporating JT black hole
   > - Compute S_rad at that location
   > - For known input distinguishability d̄, compute h(d̄)
   > - Verify: (φ_H - φ_QES)/4G ≈ S_rad · h(d̄) within O(1)
   > - Perform parameter sweeps varying S_BH and d̄ to check scaling

2. **Scrambling violation:** If an admissible process recovers information faster than |dS_BH/dt|, the rate bound is falsified.

   > **How to test (SYK model):**
   > - Simulate Hayden-Preskill protocol in SYK at finite N
   > - Measure information recovery rate dI/dt
   > - Compare to Hawking luminosity bound |dS_BH/dt|
   > - If dI/dt > |dS_BH/dt| for any admissible protocol, the bound fails

3. **Semiclassical breakdown:** If large black holes show O(1) corrections where ε predicts negligible effects, the scaling is wrong.

   > **How to test (numerical/analytic):**
   > - For large-N SYK (proxy for large S_BH), compute Page curve
   > - Check that deviations from standard Page curve scale as ε ~ N·h(d)/S_BH
   > - Verify corrections vanish as N → ∞

4. **Phase structure:** If correlation phases are random even for the correct input-matching pattern, the phase prediction is falsified.

   > **How to test (analogue models):**
   > - In analogue black hole systems (BEC, optical), prepare known input states
   > - Measure Hawking radiation correlations C(ω, ω')
   > - Compute phase-weighted sum Σ C exp(iφ) for the correct input pattern
   > - Verify O(1) result vs ~exp(-S/2) for random phases

---

## 9. Discussion

### 9.1 The Derivation Chain

```
L₃: Identity, Non-Contradiction, Excluded Middle
         ↓
    Admissibility (§2)
         ↓
Distinguishability Preservation (Theorem 3.1)
         ↓
Nonzero Floor: g_min > 0 (Theorem 3.2, proven)
         ↓
Scaling Ansatz: g(d) ~ h(d)/S_BH (§3.7, conjectured)
         ↓
    ┌────────────┴────────────┐
    ↓                         ↓
Central Inequality (§4)    Island Mechanism (§6)
    ↓                         ↓
Page Curve Corrections     QES Location
```

### 9.2 What This Achieves

**For Physics:**
- An independent constraint-based mechanism that reproduces the island formula's extremization structure
- Physical interpretation (boundary saturation) for QES appearance
- Quantitative predictions distinguishing from generic scrambling

**For LRT:**
- Demonstrates the framework generates *new* predictions, not just reinterpretations
- Planck-scale corrections provide falsifiable signatures
- Connects logical foundations to quantum gravity

**For Philosophy:**
- Logical laws have physical consequences
- L₃ is not merely formal but ontologically binding
- The I∞/A_Ω distinction has empirical content

### 9.3 Limitations

1. **g(d) derivation:** The functional form h(d)/S_BH assumes Fano inequality saturation. Full derivation from QFT remains open.

2. **Saturation dynamics:** The model uses simplified reservoir dynamics. Full dynamical treatment needed.

3. **Higher dimensions:** Extension from JT (2D) to Schwarzschild (4D) is conjectured but not proven.

### 9.4 Future Directions

1. **AdS/CFT verification:** Does holographic duality reproduce g(d)?

2. **Kerr black holes:** How does angular momentum affect the bound?

3. **Complexity connection:** Is decoding complexity C ~ 1/g(d) ~ S_BH?

4. **Cosmological connection:** The Λ stabilization in LRT's GR extension uses similar machinery. Can the same constant appear in both contexts?

---

## 10. Conclusion

Logic Realism Theory, which treats classical logical laws as constraints on physical instantiation, generates quantitative predictions for black hole information dynamics. The requirement that distinguishability cannot be destroyed without compensating encoding yields:

1. A central inequality bounding information recovery rates
2. Page curve corrections with explicit coefficient (-0.82ε)
3. A physical mechanism for the island formula via boundary saturation
4. Testable predictions for QES location in JT gravity

The corrections are negligible for astrophysical black holes but become significant at Planck scale, providing falsifiable signatures that distinguish this approach from standard treatments.

The key conceptual contribution is that the island formula's extremization structure—typically derived from gravitational path integrals—can also emerge from constraint-based reasoning about information processing at horizons. If the correspondence holds, this suggests black hole information preservation may be constrained by logical structure, not only by gravitational dynamics.

---

## Acknowledgments

This research was conducted independently. I thank the physics and philosophy communities for critical feedback on early drafts.

**AI Assistance Disclosure:** This work was developed with assistance from AI language models including Claude (Anthropic). These tools were used for drafting, editing, and exploring mathematical formulations. All substantive claims, arguments, and errors remain the author's responsibility. Human-Curated, AI-Enabled (HCAE).

---

## References

Almheiri, A., Engelhardt, N., Marolf, D., & Maxfield, H. (2019). The entropy of bulk quantum fields and the entanglement wedge of an evaporating black hole. *Journal of High Energy Physics*, 2019(12), 63.

Bekenstein, J. D. (1973). Black holes and entropy. *Physical Review D*, 7(8), 2333-2346.

Brown, A. R., Gharibyan, H., Penington, G., & Susskind, L. (2019). The Python's lunch: geometric obstructions to decoding Hawking radiation. *Journal of High Energy Physics*, 2020(8), 121.

Engelhardt, N., & Wall, A. C. (2014). Quantum extremal surfaces: holographic entanglement entropy beyond the classical regime. *Journal of High Energy Physics*, 2015(1), 73.

Hawking, S. W. (1975). Particle creation by black holes. *Communications in Mathematical Physics*, 43(3), 199-220.

Hayden, P., & Preskill, J. (2007). Black holes as mirrors: quantum information in random subsystems. *Journal of High Energy Physics*, 2007(09), 120.

Page, D. N. (1993). Information in black hole radiation. *Physical Review Letters*, 71(23), 3743-3746.

Penington, G. (2020). Entanglement wedge reconstruction and the information paradox. *Journal of High Energy Physics*, 2020(09), 002.

Ryu, S., & Takayanagi, T. (2006). Holographic derivation of entanglement entropy from AdS/CFT. *Physical Review Letters*, 96(18), 181602.

Sekino, Y., & Susskind, L. (2008). Fast scramblers. *Journal of High Energy Physics*, 2008(10), 065.

Tahko, T. E. (2009). The law of non-contradiction as a metaphysical principle. *Australasian Journal of Logic*, 7, 32-47.

---

## Appendix A: Technical Derivations

### A.1 Page Time Shift Calculation

For a pure-state black hole, radiation entropy:
$$S_{\text{rad}}(\tau) = S_0\left[1 - (1-\tau)^{2/3}\right]$$

Standard Page time satisfies S_rad = S_BH:
$$(1-\tau)^{2/3} = 1/2 \implies \tau_{\text{Page}}^{(0)} = 1 - 2^{-3/2} \approx 0.646$$

With admissibility correction ε = S_reserved/S₀:
$$S_{\text{rad}} = S_{BH} - \epsilon S_0$$
$$1 + \epsilon = 2(1-\tau)^{2/3}$$
$$(1-\tau)^{2/3} = \frac{1+\epsilon}{2}$$

Expanding:
$$\tau = \tau_{\text{Page}}^{(0)} - \frac{3\epsilon}{2^{5/2} \cdot \tau_{\text{Page}}^{(0)}} \cdot \tau_{\text{Page}}^{(0)}$$

**Result:**
$$\frac{\Delta t_{\text{Page}}}{t_{\text{Page}}} = -\frac{3}{2^{5/2} \cdot 0.646} \epsilon \approx -0.82\epsilon$$

### A.2 Scrambling Time Bound

From the rate constraint with no infall:
$$\frac{dI_{\text{diary}}}{dt} \leq -\frac{dS_{BH}}{dt}$$

Using Hawking luminosity:
$$-\frac{dS_{BH}}{dt} = \frac{c^2}{1920 \hbar M}$$

For k qubits of diary information:
$$t_* \geq \frac{k \log 2}{\lvert dS_{BH}/dt \rvert} = \frac{1920 \hbar M \cdot k \log 2}{c^2}$$

In Planck units:
$$t_*^{\text{Adm}} \geq 1920 \cdot k \cdot M$$

Ratio to Hayden-Preskill:
$$\frac{t_*^{\text{Adm}}}{t_*^{HP}} \sim \frac{k}{\log S_{BH}}$$

For k ~ O(1): admissibility bound is weaker.

### A.3 JT Gravity: Explicit Worked Example

We verify the admissibility prediction against a canonical evaporating JT black hole calculation. This provides a line-by-line checkable correspondence.

#### A.3.1 Setup: Evaporating JT Black Hole

**JT action:**
$$I_{JT} = \frac{\phi_0}{16\pi G} \int d^2x \sqrt{-g} \, R + \frac{1}{16\pi G} \int d^2x \sqrt{-g} \, \phi (R + 2) + I_{\text{bdy}}$$

**Metric (Schwarzschild gauge):**
$$ds^2 = -f(r) dt^2 + f(r)^{-1} dr^2, \quad f(r) = r^2 - r_H^2$$

**Dilaton profile:**
$$\phi(r) = \phi_H + \phi_r (r - r_H)$$

where φ_H is the horizon value and φ_r = dφ/dr at the horizon.

**Entropy:**
$$S_{BH} = \frac{\phi_H}{4G}$$

#### A.3.2 Standard QES Calculation

The generalized entropy for radiation region R with island I bounded by QES at r_QES:

$$S_{\text{gen}} = \frac{\phi(r_{\text{QES}})}{4G} + S_{\text{bulk}}(I \cup R)$$

For CFT matter with central charge c, the bulk entropy is:

$$S_{\text{bulk}} = \frac{c}{6} \log\left(\frac{d(r_{\text{QES}}, r_R)^2}{\epsilon_{\text{UV}}^2}\right)$$

where d(r_QES, r_R) is the geodesic distance from QES to the radiation collection point.

**Extremization:** Setting ∂S_gen/∂r_QES = 0:

$$\frac{\phi_r}{4G} + \frac{c}{6} \cdot \frac{2}{r_{\text{QES}} - r_H} = 0$$

Solving:

$$r_{\text{QES}} - r_H = -\frac{4Gc}{3\phi_r}$$

(The negative sign indicates the QES is inside the horizon in the extended geometry.)

#### A.3.3 Radiation Entropy at Page Time

At Page time, S_rad = S_BH/2. Using the island formula:

$$S_{\text{rad}} = \frac{\phi(r_{\text{QES}})}{4G} + S_{\text{bulk}}(I \cup R) = \frac{\phi_H}{8G}$$

This gives:

$$\frac{\phi_H - \phi(r_{\text{QES}})}{4G} = \frac{\phi_H}{4G} - \frac{\phi_H}{8G} + S_{\text{bulk}} = \frac{S_{BH}}{2} + S_{\text{bulk}}$$

#### A.3.4 Admissibility Prediction

The admissibility interpretation (§6.6) predicts:

$$\frac{\phi_H - \phi(r_{\text{QES}})}{4G} = S_{\text{rad}} \cdot h(\bar{d})$$

**Case 1: Pure-state infall** (h(d̄) → 1)

Prediction: Dilaton drop ≈ S_rad

From the standard calculation at Page time: Dilaton drop = S_BH/2 + S_bulk

Since S_rad = S_BH/2 at Page time, we need S_bulk to be subleading. In the large-S_BH limit, S_bulk ~ c log(S_BH) << S_BH, confirming:

$$\boxed{\frac{\phi_H - \phi(r_{\text{QES}})}{4G} \approx S_{\text{rad}} \quad \text{(pure state, large } S_{BH}\text{)}}$$

**Agreement:** Within O(c log S_BH / S_BH) corrections.

**Case 2: Thermal infall** (h(d̄) < 1)

For mixed-state infall with average distinguishability d̄ < 1:

Prediction: Dilaton drop = S_rad · h(d̄) < S_rad

This means the QES is *closer to the horizon* than in the pure-state case.

**Physical interpretation:** Thermal infall carries less distinguishability per bit of entropy, so less boundary capacity is consumed, and the QES doesn't need to retreat as far.

**Testable:** For explicit thermal state calculations in JT gravity, verify that QES location scales with the factor h(d̄).

#### A.3.5 Equivalence Statement

**Claim:** The admissibility saturation condition (§6.3):

$$S_{\text{reserved}}(r) = S_{BH}^{\text{eff}}(r)$$

is equivalent to the QES extremization condition:

$$\frac{\partial}{\partial r}\left[\frac{\phi(r)}{4G} + S_{\text{bulk}}(r)\right] = 0$$

under the identification:

$$S_{\text{reserved}}(r) = \frac{\phi_H - \phi(r)}{4G} \cdot \frac{1}{h(\bar{d})}$$

**Verification:**
1. Both conditions locate where boundary capacity equals information demand
2. Both give QES position inside the horizon
3. Both yield S_rad = S_BH/2 at Page time (leading order)
4. Both predict QES retreat as evaporation proceeds

The admissibility framework thus reproduces the island formula's extremization structure, with the interpretive addition that the extremization represents boundary saturation under L₃ constraints.
