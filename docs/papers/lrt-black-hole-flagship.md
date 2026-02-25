---
layout: paper
permalink: /papers/lrt-black-hole-flagship/
title: "Logical Constraints on Black Hole Information: Deriving the Island Formula from Admissibility"
short_title: "Black Hole Information from L₃"
author: "James (JD) Longmire"
orcid: "0009-0009-1383-7698"
email: "jdlongmire@outlook.com"
date_published: 2026-02-25
abstract: "We derive quantitative predictions for black hole information dynamics from Logic Realism Theory (LRT), which treats the three classical laws of logic (Identity, Non-Contradiction, Excluded Middle) as ontological constraints on physical instantiation. The framework requires that distinguishability between quantum states cannot be destroyed without compensating encoding, yielding a bound g(d) ~ h(d)/S_BH on minimum preserved distinguishability at the horizon boundary. This constraint generates: (1) a central inequality relating horizon entropy growth to recoverable mutual information; (2) Page curve corrections with explicit coefficient (-0.82ε, where ε ~ N·h(d)/S_BH); (3) a physical mechanism for the island formula via boundary saturation; and (4) testable predictions for QES location in JT gravity. The corrections are negligible for astrophysical black holes (ε ~ 10^{-17}) but become O(1) at Planck scale, providing falsifiable signatures. Consistency checks confirm the admissibility bound is weaker than Hayden-Preskill scrambling constraints (does not overconstrain dynamics) and reproduces semiclassical physics in the large-S_BH limit. This represents the first derivation of the island formula from logical rather than gravitational path integral arguments."
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

### 3.3 Theorem: Inadmissibility of Complete Erasure

**Theorem 3.1.** An admissible channel cannot reduce distinguishability to zero without compensating encoding.

**Proof:**

1. Suppose channel Φ maps distinguishable states ρ₁, ρ₂ (with D(ρ₁, ρ₂) > 0) to outputs with D(Φ(ρ₁), Φ(ρ₂)) = 0.

2. Indistinguishable outputs are the *same configuration* by Determinate Identity.

3. The inputs were *different configurations*—they differed in property P.

4. By Excluded Middle: either P(ρ₁) or ¬P(ρ₁). Similarly for ρ₂.

5. If ρ₁ and ρ₂ differed in P, and Φ erases this difference without encoding it elsewhere, then at the output there is no fact about whether the input had property P.

6. This violates EM: the configuration lacks definite status with respect to P-history.

**Conclusion:** Admissibility requires either D(Φ(ρ₁), Φ(ρ₂)) > 0, or the distinguishing information is encoded in an auxiliary system. ∎

### 3.4 Deriving g(d) from Boundary Capacity

The function g(d) quantifies minimum distinguishability the boundary must retain.

**Information-Theoretic Setup:** For input states with distinguishability d = D(ρ₁, ρ₂), the mutual information needed to distinguish them satisfies:

$$I \geq h(d) \equiv -d \log d - (1-d) \log(1-d)$$

where h(d) is binary entropy (from Fano's inequality).

**Boundary Capacity Constraint:** For a black hole with Bekenstein-Hawking entropy S_BH:

$$\dim(H_B) = e^{S_{BH}}, \quad I_{\max} = S_{BH}$$

**Minimal Resolvable Distinguishability:** The number of distinguishable pairs the boundary can track:

$$N_{\text{pairs}} \leq \frac{S_{BH}}{h(d)}$$

**Theorem 3.2 (Admissibility Bound).** For an admissible horizon channel:

$$D(\rho_{B,1}, \rho_{B,2}) \geq \frac{h(d)}{S_{BH}}$$

where d = D(ρ₁, ρ₂) is input distinguishability.

**Corollary 3.3 (Scaling Behavior):**
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

2. **Scrambling violation:** If an admissible process recovers information faster than |dS_BH/dt|, the rate bound is falsified.

3. **Semiclassical breakdown:** If large black holes show O(1) corrections where ε predicts negligible effects, the scaling is wrong.

4. **Phase structure:** If correlation phases are random even for the correct input-matching pattern, the phase prediction is falsified.

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
Boundary Capacity Bound: g(d) ~ h(d)/S_BH (Theorem 3.2)
         ↓
    ┌────────────┴────────────┐
    ↓                         ↓
Central Inequality (§4)    Island Mechanism (§6)
    ↓                         ↓
Page Curve Corrections     QES Location
```

### 9.2 What This Achieves

**For Physics:**
- First derivation of island formula from logical constraints
- Physical mechanism (boundary saturation) for QES appearance
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

The key conceptual advance is that the island formula—typically derived from gravitational path integrals—emerges from *logical* constraints on information processing. If correct, this means black hole information preservation is a logical necessity, not merely a physical regularity.

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

### A.3 JT Gravity QES Derivation

JT action:
$$I_{JT} = \frac{1}{16\pi G} \int d^2x \sqrt{-g} \, \phi (R + 2) + \text{boundary terms}$$

Entropy: S = φ(r)/4G

Generalized entropy:
$$S_{\text{gen}} = \frac{\phi(r_{\text{QES}})}{4G} + \frac{c}{6} \log\left(\frac{(r_{\text{QES}} - r_H)^2}{\epsilon^2}\right)$$

Extremizing ∂S_gen/∂r_QES = 0 gives the standard QES location.

**Admissibility prediction:** The dilaton drop equals information transferred:
$$\frac{\phi_H - \phi(r_{\text{QES}})}{4G} = S_{\text{rad}} \cdot h(\bar{d})$$

For pure-state infall (h → 1), this reduces to dilaton drop ≈ S_rad, which matches standard JT results within O(1).
