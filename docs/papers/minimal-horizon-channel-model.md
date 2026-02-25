# Minimal Horizon Channel Model

## Admissibility-Constrained Information Transfer

**Status:** Working draft — derivation attempt
**Objective:** Derive one inequality relating horizon entropy growth to recoverable mutual information from L₃ admissibility constraints

---

## 1. Setup

### 1.1 The Physical Situation

A quantum system with state ρ_in crosses a black hole horizon. Standard physics says:

- Information is preserved (unitarity)
- Information is eventually recoverable via Hawking radiation
- The *mechanism* of preservation is unspecified

LRT proposes: admissibility constrains the *channel class*, not just the outcome.

### 1.2 Formal Elements

Let:
- **H_in**: Hilbert space of infalling system
- **H_B**: Hilbert space of horizon boundary DOF
- **H_rad**: Hilbert space of outgoing radiation
- **Φ**: Quantum channel (CPTP map) implementing the crossing

The standard constraint is unitarity:

$$\text{tr}(\rho_{\text{out}}) = \text{tr}(\rho_{\text{in}}) = 1$$

with purification preserved globally.

---

## 2. The Admissibility Constraint

### 2.1 L₃ as Distinguishability Preservation

The three laws of logic (L₃):
- **Identity:** A = A
- **Non-contradiction:** ¬(A ∧ ¬A)
- **Excluded middle:** A ∨ ¬A

Translated to quantum information, admissibility requires:

> **Distinguishability cannot collapse without compensating encoding.**

Formally: if two states ρ₁ and ρ₂ are distinguishable (trace distance D(ρ₁, ρ₂) > 0), then after any admissible channel Φ:

$$D(\Phi(\rho_1), \Phi(\rho_2)) = 0 \implies \exists \text{ compensating record in } H_B$$

This is *stronger* than unitarity. Unitarity allows information to be scrambled arbitrarily. Admissibility constrains the scrambling structure.

### 2.2 The Phase-Shift Interpretation

An **admissible channel** Φ_Adm acts as:

$$\Phi_{\text{Adm}}: \rho_{\text{in}} \mapsto \text{tr}_{H_B}[U(\rho_{\text{in}} \otimes \lvert 0\rangle\langle 0\rvert_B)U^\dagger]$$

where U satisfies the **admissibility condition**:

$$I(\rho_{\text{in}} : \rho_{\text{rad}}) + I(\rho_{\text{in}} : \rho_B) \geq S(\rho_{\text{in}})$$

The total information about the input is distributed between radiation and boundary, never lost.

---

## 3. The Channel Model

### 3.1 Minimal Model: Horizon as Isometric Encoding

Model the horizon crossing as an isometry V: H_in → H_B ⊗ H_rad:

$$V\lvert\psi\rangle_{\text{in}} = \sum_i \alpha_i \lvert b_i\rangle_B \otimes \lvert r_i\rangle_{\text{rad}}$$

The reduced states are:

$$\rho_B = \text{tr}_{\text{rad}}[V\rho_{\text{in}}V^\dagger]$$
$$\rho_{\text{rad}} = \text{tr}_B[V\rho_{\text{in}}V^\dagger]$$

### 3.2 Admissibility Constraint on V

Generic isometries allow arbitrary information distribution. Admissibility restricts V:

**Constraint A1 (Distinguishability Bound):**

For any two input states with distinguishability d = D(ρ₁, ρ₂):

$$D(\rho_{B,1}, \rho_{B,2}) \geq g(d) \cdot d$$

where g(d) is a monotonic function encoding admissibility strictness.

**Interpretation:** The boundary *must* retain at least g(d) fraction of the original distinguishability. Generic scrambling has g(d) → 0 at late times. Admissibility enforces g(d) ≥ g_min > 0.

### 3.3 Connection to Horizon Entropy

Bekenstein-Hawking entropy:

$$S_{BH} = \frac{A}{4G\hbar}$$

The entropy counts distinguishable boundary microstates.

**Admissibility interpretation:** The horizon area measures the *capacity* for distinguishability preservation.

Rate of entropy change:

$$\frac{dS_{BH}}{dt} = \frac{1}{4G\hbar}\frac{dA}{dt}$$

---

## 4. The Central Inequality

### 4.1 Derivation Attempt

**Claim:** Under admissibility constraints, horizon entropy growth bounds recoverable mutual information.

Let I_rec denote the mutual information recoverable from radiation about the input:

$$I_{\text{rec}} = I(\rho_{\text{rad}} : \rho_{\text{in}})$$

By the admissibility constraint, information not in radiation must be in boundary:

$$S(\rho_{\text{in}}) - I_{\text{rec}} \leq S_B$$

The boundary entropy is bounded by horizon capacity:

$$S_B \leq S_{BH}$$

Therefore:

$$I_{\text{rec}} \geq S(\rho_{\text{in}}) - S_{BH}$$

**Dynamic form:** For a process with infalling matter carrying entropy flux ṠΘ:

$$\frac{d I_{\text{rec}}}{dt} \geq \dot{S}_{\text{in}} - \frac{dS_{BH}}{dt}$$

Rearranging:

$$\boxed{\frac{dS_{BH}}{dt} \geq \dot{S}_{\text{in}} - \frac{dI_{\text{rec}}}{dt}}$$

### 4.2 Interpretation

The inequality says:

> **Horizon entropy growth must at least compensate for information that becomes unrecoverable from radiation.**

If all information eventually appears in radiation (I_rec → S_in), then horizon growth can be arbitrarily small (Hawking evaporation allows shrinking).

If information is temporarily trapped at the boundary, horizon entropy must grow to accommodate the distinguishability encoding.

### 4.3 Comparison to Page Curve

The Page curve describes information recovery as the black hole evaporates. At the Page time, radiation entropy begins decreasing.

The admissibility constraint adds structure: **the rate of information recovery is bounded by horizon dynamics.**

$$\frac{dI_{\text{rec}}}{dt} \leq \dot{S}_{\text{in}} - \frac{dS_{BH}}{dt}$$

This predicts correlations between:
- Rate of horizon shrinkage
- Rate of correlation emergence in radiation

---

## 5. Testable Predictions

### 5.1 Qualitative Prediction

**Sign correlation:** When the horizon is shrinking (dS_BH/dt < 0), information recovery rate should increase:

$$\frac{dS_{BH}}{dt} < 0 \implies \frac{dI_{\text{rec}}}{dt} > 0$$

This is *consistent* with the Page curve but adds dynamic constraint.

### 5.2 Quantitative Prediction

**Rate bound:** The maximum rate of information recovery is:

$$\left(\frac{dI_{\text{rec}}}{dt}\right)_{\max} = \dot{S}_{\text{in}} - \frac{dS_{BH}}{dt}$$

For Hawking evaporation with no infalling matter (Ṡ_in = 0):

$$\left(\frac{dI_{\text{rec}}}{dt}\right)_{\max} = -\frac{dS_{BH}}{dt} = \frac{\pi c^3}{G\hbar} \frac{1}{M^2} \cdot M \cdot \frac{dM}{dt}$$

Using Hawking luminosity:

$$\frac{dM}{dt} = -\frac{\hbar c^6}{15360 \pi G^2 M^2}$$

This gives a specific functional form for information recovery rate.

### 5.3 Distinguishing from Generic Scrambling

Generic unitarity allows any rate of information recovery (including all at once at Page time). Admissibility predicts:

$$\frac{dI_{\text{rec}}}{dt} \leq -\frac{dS_{BH}}{dt}$$

The bound should be saturated for maximally efficient (minimally lossy) channels.

---

## 6. Derivation of the Distinguishability Bound g(d)

This section closes the quantitative gap by deriving g(d) from L₃ admissibility constraints.

### 6.1 L₃ Applied to Quantum Channels

From the Position Paper §2.4, a configuration i is admissible when:

$$L_3(i) := \text{Id}(i) \land \text{NC}(i) \land \text{EM}(i)$$

For a quantum channel Φ acting on states, these translate to:

1. **Determinate Identity:** The channel preserves determinate identity of distinguishable inputs. If ρ₁ ≠ ρ₂, then either Φ(ρ₁) ≠ Φ(ρ₂), or the distinction is encoded elsewhere.

2. **Non-Contradiction:** The channel doesn't map a single input to contradictory outputs. Each input has a determinate image.

3. **Excluded Middle:** Each output configuration is definite with respect to applicable properties. No superposition of "information exists" and "information doesn't exist."

### 6.2 Distinguishability as L₃ Encoding

Two quantum states ρ₁, ρ₂ are **distinguishable** when D(ρ₁, ρ₂) > 0, where trace distance:

$$D(\rho_1, \rho_2) = \frac{1}{2}\|\rho_1 - \rho_2\|_1$$

Operational meaning: D(ρ₁, ρ₂) equals the maximum probability of correctly distinguishing the states in a single measurement.

**L₃ Interpretation:** Distinguishability encodes the fact that ρ₁ and ρ₂ are *different configurations*. By **Determinate Identity**, each configuration is determinately what it is. The trace distance quantifies this difference.

### 6.3 The Inadmissibility of Complete Erasure

**Theorem 6.1 (Admissibility Requires Distinguishability Preservation):**
An admissible channel cannot reduce distinguishability to zero without compensating encoding.

**Proof:**

1. Suppose channel Φ maps distinguishable states ρ₁, ρ₂ (with D(ρ₁, ρ₂) > 0) to outputs with D(Φ(ρ₁), Φ(ρ₂)) = 0.

2. If the outputs are indistinguishable, they are the *same configuration* by Determinate Identity. There exists no measurement distinguishing them.

3. But the inputs were *different configurations* (D(ρ₁, ρ₂) > 0). They differed in at least one property P.

4. By **Excluded Middle**, for any property P: either P(ρ₁) or ¬P(ρ₁). Similarly for ρ₂.

5. If ρ₁ and ρ₂ differed in property P (say P(ρ₁) and ¬P(ρ₂)), and Φ erases this difference without encoding it elsewhere, then at the output:
   - There is no fact of the matter about whether the input had property P
   - This violates EM: the configuration is not definite with respect to P-history

6. **Conclusion:** Admissibility requires either:
   - D(Φ(ρ₁), Φ(ρ₂)) > 0 (distinguishability preserved in output), OR
   - The distinguishing information is encoded in an auxiliary system

For horizon channels, the auxiliary system is the boundary DOF (H_B). ∎

### 6.4 Deriving g_min from Boundary Capacity

The function g(d) quantifies minimum distinguishability the boundary must retain. We derive it from dimensional constraints.

**Information-Theoretic Setup:**

For input states ρ₁, ρ₂ with distinguishability d = D(ρ₁, ρ₂), the mutual information I needed to distinguish them satisfies:

$$I \geq h(d) \equiv -d \log d - (1-d) \log(1-d)$$

where h(d) is binary entropy. This follows from Fano's inequality: distinguishing requires at least h(d) bits.

**Boundary Capacity Constraint:**

The boundary Hilbert space H_B has finite dimension. For a black hole with Bekenstein-Hawking entropy S_BH:

$$\dim(H_B) = e^{S_{BH}}$$

The maximum mutual information the boundary can encode is:

$$I_{\max} = \log(\dim H_B) = S_{BH}$$

**Minimal Resolvable Distinguishability:**

For the boundary to encode distinguishability d, it must allocate at least h(d) bits. Given finite capacity, there exists a minimum resolvable distinguishability d_min where:

$$h(d_{\min}) \sim \frac{1}{S_{BH}}$$

For small d, h(d) ≈ d(1 - log d), so:

$$d_{\min} \sim \frac{1}{S_{BH}}$$

More precisely, the number of distinguishable pairs the boundary can track is bounded by:

$$N_{\text{pairs}} \leq \frac{S_{BH}}{h(d)}$$

For distinguishability to be preserved, at least one bit must be allocated per pair. This gives:

$$g_{\min} = \frac{1}{S_{BH}} \cdot \frac{1}{d}$$

for small d, or more generally:

$$\boxed{g(d) = \frac{h(d)}{S_{BH} \cdot d} \approx \frac{1 - \log d}{S_{BH}}}$$

### 6.5 The Derived Constraint

**Theorem 6.2 (Admissibility Bound):**
For an admissible horizon channel with Bekenstein-Hawking entropy S_BH, the minimum distinguishability preserved at the boundary satisfies:

$$D(\rho_{B,1}, \rho_{B,2}) \geq \frac{h(d)}{S_{BH}}$$

where d = D(ρ₁, ρ₂) is the input distinguishability and h(d) is binary entropy.

**Corollary 6.3 (Scaling Behavior):**
- **Large black holes** (S_BH >> 1): The bound is weak. g_min → 0, and nearly all distinguishability can be encoded in radiation. This is consistent with semiclassical physics.

- **Small black holes** (S_BH ~ O(1)): The bound is sharp. Significant distinguishability must remain at the boundary, constraining radiation correlations.

- **Near Page time** (S_BH halved from initial): The effective g doubles, forcing more rapid information transfer to radiation.

### 6.6 Physical Interpretation

The derivation shows:

1. **L₃ forbids information destruction** — this is the qualitative content
2. **Boundary capacity limits encoding** — this is finite-dimensional QM
3. **The combination yields a quantitative bound** — g_min scales inversely with S_BH

The bound is:
- **Trivially satisfied** for astrophysical black holes (S_BH ~ 10^77 for solar mass)
- **Non-trivial** for Planck-scale black holes (S_BH ~ 1)
- **Dynamically relevant** near Page time when capacity halves

---

## 7. Page Curve Predictions

The admissibility bound has direct implications for the Page curve.

### 7.1 Standard Page Curve

The Page curve describes entropy of Hawking radiation S_rad as a function of time:

1. **Early times:** S_rad increases (radiation looks thermal)
2. **Page time t_Page:** S_rad reaches maximum when half the black hole has evaporated
3. **Late times:** S_rad decreases (correlations emerge, information recovered)

The curve satisfies:

$$S_{\text{rad}}(t) = \min\{S_{\text{in}}(t), S_{BH}(t)\}$$

where S_in is cumulative entropy crossed into the hole.

### 7.2 Admissibility-Modified Page Curve

The admissibility constraint (Theorem 6.2) adds structure. The recoverable mutual information satisfies:

$$I_{\text{rec}}(t) = S(\rho_{\text{in}}) - S(\rho_B) + \text{correlations}$$

With the constraint D(ρ_B) ≥ h(d)/S_BH, the boundary entropy satisfies:

$$S_B \leq S_{BH} - \frac{N_{\text{distinct}} \cdot h(d_{\text{avg}})}{S_{BH}}$$

where N_distinct counts distinguishable infalling states.

**Prediction 7.1 (Modified Page Curve):**

The Page curve slope is bounded by:

$$\left\lvert\frac{dS_{\text{rad}}}{dt}\right\rvert \leq \left\lvert\frac{dS_{BH}}{dt}\right\rvert \cdot \left(1 - \frac{N_{\text{distinct}} \cdot h(d)}{S_{BH}^2}\right)$$

The correction term N · h(d)/S_BH² is:
- Negligible for large black holes
- O(1) near final evaporation

### 7.3 Page Time Shift

**Prediction 7.2 (Page Time Correction):**

If the boundary must retain minimal distinguishability, the effective capacity for thermal radiation is reduced. The Page time shifts:

$$t_{\text{Page}}^{\text{Adm}} = t_{\text{Page}}^{\text{std}} \cdot \left(1 + O\left(\frac{N_{\text{distinct}}}{S_{BH}}\right)\right)$$

For astrophysical black holes, the correction is negligible (~ 10^{-77}).

For primordial black holes or late-stage evaporation, the correction could be measurable:

$$\Delta t_{\text{Page}} \sim t_{\text{Page}} \cdot \frac{N_{\text{distinct}}}{S_{BH}}$$

### 7.4 Correlation Spectrum Prediction

**Prediction 7.3 (Correlation Structure):**

Generic scrambling produces correlations with random phases. Admissibility-constrained channels produce correlations with structure:

For late Hawking quanta with frequency ω, the correlation with early quanta satisfies:

$$C(\omega) \propto e^{-\omega / T_H} \cdot \left(1 - e^{-S_{BH}(t)}\right)$$

where T_H is Hawking temperature. The second factor encodes admissibility: correlations emerge faster as S_BH shrinks.

**Distinguishing from Generic Scrambling:**

| Property | Generic Scrambling | Admissibility-Constrained |
|----------|-------------------|--------------------------|
| Correlation emergence | Any pattern consistent with Page curve | Rate bounded by dS_BH/dt |
| Phase structure | Random | Constrained by g(d) |
| Late-time spectrum | Thermal | Sub-thermal corrections |

---

## 8. Island Formula Connection

### 8.1 The Island Formula

Recent work (Almheiri et al., Penington) derives the Page curve using "islands" — regions inside the horizon that contribute to radiation entropy via:

$$S_{\text{rad}} = \min_{\mathcal{I}} \left\{ \frac{\text{Area}(\partial \mathcal{I})}{4G\hbar} + S_{\text{bulk}}(\mathcal{I} \cup R) \right\}$$

where R is the radiation region and I is the island.

The formula reproduces the Page curve but doesn't specify *why* islands contribute — it's a consistency condition.

### 8.2 Admissibility as Island Mechanism

**Conjecture 8.1:** Admissibility constraints are the microscopic mechanism behind island contributions.

Argument:

1. Admissibility requires information preservation with minimal boundary encoding (§6)
2. When boundary capacity is exhausted, information must transfer to radiation
3. The island formula captures this: the island boundary area encodes the capacity cost
4. The transition at Page time corresponds to boundary saturation

**Prediction 8.2:** The island boundary should appear where admissibility constraints saturate:

$$\frac{\text{Area}(\partial \mathcal{I})}{4G\hbar} = S_{BH} - S_{\text{available}}$$

where S_available is remaining encoding capacity.

### 8.3 The Extremization Principle

The "min" in the island formula selects the dominant saddle. In admissibility terms:

**Conjecture 8.3:** Extremization selects the configuration that saturates admissibility constraints with minimum encoding cost.

This would explain why islands appear at Page time: before Page time, boundary encoding is cheaper (no island needed). After Page time, radiation encoding is cheaper (island dominates).

---

## 9. Connection to Λ Discussion

### 9.1 Local vs Global Admissibility

The horizon channel model describes **local** admissibility enforcement:
- Information crossing a boundary must be preserved
- Boundary DOF encode distinguishability

The Λ stabilization describes **global** admissibility enforcement:
- Cosmological evolution must preserve global distinguishability
- Dark energy enforces asymptotic constraint saturation

### 9.2 Unification

Both arise from the same invariant: **bounded distinguishability**.

- Locally: horizon area bounds distinguishable states
- Globally: cosmological volume bounds total phase space

The Λ term emerges when global distinguishability saturates. Black hole entropy emerges when local distinguishability saturates.

**Prediction 9.1:** The same constant (Planck-scale distinguishability bound) should appear in both contexts.

### 9.3 Cross-Scale Consistency

The admissibility bound g(d) ~ 1/S_BH for horizons parallels the cosmological constraint.

For cosmological horizon with area A_cosmo:

$$S_{\text{cosmo}} = \frac{A_{\text{cosmo}}}{4G\hbar} \sim \frac{3\pi}{\Lambda G\hbar}$$

**Prediction 9.2:** The Λ value emerges when:

$$g_{\text{global}} \cdot S_{\text{cosmo}} \sim 1$$

This would constrain Λ from below: too small a Λ means too large a cosmological horizon, violating global distinguishability bounds.

---

## 10. Summary

### 10.1 What We Derived

1. **A channel model** for horizon crossing under admissibility constraints (§3)

2. **The central inequality** relating horizon entropy growth to information recovery (§4):

$$\frac{dS_{BH}}{dt} \geq \dot{S}_{\text{in}} - \frac{dI_{\text{rec}}}{dt}$$

3. **A rate bound** on information recovery (§5):

$$\frac{dI_{\text{rec}}}{dt} \leq -\frac{dS_{BH}}{dt} + \dot{S}_{\text{in}}$$

4. **The distinguishability bound g(d)** from L₃ constraints (§6):

$$g(d) \approx \frac{1 - \log d}{S_{BH}}$$

5. **Page curve predictions** with admissibility corrections (§7)

6. **Island formula connection** — admissibility as the mechanism (§8)

### 10.2 Key Results Table

| Result | Equation | Status |
|--------|----------|--------|
| Central inequality | dS_BH/dt ≥ Ṡ_in - dI_rec/dt | Derived from admissibility |
| Distinguishability bound | g(d) ~ (1 - log d)/S_BH | Derived from L₃ + capacity |
| Page time correction | Δt ~ t_Page · N/S_BH | Prediction |
| Island mechanism | Boundary saturation triggers islands | Conjecture |
| Λ connection | Same g_min in both contexts | Prediction |

### 10.3 Derivation Chain

```
L₃ (logical laws)
    ↓
Admissibility (instantiation constraint)
    ↓
Distinguishability preservation (Theorem 6.1)
    ↓
Boundary encoding requirement
    ↓
Capacity bound (Bekenstein-Hawking)
    ↓
g(d) ~ 1/S_BH (Theorem 6.2)
    ↓
Central inequality
    ↓
Page curve corrections
```

### 10.4 What Remains

1. ~~Derivation of g_min from L₃~~ — **DONE** (§6)
2. ~~Connection to island formula~~ — **Conjecture stated** (§8)
3. **Quantitative comparison** to explicit Page curve calculations
4. **Numerical analysis** of correlation spectrum predictions
5. **Holographic verification** — does AdS/CFT reproduce g(d)?

### 10.5 Status Assessment

| Aspect | Before | After |
|--------|--------|-------|
| Mechanism claim | Narrative ("phase shift") | Mathematical (channel constraint) |
| Quantitative bound | Unspecified g(d) | g(d) ~ (1-log d)/S_BH |
| Testable predictions | Rate correlation only | Page time shift, spectrum structure |
| Island connection | None | Mechanism conjecture |

This paper now provides:
- A derivation chain from L₃ to quantitative predictions
- Specific corrections to Page curve
- A mechanism conjecture for the island formula
- Cross-scale connection to cosmological constant

The model is **falsifiable**: the Page time shift and correlation spectrum predictions can be compared to island formula calculations.

---

## References

- Bekenstein, J. (1973). Black holes and entropy. *Physical Review D*.
- Hawking, S. (1975). Particle creation by black holes. *Communications in Mathematical Physics*.
- Page, D. (1993). Information in black hole radiation. *Physical Review Letters*.
- Almheiri et al. (2019). The entropy of Hawking radiation. *Reviews of Modern Physics*.
