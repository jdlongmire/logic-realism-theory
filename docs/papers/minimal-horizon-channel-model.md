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

## 6. The Gap

### 6.1 What This Derivation Assumes

1. **Horizon DOF exist as a system H_B** — standard in holography
2. **Admissibility enforces distinguishability preservation** — the LRT premise
3. **Distinguishability maps to entropy** — standard information theory
4. **Horizon entropy = boundary capacity** — Bekenstein-Hawking

### 6.2 What Remains Underived

The function g(d) in Constraint A1 is not derived from L₃. This is the **quantitative gap**.

To close it, we need:

> A derivation of g_min from the logical structure of admissibility predicates.

**Candidate approach:** g_min corresponds to the minimal phase-space volume distinguishable by any admissible observer — a Planck-scale bound on resolution.

If g_min ~ exp(-S_BH), then the bound becomes trivial for large black holes but sharp for small ones. This would predict quantum corrections to Hawking radiation near Page time.

---

## 7. Connection to Λ Discussion

### 7.1 Local vs Global Admissibility

The horizon channel model describes **local** admissibility enforcement:
- Information crossing a boundary must be preserved
- Boundary DOF encode distinguishability

The Λ stabilization describes **global** admissibility enforcement:
- Cosmological evolution must preserve global distinguishability
- Dark energy enforces asymptotic constraint saturation

### 7.2 Unification

Both arise from the same invariant: **bounded distinguishability**.

- Locally: horizon area bounds distinguishable states
- Globally: cosmological volume bounds total phase space

The Λ term emerges when global distinguishability saturates. Black hole entropy emerges when local distinguishability saturates.

**Prediction:** The same constant (Planck-scale distinguishability bound) should appear in both contexts.

---

## 8. Summary

### What We Derived

1. **A channel model** for horizon crossing under admissibility constraints
2. **An inequality** relating horizon entropy growth to information recovery:

$$\frac{dS_{BH}}{dt} \geq \dot{S}_{\text{in}} - \frac{dI_{\text{rec}}}{dt}$$

3. **A rate bound** on information recovery:

$$\frac{dI_{\text{rec}}}{dt} \leq -\frac{dS_{BH}}{dt} + \dot{S}_{\text{in}}$$

4. **Testable prediction:** Sign correlation between horizon shrinkage and correlation emergence

### What Remains

1. **Derivation of g_min** from L₃ admissibility structure
2. **Quantitative comparison** to Page curve calculations
3. **Connection to island formula** (is admissibility the mechanism behind islands?)

### Status

This is a **minimal model**, not a complete derivation. It converts the phase-shift narrative into inequality form.

The inequality is *consistent* with known physics but *constrains* the allowed channels more than unitarity alone.

Whether it's correct depends on whether admissibility is the right constraint — which traces back to the L₃ derivation gap.

---

## References

- Bekenstein, J. (1973). Black holes and entropy. *Physical Review D*.
- Hawking, S. (1975). Particle creation by black holes. *Communications in Mathematical Physics*.
- Page, D. (1993). Information in black hole radiation. *Physical Review Letters*.
- Almheiri et al. (2019). The entropy of Hawking radiation. *Reviews of Modern Physics*.
