# Scrambling Time and Admissibility

## Does L₃ Constrain the Scrambling Rate?

**Status:** Exploratory derivation
**Depends on:** minimal-horizon-channel-model.md, page-curve-corrections.md

---

## 1. The Scrambling Problem

### 1.1 Hayden-Preskill Protocol

Setup:
1. Alice holds a black hole that has already radiated half its entropy
2. Bob collects all early radiation
3. Alice throws a diary (k qubits) into the black hole
4. After time t*, Bob can reconstruct the diary from combined early + late radiation

**Result (Hayden-Preskill 2007):** The scrambling time is:

$$t_* \sim \frac{\beta}{2\pi} \log S_{BH}$$

where β = 1/T_H is inverse Hawking temperature.

For a Schwarzschild black hole:

$$t_* \sim r_s \log S_{BH} \sim \frac{GM}{c^3} \log\left(\frac{GM^2}{\hbar c}\right)$$

### 1.2 The Question

Does admissibility constrain t*?

Possibilities:
- **No constraint:** t* set entirely by dynamics, admissibility doesn't care about timing
- **Lower bound:** Admissibility forbids scrambling faster than some rate
- **Upper bound:** Admissibility requires information to become accessible within some time

---

## 2. Admissibility and Scrambling

### 2.1 The Rate Bound from §4

From the minimal model, information recovery rate satisfies:

$$\frac{dI_{\text{rec}}}{dt} \leq -\frac{dS_{BH}}{dt} + \dot{S}_{\text{in}}$$

For no infall (Ṡ_in = 0):

$$\frac{dI_{\text{rec}}}{dt} \leq -\frac{dS_{BH}}{dt}$$

### 2.2 Scrambling as Information Recovery

The diary information I_diary = k log 2 must become accessible.

Before scrambling: diary information is in boundary DOF
After scrambling: diary information is distributed to radiation

Rate of diary information transfer:

$$\frac{dI_{\text{diary}}}{dt} \leq -\frac{dS_{BH}}{dt}$$

### 2.3 Lower Bound on Scrambling Time

For complete transfer: I_diary = k log 2 bits must move to radiation.

Minimum time:

$$t_* \geq \frac{k \log 2}{\lvert dS_{BH}/dt \rvert}$$

Using Hawking luminosity:

$$-\frac{dS_{BH}}{dt} = \frac{8\pi G M}{\hbar c} \cdot \left\lvert\frac{dM}{dt}\right\rvert = \frac{c^3}{15360 \pi G M} \cdot \frac{8\pi G}{\hbar c} = \frac{c^2}{1920 \hbar M}$$

Therefore:

$$t_*^{\text{Adm}} \geq \frac{1920 \hbar M \cdot k \log 2}{c^2}$$

In Planck units (ℏ = c = G = 1):

$$t_*^{\text{Adm}} \geq 1920 \cdot k \cdot M \cdot \log 2$$

### 2.4 Comparison to Hayden-Preskill

Hayden-Preskill gives:

$$t_*^{HP} \sim M \log(M^2)$$

Admissibility gives:

$$t_*^{\text{Adm}} \geq 1920 k M$$

**Ratio:**

$$\frac{t_*^{\text{Adm}}}{t_*^{HP}} \sim \frac{1920 k}{\log(M^2)} \sim \frac{k}{\log S_{BH}}$$

For k ~ O(1) qubits:

$$t_*^{\text{Adm}} < t_*^{HP}$$

The admissibility bound is **weaker** than Hayden-Preskill.

**Conclusion:** Admissibility does not constrain scrambling time beyond what dynamics already requires.

---

## 3. Upper Bound Attempt

### 3.1 Does Admissibility Require Timely Recovery?

Consider: Could a black hole hold information at the boundary indefinitely without violating admissibility?

**Argument for no constraint:**
- Admissibility requires information *preservation*, not *accessibility*
- Information at the boundary satisfies L₃ — it has determinate identity, no contradiction
- There's no logical requirement for temporal availability

**Argument for constraint:**
- If information is "phase-shifted" at the boundary, it must eventually un-shift
- Hawking evaporation is the mechanism for un-shifting
- Evaporation rate is set by physics, not logic

**Conclusion:** No upper bound from admissibility. The scrambling time is set by dynamics.

### 3.2 What About Eternal Black Holes?

In AdS/CFT, eternal black holes (no evaporation) have a thermofield double state.

Question: Does admissibility require the two sides to be correlated?

**Analysis:**
- The TFD state: $\lvert TFD \rangle = \sum_n e^{-\beta E_n / 2} \lvert n \rangle_L \lvert n \rangle_R$
- This is a pure state — maximal correlation between L and R
- The correlation satisfies admissibility: distinguishability is preserved in the joint state

Admissibility doesn't require *accessible* correlation, only *existing* correlation.

---

## 4. Refined Analysis

### 4.1 The Distinguishability Transfer Rate

Return to Theorem 6.2:

$$D(\rho_{B,1}, \rho_{B,2}) \geq \frac{h(d)}{S_{BH}}$$

As S_BH decreases (evaporation), the bound strengthens.

Define the "distinguishability pressure":

$$P_D = \frac{\partial}{\partial t}\left[\frac{h(d)}{S_{BH}}\right] = \frac{h(d)}{S_{BH}^2} \cdot \left\lvert\frac{dS_{BH}}{dt}\right\rvert$$

This is the rate at which the boundary must "shed" distinguishability to stay within capacity.

### 4.2 Scrambling as Pressure Release

**Interpretation:** Scrambling is how the boundary relieves distinguishability pressure.

The scrambling rate ṙ_scramble must satisfy:

$$\dot{r}_{\text{scramble}} \geq P_D = \frac{h(d)}{S_{BH}^2} \cdot \left\lvert\frac{dS_{BH}}{dt}\right\rvert$$

For d ~ 1 (maximally distinguishable states), h(d) ~ 1:

$$\dot{r}_{\text{scramble}} \geq \frac{1}{S_{BH}^2} \cdot \left\lvert\frac{dS_{BH}}{dt}\right\rvert$$

Using |dS_BH/dt| ~ c²/(ℏM) ~ S_BH / (M · t_P):

$$\dot{r}_{\text{scramble}} \geq \frac{1}{S_{BH} \cdot M \cdot t_P}$$

### 4.3 Scrambling Time from Pressure

Total distinguishability to transfer: D_total ~ k · d ~ k for k qubits.

Time required:

$$t_* \geq \frac{k}{\dot{r}_{\text{scramble}}} \geq k \cdot S_{BH} \cdot M \cdot t_P$$

In natural units:

$$t_* \geq k \cdot S_{BH} \cdot M$$

Since S_BH ~ M²:

$$t_* \geq k \cdot M^3$$

This is **much stronger** than Hayden-Preskill (t* ~ M log M²).

### 4.4 Resolution

The discrepancy suggests the analysis in §4.2-4.3 is wrong.

**Error:** The distinguishability pressure is cumulative, but scrambling doesn't require *all* prior distinguishability to be transferred — only the current diary.

**Correct bound:** The bound in §2.3 (t* ≥ k · M) is the right one, and it's weaker than Hayden-Preskill.

---

## 5. What Admissibility Actually Constrains

### 5.1 Not the Scrambling Time

Admissibility doesn't determine *when* information becomes accessible.

### 5.2 The Scrambling Structure

Admissibility constrains *how* information is distributed:

**Constraint 5.1:** At any time t, the total mutual information satisfies:

$$I(\rho_{\text{diary}} : \rho_{\text{rad}}) + I(\rho_{\text{diary}} : \rho_B) \geq k \log 2$$

**Constraint 5.2:** The boundary contribution satisfies:

$$I(\rho_{\text{diary}} : \rho_B) \leq S_B \leq S_{BH} - S_{B,\text{reserved}}$$

**Constraint 5.3:** Transfer rate satisfies:

$$\frac{d}{dt}I(\rho_{\text{diary}} : \rho_{\text{rad}}) \leq \left\lvert\frac{dS_{BH}}{dt}\right\rvert$$

These are *structural* constraints, not timing constraints.

### 5.3 Connection to Complexity

The Hayden-Preskill result depends on:
1. Black holes are fast scramblers (Sekino-Susskind)
2. Scrambling time ~ β log S

Admissibility doesn't constrain computational complexity of unscrambling.

**Question for future work:** Does the g(d) bound imply anything about the complexity of the decoding operation?

---

## 6. Summary

### 6.1 Results

| Question | Answer |
|----------|--------|
| Does admissibility set t*? | No — weaker than dynamics |
| Does it constrain scrambling structure? | Yes — via g(d) |
| Does it bound recovery rate? | Yes — Theorem 4.1 |
| Does it require eventual recovery? | No — only preservation |

### 6.2 The Bound Hierarchy

$$t_*^{\text{Adm}} \lesssim t_*^{HP} \lesssim t_*^{\text{Page}}$$

- Admissibility: t* ≥ kM (weakest)
- Hayden-Preskill: t* ~ M log M² (intermediate)
- Full recovery: t* ~ M³ / t_evap ~ Page time (strongest)

### 6.3 Physical Interpretation

Admissibility sets a **floor** on scrambling time (information can't transfer faster than horizon entropy changes), but actual scrambling time is set by **dynamics** (chaotic evolution, fast scrambling).

The admissibility bound is not saturated because:
1. Scrambling involves complex correlations, not just bit transfer
2. The boundary has finite capacity but scrambling uses that capacity efficiently
3. Quantum error correction allows information to be spread non-locally

---

## 7. Next Directions

### 7.1 Complexity Connection

If g(d) constrains distinguishability, does it constrain the circuit complexity of decoding?

**Conjecture:** The decoding complexity C_decode satisfies:

$$C_{\text{decode}} \gtrsim \frac{S_{BH}}{g(d)} \sim S_{BH}^2$$

This would connect admissibility to computational complexity bounds.

### 7.2 Fast Scrambling

Black holes are conjectured to be fastest possible scramblers.

**Question:** Is fast scrambling *required* by admissibility, or merely permitted?

**Hypothesis:** Admissibility permits but doesn't require fast scrambling. Slower scramblers would satisfy admissibility but might violate other physical constraints (energy, entropy production).

### 7.3 Quantum Error Correction

Holographic quantum error correction suggests boundary DOF encode bulk information redundantly.

**Question:** Does the g(d) bound constrain the error correction code?

**Hypothesis:** The code must have rate R ≥ g(d), ensuring sufficient distinguishability preservation.

---

## References

- Hayden, P. & Preskill, J. (2007). Black holes as mirrors. *JHEP* 09, 120.
- Sekino, Y. & Susskind, L. (2008). Fast scramblers. *JHEP* 10, 065.
- Maldacena, J. & Susskind, L. (2013). Cool horizons for entangled black holes. *Fortsch. Phys.* 61, 781.
- Almheiri, A. et al. (2015). Bulk locality and quantum error correction. *JHEP* 04, 163.
