# Page Curve Corrections from Admissibility Constraints

## Explicit Derivation of Prediction 7.2

**Status:** Working derivation
**Depends on:** minimal-horizon-channel-model.md §6-7

---

## 1. Setup

### 1.1 Standard Page Curve

For a black hole formed from pure state with initial entropy S₀, the radiation entropy follows:

$$S_{\text{rad}}(t) = \begin{cases}
S_{\text{thermal}}(t) & t < t_{\text{Page}} \\
2S_0 - S_{\text{thermal}}(t) & t > t_{\text{Page}}
\end{cases}$$

where S_thermal(t) = S_BH(t) for a maximally mixed state.

Page time occurs when S_rad = S_BH:

$$t_{\text{Page}} = \frac{1}{2} t_{\text{evap}}$$

### 1.2 Black Hole Evolution

For a Schwarzschild black hole, Hawking evaporation gives:

$$\frac{dM}{dt} = -\frac{\hbar c^6}{15360 \pi G^2 M^2}$$

Integrating:

$$M(t) = M_0 \left(1 - \frac{t}{t_{\text{evap}}}\right)^{1/3}$$

where:

$$t_{\text{evap}} = \frac{5120 \pi G^2 M_0^3}{\hbar c^4}$$

Bekenstein-Hawking entropy:

$$S_{BH}(t) = \frac{4\pi G M(t)^2}{\hbar c} = S_0 \left(1 - \frac{t}{t_{\text{evap}}}\right)^{2/3}$$

---

## 2. Admissibility Correction

### 2.1 The Constraint

From Theorem 6.2, the boundary must retain distinguishability:

$$D(\rho_{B,1}, \rho_{B,2}) \geq \frac{h(d)}{S_{BH}(t)}$$

where h(d) = -d log d - (1-d) log(1-d) is binary entropy.

### 2.2 Entropy Cost of Distinguishability

Each distinguishable pair of infalling states costs entropy at the boundary:

$$\Delta S_B \geq h(d)$$

For N_distinct distinguishable states crossing the horizon, the boundary must allocate:

$$S_{B,\text{reserved}} \geq \sum_{i<j} h(d_{ij}) \cdot \theta_{ij}$$

where θ_ij = 1 if the pair (i,j) must be distinguished at the boundary, 0 if distinguished via radiation.

### 2.3 Effective Boundary Capacity

The **effective** capacity for thermal radiation is reduced:

$$S_{BH}^{\text{eff}}(t) = S_{BH}(t) - S_{B,\text{reserved}}(t)$$

For a pure state input (maximum distinguishability), the reservation is maximal:

$$S_{B,\text{reserved}} \sim N_{\text{distinct}} \cdot h(d_{\text{typ}})$$

### 2.4 Simplified Model

For a continuous infalling flux, model the distinguishability reservoir as:

$$S_{B,\text{reserved}}(t) = \int_0^t \dot{N}(t') \cdot h(\bar{d}) \cdot \left(1 - \frac{t - t'}{t_{\text{Page}}}\right)^+ dt'$$

where:
- Ṅ is the rate of distinguishable states entering
- h(d̄) is typical entropy per pair
- The decay factor models information transfer to radiation

For steady-state infall with rate Ṅ₀:

$$S_{B,\text{reserved}} \approx \dot{N}_0 \cdot h(\bar{d}) \cdot t_{\text{Page}} \cdot f(t/t_{\text{Page}})$$

where f is an O(1) function.

---

## 3. Modified Page Curve

### 3.1 Effective Entropy Relation

The Page curve condition (radiation = boundary) becomes:

$$S_{\text{rad}}(t_{\text{Page}}^{\text{Adm}}) = S_{BH}^{\text{eff}}(t_{\text{Page}}^{\text{Adm}})$$

Expanding:

$$S_{\text{rad}} = S_{BH} - S_{B,\text{reserved}}$$

### 3.2 Page Time Shift

Let τ = t/t_evap. Standard Page time: τ_Page = 1/2.

Define the correction parameter:

$$\epsilon = \frac{S_{B,\text{reserved}}(t_{\text{Page}})}{S_0}$$

The modified Page time satisfies:

$$S_0 \left(1 - \tau_{\text{Page}}^{\text{Adm}}\right)^{2/3} - \epsilon S_0 = S_0 \cdot \tau_{\text{Page}}^{\text{Adm}} \cdot \frac{2}{3}$$

Linearizing around τ = 1/2:

$$\tau_{\text{Page}}^{\text{Adm}} \approx \frac{1}{2} + \frac{3\epsilon}{4 \cdot 2^{1/3}}$$

**Result:**

$$\boxed{\frac{\Delta t_{\text{Page}}}{t_{\text{Page}}} = \frac{3\epsilon}{2 \cdot 2^{1/3}} \approx 1.19 \epsilon}$$

### 3.3 Estimating ε

For N_distinct infalling quanta with typical distinguishability d_typ:

$$\epsilon = \frac{N_{\text{distinct}} \cdot h(d_{\text{typ}})}{S_0}$$

**Case 1: Thermal infall**

For thermal radiation at temperature T falling in:

$$\dot{N}_{\text{thermal}} \sim \frac{\sigma T^4 A}{E_{\text{photon}}}$$

With d_typ ~ 1/2 (random thermal states), h(d_typ) ~ 1.

$$\epsilon_{\text{thermal}} \sim \frac{t_{\text{Page}} \cdot \dot{N}}{S_0}$$

**Case 2: Pure state collapse**

For initial collapse from a pure state with S_in bits of information:

$$N_{\text{distinct}} = 2^{S_{\text{in}}}$$

But pairs are bounded by $\binom{N}{2}$, and we only count independent bits.

$$\epsilon_{\text{pure}} \sim \frac{S_{\text{in}}}{S_0}$$

---

## 4. Numerical Estimates

### 4.1 Solar Mass Black Hole

- $M_0 = M_\odot = 2 \times 10^{30}$ kg
- $S_0 = 4\pi G M_0^2 / \hbar c \approx 10^{77}$
- $t_{\text{evap}} \approx 10^{67}$ years

For infalling CMB radiation over cosmic time:
- $\dot{N} \sim 10^{43}$ photons/s
- $N_{\text{total}} \sim 10^{60}$ over evaporation

$$\epsilon \sim \frac{10^{60}}{10^{77}} = 10^{-17}$$

**Conclusion:** Completely negligible for astrophysical black holes.

### 4.2 Primordial Black Hole (10⁹ kg)

- $S_0 \sim 10^{38}$
- $t_{\text{evap}} \sim 10^{10}$ years (approximately now)

For a black hole evaporating today:

$$\epsilon \sim \frac{10^{20}}{10^{38}} = 10^{-18}$$

Still negligible.

### 4.3 Planck Mass Black Hole

- $M_0 = M_P \approx 2 \times 10^{-8}$ kg
- $S_0 \sim O(1)$
- $t_{\text{evap}} \sim t_P \approx 10^{-43}$ s

Here:

$$\epsilon \sim O(1)$$

**Conclusion:** Admissibility corrections are only significant at Planck scale.

---

## 5. Observable Consequences

### 5.1 Where Corrections Matter

The corrections are significant when:

$$\epsilon \sim \frac{N_{\text{distinct}} \cdot h(d)}{S_{BH}} \gtrsim 0.01$$

This requires $S_{BH} \lesssim 100 \cdot N_{\text{distinct}}$.

For quantum information experiments (N_distinct ~ 10-100 qubits):

$$S_{BH} \lesssim 10^3$$

This corresponds to black holes with:

$$M \lesssim 10^3 M_P \sim 10^{-5} \text{ kg}$$

Not accessible to observation, but potentially relevant for:
1. Final stages of primordial black hole evaporation
2. Black hole analogues in condensed matter systems
3. Gedanken experiments for quantum gravity

### 5.2 Correlation Spectrum

Even when ε is negligible, the *structure* of correlations may differ.

**Prediction:** Admissibility-constrained channels produce correlations with:

$$\langle a_\omega^\dagger a_{\omega'} \rangle_{\text{Adm}} = \langle a_\omega^\dagger a_{\omega'} \rangle_{\text{thermal}} + \delta C(\omega, \omega')$$

where:

$$\delta C(\omega, \omega') \propto \frac{1}{S_{BH}} \cdot e^{-(\omega + \omega')/T_H}$$

The correction term encodes phase relationships mandated by admissibility.

### 5.3 Comparison to Island Calculations

Island formula predicts the same Page curve shape. The admissibility model predicts:

1. **Same qualitative behavior** — information recovery at Page time
2. **Different dynamics** — rate bounded by dS_BH/dt
3. **Specific correlations** — phase structure from g(d) constraint

**Test:** Explicit island calculations with probe fields should match the correlation spectrum prediction.

---

## 6. Derivation Summary

### What We Derived

| Quantity | Formula | Regime |
|----------|---------|--------|
| Page time shift | Δt/t ~ 1.19 ε | ε << 1 |
| Correction parameter | ε ~ N·h(d)/S_BH | All |
| Correlation correction | δC ~ 1/S_BH | Late time |

### Derivation Chain

```
Theorem 6.2 (g(d) bound)
    ↓
Entropy reservation: S_reserved ~ N·h(d)
    ↓
Effective capacity: S_eff = S_BH - S_reserved
    ↓
Modified Page condition: S_rad = S_eff
    ↓
Page time shift: Δt/t ~ 1.19 ε
```

### Status

The Page curve corrections are **derived** but **practically unmeasurable** for astrophysical black holes.

The value of the derivation is:
1. **Consistency check** — corrections are negligible where they should be
2. **Planck regime prediction** — corrections are O(1) where quantum gravity matters
3. **Structural constraint** — even unmeasurable corrections constrain the theory

---

## 7. Next Steps

### 7.1 Immediate

1. Verify correlation spectrum against explicit island calculations
2. Check consistency with scrambling time bounds (Sekino-Susskind)
3. Derive the O(1) function f(t/t_Page) in §2.4

### 7.2 Extensions

1. Rotating black holes (Kerr) — how does angular momentum affect g(d)?
2. Charged black holes (Reissner-Nordström) — inner horizon complication
3. AdS black holes — holographic verification of g(d)

### 7.3 Connections

1. **Hayden-Preskill:** The "fast scrambling" result says information becomes accessible after scrambling time. Does admissibility constrain the scrambling rate?

2. **Quantum extremal surfaces:** The QES formula determines where islands appear. Can admissibility predict QES location?

3. **Complexity:** Does admissibility constrain computational complexity of information recovery?

---

## References

- Page, D.N. (1993). Information in black hole radiation. *Phys. Rev. Lett.* 71, 3743.
- Hayden, P. & Preskill, J. (2007). Black holes as mirrors. *JHEP* 09, 120.
- Sekino, Y. & Susskind, L. (2008). Fast scramblers. *JHEP* 10, 065.
- Almheiri, A. et al. (2020). The entropy of Hawking radiation. *Rev. Mod. Phys.* 93, 035002.
- Penington, G. (2020). Entanglement wedge reconstruction and the information paradox. *JHEP* 09, 002.
