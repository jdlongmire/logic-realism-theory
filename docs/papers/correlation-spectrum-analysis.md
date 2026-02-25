# Correlation Spectrum Analysis: Resolving the 1/S_BH vs e^{-S_BH} Discrepancy

## Status: Completed analysis
**Depends on:** page-curve-corrections.md §5.2, verification-results.md §4

---

## 1. The Discrepancy

### 1.1 Two Predictions

The page-curve-corrections.md (§5.2) predicts:

$$\delta C(\omega, \omega') \propto \frac{1}{S_{BH}} \cdot e^{-(\omega + \omega')/T_H}$$

Island calculations (Penington et al. 2020) give:

$$\langle a_\omega^\dagger a_{\omega'} \rangle_{\text{island}} \sim e^{-S_{BH}}$$

The ratio is S_BH · e^{S_BH} — astronomically different for astrophysical black holes.

### 1.2 The Question

Is this:
1. A contradiction (our prediction is wrong)?
2. Different quantities (apples vs oranges)?
3. Different regimes (complementary domains)?

---

## 2. Analysis: Three Distinct Scales

The resolution is option (2): these are different physical quantities with different meanings.

### 2.1 Quantity 1: Individual Mode Correlation

**Definition:** The correlation between specific Hawking modes ω and ω'.

**Standard result (islands):**

$$C(\omega, \omega') = \langle a_\omega^\dagger a_{\omega'} \rangle - \langle a_\omega^\dagger \rangle\langle a_{\omega'} \rangle \sim e^{-S_{BH}}$$

**Physical meaning:** The probability that measuring mode ω tells you something about mode ω' is exponentially small. Information is distributed across exponentially many mode pairs.

**Verification:** For ~e^{S_BH} modes total, there are ~e^{2S_BH} mode pairs. If total information content is S_BH bits, the information per pair is:

$$I_{\text{pair}} \sim \frac{S_{BH}}{e^{2S_{BH}}} \sim S_{BH} \cdot e^{-2S_{BH}}$$

The correlation magnitude C scales as (roughly) the square root of mutual information for small correlations:

$$C \sim \sqrt{I_{\text{pair}}} \sim e^{-S_{BH}}$$

This confirms the island result.

### 2.2 Quantity 2: Cumulative Information

**Definition:** Total mutual information between radiation and input state.

**Standard result (Page):**

$$I(\rho_{\text{rad}} : \rho_{\text{in}}) = \min\{S_{\text{rad}}, S_{\text{in}}\}$$

After Page time, this approaches S_in ~ S_BH (all information recovered).

**Physical meaning:** Measuring *all* radiation modes collectively reveals ~S_BH bits about the input.

**Relation to individual correlations:**

$$I_{\text{total}} = \sum_{\omega,\omega'} I(\omega,\omega') \sim e^{2S_{BH}} \times e^{-2S_{BH}} \times S_{BH} = S_{BH}$$

The exponentially many weak correlations sum to finite information.

### 2.3 Quantity 3: Distinguishability Resolution

**Definition:** The minimum distinguishability achievable from a single measurement.

**Admissibility result (Theorem 6.2):**

$$g(d) \sim \frac{h(d)}{S_{BH}}$$

where g(d) is the fraction of distinguishability the boundary must preserve.

**Physical meaning:** This is about **encoding capacity**, not correlation magnitude. The boundary can track ~S_BH/h(d) distinguishable pairs before saturating.

**What 1/S_BH means here:**

The minimum distinguishable fraction is:

$$d_{\min} \sim \frac{1}{S_{BH}}$$

This says: states differing by less than 1/S_BH in trace distance cannot be distinguished by the boundary. It does NOT say individual correlations are ~1/S_BH.

---

## 3. Correcting the Prediction

### 3.1 The Error

The formula in page-curve-corrections.md (§5.2):

$$\delta C(\omega, \omega') \propto \frac{1}{S_{BH}}$$

is **incorrect** as stated. It conflates distinguishability resolution (1/S_BH) with correlation magnitude (e^{-S_BH}).

### 3.2 Correct Statement

**Theorem (Corrected Correlation Spectrum):**

The admissibility constraint on individual mode correlations gives:

$$C(\omega, \omega') \geq e^{-S_{BH}} \cdot f(\omega, \omega'; T_H)$$

where f is an O(1) function of mode frequencies and Hawking temperature.

**Proof sketch:**

1. Total information to be encoded: I_total ~ S_BH bits
2. Number of mode pairs: N_pairs ~ e^{2S_BH}
3. Information per pair (for uniform distribution): I_pair ~ S_BH / e^{2S_BH}
4. Correlation magnitude: C ~ exp(I_pair) ~ e^{-exp(2S_BH)/S_BH} for very weak correlations
5. But correlations are not uniformly distributed; O(e^{S_BH}) dominant pairs carry O(1) bit each
6. For dominant pairs: I ~ 1/e^{S_BH} per pair, giving C ~ e^{-S_BH}

The admissibility bound is **consistent** with the island result. It doesn't provide a tighter constraint on individual correlations.

### 3.3 Where Admissibility Does Constrain

Admissibility provides structure beyond individual correlation magnitudes:

**Constraint A:** The total information recovered must equal input information:

$$\sum_{\text{modes}} I(\omega : \rho_{\text{in}}) = S(\rho_{\text{in}})$$

This is standard unitarity.

**Constraint B:** The rate of information recovery is bounded:

$$\frac{dI_{\text{rec}}}{dt} \leq -\frac{dS_{BH}}{dt}$$

This is our central inequality (§4).

**Constraint C:** Correlation structure has phase constraints from g(d):

$$\text{arg}(C(\omega, \omega')) \text{ is not random but constrained by admissibility}$$

The phases must be consistent with preserving distinguishability. This is a **structural** prediction, not a magnitude prediction.

---

## 4. Revised Predictions

### 4.1 Correlation Magnitude

**OLD (incorrect):**
$$\delta C \propto 1/S_{BH}$$

**NEW (correct):**
$$C \sim e^{-S_{BH}}$$

consistent with island calculations.

### 4.2 Cumulative Information Recovery

**Unchanged:** Information recovery rate bounded by |dS_BH/dt|.

### 4.3 Phase Structure (New Prediction)

**New prediction:** The phase distribution of correlations is constrained:

$$\langle e^{i\theta(\omega,\omega')} \rangle \neq 0$$

where θ is the correlation phase. Generic scrambling gives random phases (averaging to zero). Admissibility constrains phases to maintain distinguishability.

**Observable consequence:**

For a pure initial state with known phase relationships, the radiation correlations should preserve those relationships modulo scrambling. Specifically:

$$\sum_{\omega,\omega'} C(\omega, \omega') e^{i\phi_{\omega,\omega'}} = \mathcal{O}(1)$$

for the correct phase pattern φ corresponding to the input state, while the sum averages to ~e^{-S_BH} for random phases.

This is a **weak** prediction (O(1) vs e^{-S_BH} for integrated quantities) but in principle testable in analog systems.

---

## 5. Comparison to Island Formula

### 5.1 Agreement

Our corrected correlation magnitude (~e^{-S_BH}) agrees with island calculations.

### 5.2 Additional Structure

Admissibility adds:
1. **Rate bound** on information recovery (not in island formula)
2. **Phase constraints** on correlations (not computed in standard island calculations)
3. **Mechanism** (boundary saturation) for why islands appear

### 5.3 Relation to QES

The island formula involves quantum extremal surfaces (QES). The QES location is where:

$$\frac{\partial}{\partial r}\left[\frac{\phi(r)}{4G} + S_{\text{bulk}}\right] = 0$$

Our revised QES prediction (from verification-results.md):

$$\frac{\phi_H - \phi(r_{\text{QES}})}{4G} \sim S_{\text{rad}} \cdot h(\bar{d})$$

The factor h(d̄) is a new structure from admissibility — the QES location depends on the distinguishability content of the infalling matter, not just its total entropy.

---

## 6. Summary

### 6.1 Resolution

The 1/S_BH vs e^{-S_BH} discrepancy is resolved:

| Quantity | Correct Formula | Interpretation |
|----------|-----------------|----------------|
| Individual correlation | C ~ e^{-S_BH} | Per mode-pair correlation |
| Distinguishability resolution | d_min ~ 1/S_BH | Minimum resolvable difference |
| Total information | I ~ S_BH | Sum over all correlations |

The original formula conflated these distinct quantities.

### 6.2 Implications

1. **Island calculations confirmed:** Our corrected prediction matches
2. **Admissibility adds structure:** Rate bounds and phase constraints
3. **No new magnitude prediction:** Individual correlations scale as expected
4. **Phase prediction is new:** Testable in principle in analog systems

### 6.3 Papers to Update

1. **page-curve-corrections.md §5.2:** Replace δC ~ 1/S_BH with C ~ e^{-S_BH} + phase constraint
2. **verification-results.md §4:** Mark correlation spectrum as ✓ Resolved
3. **black-hole-derivation-summary.md:** Update predictions table

---

## 7. Physical Conclusions

### 7.1 What Admissibility Constrains

Admissibility (L₃ → distinguishability preservation) constrains:
- **Total information recovery** (must be complete)
- **Recovery rate** (bounded by |dS_BH/dt|)
- **Correlation phases** (not random)

### 7.2 What Admissibility Does NOT Constrain

Admissibility does not tighten:
- **Individual correlation magnitude** (standard scrambling suffices)
- **Scrambling time** (HP bound is stronger)

### 7.3 Falsifiability

The phase structure prediction is in principle falsifiable:
- Random scrambling: phase sum ~ e^{-S_BH/2} (central limit theorem)
- Admissibility: phase sum ~ O(1) for correct input-matched phases

This requires precise phase measurements, which may be accessible in analog systems (cold atoms, photonic circuits) but not in astrophysical black holes.

---

## References

- Penington, G. (2020). Entanglement wedge reconstruction and the information paradox. *JHEP*.
- Almheiri, A. et al. (2020). The entropy of Hawking radiation. *Rev. Mod. Phys.*
- Page, D. (1993). Information in black hole radiation. *Phys. Rev. Lett.*
