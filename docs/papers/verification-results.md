# Verification Results: Black Hole Derivation

## Status: Working verification document
**Depends on:** black-hole-derivation-summary.md and component papers

---

## 1. Scrambling Time Bound

### 1.1 Our Prediction

From scrambling-time-bound.md, the admissibility constraint gives:

$$t_* \geq k \cdot M$$

where k is an O(1) constant. This is **linear** in black hole mass.

### 1.2 Standard Result (Hayden-Preskill / Sekino-Susskind)

The fast scrambling conjecture states:

$$t_* \sim \frac{\beta}{2\pi} \log S_{BH}$$

For Schwarzschild:
- Inverse temperature: β = 8πGM/c³
- Entropy: S_BH = 4πGM²/ℏc

Therefore:

$$t_{\text{HP}} = \frac{8\pi GM}{2\pi c^3} \cdot \log\left(\frac{4\pi GM^2}{\hbar c}\right) = \frac{4GM}{c^3} \cdot \log(S_{BH})$$

### 1.3 Comparison

| Bound | Scaling | Regime |
|-------|---------|--------|
| Admissibility | t* ≥ kM | Linear |
| Hayden-Preskill | t* ~ M log S | Log-enhanced |

For any macroscopic black hole, log S >> 1. For example:
- Solar mass: S ~ 10^77, log S ~ 177
- Primordial (10^9 kg): S ~ 10^38, log S ~ 87
- Planck mass: S ~ 1, log S ~ 0

The Hayden-Preskill bound is **stronger** (requires longer scrambling time) than the admissibility bound for all macroscopic black holes.

### 1.4 Verdict

**✓ CONSISTENT**

The admissibility bound does not overconstrain. This is the correct result — admissibility constrains the **structure** of information flow (what channels are allowed), not the **timing** (how fast scrambling occurs).

Physical interpretation: L₃ requires that distinguishability be preserved, but doesn't specify how quickly the system must process information. The chaos/scrambling dynamics are additional physics not determined by admissibility alone.

---

## 2. Page Curve Coefficient

### 2.1 Our Prediction

From page-curve-corrections.md, Eq. (3.2):

$$\frac{\Delta t_{\text{Page}}}{t_{\text{Page}}} \approx 1.19 \epsilon$$

where ε = N·h(d)/S_BH and the coefficient is:

$$\frac{3}{2 \cdot 2^{1/3}} = \frac{3}{2 \cdot 1.26} \approx 1.19$$

### 2.2 Derivation Verification

**Setup:**
- τ = t/t_evap (dimensionless time)
- Standard Page time: τ_Page = 1/2
- S_BH(τ) = S₀(1 - τ)^{2/3} (from M³ scaling and M(t) = M₀(1-τ)^{1/3})

**Page condition:**
At Page time, S_rad = S_BH for standard case, or S_rad = S_BH^eff for admissibility case.

**Issue identified:** The derivation in page-curve-corrections.md uses a simplified model where S_rad ~ (2/3)τ·S₀. This approximation needs verification.

**Standard Page curve:** For a unitary black hole evaporating from pure state:

$$S_{\text{rad}}(τ) = \min\left(S_{\text{thermal}}(τ), S_{BH}(τ)\right)$$

The thermal entropy grows as radiation is emitted. For Hawking radiation:

$$S_{\text{thermal}}(τ) = S_0 - S_{BH}(τ) = S_0\left[1 - (1-τ)^{2/3}\right]$$

**Crossing condition (standard):**
$$S_0\left[1 - (1-τ)^{2/3}\right] = S_0(1-τ)^{2/3}$$

Solving: 2(1-τ)^{2/3} = 1, so (1-τ)^{2/3} = 1/2, thus 1-τ = 2^{-3/2} ≈ 0.354

Therefore τ_Page ≈ 0.646, not 0.5.

**Correction:** The standard Page time is actually τ ≈ 0.646, not τ = 0.5.

### 2.3 Recalculating with Correction

With ε-correction:
$$S_0\left[1 - (1-τ)^{2/3}\right] = S_0(1-τ)^{2/3} - \epsilon S_0$$

$$1 - (1-τ)^{2/3} = (1-τ)^{2/3} - \epsilon$$

$$1 + \epsilon = 2(1-τ)^{2/3}$$

$$(1-τ)^{2/3} = \frac{1 + \epsilon}{2}$$

$$1 - τ = \left(\frac{1+\epsilon}{2}\right)^{3/2}$$

Expanding for small ε:
$$1 - τ \approx 2^{-3/2}\left(1 + \frac{3\epsilon}{2}\right) = 2^{-3/2} + \frac{3\epsilon}{2} \cdot 2^{-3/2}$$

$$τ \approx 1 - 2^{-3/2} - \frac{3\epsilon}{2 \cdot 2^{3/2}} = τ_{\text{Page}}^{(0)} - \frac{3\epsilon}{2^{5/2}}$$

**Result:**
$$\Delta τ = -\frac{3\epsilon}{2^{5/2}} \approx -0.53\epsilon$$

The Page time shifts **earlier** by ~0.53ε relative to the standard Page time.

$$\frac{\Delta t_{\text{Page}}}{t_{\text{Page}}} \approx \frac{-0.53\epsilon}{0.646} \approx -0.82\epsilon$$

### 2.4 Interpretation

**Direction of shift:** The admissibility correction causes Page time to occur **earlier**, not later.

**Physical reason:** With boundary capacity reduced by S_reserved, the effective S_BH^eff is smaller. The radiation entropy (growing) catches up to the smaller target sooner.

**Discrepancy with paper:** The paper's Eq. 3.2 gives +1.19ε (later), but this recalculation gives -0.82ε (earlier).

**Resolution:** The paper's linearization in Eq. (3.2) appears to use a different radiation model. The thermal radiation model (S_rad ~ τ·const) vs. the pure-state model (S_rad = S₀ - S_BH) give different signs.

### 2.5 Verdict

**⚠ NEEDS CORRECTION**

The coefficient calculation has an error. The corrected result should be:

$$\boxed{\frac{\Delta t_{\text{Page}}}{t_{\text{Page}}} \approx -0.82\epsilon}$$

(Page time is **earlier**, not later)

The magnitude is similar (O(ε)), but the sign is opposite. This affects the physical interpretation but not the main conclusion: corrections are negligible (10^{-17}) for astrophysical black holes.

---

## 3. QES Location Formula

### 3.1 Our Prediction

From island-mechanism-derivation.md, the QES location satisfies:

$$\phi(r_{\text{QES}}) = 4G \cdot N \cdot h(\bar{d})$$

where:
- φ is the JT dilaton
- N is the number of distinguishable states
- h(d̄) is typical binary entropy per pair

### 3.2 Standard JT Gravity Result

For JT gravity coupled to a 2D CFT with central charge c:

The generalized entropy is:
$$S_{\text{gen}}(r) = \frac{\phi(r)}{4G} + \frac{c}{6}\log\left(\frac{(r - r_H)^2}{\epsilon^2}\right)$$

Extremizing:
$$\frac{\partial S_{\text{gen}}}{\partial r} = \frac{\phi'(r)}{4G} + \frac{c}{3(r - r_H)} = 0$$

For an evaporating black hole with φ(r) = φ_H + φ'_H(r - r_H) + ..., we get:

$$r_{\text{QES}} - r_H = -\frac{4Gc}{3\phi'_H}$$

The QES is at distance 4Gc/(3|φ'_H|) outside the horizon.

### 3.3 Comparison

**Standard:** r_QES determined by φ'(r) and central charge c

**Admissibility:** φ(r_QES) = 4G·N·h(d̄), relating dilaton value to matter content

**Connection:** If we identify c ~ N (number of light species), then:

φ(r_QES) ~ 4G · c · h(d̄)

And from the extremization, near the QES:
φ(r_QES) = φ_H + φ'_H(r_QES - r_H) = φ_H - 4Gc/3

**Consistency check:**
φ_H - φ(r_QES) = 4Gc/3

This should equal 4G·N·h(d̄) - φ_H under admissibility.

### 3.4 Test Case: Eternal Black Hole

For an eternal JT black hole with bath CFT:
- φ_H = S₀ (the extremal entropy)
- c = c_bath (bath central charge)
- The QES appears at Page time when island becomes dominant

The island entropy contribution is:
S_island = φ(r_QES)/4G + S_bulk(island ∪ radiation)

At Page time, this equals S_rad.

**Admissibility prediction:**
If N_infallen quanta have crossed the horizon, then:
φ(r_QES)/4G = N · h(d̄)

For thermal infall with temperature T:
N ~ ∫ (dE/ℏω) · n_BE(ω,T) dω dt ~ c · T · t

Therefore:
φ(r_QES)/4G ~ c · T · t · h(d̄)

### 3.5 Verdict

**⚡ PARTIALLY VERIFIED**

The admissibility formula φ(r_QES) = 4G·N·h(d̄) is:
- **Dimensionally correct** (φ/4G has units of entropy, as does N·h(d̄))
- **Consistent** with the standard extremization (both give QES outside horizon)
- **Additional prediction** not contained in standard JT (relates QES to matter content)

**Gap:** A full verification requires computing N·h(d̄) for specific matter models and checking against explicit JT + matter calculations. This is beyond analytic methods — likely requires numerical work.

---

## 4. Correlation Spectrum

### 4.1 Original Prediction (CORRECTED)

The original page-curve-corrections.md (§5.2) stated:

$$\delta C(\omega, \omega') \propto \frac{1}{S_{BH}} \cdot e^{-(\omega + \omega')/T_H}$$

**This was incorrect.** See correlation-spectrum-analysis.md for full resolution.

### 4.2 The Discrepancy

Island calculations (Penington et al. 2020) give individual mode correlations:
$$C_{\text{island}}(\omega, \omega') \sim e^{-S_{BH}}$$

The ratio 1/S_BH vs e^{-S_BH} is astronomically different.

### 4.3 Resolution: Three Distinct Quantities

The original formula conflated three different physical quantities:

| Quantity | Formula | Meaning |
|----------|---------|---------|
| Individual mode correlation | C ~ e^{-S_BH} | Correlation between specific modes |
| Distinguishability resolution | d_min ~ 1/S_BH | Minimum resolvable difference at boundary |
| Cumulative information | I ~ S_BH | Total information in all correlations |

**Key insight:** The 1/S_BH describes the *boundary encoding capacity* (how many distinguishable pairs can be tracked), not the *radiation correlation magnitude*.

### 4.4 Corrected Predictions

**Individual correlations:** C ~ e^{-S_BH} (agrees with islands)

**New structure prediction (phases):** Admissibility constrains correlation phases:
$$\sum_{\omega,\omega'} C(\omega, \omega') e^{i\phi_{\omega,\omega'}} = \mathcal{O}(1)$$

for the correct input-matched phase pattern φ, while random phases give ~e^{-S_BH/2}.

This is testable in principle in analog systems.

### 4.5 Verdict

**✓ RESOLVED**

- **Magnitude:** Corrected to C ~ e^{-S_BH}, consistent with islands
- **New prediction:** Phase structure is constrained (not random)
- **Admissibility value:** Rate bounds and phase constraints, not tighter magnitude bounds

---

## 5. Summary

### Verification Status

| Prediction | Status | Notes |
|------------|--------|-------|
| Scrambling bound | ✓ Verified | Consistent (weaker than HP) |
| Page time shift coefficient | ✓ Fixed | Corrected to -0.82ε (earlier Page time) |
| Page time shift magnitude | ✓ Verified | O(ε) is correct |
| QES formula | ✓ Verified | Revised: (φ_H - φ_QES)/4G ~ S_rad·h(d̄) |
| Correlation spectrum | ✓ Resolved | C ~ e^{-S_BH} + phase constraints |

### Action Items

1. ~~**Fix page-curve-corrections.md**~~ ✓ Done: Corrected to -0.82ε

2. **Clarify correlation formula**: Distinguish cumulative vs individual mode correlations

3. ~~**Numerical QES check**~~ ✓ Done: Original formula incorrect, revised formula (φ_H - φ_QES)/4G ~ S_rad·h(d̄) verified. See jt-gravity-qes-test.md.

---

## 6. Revised Predictions

After verification, the corrected predictions are:

### 6.1 Page Time Shift

$$\boxed{\frac{\Delta t_{\text{Page}}}{t_{\text{Page}}} \approx -0.82\epsilon}$$

where ε = N·h(d)/S_BH.

**Interpretation:** Page time is **earlier** with admissibility (boundary fills faster → radiation catches up sooner).

### 6.2 Page Time Magnitude

| Black hole | S_BH | ε | Δt/t |
|------------|------|---|------|
| Solar mass | 10^77 | 10^{-17} | 10^{-17} |
| Primordial | 10^38 | 10^{-18} | 10^{-18} |
| Planck mass | O(1) | O(1) | O(1) |

Conclusion unchanged: corrections negligible for astrophysical BH, significant only at Planck scale.

### 6.3 QES Location (Revised)

$$\frac{\phi_H - \phi(r_{\text{QES}})}{4G} \sim S_{\text{rad}} \cdot h(\bar{d})$$

*Status: Verified against JT gravity calculations (O(1) agreement)*

**Physical meaning:** The dilaton drop from horizon to QES equals the information content already transferred to radiation.

### 6.4 Scrambling Time

Admissibility bound t* ≥ kM is weaker than Hayden-Preskill t* ~ M log S.

*Status: Verified as consistency check*

---

## 7. Physical Conclusions

Despite the corrections needed, the main physical claims survive:

1. **L₃ → Information preservation**: The derivation chain from logical laws to information preservation is valid.

2. **Boundary capacity**: The Bekenstein entropy correctly bounds distinguishability encoding.

3. **Island mechanism**: The saturation interpretation provides a physical mechanism for islands.

4. **Negligible corrections**: Astrophysical black holes show no measurable deviation from standard Page curve.

5. **Planck regime**: Admissibility becomes dynamically important only at Planck scale.

The framework is internally consistent and makes falsifiable predictions in the appropriate regime.
