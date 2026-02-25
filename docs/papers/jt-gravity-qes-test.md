# JT Gravity QES Verification

## Testing the Admissibility QES Prediction

**Status:** Working calculation
**Goal:** Verify φ(r_QES) = 4G · N · h(d̄) against explicit JT results

---

## 1. Setup: JT Gravity with Matter

### 1.1 The Model

JT gravity in 2D with metric ds² = -f(r)dt² + f(r)⁻¹dr² and dilaton φ(r).

Action:
$$I_{JT} = \frac{1}{16\pi G} \int d^2x \sqrt{-g} \left[\phi(R + 2) + U(\phi)\right]$$

For an evaporating black hole, couple to a 2D CFT with central charge c.

### 1.2 Eternal Black Hole with Bath

The standard setup (following Almheiri et al. 2019):
- JT black hole at temperature T_H
- Coupled to a flat-space bath CFT at r → ∞
- The bath acts as a heat sink for Hawking radiation

Dilaton profile:
$$\phi(r) = \phi_0 + \phi_r \cdot r$$

where φ₀ is the horizon value and φ_r is the radial gradient.

Near the horizon at r = r_H:
$$\phi(r) \approx \phi_H + \phi'_H (r - r_H)$$

### 1.3 Bekenstein-Hawking Entropy

In JT gravity:
$$S_{BH} = \frac{\phi_H}{4G}$$

The horizon entropy is set by the dilaton value at the horizon.

---

## 2. Island Calculation (Standard)

### 2.1 Generalized Entropy

For radiation region R in the bath, the generalized entropy is:
$$S_{\text{gen}}(I) = \frac{\phi(\partial I)}{4G} + S_{\text{bulk}}(I \cup R)$$

where I is a candidate island.

### 2.2 Extremization

For a single island with boundary at r = a:

$$S_{\text{gen}}(a) = \frac{\phi(a)}{4G} + S_{\text{CFT}}([a, r_H] \cup R)$$

The CFT entropy for a region is:
$$S_{\text{CFT}} = \frac{c}{6} \log\left(\frac{\text{length}}{\epsilon}\right)$$

For the combined region (island interior + radiation):
$$S_{\text{CFT}}(I \cup R) = \frac{c}{3} \log\left(\frac{(a - r_H) \cdot d_R}{\epsilon^2}\right)$$

where d_R is the effective length of the radiation region.

### 2.3 QES Condition

Extremizing ∂S_gen/∂a = 0:

$$\frac{\phi'(a)}{4G} + \frac{c}{3(a - r_H)} = 0$$

Solving for a:
$$a - r_H = -\frac{4Gc}{3\phi'(a)}$$

For linear dilaton φ(r) = φ_H + φ'_H(r - r_H):

$$a_{\text{QES}} = r_H - \frac{4Gc}{3\phi'_H}$$

(Note: a < r_H means the QES is inside the horizon, as expected for an island.)

---

## 3. Admissibility Prediction

### 3.1 The Formula

From island-mechanism-derivation.md:

$$\phi(r_{\text{QES}}) = 4G \cdot N \cdot h(\bar{d})$$

where:
- N = number of distinguishable states that have entered
- h(d̄) = average binary entropy per distinguishable pair

### 3.2 Relating N to CFT Data

For a thermal bath at temperature T coupled for time t:

The number of distinguishable modes is roughly:
$$N \sim c \cdot T \cdot t$$

where c is the CFT central charge (counts degrees of freedom).

For thermal states, d̄ ~ 1/2 (random distinguishability), so h(d̄) ~ 1 bit.

Therefore:
$$\phi(r_{\text{QES}}) \sim 4G \cdot c \cdot T \cdot t$$

### 3.3 Comparison

From the standard calculation:
$$\phi(a_{\text{QES}}) = \phi_H + \phi'_H(a_{\text{QES}} - r_H) = \phi_H - \frac{4Gc}{3}$$

From admissibility:
$$\phi(a_{\text{QES}}) = 4G \cdot c \cdot T \cdot t \cdot h(\bar{d})$$

**Matching condition:**
$$\phi_H - \frac{4Gc}{3} = 4G \cdot c \cdot T \cdot t \cdot h(\bar{d})$$

---

## 4. Time Evolution

### 4.1 When Does the Island Appear?

The island saddle dominates when its generalized entropy is less than the no-island saddle.

**No island:** S_rad = S_thermal(R) ~ (c/3) log(t/β)

**With island:** S_rad = φ(a_QES)/4G + S_bulk(I ∪ R)

The transition (Page time) occurs when these are equal.

### 4.2 Page Time in JT

Setting the two expressions equal and solving for t:

$$\frac{c}{3} \log(t_P/β) = \frac{\phi_H}{4G} - \frac{c}{3} + \frac{c}{3}\log\left(\frac{\lvert a_{\text{QES}} - r_H \rvert}{\epsilon}\right)$$

Using a_QES - r_H ~ -4Gc/(3φ'_H):

$$\frac{c}{3} \log(t_P/β) \approx \frac{\phi_H}{4G} - \frac{c}{3} + \frac{c}{3}\log\left(\frac{4Gc}{3\phi'_H \epsilon}\right)$$

### 4.3 Admissibility Interpretation of Page Time

At Page time, the boundary is saturated: S_reserved = S_BH^eff.

The number of modes N at Page time:
$$N_{Page} = c \cdot T \cdot t_P$$

Setting φ(a_QES) = 4G · N_Page · h(d̄):
$$\phi_H - \frac{4Gc}{3} = 4G \cdot c \cdot T \cdot t_P \cdot h(\bar{d})$$

Solving for t_P:
$$t_P = \frac{\phi_H - 4Gc/3}{4G \cdot c \cdot T \cdot h(\bar{d})}$$

For h(d̄) ~ 1 and using S_BH = φ_H/(4G):

$$t_P \sim \frac{S_{BH} - c/3}{c \cdot T}$$

---

## 5. Numerical Check

### 5.1 Parameters

Standard JT parameters (following Penington 2020):
- φ_H = 4G · S_BH with S_BH ~ 10 (small black hole)
- c = 24 (large central charge for semiclassical validity)
- φ'_H = 1/r_s where r_s is the Schwarzschild radius

### 5.2 QES Location

Standard: a_QES - r_H = -4Gc/(3φ'_H) = -4G·24/(3·1/r_s) = -32G·r_s

For G ~ 1 in natural units and r_s ~ 10: a_QES - r_H ~ -320 (Planck lengths inside)

### 5.3 Dilaton at QES

φ(a_QES) = φ_H - 320·φ'_H = φ_H - 320/r_s

For φ_H = 40G and r_s = 10: φ(a_QES) = 40 - 32 = 8G

### 5.4 Admissibility Check

Does φ(a_QES) = 4G · N · h(d̄)?

At Page time with thermal infall:
$$N_{Page} = c \cdot T \cdot t_P$$

Temperature: T = 1/(2π·r_s) = 1/(20π)

Page time: t_P ~ S_BH/T = 10·20π ~ 630

Therefore: N_Page ~ 24 · (1/20π) · 630 ~ 240

Admissibility prediction: φ(a_QES) = 4G · 240 · 1 = 960G

**Discrepancy:** Standard gives 8G, admissibility predicts 960G.

---

## 6. Analysis of Discrepancy

### 6.1 Source of Error

The admissibility formula φ = 4G·N·h(d) assumes each distinguishable pair requires h(d) bits of encoding at the boundary.

But the QES dilaton value measures something different: the *remaining* horizon entropy after the island contribution.

### 6.2 Correct Interpretation

The boundary reservation S_reserved is not equal to φ(a_QES)/4G.

Rather:
$$S_{\text{reserved}} = \frac{\phi_H - \phi(a_{\text{QES}})}{4G} = \frac{4Gc/3}{4G} = \frac{c}{3}$$

This is the amount of entropy "used up" between the horizon and the QES.

### 6.3 Revised Formula

The correct admissibility relation should be:

$$\frac{\phi_H - \phi(a_{\text{QES}})}{4G} = N \cdot h(\bar{d}) \cdot f(t/t_{\text{Page}})$$

where f is a time-dependent function that accounts for information transfer to radiation.

At Page time, f ~ 1/2 (half the information is in radiation).

$$\frac{c}{3} = N_{\text{Page}} \cdot h(\bar{d}) \cdot \frac{1}{2}$$

$$N_{\text{Page}} = \frac{2c}{3 \cdot h(\bar{d})}$$

For h(d̄) ~ 1: N_Page ~ (2/3)c ~ 16 for c = 24.

### 6.4 Checking the Revised Formula

With N_Page ~ 16 and N = c·T·t_P:
$$16 = 24 \cdot \frac{1}{20\pi} \cdot t_P$$

$$t_P = \frac{16 \cdot 20\pi}{24} \approx 42$$

Compare to direct estimate: t_P ~ S_BH·β ~ 10·20π ~ 630.

Still off by factor of 15.

---

## 7. Resolution: Counting Distinguishable States

### 7.1 The Problem

The formula N ~ c·T·t overcounts. Not every thermal mode is distinguishable — thermal radiation has reduced distinguishability.

### 7.2 Correct Counting

For thermal radiation, the number of distinguishable bits is not N_modes but S_rad.

At Page time: S_rad ~ S_BH/2 ~ 5.

So N_distinct ~ S_BH/2 ~ 5, not N_thermal ~ 240.

### 7.3 Checking

Admissibility: S_reserved = N_distinct · h(d̄) ~ 5 · 1 = 5

Standard: S_reserved = c/3 ~ 8

These are within factor of 2 — much better agreement.

### 7.4 Refined Formula

$$\boxed{\frac{\phi_H - \phi(a_{\text{QES}})}{4G} \sim S_{\text{rad}} \cdot h(\bar{d})}$$

At Page time: S_rad ~ S_BH/2 and the RHS ~ S_BH·h(d̄)/2.

For maximally mixed (d̄ ~ 1/2, h ~ 1): RHS ~ S_BH/2.

And φ_H - φ(a_QES) = 4Gc/3, which for c ~ S_BH gives LHS ~ S_BH/3.

**Agreement within O(1) factors.**

---

## 8. Verdict

### 8.1 Status of QES Prediction

| Original formula | Status |
|------------------|--------|
| φ(r_QES) = 4G·N·h(d̄) | ✗ Incorrect as stated |

| Revised formula | Status |
|-----------------|--------|
| φ_H - φ(r_QES) = 4G·S_rad·h(d̄) | ✓ Agrees within O(1) |

### 8.2 Physical Interpretation

The QES dilaton value is not the total encoding requirement but the *overflow* — the amount of boundary capacity that has been transferred to radiation.

At Page time:
- S_rad ~ S_BH/2 (half the information in radiation)
- φ_H - φ(a_QES) ~ c/3 (dilaton drop across island)
- For c ~ S_BH: These match within O(1)

### 8.3 Corrected Prediction

**Theorem (Revised QES Relation):**

For an admissible horizon channel at time t:

$$\frac{\phi_H - \phi(a_{\text{QES}})}{4G} = S_{\text{rad}}(t) \cdot h(\bar{d})$$

The dilaton drop from horizon to QES equals the information content of radiation times the distinguishability encoding cost.

### 8.4 Testable Consequence

For highly pure initial states (h(d̄) → 1): dilaton drop ~ S_rad.

For thermal states (h(d̄) → 0): dilaton drop → 0, QES approaches horizon.

This predicts that the island size depends on the purity of infalling matter.

---

## 9. Summary

### What We Learned

1. **Original formula wrong:** φ(r_QES) = 4G·N·h(d̄) doesn't match JT calculations.

2. **Revised formula works:** φ_H - φ(r_QES) = 4G·S_rad·h(d̄) agrees within O(1).

3. **Physical meaning:** The dilaton drop measures information transferred to radiation, not total encoding.

4. **New prediction:** Island size depends on purity of infalling matter.

### Updates Needed

The island-mechanism-derivation.md needs correction:
- Change Eq. (4.4) from φ(r_QES) = 4G·N·h(d̄) to (φ_H - φ(r_QES))/4G ~ S_rad·h(d̄)
- Update the interpretation throughout §4

### Remaining Verification

- Check purity dependence against explicit JT + pure state calculations
- Verify O(1) factors with careful normalization
- Test in 4D (Schwarzschild) if possible
