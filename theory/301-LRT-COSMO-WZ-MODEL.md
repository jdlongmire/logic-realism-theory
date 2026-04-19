# LRT Cosmology: Toy Model for $w(z)$ Evolution

**Status:** Exploratory quantitative model
**Epistemic flag:** Toy model — parameterized, not derived from first principles
**Dependencies:** 300-LRT-COSMOLOGY §5–6 (emission-absorption balance, $w = -1$ derivation)
**Issue:** #74

---

## 1. Motivation

The strongest potential discriminant between LRT's actualization-residue picture of dark energy and $\Lambda$CDM is the equation of state as a function of redshift, $w(z)$. In §6 of 300-LRT-COSMOLOGY, we derived $w = -1$ exactly from L₃ incompressibility — but that derivation assumes perfect emission-absorption equilibrium. §5.4 already noted that this balance shifts across cosmic history:

| Era | Emission $\Gamma_{\text{em}}$ | Absorption $\Gamma_{\text{abs}}$ | Net |
|-----|------|------|-----|
| Early universe ($z \gg 2$) | High | Low (few BHs) | Rapid $\rho_\Lambda$ buildup |
| Present ($z \approx 0$) | Moderate | Moderate | Near equilibrium |
| Far future | Low | Dominant | $\rho_\Lambda$ decline |

If the balance is imperfect, $\rho_\Lambda$ varies in time, and an observer inferring an equation of state from expansion data would measure $w(z) \neq -1$. This document constructs a toy model for $w(z)$ using known astrophysical inputs and compares the result with DESI BAO hints of dark energy evolution.

---

## 2. Framework: Effective $w$ from Source Terms

### 2.1 The Fluid Equation with Sources

In standard cosmology, a dark energy fluid with equation of state $w$ obeys:

$$\dot{\rho} + 3H(1 + w)\rho = 0$$

In LRT, the actualization residue has an *intrinsic* equation of state $w_{\text{int}} = -1$ (from L₃ incompressibility, §6), but also a source term from the emission-absorption imbalance:

$$\dot{\rho}_\Lambda = \Gamma_{\text{em}}(t) - \Gamma_{\text{abs}}(t) \equiv S(t)$$

An observer who does not know about $S(t)$ and fits the expansion history assuming a source-free fluid would infer an *effective* equation of state:

$$\dot{\rho} + 3H(1 + w_{\text{eff}})\rho = 0 \implies w_{\text{eff}} = -1 - \frac{\dot{\rho}}{3H\rho}$$

Substituting $\dot{\rho} = S$:

$$\boxed{w_{\text{eff}}(z) = -1 - \frac{\Gamma_{\text{em}}(z) - \Gamma_{\text{abs}}(z)}{3\,H(z)\,\rho_\Lambda(z)}}$$

**Sign conventions:**
- $\Gamma_{\text{em}} > \Gamma_{\text{abs}}$ (net residue production): $\dot{\rho} > 0 \implies w_{\text{eff}} < -1$ (phantom-like)
- $\Gamma_{\text{em}} < \Gamma_{\text{abs}}$ (net absorption): $\dot{\rho} < 0 \implies w_{\text{eff}} > -1$ (quintessence-like)

### 2.2 Two-Component Decomposition

We write the effective equation of state as:

$$w(z) = -1 + \alpha\,\Phi_{\text{abs}}(z) - \beta\,\Phi_{\text{em}}(z)$$

where:
- $\Phi_{\text{em}}(z) = \hat{\psi}(z) / E(z)$ — normalized emission shape function
- $\Phi_{\text{abs}}(z) = f_{\text{BH}}(z) / E(z)$ — normalized absorption shape function
- $\hat{\psi}(z) = \psi_{\text{MD}}(z)/\psi_{\text{MD}}(0)$ — normalized star formation rate density
- $f_{\text{BH}}(z) = \rho_{\text{BH}}(z)/\rho_{\text{BH}}(0)$ — cumulative BH mass assembly fraction
- $E(z) = H(z)/H_0 = \sqrt{\Omega_m(1+z)^3 + \Omega_\Lambda}$
- $\alpha, \beta > 0$ — free amplitudes encoding unknown LRT microphysics

**Physical interpretation:** $\beta\,\Phi_{\text{em}}$ drives $w$ toward phantom (emission $\to$ residue buildup), while $\alpha\,\Phi_{\text{abs}}$ drives $w$ toward quintessence (absorption $\to$ residue depletion). Both are modulated by the Hubble rate (higher $H$ dilutes the source-term effect).

At $z = 0$: $\Phi_{\text{em}}(0) = \Phi_{\text{abs}}(0) = 1$, so:

$$w_0 = -1 + \alpha - \beta$$

---

## 3. Parameterizing Emission: $\Gamma_{\text{em}}(z)$

### 3.1 Madau–Dickinson Star Formation Rate Density

Stars are the dominant actualization factories (300-LRT-COSMOLOGY §3.1.1). The cosmic star formation rate density (SFRD) is well-measured and parameterized by Madau & Dickinson (2014):

$$\psi_{\text{MD}}(z) = 0.015\,\frac{(1+z)^{2.7}}{1 + \left(\frac{1+z}{2.9}\right)^{5.6}} \quad [M_\odot\,\text{yr}^{-1}\,\text{Mpc}^{-3}]$$

This peaks at $z \approx 1.9$ and declines steeply at higher redshifts (fewer stars) and lower redshifts (declining gas supply).

### 3.2 Normalized Emission Shape

Defining $\hat{\psi}(z) = \psi_{\text{MD}}(z)/\psi_{\text{MD}}(0)$, we compute the emission shape function $\Phi_{\text{em}}(z) = \hat{\psi}(z)/E(z)$:

| $z$ | $\hat{\psi}(z)$ | $E(z)$ | $\Phi_{\text{em}}(z)$ |
|-----|-----------------|---------|----------------------|
| 0   | 1.00            | 1.00    | 1.00                 |
| 0.5 | 2.84            | 1.31    | 2.17                 |
| 1.0 | 5.15            | 1.76    | 2.93                 |
| 1.5 | 6.97            | 2.33    | 2.99                 |
| 2.0 | 7.82            | 2.97    | 2.63                 |
| 3.0 | 5.88            | 4.46    | 1.32                 |
| 5.0 | 1.14            | 8.09    | 0.14                 |

**Key feature:** $\Phi_{\text{em}}$ peaks at $z \approx 1.5$ and falls at both lower and higher redshifts.

### 3.3 What the SFRD Proxy Misses

The Madau–Dickinson SFRD captures stellar actualization only. At $z \gtrsim 6$, pre-stellar sources (BBN residuals, reionization-epoch processes) may contribute additional emission not tracked by the SFRD. We neglect these for the toy model; their inclusion would *strengthen* the phantom signal at very high $z$.

---

## 4. Parameterizing Absorption: $\Gamma_{\text{abs}}(z)$

### 4.1 Black Hole Mass Assembly History

In LRT, absorption (deactualization) is dominated by black holes (§5 of 300-LRT-COSMOLOGY). The cosmic supermassive black hole (SMBH) mass density grew over time as galaxies merged, AGN accreted, and stellar-mass BHs formed. At high $z$, few BHs existed; absorption capacity was low.

The cumulative SMBH mass density at redshift $z$, normalized to the present, is parameterized as:

$$f_{\text{BH}}(z) = \frac{\rho_{\text{BH}}(z)}{\rho_{\text{BH}}(0)} = \frac{1}{1 + (z / z_h)^{n_h}}$$

We adopt $z_h = 1.5$ and $n_h = 2$, consistent with observational constraints:
- The Soltan argument links SMBH mass to integrated AGN luminosity (Soltan 1982; Yu & Tremaine 2002)
- About 50% of SMBH mass was assembled by $z \approx 1.5$ (Shankar et al. 2009)
- BH mass assembly broadly tracks the SFRD but with a lag at high $z$ (Aird et al. 2015)

### 4.2 Normalized Absorption Shape

The absorption shape function $\Phi_{\text{abs}}(z) = f_{\text{BH}}(z)/E(z)$:

| $z$ | $f_{\text{BH}}(z)$ | $E(z)$ | $\Phi_{\text{abs}}(z)$ |
|-----|---------------------|---------|------------------------|
| 0   | 1.00                | 1.00    | 1.00                   |
| 0.5 | 0.90                | 1.31    | 0.69                   |
| 1.0 | 0.69                | 1.76    | 0.39                   |
| 1.5 | 0.50                | 2.33    | 0.21                   |
| 2.0 | 0.36                | 2.97    | 0.12                   |
| 3.0 | 0.20                | 4.46    | 0.045                  |
| 5.0 | 0.083               | 8.09    | 0.010                  |

**Key feature:** $\Phi_{\text{abs}}$ is monotonically decreasing — absorption capacity was always lower in the past.

---

## 5. The Imbalance Function and $w(z)$

### 5.1 Shape of the Deviation

The net deviation from $w = -1$ is:

$$\varepsilon(z) \equiv w(z) - (-1) = \alpha\,\Phi_{\text{abs}}(z) - \beta\,\Phi_{\text{em}}(z)$$

Since $\Phi_{\text{em}}$ is large at intermediate $z$ (peak SFRD era) while $\Phi_{\text{abs}}$ is suppressed (few BHs in the past), the emission term dominates at $z > 0$, making $\varepsilon < 0$ (phantom). Only at $z \approx 0$, where BH absorption has caught up, can $\varepsilon \geq 0$ (quintessence-like).

### 5.2 Fiducial Parameter Choice

We choose $\alpha$ and $\beta$ to approximately reproduce DESI-like behavior:

$$w_0 = -1 + \alpha - \beta \approx -0.7 \implies \alpha - \beta = 0.30$$

We additionally require $|w(z=2)| - 1 \sim 0.2$ to match the DESI phantom signal. A fiducial parameter set satisfying both:

$$\alpha = 0.40, \quad \beta = 0.10$$

### 5.3 Numerical $w(z)$ Profile

With these parameters:

| $z$ | $\alpha\,\Phi_{\text{abs}}$ | $\beta\,\Phi_{\text{em}}$ | $\varepsilon(z)$ | $w(z)$ |
|-----|----------------------------|---------------------------|-------------------|---------|
| 0   | $+0.40$                    | $-0.10$                   | $+0.30$           | $-0.70$ |
| 0.5 | $+0.27$                    | $-0.22$                   | $+0.06$           | $-0.94$ |
| 1.0 | $+0.16$                    | $-0.29$                   | $-0.14$           | $-1.14$ |
| 1.5 | $+0.086$                   | $-0.30$                   | $-0.21$           | $-1.21$ |
| 2.0 | $+0.048$                   | $-0.26$                   | $-0.22$           | $-1.22$ |
| 3.0 | $+0.018$                   | $-0.13$                   | $-0.11$           | $-1.11$ |
| 5.0 | $+0.004$                   | $-0.014$                  | $-0.010$          | $-1.01$ |

### 5.4 Key Features of $w(z)$

**Feature 1: Phantom divide crossing.** $w(z)$ crosses $-1$ at $z_{\text{cross}} \approx 0.6$, transitioning from quintessence-like ($w > -1$) at low $z$ to phantom-like ($w < -1$) at higher $z$. This is a natural consequence of BH absorption catching up to stellar emission at late cosmic times.

**Feature 2: Non-monotonic phantom deviation.** The maximum phantom deviation occurs at $z \approx 1.5$–$2.0$, coinciding with peak cosmic star formation. At $z > 2$, the declining SFRD reduces emission, and $w(z)$ returns toward $-1$.

**Feature 3: Asymptotic $w \to -1$ at high $z$.** Unlike CPL (which extrapolates linearly to ever-more-phantom values), the LRT model predicts $w \to -1$ at $z \gg 3$ because both emission and absorption rates vanish (few stars, few BHs). The underlying L₃-incompressibility mechanism remains, enforcing $w = -1$ in the absence of astrophysical source terms.

**Feature 4: $w \to -1$ in the far future.** As star formation ceases ($\hat{\psi} \to 0$) and BH accretion dominates, the residue is drained, driving $w$ back toward (and eventually past) $-1$.

---

## 6. Comparison with DESI BAO Results

### 6.1 DESI Y1 Results

The DESI collaboration (DESI 2024, arXiv:2404.03002) reported hints of dark energy evolution using the CPL parameterization $w(a) = w_0 + w_a(1-a)$. Combined with CMB (Planck) and supernova data (various compilations):

$$w_0 \approx -0.55 \pm 0.21, \quad w_a \approx -1.3 \pm 0.7 \quad (2\text{–}3\sigma \text{ from } \Lambda\text{CDM})$$

The CPL model gives:

| $z$ | $w_{\text{CPL}}$ (DESI+CMB+SN) |
|-----|--------------------------------|
| 0   | $-0.55$                        |
| 0.5 | $-0.98$                        |
| 1.0 | $-1.20$                        |
| 2.0 | $-1.42$                        |
| 3.0 | $-1.53$                        |
| 5.0 | $-1.64$                        |

### 6.2 LRT vs. CPL Comparison

| $z$ | $w_{\text{LRT}}$ | $w_{\text{CPL}}$ | $\Delta$ |
|-----|-------------------|-------------------|----------|
| 0   | $-0.70$           | $-0.55$           | $-0.15$  |
| 0.5 | $-0.94$           | $-0.98$           | $+0.04$  |
| 1.0 | $-1.14$           | $-1.20$           | $+0.06$  |
| 2.0 | $-1.22$           | $-1.42$           | $+0.20$  |
| 3.0 | $-1.11$           | $-1.53$           | $+0.42$  |
| 5.0 | $-1.01$           | $-1.64$           | $+0.63$  |

**Qualitative agreement at $z \lesssim 2$:** Both models show quintessence-to-phantom transition at $z \sim 0.5$–$0.7$, consistent with the same DESI data. The LRT and CPL curves nearly coincide at $z \sim 0.5$–$1.5$, which is precisely the redshift range where DESI has the strongest constraining power.

**Qualitative disagreement at $z \gtrsim 2$: the key discriminant.** The CPL extrapolation continues deepening into phantom territory without bound ($w \to w_0 + w_a = -1.85$), while LRT predicts a turnaround: $w(z)$ reaches its minimum near $z \sim 2$ and returns toward $-1$. This reflects the physical fact that the SFRD declines at $z > 2$.

### 6.3 Testable Prediction

**The LRT model predicts:** $w(z)$ at $z > 2.5$ is *less phantom* than CPL extrapolation — specifically, $|1 + w(z)|$ decreases at $z \gtrsim 2$ and $w \to -1$ by $z \sim 5$.

**Current observational reach:** DESI BAO primarily constrains $w(z)$ at $z < 2.1$ (from galaxy, quasar, and Ly-$\alpha$ forest tracers). At $z > 2$, constraints weaken substantially. Future surveys may discriminate:

- **Euclid** (2024–2030): galaxy clustering and weak lensing to $z \sim 2$; combined with CMB lensing, may probe $z \sim 3$
- **Roman Space Telescope** (late 2020s): SN Ia to $z \sim 2.5$
- **LSST/Rubin** (2025+): photometric BAO and SN Ia, extending redshift coverage
- **CMB-S4 + DESI full dataset**: cross-correlations may probe $w(z)$ at $z \sim 3$–$5$ indirectly

The definitive test requires measuring $w(z)$ at $z > 2.5$ with $\sigma_w \lesssim 0.2$ precision — challenging but within reach of combined next-generation datasets.

---

## 7. Magnitude Estimate: Is $\varepsilon \sim 0.3$ Physical?

### 7.1 The Amplitude Question

The free parameters $\alpha$ and $\beta$ encode unknown LRT microphysics — specifically, the energy per actualization residue unit and the efficiency of BH deactualization. Can the required amplitudes ($\alpha \sim 0.4$, $\beta \sim 0.1$) be justified physically?

### 7.2 Order-of-Magnitude Estimate

From 300-LRT-COSMOLOGY §3.1.1, the cosmic actualization rate from stars alone is:

$$\dot{N}_A \sim 10^{62} \text{ events/s} \quad (\text{present epoch})$$

Let $\varepsilon_{\text{res}}$ be the energy per residue actualization event. The residue energy injection rate is:

$$\Gamma_{\text{em}} = (1 - f_{\text{int}}) \cdot \dot{N}_A \cdot \varepsilon_{\text{res}} / V_{\text{obs}}$$

where $V_{\text{obs}} \approx 4 \times 10^{80}$ m³ is the comoving observable volume and $f_{\text{int}}$ is the interaction fraction.

The characteristic scale for $\varepsilon(z)$ is:

$$\varepsilon \sim \frac{\Gamma_{\text{em}}}{3 H_0 \rho_\Lambda} = \frac{(1-f_{\text{int}}) \cdot \dot{N}_A \cdot \varepsilon_{\text{res}}}{3 H_0 \rho_\Lambda V_{\text{obs}}}$$

With $3 H_0 \rho_\Lambda \approx 4 \times 10^{-27}$ J m⁻³ s⁻¹:

$$\varepsilon \sim \frac{(1 - f_{\text{int}}) \cdot 10^{62} \cdot \varepsilon_{\text{res}}}{4 \times 10^{-27} \times 4 \times 10^{80}} \approx (1-f_{\text{int}}) \cdot \varepsilon_{\text{res}} \cdot 6 \times 10^{7} \text{ J}^{-1}$$

For $\varepsilon \sim 0.1$–$0.4$:

$$\varepsilon_{\text{res}} \sim \frac{0.1}{(1-f_{\text{int}}) \cdot 6 \times 10^7} \approx \frac{10^{-9}}{1-f_{\text{int}}} \text{ J}$$

If $f_{\text{int}} \approx 0.999$ (only 0.1% of actualization events produce residue):

$$\varepsilon_{\text{res}} \sim 10^{-6} \text{ J} \approx 6 \text{ TeV per event}$$

If $f_{\text{int}} \approx 0.9$ (10% residue):

$$\varepsilon_{\text{res}} \sim 10^{-8} \text{ J} \approx 60 \text{ GeV per event}$$

### 7.3 Assessment

The required energy per residue event falls in the range $\sim 10$–$10^4$ GeV, depending on the interaction fraction. This is:
- **Below the Planck scale** ($10^{19}$ GeV) by many orders of magnitude
- **At or above the electroweak scale** ($\sim 100$ GeV)
- **Comparable to** the energy scale of individual nuclear processes ($\sim$ MeV–GeV) if the interaction fraction is high

**Verdict:** The required amplitude is not ruled out on energetic grounds, but it is a free parameter. LRT does not predict $\varepsilon_{\text{res}}$ from first principles. An independent derivation of the residue energy scale from the actualization operator formalism would significantly strengthen the model.

---

## 8. Model Limitations and Honest Uncertainties

### 8.1 What Is Constrained

1. **Shape of $w(z)$:** Determined by known astrophysics (SFRD from Madau–Dickinson 2014; BH mass assembly from Soltan argument / AGN surveys). This is the model's strongest feature — the $z$-dependence is not arbitrary but tracks measured cosmic history.

2. **Qualitative behavior:** The phantom crossing near $z \sim 0.5$–$0.7$ and the turnaround at $z \sim 2$ are robust features for any $\alpha, \beta > 0$ with $\alpha > \beta$.

3. **Asymptotic return to $w = -1$:** Guaranteed by the decline of both SFRD and BH formation at high $z$. This is physically motivated and distinguishes LRT from CPL.

### 8.2 What Is Not Constrained

1. **Overall amplitude ($\alpha, \beta$):** These absorb all unknown microphysics (residue energy, interaction fraction, deactualization efficiency). The model is predictive in *shape* but not in *amplitude*.

2. **BH assembly parameterization:** The sigmoid $f_{\text{BH}}(z)$ is a simplified model. Real BH mass assembly depends on merger trees, accretion modes, and seed populations. The qualitative behavior (low at high $z$, growing to present) is robust; the exact shape has $\sim 30\%$ uncertainty.

3. **Non-stellar emission at high $z$:** Early universe actualization from BBN, reionization, and other pre-stellar processes is not captured by the SFRD proxy. Including these would enhance the phantom signal at $z > 6$.

4. **Backreaction:** The model treats $\rho_\Lambda$ as approximately constant when computing $H(z)$. If $\rho_\Lambda$ evolves significantly (large $\varepsilon$), the expansion history itself changes, requiring self-consistent numerical solution. For $|\varepsilon| \lesssim 0.3$, this is a $\sim 10\%$ correction.

5. **Physical nature of residue:** The model does not specify what actualization residue *is* in field-theoretic terms. It could be a new sector, a modification of vacuum energy, or something without standard-model analogue. This is the deepest open question (cf. OPN-COSM-004).

### 8.3 Potential Failure Modes

- If future data show $w(z)$ continuing to deepen into phantom territory at $z > 3$ (rather than turning around), the LRT toy model is falsified in its current form
- If $w(z)$ shows no correlation with star formation history (e.g., $w$ evolution in voids vs. overdense regions is identical), the emission-source mechanism is disfavored
- If $w_0 = -1.000 \pm 0.01$ with no evolution — pure $\Lambda$CDM survives, and the source term $S(z)$ is either zero or negligibly small

---

## 9. Summary

### 9.1 The Model in One Equation

$$w(z) = -1 + \frac{\alpha\,f_{\text{BH}}(z) - \beta\,\hat{\psi}_{\text{MD}}(z)}{\sqrt{\Omega_m(1+z)^3 + \Omega_\Lambda}}$$

with $\hat{\psi}_{\text{MD}}(z)$ from Madau & Dickinson (2014), $f_{\text{BH}}(z) = [1 + (z/1.5)^2]^{-1}$ from BH assembly observations, and two free amplitudes $(\alpha, \beta)$ encoding LRT microphysics.

### 9.2 What LRT Predicts That $\Lambda$CDM Does Not

1. **$w(z) \neq -1$:** The emission-absorption imbalance produces redshift-dependent deviations
2. **Phantom crossing at $z \sim 0.5$–$0.7$:** Natural consequence of BH absorption catching up to declining star formation
3. **Non-monotonic $w(z)$:** Maximum phantom deviation at $z \sim 1.5$–$2$ (peak SFRD), returning to $w = -1$ at $z \gg 3$
4. **Correlation with astrophysical history:** $w(z)$ evolution is tied to star formation and BH growth — testable via cross-correlation

### 9.3 What Is Needed Next

- **Self-consistent numerical solution** incorporating $\rho_\Lambda(z)$ backreaction on $H(z)$
- **Fit to DESI + Planck + SN data** to constrain $\alpha$ and $\beta$ (or their physical counterparts)
- **Derivation of $\varepsilon_{\text{res}}$** from the actualization operator formalism — would eliminate a free parameter
- **Environment-dependent test:** If dark energy density correlates with local matter density (galaxy clusters vs. voids), this would be strong evidence for the emission-source picture

---

## References

- Madau, P. & Dickinson, M. (2014). Cosmic star-formation history. *Annual Review of Astronomy and Astrophysics*, 52, 415–486. arXiv:1403.0007
- DESI Collaboration (2024). DESI 2024 VI: Cosmological constraints from BAO measurements. arXiv:2404.03002
- Soltan, A. (1982). Masses of quasars. *Monthly Notices of the Royal Astronomical Society*, 200, 115–122.
- Shankar, F., Weinberg, D. H., & Miralda-Escudé, J. (2009). Self-consistent models of the AGN and black hole populations. *Astrophysical Journal*, 690, 20–41.
- Aird, J. et al. (2015). The evolution of the X-ray luminosity function of AGN. *Monthly Notices of the Royal Astronomical Society*, 451, 1892–1927.
- Yu, Q. & Tremaine, S. (2002). Observational constraints on growth of massive black holes. *Monthly Notices of the Royal Astronomical Society*, 335, 965–976.
- Kormendy, J. & Ho, L. C. (2013). Coevolution of supermassive black holes and host galaxies. *Annual Review of Astronomy and Astrophysics*, 51, 511–653.
- Longmire, J. (2026). *LRT Cosmology: Speculative Extensions* (300-LRT-COSMOLOGY).
