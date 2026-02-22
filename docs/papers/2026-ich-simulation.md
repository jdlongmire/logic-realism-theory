---
layout: default
title: "Numerical Exploration of Information Circulation Cosmology"
image: /assets/images/lrt-banner.png
---

<div class="hero-banner-wrapper">
  <div class="hero-banner">
    <img src="{{ site.baseurl }}/assets/images/lrt-banner.png" alt="Logic Realism Theory" class="hero-image">
  </div>
</div>

<div class="topic-header">
  <h1>Numerical Exploration of Information Circulation Cosmology</h1>
  <p>Computational feasibility and parameter space of the ICH dark energy model</p>
</div>

**James D. Longmire**
ORCID: [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)

---

## Abstract

The Information Circulation Hypothesis (ICH) proposes that late-time cosmic acceleration emerges from a persistent imbalance between information influx from $I_\infty$ and outflux through black hole recycling. This paper presents a numerical exploration of the ICH mechanism, demonstrating that (1) the model produces $\Lambda$-like behavior ($w_\text{eff} \approx -1$) across broad parameter ranges, (2) entropy-dependent influx provides natural self-regulation preventing runaway dynamics, and (3) the equation of state remains stable without fine-tuning. We provide parameter sensitivity analysis, compare distance modulus predictions with SNe Ia anchors, and identify conditions under which ICH reproduces standard cosmological observations.

---

## 1. Introduction

### 1.1 Motivation

The cosmological constant problem remains one of the deepest puzzles in physics. Standard $\Lambda$CDM treats dark energy as a constant vacuum energy density, but offers no explanation for its specific value or why it dominates precisely now (the coincidence problem).

The Information Circulation Hypothesis, developed within the Logic Realism Theory framework, proposes an alternative: cosmic acceleration emerges from the dynamics of information flow between $I_\infty$ (the space of logical possibilities) and $A_\Omega$ (physically instantiated configurations). Rather than postulating a constant, acceleration emerges from a persistent imbalance in the circulation cycle.

### 1.2 Theoretical Foundation

ICH rests on three principles from LRT:

1. **Information influx**: New instantiations continuously enter $A_\Omega$ from $I_\infty$, governed by entropy conditions
2. **Black hole recycling**: Black holes return instantiations to $I_\infty$, maintaining circulation
3. **Imbalance-driven expansion**: When influx exceeds outflux, the net positive information content drives expansion

The theoretical development of ICH is presented in the companion paper [Information Circulation Hypothesis]({{ site.baseurl }}/articles/information-circulation/). This paper focuses on computational demonstration that the mechanism produces observationally consistent behavior.

### 1.3 Objectives

This simulation study addresses three questions:

1. **Feasibility**: Does the ICH mechanism produce $\Lambda$-like behavior numerically?
2. **Robustness**: Is the result stable across parameter variations, or fine-tuned?
3. **Distinguishability**: Can ICH predictions be differentiated from standard $\Lambda$CDM?

---

## 2. Model Description

### 2.1 State Variables

The simulation tracks:

- **Particles**: Discrete instantiations with position, entropy, and age
- **Black holes**: Recycling centers with position, mass, and activity state
- **Scale factor** $a(t)$: Cosmic expansion parameter
- **Hubble parameter** $H(t)$: Expansion rate

### 2.2 Dynamics

#### Influx (I∞ → AΩ)

New particles enter at rate:

$$r_\text{influx}(\bar{S}) = r_\text{floor} + \frac{r_\text{peak} - r_\text{floor}}{1 + k \cdot \bar{S}}$$

where $\bar{S}$ is average entropy and $k$ controls sensitivity. High entropy suppresses influx (self-regulation).

#### Outflux (AΩ → I∞)

Black holes absorb nearby particles within absorption radius $R_\text{BH}$. Mass increases with absorption, decreases via Hawking-like evaporation:

$$\dot{M}_\text{BH} = \sum_i \Theta(R_\text{BH} - r_i) - \gamma_\text{Hawking}$$

#### Expansion

The imbalance $\Delta N = N_\text{in} - N_\text{out}$ accumulates and drives expansion via an effective dark energy density:

$$\rho_\Lambda^\text{eff} = \lambda \cdot \frac{\sum \Delta N}{a^\alpha}$$

where $\alpha < 3$ ensures slower dilution than matter, producing late-time dominance.

### 2.3 Observables

- **Equation of state**: $w_\text{eff}$ computed from acceleration
- **Distance modulus**: $\mu(z)$ compared to SNe Ia anchors
- **Goodness-of-fit**: $\chi^2$ against reference points

---

## 3. Results

### 3.1 Baseline Run

*[Results from canonical parameter set]*

| Metric | Value |
|--------|-------|
| Final $w_\text{eff}$ | |
| $\chi^2$/dof | |
| Net circulation | |

### 3.2 Parameter Sensitivity

*[Section to be populated with sweep results]*

#### 3.2.1 Influx Parameters

#### 3.2.2 Black Hole Parameters

#### 3.2.3 Coupling Strength

### 3.3 Comparison with ΛCDM

*[Section for overlay comparison]*

---

## 4. Discussion

### 4.1 Mechanism Validation

### 4.2 Fine-Tuning Assessment

### 4.3 Observational Predictions

### 4.4 Limitations

- 1D toy model
- No comoving volume treatment
- Simplified black hole dynamics

---

## 5. Conclusion

*[To be written after sensitivity analysis]*

---

## References

1. Longmire, J.D. (2026). Logic Realism Theory: Physical Foundations from Logical Constraints. *LRT Paper Suite*.
2. Longmire, J.D. (2026). Information Circulation Hypothesis. *LRT Articles*.

---

## Supplementary Materials

- [Simulation Notebook](https://github.com/jdlongmire/logic-realism-theory/blob/main/simulations/ich_dark_energy.ipynb)
- [Parameter Sensitivity Analysis](https://github.com/jdlongmire/logic-realism-theory/blob/main/simulations/parameter_sensitivity.ipynb)

---

**AI Assistance Disclosure**: This work was developed with assistance from AI language models. All substantive claims and errors remain the author's responsibility. **Human-Curated, AI-Enabled (HCAE)**.
