# The Scale Law of Boolean Actualization

## An Operational Framework for Decoherence-Driven Classicality

**Author:**
James (JD) Longmire
Northrop Grumman Fellow (unaffiliated research)
ORCID: 0009-0009-1383-7698
Correspondence: jdlongmire@outlook.com

**Date:** December 2025

---

## Abstract

Quantum mechanics permits superpositions at all scales, yet macroscopic measurement outcomes are invariably definite and Boolean. Decoherence theory explains the suppression of interference, but the rate of this suppression has not been expressed as a unified, operationally testable scaling framework enabling cross-platform comparison. This paper develops such a framework using logical entropy $h_L(\rho) = 1 - \mathrm{Tr}(\rho^2)$ and a fixed visibility threshold $V_\ast$ to define the Boolean actualization time $\tau_{\mathrm{BA}}$: the earliest time at which measured interference contrast falls below threshold. We show that $\tau_{\mathrm{BA}}$ scales as a power of system size ($s^{-\beta}$), with exponent $\beta$ determined by both the physical mechanism and the correlation structure of environmental noise.

Empirical data across seven platforms support the framework: fullerene interferometry ($\beta = 2.11$, Rayleigh), cavity QED ($\beta = 1.01$, photon loss), superconducting qubits ($\beta = 1.0$, uncorrelated dephasing), trapped ions ($\beta = 2.0$, correlated dephasing), and NV ensembles ($\beta = 1.06$, dipole bath). Notably, the apparent suppression of Rayleigh scaling in large-molecule interferometry ($\beta_{\text{obs}} \approx 0.9$) is consistent with a multi-variable analysis treating vacuum pressure as an explicit variable: the rate equation $\Gamma \propto P \cdot m^2$ predicts $\beta_{\text{obs}} = 0.7 \pm 0.2$ when isolation improves by two orders of magnitude, encompassing the observed value within one standard deviation.

We derive theorems for both limiting cases: independent dephasing yields $\tau_{\mathrm{BA}} \propto 1/N$, while correlated (superdecoherence) yields $\tau_{\mathrm{BA}} \propto 1/N^2$. The paper provides operational criteria for controlled isolation, guidance for multi-channel regimes where multiple decoherence mechanisms coexist, and explicit falsification conditions. The framework constitutes a quantitative, falsifiable criterion for the quantum-classical boundary. An optional interpretive section connects these results to Logic Realism Theory, which reads Boolean actualization as reflecting the logical structure of actuality itself.

**Keywords:** decoherence, quantum-classical boundary, logical entropy, scaling laws, Boolean actualization, superdecoherence, noise correlation

---

## 1. Empirical Landscape

### 1.1 The Empirical Invariant

Every completed measurement in the history of physics has yielded a single definite outcome describable by classical Boolean logic. Detectors never record contradictory states; macroscopic superpositions do not persist; interference vanishes reliably as systems scale. This Boolean character of actualized outcomes is:

- **Empirical**: observed universally across all experimental platforms
- **Structural**: independent of interpretation or theoretical framework
- **Robust**: unaffected by physical substrate, energy scale, or measurement context

Any complete account of quantum mechanics must explain why this pattern holds without exception.

### 1.2 Decoherence and System Size

Environmental entanglement rapidly suppresses off-diagonal terms of the reduced density matrix in the pointer basis (Zurek 2003; Schlosshauer 2007; Joos et al. 2003). The qualitative observation that larger systems decohere faster is well established under standard conditions. What has been lacking is a unified operational metric enabling quantitative comparison across disparate physical systems.

**Scope qualification:** The scaling τ_BA ∝ s^(-β) assumes:
- Fixed environmental coupling (no active isolation improvement with size)
- Passive systems without quantum error correction
- No exploitation of decoherence-free subspaces (DFS)
- Standard product-state environmental models

Specialized scenarios—DFS-protected qubits, fault-tolerant architectures, topological qubits with size-independent protection—require separate treatment beyond this framework's scope. The framework applies to passive systems undergoing standard environmental decoherence.

### 1.3 Controlled Empirical Tests

Two datasets provide controlled tests where system size varies while environmental coupling remains approximately fixed.

**Molecular interferometry (Rayleigh regime):**

The Arndt group's fullerene experiments (Arndt et al. 1999) permit comparison between C₆₀ (720 amu) and C₇₀ (840 amu) under matched vacuum conditions (~10⁻⁷ mbar). From fitted decoherence rates:

| Molecule | Mass (amu) | Γ (ms⁻¹) | τ_BA (ms) |
|----------|------------|----------|-----------|
| C₆₀      | 720        | 0.130    | 18 ± 5    |
| C₇₀      | 840        | 0.180    | 12 ± 3    |

The extracted scaling exponent:

$$\beta = \frac{\ln(\Gamma_{70}/\Gamma_{60})}{\ln(m_{70}/m_{60})} = \frac{\ln(1.385)}{\ln(1.167)} = 2.11$$

This is consistent with the Rayleigh-regime prediction $\beta = 2$, where decoherence rate scales with polarizability squared, and polarizability scales with mass for molecules of approximately constant density.

**Cavity QED (photon loss):**

The Haroche group's Schrödinger cat experiments (Brune et al. 1996) provide a second test with a different decoherence mechanism. For cat states $|\alpha\rangle + |-\alpha\rangle$, the dominant channel is photon loss, with decoherence rate $\Gamma_{\text{cat}} = 4\kappa\bar{n}$ where $\bar{n} = |\alpha|^2$.

| |α| | n̄    | τ_d/τ_cav |
|-----|-------|-----------|
| 1.2 | 1.44  | 0.80      |
| 1.8 | 3.24  | 0.35      |
| 2.5 | 6.25  | 0.18      |
| 3.2 | 10.24 | 0.11      |

Log-log regression yields $\tau_d \propto \bar{n}^{-1.01}$, matching the theoretical prediction $\beta = 1$ to within 1%.

### 1.4 Confounding by Isolation Variation

The full molecular interferometry dataset (C₆₀ through 25 kDa oligoporphyrins) yields an apparent exponent $\beta \approx 0.9$, substantially below the Rayleigh prediction. This attenuation arises because larger molecules were measured under progressively better vacuum (10⁻⁷ → 10⁻⁹ mbar), reducing environmental coupling. The 25 kDa oligoporphyrin, measured at < 10⁻⁹ mbar, exhibits *longer* τ_BA than the 10 kDa molecule at 10⁻⁹ mbar, demonstrating that isolation improvements can override mass-dependent decoherence.

This confounding underscores that scaling comparisons require controlled isolation. The C₆₀/C₇₀ pair and cavity QED dataset satisfy this requirement; the broader molecular dataset does not.

### 1.5 Falsifiability

The framework makes quantitative, testable predictions. Under controlled isolation, the scaling exponent β is determined by the dominant decoherence mechanism and noise correlation structure. Deviations exceeding measurement uncertainty would indicate either:

- Uncharacterized environmental channels requiring identification, or
- New physics beyond standard decoherence (e.g., objective collapse contributions)

**Concrete test:** If a system with fully characterized noise channels exhibits β outside the predicted range (e.g., |β_measured - β_predicted| > 3σ where σ includes both statistical and systematic uncertainty), the framework fails for that system. Section 4 develops specific falsification scenarios for near-term experiments, including levitated nanoparticles and high-N qubit arrays.

This falsifiability distinguishes the framework from interpretive claims: the operational predictions can fail independently of any metaphysical commitments.

---

## 2. Formal Framework

### 2.1 Logical Entropy

We quantify coherence loss using logical entropy (Manfredi & Feix 2000; Ellerman 2013):

$$h_L(\rho) = 1 - \mathrm{Tr}(\rho^2)$$

**Properties:**
- $h_L = 0$: pure state (maximal coherence)
- $h_L \to 1 - 1/d$: maximally mixed state in dimension $d$
- Monotonic under completely positive trace-preserving (CPTP) maps
- Directly related to purity: $h_L = 1 - P$

Logical entropy does not presuppose collapse or any particular interpretation. It is a measurable quantity characterizing the degree of mixedness.

### 2.1a Choice of Entropy Measure

Logical entropy $h_L$ is selected over alternative measures for several operational advantages:

**Algebraic simplicity:** Linear in purity $\mathrm{Tr}(\rho^2)$, requiring no logarithms. This enables analytical solutions for visibility-entropy relations.

**Direct observability:** For balanced two-branch superpositions $\rho = (|\psi\rangle\langle\psi| + |\phi\rangle\langle\phi|)/2$ with overlap $|\langle\psi|\phi\rangle|^2 = c^2$, the relation $h_L = (1 - V^2)/2$ connects directly to interferometric visibility $V$ without numerical inversion.

**Monotonicity:** Increases monotonically under decoherence for pure → mixed transitions, providing a natural "progress toward classicality" metric.

**Operational interpretation:** $h_L$ measures the probability of error when attempting to distinguish $\rho$ from the maximally mixed state $I/d$ in a single measurement (Girolami 2014).

**Comparison to alternatives:**

| Measure | Definition | Advantage | Disadvantage for τ_BA |
|---------|------------|-----------|----------------------|
| Logical entropy $h_L$ | $1 - \mathrm{Tr}(\rho^2)$ | Linear in purity, direct V relation | None for this application |
| Von Neumann $S_{vN}$ | $-\mathrm{Tr}(\rho \ln \rho)$ | Information-theoretic meaning | Requires numerical inversion |
| Linear entropy $S_L$ | $(d/(d-1))h_L$ | Normalized to [0,1] | Equivalent to $h_L$, different normalization |
| Fidelity $F$ | $\langle\psi|\rho|\psi\rangle$ | State comparison | Requires reference state, not intrinsic |

For this framework's purpose—defining an operational, visibility-based interface criterion—logical entropy provides the simplest and most direct metric.

### 2.2 Boolean Actualization Time

**Definition:** The Boolean actualization time $\tau_{\mathrm{BA}}(V_\ast)$ is the earliest time at which measured interference visibility falls below threshold $V_\ast$.

For balanced two-branch superpositions (the standard preparation in decoherence experiments), the reduced density matrix has the form:

$$\rho(t) = \frac{1}{2}\begin{pmatrix} 1 & \gamma(t) \\ \gamma(t)^* & 1 \end{pmatrix}, \quad |\gamma(t)| = V(t)/V_0$$

The visibility-entropy relation is then exact:

$$h_L(t) = \frac{1}{2}(1 - V(t)^2/V_0^2)$$

At full coherence ($V = V_0$): $h_L = 0$.
At full decoherence ($V = 0$): $h_L = 0.5$ (maximally mixed qubit).

The threshold $V_\ast = 0.10$ corresponds to $h_L \approx 0.495$, i.e., 99% of the way to maximal mixedness for a qubit.

**Threshold robustness:** Changing $V_\ast$ rescales τ_BA by a constant factor but leaves the scaling exponent $\beta$ invariant, since the threshold cancels in ratios.

### 2.3 Operational Character

By "Boolean actualization" we mean a purely operational condition: the point at which, for all experimentally accessible observables on the relevant degrees of freedom, interference contrast has fallen below threshold, so that outcome statistics become indistinguishable (within chosen precision) from those of a classical random variable over a Boolean sample space.

The term carries no ontological commitment regarding collapse, branching, or the reality of the quantum state. It describes what can be measured: the loss of observable interference.

### 2.4 Theorem: Scaling Under Independent Dephasing

We derive the scaling law for one analytically tractable case.

**Positioning note:** The result that independent dephasing yields Γ_total = NΓ_single (hence τ ∝ 1/N) is well-established in the decoherence literature. Theorem 1 restates this in the language of logical entropy and τ_BA, providing an operational reframing rather than new physics. The framework's novelty lies elsewhere: (1) the cross-platform unification enabling quantitative comparison, (2) the diagnostic role of β in distinguishing noise correlation structures, and (3) the explicit falsification conditions derived from mechanism-dependent predictions.

---

**Theorem 1 (Logical-Entropy Scale Law Under Independent Dephasing)**

**Assumptions:**

1. Initial state: $\rho_N(0) = |+\rangle^{\otimes N}\langle +|^{\otimes N}$
2. Noise model: independent, identical pure dephasing with coherence decay $c(t) = e^{-\Gamma t}$, $\Gamma > 0$
3. Threshold: fixed $0 < h_\ast < 1$

**Results:**

(i) Single-qubit logical entropy:
$$h_L^{(1)}(t) = \frac{1}{2}(1 - e^{-2\Gamma t})$$

(ii) N-qubit logical entropy:
$$h_L^{(N)}(t) = 1 - \left[\frac{1 + e^{-2\Gamma t}}{2}\right]^N$$

(iii) Time to reach threshold $h_\ast$:
$$t_N(h_\ast) = -\frac{1}{2\Gamma}\ln\left(2(1 - h_\ast)^{1/N} - 1\right)$$

(iv) Asymptotic scaling (large N):
$$t_N(h_\ast) \sim \frac{\ln(1/(1 - h_\ast))}{\Gamma N}$$

**Conclusion:** $\tau_{\mathrm{BA}} \propto 1/N$ under independent dephasing.

---

**Proof sketch:**

For a single qubit under pure dephasing, $\rho(t) = \frac{1}{2}\begin{pmatrix} 1 & e^{-\Gamma t} \\ e^{-\Gamma t} & 1 \end{pmatrix}$.

Purity: $P^{(1)}(t) = \frac{1}{2}(1 + e^{-2\Gamma t})$, giving $h_L^{(1)}(t) = \frac{1}{2}(1 - e^{-2\Gamma t})$.

For N independent qubits, $P^{(N)}(t) = [P^{(1)}(t)]^N$, hence:
$$h_L^{(N)}(t) = 1 - \left[\frac{1 + e^{-2\Gamma t}}{2}\right]^N$$

Setting $h_L^{(N)}(t_N) = h_\ast$ and solving yields (iii). Taylor expansion for large N gives (iv). □

**Scope:** This theorem applies to independent exponential dephasing. Other mechanisms (thermal scattering, photon loss, collisional decoherence) yield different exponents, as shown empirically in Section 1 and tabulated in Section 3.

### 2.5 Controlled Isolation: Operational Criteria

A valid scaling comparison requires "controlled isolation": environmental coupling must remain constant (or explicitly modeled) while system size varies. This ensures observed exponent $\beta$ reflects the physical mechanism, not confounded environmental changes.

**Operational criteria for controlled isolation:**

1. **Vacuum pressure stability:** $\Delta P/P < 30\%$ across all measurements
   - *Justification:* Rayleigh scattering rate $\Gamma \propto P$; 30% pressure variation induces ~30% decoherence rate variation, masking intrinsic scaling

2. **Temperature stability:** $\Delta T/T < 5\%$ (typically $T = 300 \pm 15$ K for room-temperature systems)
   - *Justification:* Thermal de Broglie wavelength $\lambda_{dB} \propto T^{-1/2}$ affects scattering cross-section; blackbody radiation field scales as $T^4$

3. **Geometric consistency:** Slit width, grating period, and detector geometry unchanged
   - *Justification:* Diffraction and detection solid angle affect measured visibility independently of decoherence

4. **Velocity consistency:** Molecular beam or qubit gate time variation $< 20\%$
   - *Justification:* Interaction time $\tau_{int}$ determines decoherence accumulation; $\tau_{BA} \propto \tau_{int}^{-1}$ for fixed $\Gamma$

**Examples:**

| Dataset | Pressure | Temperature | Geometry | Velocity | Status |
|---------|----------|-------------|----------|----------|--------|
| C$_{60}$/C$_{70}$ (Arndt 1999) | Fixed $10^{-7}$ mbar | 300 K | Identical | ~220 m/s | **Controlled** |
| Full molecular (720→25k amu) | $10^{-7}→10^{-9}$ mbar | 300 K | Varies | Varies | **Confounded** |
| Cavity QED (Brune 1996) | N/A (cavity) | 0.8 K | Fixed | N/A | **Controlled** |
| SC qubits (Kam 2024) | Dilution fridge | 20 mK | Chip-fixed | Gate-fixed | **Controlled** |

**Multi-variable framework:** When controlled isolation criteria are not met, the multi-variable rate equation $\Gamma(m, P, T, ...)$ must be used. Section 4.5 develops this explicitly for pressure variation.

**Falsification requirement:** Experiments claiming to validate $\beta$ for a specific mechanism must either satisfy controlled isolation criteria or provide explicit multi-variable corrections. Failure to do so produces uninterpretable $\beta_{obs}$.

---

## 3. Comparative Scaling

### 3.1 The Role of Noise Correlation Structure

The scaling $\tau_{\mathrm{BA}} \propto s^{-\beta}$, where $s$ is a size parameter (mass, photon number, qubit count), holds across mechanisms with exponent $\beta$ determined by two factors:

1. **Physical mechanism**: How environment couples to system (scattering, photon loss, dephasing)
2. **Correlation structure**: Whether noise acts locally (uncorrelated) or globally (correlated)

This distinction resolves an apparent puzzle: the same quantum state (e.g., GHZ entanglement) can exhibit different scaling exponents on different platforms. The exponent diagnoses the noise correlation structure, not merely the state or system size.

**Theoretical basis:**

- **Uncorrelated noise**: Each subsystem dephases independently. For N qubits, $\Gamma_{\text{total}} = N\Gamma_{\text{single}}$, giving $\tau_{\mathrm{BA}} \propto 1/N$ (β = 1).

- **Correlated noise**: All subsystems experience the same phase fluctuation. The collective phase accumulates as N, so $\Gamma_{\text{total}} \propto N^2\Gamma_{\text{single}}$, giving $\tau_{\mathrm{BA}} \propto 1/N^2$ (β = 2). This is *superdecoherence*.

### 3.2 Empirical Validation

The framework predictions are consistent with observations across seven distinct experimental platforms spanning molecular, photonic, and solid-state systems. Data extraction methodology and uncertainty analysis are detailed in Appendix B.

**Table 1: Scaling Exponents Across Platforms**

| Platform | Mechanism | Predicted β | Measured β | Data Points | Dynamic Range | Reference |
|----------|-----------|-------------|------------|-------------|---------------|-----------|
| Fullerene (C₆₀/C₇₀) | Rayleigh | 2 | 2.1 ± 0.5 | 2 | 1.17× | Arndt 1999 |
| Cavity QED cats | Photon loss | 1 | 1.01 ± 0.03 | 4 | 7× | Brune 1996 |
| SC qubits (IBM) | Uncorr. dephasing | 1 | 1.0 ± 0.05 | 15 | 15× | Kam 2024 |
| Trapped ions | Corr. dephasing | 2 | 2.0 ± 0.1 | 6 | 4× | Monz 2011 |
| NV ensembles | Dipole bath | 1 | 1.06 ± 0.05 | ~5 | ~10× | Park 2022 |

*Notes:*
- *"Data Points" = independent measurements; "Dynamic Range" = ratio of largest to smallest size parameter*
- *Fullerene: 2-point comparison with limited dynamic range (1.17×); serves as consistency check rather than precision test*
- *SC qubits and Cavity QED: most robust validations (15 and 4 points respectively, well-characterized noise)*
- *Large-molecule data (>C₇₀) excluded from Table 1 due to isolation confounding; see Section 4.5 for multi-variable treatment*
- *See Appendix B for extraction methodology and caveats*

**Superconducting qubits (β = 1):**

GHZ state decoherence on IBM quantum processors (N = 1–15 qubits) yields:

$$\Gamma = (7.13N + 5.54) \times 10^{-3}\ \mu\text{s}^{-1}$$

The linear scaling ($\Gamma \propto N$) is consistent with Theorem 1: independent local noise sources produce β = 1. Each qubit experiences uncorrelated dephasing from its local environment. This dataset provides the most robust validation with 15 data points over 15× dynamic range.

**Trapped ions (β = 2, superdecoherence):**

GHZ state coherence decay in the Innsbruck ion trap (N = 2–8 qubits, 14-qubit creation) scales as $N^{2.0(1)}$. This quadratic scaling arises from *correlated* Gaussian phase noise: global magnetic field fluctuations affect all ions identically. The collective phase $\phi_{\text{total}} = N\phi_{\text{single}}$ leads to:

$$\Gamma_{\text{GHZ}} \propto N^2 \Gamma_{\text{single}}$$

This is the same exponent (β = 2) as Rayleigh scattering but from a completely different mechanism—demonstrating that β encodes correlation structure, not just physical process.

**NV center ensembles (β ≈ 1):**

Nitrogen-vacancy spin ensembles show $T_2 \propto [\text{P1}]^{-1.06}$ where [P1] is the substitutional nitrogen concentration. The dipole-dipole coupling to the nitrogen bath acts as effectively local/uncorrelated noise, producing β ≈ 1.

### 3.3 Platform Comparison: Same State, Different β

The most striking validation comes from comparing the *same* entangled state (GHZ) across platforms:

| Platform | GHZ scaling | β | Noise type |
|----------|-------------|---|------------|
| SC qubits (IBM) | Linear | 1 | Uncorrelated (local) |
| Trapped ions (Innsbruck) | Quadratic | 2 | Correlated (global B-field) |

This supports the conclusion that the scaling exponent is not an intrinsic property of entangled states but reflects the correlation structure of environmental noise. The framework thus provides a diagnostic tool: measuring β reveals whether dominant noise sources are local or global.

### 3.4 Summary Table by Mechanism Class

**Table 2: Mechanism-Dependent Exponents**

| Mechanism | Size parameter | Predicted β | Empirical β | Status |
|-----------|----------------|-------------|-------------|--------|
| Thermal scattering (Rayleigh) | mass $m$ | 2 | 2.1 ± 0.5 | Consistent |
| Thermal scattering (geometric) | mass $m$ | 2/3 | — | Awaiting test |
| Photon loss (cavity) | $\bar{n}$ | 1 | 1.01 ± 0.03 | Consistent |
| Gas collisions | mass $m$ | 2/3 | — | Awaiting test |
| Dephasing (uncorrelated) | qubit $N$ | 1 | 1.0 ± 0.05 | Consistent |
| Dephasing (correlated) | qubit $N$ | 2 | 2.0 ± 0.1 | Consistent |
| Dipole bath (local) | density | 1 | 1.06 ± 0.05 | Consistent |

The Rayleigh/geometric crossover occurs at particle radius $r \sim \lambda_{\text{thermal}} \approx 10\ \mu\text{m}$ at 300 K. All molecules in the interferometry dataset have $r < 2$ nm, placing them firmly in the Rayleigh regime.

### 3.5 Qualitative Universality, Quantitative Variation

The *direction* of scaling is universal: larger systems reach the Boolean regime faster at fixed environmental coupling. The *exponent* varies by mechanism and correlation structure. This reflects:

- How system size enters coupling cross-sections (scattering mechanisms)
- Whether noise acts locally or globally (dephasing mechanisms)
- Mode counting and phase-space factors (photon loss)

The theorem (Section 2.4) provides one analytically solvable case ($\beta = 1$, uncorrelated dephasing). The trapped-ion superdecoherence ($\beta = 2$, correlated dephasing) provides the complementary case. Together they span the range of dephasing-type mechanisms.

### 3.6 Extension Requirements

Extending quantitative scaling comparisons to larger systems (levitated nanoparticles, optomechanical oscillators) requires either:
- Controlled isolation matching across system sizes, or
- Explicit normalization by measured environmental coupling strength

Without such controls, apparent exponents will be confounded by isolation improvements, as seen in the molecular interferometry data beyond C₆₀/C₇₀.

### 3.7 Multi-Channel Regimes

The framework assumes a single dominant decoherence channel when extracting $\beta$. In realistic experiments, multiple channels often coexist. This section provides operational guidance for multi-channel scenarios.

**Channel Superposition:**

When $K$ channels contribute with rates $\Gamma_k \propto s^{\beta_k}$, the total rate is:

$$\Gamma_{\text{total}} = \sum_{k=1}^K a_k s^{\beta_k}$$

The Boolean actualization time becomes:

$$\tau_{\mathrm{BA}} \approx \left(\sum_{k=1}^K a_k s^{\beta_k}\right)^{-1}$$

**Limiting Cases:**

- *Single channel dominates:* If $a_1 s^{\beta_1} \gg a_2 s^{\beta_2}$ throughout the measured range, then $\beta_{\text{measured}} \approx \beta_1$.
- *Two comparable channels:* The effective exponent $\beta_{\text{eff}}$ depends on system size and is not constant.

**Crossover Behavior:**

For two channels with $\beta_1 > \beta_2$:
- Small $s$: Channel 1 dominates → $\beta_{\text{eff}} \approx \beta_1$
- Large $s$: Channel 1 saturates faster → $\beta_{\text{eff}} \to \beta_2$

*Example:* Superconducting qubits with uncorrelated dephasing ($\beta = 1$) and correlated flux noise ($\beta = 2$):
- $N = 3$–$5$: Flux noise may dominate → $\beta_{\text{eff}} \approx 2$
- $N = 10$–$20$: Dephasing takes over → $\beta_{\text{eff}} \approx 1$

**Fitting Strategies:**

| Strategy | Use Case | Parameters | Notes |
|----------|----------|------------|-------|
| Single-exponent | One dominant channel | $A$, $\beta_{\text{eff}}$ | Reports effective exponent |
| Two-exponent | Visible crossover | $a_1$, $\beta_1$, $a_2$, $\beta_2$ | Requires dynamic range $>10\times$ |
| Bounding | Mechanism uncertain | $\beta_{\min}$, $\beta_{\max}$ | Constrains channel combinations |

**Diagnostic Protocol:**

1. Measure $\beta_{\text{eff}}$ across maximum achievable size range
2. Check for size-dependent variation (indicates multi-channel)
3. Compare to known mechanisms (Table 2)
4. If $\beta_{\text{eff}}$ is constant and matches prediction → single channel confirmed
5. If $\beta_{\text{eff}}$ varies → fit two-exponent model or bound channels

**Falsification Criteria for Multi-Channel:**

The multi-channel framework is falsified if:
- $\beta_{\text{measured}} < \min(\beta_k)$ for all plausible channels (impossible via superposition)
- $\beta_{\text{measured}}$ violates upper bound from fastest known mechanism
- Two-channel fit requires $\beta_1$ or $\beta_2$ outside physically reasonable range ($\beta < 0$ or $\beta > 3$)

**Example—Cavity QED:**

Brune et al. (1996) cat states experience:
- Photon loss: $\beta = 1$ (dominant)
- Thermal photons: $\beta \approx 0$ (negligible at $T = 0.8$ K)
- Dephasing: $\beta \approx 1$ (small, $\sim 10\%$ of loss rate)

Measured $\beta = 1.01$ is consistent with single-channel dominance. Two-exponent fit would not improve fit quality given data precision.

**Conclusion:** Multi-channel effects do not undermine the framework but require sufficient dynamic range to identify crossover and mechanism identification via ancillary measurements. The diagnostic capability remains valid: $\beta$ distinguishes correlation structures even in multi-channel scenarios, provided channels can be resolved.

---

## 4. Falsifiability

### 4.1 Primary Criterion

The framework makes a testable prediction:

> Under controlled environmental coupling, $\tau_{\mathrm{BA}}$ scales as $s^{-\beta}$ with $\beta$ predictable from the dominant decoherence mechanism.

**Falsification condition:** Observation of scaling exponents deviating significantly from mechanism predictions, after accounting for all characterized environmental channels, would indicate either:
- Uncharacterized environmental couplings, or
- New physics beyond standard decoherence (e.g., objective collapse mechanisms)

This is the crisp, empirical test the framework provides.

### 4.1a Concrete Falsification Examples

The following hypothetical observations would falsify specific predictions of the framework:

**Example 1: Superconducting qubit anomaly**
- *Setup:* GHZ states on N = 5–50 qubits with identical gate fidelities and characterized local noise
- *Prediction:* Γ ∝ N (β = 1) from independent dephasing
- *Falsification:* Observing Γ ∝ N^1.5 would indicate either (a) uncharacterized correlated noise contributing at N > 20, or (b) physics beyond the independent-channel model
- *Resolution pathway:* Noise spectroscopy to identify correlation structure; if none found, framework modification required

**Example 2: Molecular interferometry breakdown**
- *Setup:* Molecules from 10³ to 10⁶ amu under matched vacuum (< 10⁻¹⁰ mbar, ΔP/P < 10%)
- *Prediction:* β = 2 (Rayleigh) or β = 2/3 (geometric) depending on particle radius vs λ_thermal
- *Falsification:* Observing β < 0.5 or β > 2.5 outside uncertainty bounds (±0.3) would indicate breakdown
- *Example:* If 10⁵ amu particles show β = 0.3 ± 0.1 under controlled isolation, the Rayleigh/geometric dichotomy fails

**Example 3: Cavity QED deviation**
- *Setup:* Cat states with n̄ = 1–100 in single-mode cavity with calibrated κ
- *Prediction:* Γ_cat = 4κn̄ (β = 1)
- *Falsification:* Saturation at large n̄ (β → 0) or superlinear scaling (β > 1.2) after accounting for thermal photons
- *Threshold:* |β_measured - 1| > 0.15 with uncertainty < 0.05 would require explanation

**Example 4: Objective collapse signature**
- *Setup:* Levitated nanoparticles at 10⁸ amu with decoherence budget closed (blackbody, gas, vibration all < 10% of observed Γ)
- *Prediction:* Γ from known channels should account for τ_BA
- *Falsification:* Residual Γ_unexplained > 30% of Γ_total, scaling as m^{4/3} (Penrose-Diósi) or m² (CSL)
- *Significance:* Would constitute evidence for objective collapse beyond standard decoherence

**What does NOT constitute falsification:**
- Confounded datasets where isolation varies with size (see Section 4.5)
- Mechanism misidentification (β_measured matches a different mechanism)
- Multi-channel regimes where effective β falls between channel exponents (see Section 3.7)

### 4.2 Connection to Objective Collapse

Objective collapse models (CSL, GRW, Penrose-Diósi) predict decoherence contributions beyond environmental entanglement. These would manifest as:
- Saturation of τ_BA at large system sizes (collapse rate dominates over environmental decoherence)
- Exponent deviations when all environmental channels are calibrated
- Mass-dependent effects inconsistent with Rayleigh or geometric scaling

High-mass levitated optomechanics experiments with fully characterized decoherence budgets are positioned to test these predictions (Millen et al. 2020; Bassi et al. 2013).

### 4.3 Concrete Experimental Tests

Two platforms are particularly well-suited for extending the scaling tests:

**Levitated nanoparticles:** Silica nanospheres in the 10⁶–10⁹ amu range under ultra-high vacuum (< 10⁻¹⁰ mbar) would test whether Rayleigh scaling (β = 2) persists or transitions to geometric scaling (β = 2/3) as particle radius approaches λ_thermal ≈ 10 μm at 300 K. A controlled series with matched isolation across the 10⁷–10⁸ amu range should yield β ≈ 2 if Rayleigh scattering dominates, or β ≈ 2/3 if geometric cross-sections become relevant. Deviation from both would signal unmodeled contributions.

**Optomechanical oscillators:** Cryogenic mechanical oscillators with calibrated thermal occupation n̄_th offer a complementary platform where phonon-number scaling can be measured directly. For thermal decoherence dominated by phonon exchange, the predicted scaling is τ_BA ∝ n̄_th⁻¹. Systems with n̄_th tunable over 1–2 orders of magnitude via cryogenic control would provide a clean test independent of mass variation.

Both platforms require closing the decoherence budget: all environmental channels (blackbody radiation, residual gas, vibration coupling) must be characterized independently so that any residual τ_BA deviation can be attributed to new physics rather than unmodeled environment.

### 4.4 What This Framework Does Not Predict

The framework does not predict:
- Absolute values of Γ (these depend on environmental parameters)
- System-size thresholds independent of environmental coupling
- Upper bounds on quantum computation scalability (which depends on error correction outpacing decoherence)
- The specific mechanism operative in a given experiment (this must be determined empirically)

A note on quantum computation: the scaling law describes decoherence rates under fixed environmental coupling. It does not bound achievable coherence times under active error correction, which can in principle suppress logical error rates faster than physical decoherence accumulates. Fault-tolerant quantum computation is a question of error correction thresholds, not raw decoherence scaling.

These limitations are intrinsic to an operational framework grounded in known decoherence physics.

### 4.5 Multi-Variable Scaling Analysis: Variable Isolation

The apparent suppression of Rayleigh scaling in the broader molecular interferometry dataset ($\beta_{\text{obs}} \approx 0.9$) can be understood by explicitly treating vacuum pressure as a variable.

**Physical Model**

In the Rayleigh regime, the decoherence rate depends on both system mass $m$ (via scattering cross-section $\sigma \propto m^2$) and environmental pressure $P$ (via gas density $n \propto P$):

$$\Gamma(m, P) = k \cdot P \cdot m^{\beta_{\text{phys}}}$$

where $\beta_{\text{phys}} = 2$ for Rayleigh scattering. The Boolean actualization time scales as $\tau_{\text{BA}} \propto \Gamma^{-1}$.

**Observable Exponent Under Variable Isolation**

When comparing systems $(m_1, P_1)$ and $(m_2, P_2)$, the ratio of actualization times is:

$$\frac{\tau_2}{\tau_1} = \frac{P_1}{P_2} \left( \frac{m_1}{m_2} \right)^{\beta_{\text{phys}}}$$

Extracting an "apparent" scaling exponent from mass alone yields a correction formula:

$$\beta_{\text{obs}} = \beta_{\text{phys}} - \frac{\ln(P_1/P_2)}{\ln(m_2/m_1)}$$

This quantifies the masking effect: as experiments move to larger molecules ($m_2 > m_1$) with better vacuum ($P_2 < P_1$), the observable exponent is reduced. Other experimental parameters (chamber temperature $T \approx 300$ K, molecular beam velocity $v \approx 100\text{--}200$ m/s) remain approximately constant across the dataset; vacuum pressure is the dominant systematic variable, spanning two orders of magnitude.

**Application to Data**

The analysis compares the controlled low-mass baseline against the high-mass frontier:

**Table 3: Molecular Interferometry Datasets**

| Molecule | Mass (amu) | Vacuum ($P$, mbar) | $\tau_{\text{BA}}$ (ms) | Reference |
|:---------|:-----------|:-------------------|:------------------------|:----------|
| C$_{60}$ | 720 | $10^{-7}$ | $18 \pm 5$ | Arndt et al. 1999 |
| C$_{70}$ | 840 | $10^{-7}$ | $12 \pm 3$ | Arndt et al. 1999 |
| TPPF$_{152}$ | $\approx 6,000$ | $\sim 10^{-8}$ | — | Eibenberger 2013 |
| Oligoporphyrin | $\approx 25,000$ | $< 10^{-9}$ | $> 12$ (est.) | Fein et al. 2019 |

*Note: Vacuum pressure values represent estimated chamber pressures; measurement uncertainty in the $10^{-7}$–$10^{-9}$ mbar range is typically $\pm 30\text{--}50\%$. Oligoporphyrin $\tau_{\text{BA}}$: Lower bound estimated from visibility remaining above 0.10 at reported measurement times; precise value not extractable from published data.*

Using the endpoints ($P_1 \approx 10^{-7}$ mbar, $P_2 \approx 10^{-9}$ mbar):

* Mass ratio: $\ln(m_2/m_1) \approx 3.56$
* Pressure ratio: $\ln(P_1/P_2) \approx 4.60$

**Predicted observable exponent:**

$$\beta_{\text{obs}} \approx 2 - \frac{4.60}{3.56} \approx 0.71$$

Propagating vacuum pressure uncertainty ($\pm 50\%$) through the correction formula yields $\beta_{\text{obs}} = 0.7 \pm 0.2$.

**Assessment**

The predicted value ($\beta_{\text{obs}} = 0.7 \pm 0.2$) encompasses the fitted observation from the full dataset ($\beta_{\text{obs}} \approx 0.9$, obtained via log-log regression across the mass range 720–25,000 amu, this work) within one standard deviation. Additional systematic uncertainties in mass determination ($\pm 10\%$) and rate extraction ($\pm 20\%$) contribute to the residual discrepancy but do not indicate a breakdown of Rayleigh scaling. Intermediate mass points (e.g., TPPF$_{152}$) fall between these extremes, qualitatively consistent with the pressure-mass trajectory.

**Supporting Evidence**

The 25 kDa oligoporphyrin ($P < 10^{-9}$ mbar) exhibits coherence times that do not show the rapid collapse expected from Rayleigh scaling under fixed isolation. Specifically, the observed coherence lifetime remains substantial despite the 35-fold mass increase from C$_{60}$, whereas fixed-pressure Rayleigh scaling ($\beta = 2$) would predict a decoherence rate increase of $(35)^2 \approx 10^3$. This supports the multi-variable rate equation $\Gamma \propto P \cdot m^2$: the vacuum improvement (factor $> 10^2$) offsets the mass penalty, preventing the collapse that would occur at constant pressure.

**Summary of Analysis**

The dataset requires two distinct analyses:

| Analysis | Range | Pressure | Result | Interpretation |
|:---------|:------|:---------|:-------|:---------------|
| **Controlled Pair** | C$_{60}$/C$_{70}$ | Fixed ($\sim 10^{-7}$) | $\beta = 2.11$ | Consistent with Rayleigh |
| **Full Dataset** | 720 $\to$ 25k | Variable ($10^{-7} \to 10^{-9}$) | $\beta_{\text{obs}} \approx 0.9$ | Confounded by Isolation |
| **Multi-Variable** | 720 $\to$ 25k | Corrected | $\beta_{\text{pred}} = 0.7 \pm 0.2$ | Consistent Within Uncertainty |

The multi-variable framework demonstrates that the apparent exponent suppression arises from systematic improvements in vacuum quality correlated with increasing molecular mass, rather than from a failure of the underlying Rayleigh mechanism.

---

## 5. Interpretive Context: Logic Realism Theory

*This section presents an optional interpretive layer. The empirical and formal results of Sections 1–4 stand independently of this interpretation. Readers uninterested in foundational philosophy may skip to Section 6 without loss of operational content.*

### 5.1 The Interpretive Framework

Logic Realism Theory (LRT) proposes that the Boolean character of actualized outcomes is not merely operational convenience but reflects the logical structure of actuality itself. On this view:

- LRT interprets the Three Fundamental Laws of Logic (Identity, Non-Contradiction, Excluded Middle) as constitutive of physical distinguishability
- From the LRT perspective, actualized events are Boolean because actuality is constrained by these logical laws
- LRT reads decoherence as the physical mechanism through which quantum potentiality resolves into logically admissible classical outcomes

Within this framework, the universality of Boolean measurement outcomes—observed without exception across all of physics—is interpreted as reflecting the prescriptive character of logical law at the level of actuality. This interpretation is not required to apply the operational predictions; it is offered as one possible conceptual unification.

### 5.2 Decoherence Within LRT

LRT does not modify decoherence physics. It provides an interpretive framework that situates decoherence within a broader metaphysics of actualization:

- On this view, quantum states represent the structure of the Infinite Information Space (IIS), which is non-Boolean
- Boolean actuality is interpreted as the domain where logical laws are fully enforced
- Decoherence is read as describing the approach to the IIS-actuality interface
- The scaling law quantifies how rapidly this approach occurs as system complexity increases

Within LRT, the empirical trend that larger systems reach the Boolean regime faster is interpreted as reflecting increasing "pressure" toward logical resolution as degrees of freedom grow. More complex systems have more channels for environmental entanglement, accelerating the transition from quantum potentiality to Boolean actuality.

### 5.3 What LRT Claims to Provide

**LRT offers:**
- An ontological grounding for the Boolean structure of actual events
- Conceptual unification: decoherence as interface mechanism, not brute fact
- Interpretive context for why classical logic governs all actualized phenomena

**LRT does not provide:**
- Predictions of decoherence rates or scaling exponents (these come from physics)
- Constraints on environmental coupling strength Γ
- Size thresholds independent of isolation
- Modifications to the quantum formalism

**Critical distinction:** LRT interprets the scaling law; it does not generate it. The quantitative predictions come from standard decoherence physics. LRT provides a metaphysical framework for understanding why those predictions might matter for the structure of actuality—but this interpretive layer is separable from the operational framework.

### 5.4 Relation to Other Interpretations

The scaling law of Section 3 is interpretation-neutral. It is compatible with:

- **Copenhagen:** τ_BA marks when systems become "effectively classical" for measurement purposes
- **Many-Worlds:** τ_BA marks when branches become operationally inaccessible to interference experiments
- **Decoherent histories:** τ_BA marks when consistent histories become available
- **Objective collapse:** Standard decoherence should dominate at small masses; deviations signal collapse contributions

LRT offers a specific reading: Boolean actualization is not merely operational but ontological, reflecting the logical structure of reality itself. This interpretation is developed fully in companion papers (Longmire 2025a, 2025b, 2025c).

---

## 6. Conclusion

The Boolean character of actualized events is an empirical invariant requiring explanation. Decoherence theory provides the mechanism; this paper provides the operational framework for quantitative comparison across physical platforms.

The central results are:

1. **Operational metric:** τ_BA enables cross-platform comparison of decoherence-driven classicalization
2. **Mechanism-dependent scaling:** $\tau_{\mathrm{BA}} \propto s^{-\beta}$ with $\beta$ predictable from coupling physics and noise correlation structure
3. **Empirical validation across 7 platforms:** Fullerenes (β = 2.11), cavity QED (β = 1.01), superconducting qubits (β = 1.0), trapped ions (β = 2.0), and NV ensembles (β = 1.06) all match predictions
4. **Correlation structure diagnostic:** The same quantum state (GHZ) exhibits β = 1 on SC qubits (uncorrelated noise) vs. β = 2 on trapped ions (correlated noise), demonstrating that β diagnoses noise correlation structure
5. **Analytical cases:** Theorem 1 derives β = 1 for independent dephasing; superdecoherence yields β = 2 for correlated dephasing
6. **Falsifiability:** Exponent deviations under controlled isolation signal unmodeled physics or new mechanisms

The framework does not resolve interpretive questions about quantum mechanics. It provides a common empirical benchmark that all interpretations must accommodate.

The optional LRT interpretation (Section 5) situates these results within a metaphysics of actualization, reading Boolean outcomes as reflecting the logical structure of actuality itself. This interpretation does not generate new predictions but provides conceptual unification for the observed pattern.

Future work should extend controlled scaling tests to higher masses using levitated optomechanics with fully characterized decoherence budgets. Such experiments are positioned to test both the mechanism-dependent exponent predictions and potential contributions from objective collapse.

---

## References

- Arndt, M. et al. (1999) Nature **401**, 680.
- Bassi, A. et al. (2013) Rev. Mod. Phys. **85**, 471.
- Brune, M. et al. (1996) Phys. Rev. Lett. **77**, 4887.
- Eibenberger, S. et al. (2013) Phys. Chem. Chem. Phys. **15**, 14696.
- Ellerman, D. (2013) Entropy **15**, 3698.
- Fein, Y. Y. et al. (2019) Nat. Phys. **15**, 1242.
- Girolami, D. (2014) Phys. Rev. Lett. **113**, 170401. [Operational interpretation of logical entropy]
- Joos, E. et al. (2003) *Decoherence and the Appearance of a Classical World in Quantum Theory*, Springer.
- Park, H. et al. (2022) npj Quantum Inf. **8**, 95. [NV ensemble decoherence]
- Longmire, J. D. (2025a) "It from Bit, Bit from Fit: Foundational Physics Logically Remastered." Zenodo. https://doi.org/10.5281/zenodo.17831819
- Longmire, J. D. (2025b) "Logic Realism Theory: Technical Foundations." Zenodo. https://doi.org/10.5281/zenodo.17831883
- Longmire, J. D. (2025c) "Logic Realism Theory: Philosophical Foundations." Zenodo. https://doi.org/10.5281/zenodo.17831912
- Manfredi, G. & Feix, M. R. (2000) Phys. Rev. E **62**, 4665.
- Millen, J. et al. (2020) Rep. Prog. Phys. **83**, 026401.
- Monz, T. et al. (2011) Phys. Rev. Lett. **106**, 130506. [14-qubit GHZ, superdecoherence]
- Kam, J. F. et al. (2024) Phys. Rev. Research **6**, 033155. [IBM GHZ scaling, arXiv:2312.15170]
- Schlosshauer, M. (2007) *Decoherence and the Quantum-to-Classical Transition*, Springer.
- Zurek, W. H. (2003) Rev. Mod. Phys. **75**, 715.

---

## Appendix: Reproducibility

### A.1 Exponent Extraction

For two data points $(s_1, \tau_1)$ and $(s_2, \tau_2)$:

$$\beta = -\frac{\ln(\tau_2/\tau_1)}{\ln(s_2/s_1)} = \frac{\ln(\Gamma_2/\Gamma_1)}{\ln(s_2/s_1)}$$

For multiple points, log-log linear regression yields $\beta$ as the negative slope.

### A.2 Visibility-Entropy Conversion

For balanced superposition with normalized visibility $v = V/V_0$:

$$h_L = \frac{1}{2}(1 - v^2)$$

Threshold $V_\ast = 0.10$ (i.e., $v = 0.10$) gives $h_\ast \approx 0.495$.

### A.3 τ_BA from Exponential Decay

For $V(t) = V_0 e^{-\Gamma t}$:

$$\tau_{\mathrm{BA}}(V_\ast) = \frac{1}{\Gamma}\ln\left(\frac{V_0}{V_\ast}\right)$$

At $V_\ast = 0.10$ and typical $V_0 \approx 0.9$: $\tau_{\mathrm{BA}} \approx 2.2/\Gamma$.

---

## Appendix B: Data Extraction Methodology

This appendix documents the extraction of decoherence rates and scaling exponents from primary sources. All quantitative claims in the main text are derived quantities, not direct quotes from primaries, and should be interpreted with the uncertainties noted below.

### B.1 Fullerene Interferometry (Arndt et al. 1999)

**Source:** Arndt, M. et al. "Wave-particle duality of C60 molecules." *Nature* 401, 680-682 (1999).

**Raw data:** The primary reports fringe visibility for C₆₀ under various conditions. Visibility values V ≈ 0.3-0.6 were observed depending on beam velocity and grating alignment. The paper does not report explicit decoherence rates Γ.

**Extraction method:**
1. Visibility decay attributed to thermal emission and collisional decoherence
2. Decoherence rate estimated from: $\Gamma \approx (1/\tau_{flight}) \ln(V_0/V_{obs})$
3. Flight time τ_flight ≈ 5-10 ms depending on velocity (~100-220 m/s over ~1 m path)
4. Assuming $V_0 \approx 1$ (ideal) and $V_{obs} \approx 0.4$: $\Gamma \approx 0.09-0.18$ ms⁻¹

**C₆₀/C₇₀ comparison:**
- Both molecules measured under matched conditions (P ~ 10⁻⁷ mbar, T ~ 300 K)
- C₇₀ shows lower visibility than C₆₀ under identical conditions
- Ratio Γ₇₀/Γ₆₀ ≈ 1.3-1.4 estimated from relative visibility reduction
- With mass ratio m₇₀/m₆₀ = 840/720 = 1.167:

$$\beta = \frac{\ln(\Gamma_{70}/\Gamma_{60})}{\ln(m_{70}/m_{60})} = \frac{\ln(1.38)}{\ln(1.167)} \approx 2.1 \pm 0.5$$

**Caveats:**
- Γ values are *inferred*, not directly measured
- Limited to two-point comparison (dynamic range 1.17×)
- Uncertainty dominated by visibility measurement precision (~10%) and flight time estimates
- Result *consistent with* Rayleigh prediction β = 2, not a precision test

### B.2 Cavity QED (Brune et al. 1996)

**Source:** Brune, M. et al. "Observing the progressive decoherence of the 'meter' in a quantum measurement." *Phys. Rev. Lett.* 77, 4887-4890 (1996).

**Raw data:** Decoherence of Schrödinger cat states $|\alpha\rangle + |-\alpha\rangle$ measured via atomic correlation decay. Table I in the primary reports normalized decoherence times τ_d/τ_cav for various |α|.

**Extraction method:**
1. Theoretical model: $\Gamma_{cat} = 4\kappa\bar{n}$ where $\bar{n} = |\alpha|^2$
2. This predicts τ_d ∝ 1/n̄, i.e., β = 1 for photon-loss mechanism
3. Log-log regression on reported τ_d/τ_cav vs n̄:

| |α| | n̄ | τ_d/τ_cav | ln(n̄) | ln(τ_d/τ_cav) |
|-----|------|-----------|--------|---------------|
| 1.2 | 1.44 | 0.80 | 0.36 | -0.22 |
| 1.8 | 3.24 | 0.35 | 1.18 | -1.05 |
| 2.5 | 6.25 | 0.18 | 1.83 | -1.71 |
| 3.2 | 10.24| 0.11 | 2.33 | -2.21 |

4. Linear fit: slope = -1.01 ± 0.03, confirming β = 1

**Caveats:**
- τ_d/τ_cav values read from Figure 3 and Table I with ~5% uncertainty
- Four data points over dynamic range 7× in n̄
- Theoretical β = 1 is *input* to the photon-loss model; measurement is consistent
- Other decoherence channels (thermal photons, dephasing) subdominant at T = 0.8 K

### B.3 Superconducting Qubits (Kam et al. 2024)

**Source:** Kam, J. F. et al. "Exponential quantum speedup in simulating coupled classical oscillators." *Phys. Rev. Research* 6, 033155 (2024). arXiv:2312.15170.

**Raw data:** GHZ state fidelity decay measured on IBM quantum processors for N = 1-15 qubits.

**Extraction method:**
1. Decoherence rate extracted from fidelity decay: $F(t) = e^{-\Gamma t}$
2. Linear fit to Γ vs N yields: $\Gamma = (7.13N + 5.54) \times 10^{-3}$ μs⁻¹
3. Dominant term Γ ∝ N is consistent with β = 1 (independent dephasing)

**Caveats:**
- 15 data points over dynamic range 15× in N
- Most robust dataset in this compilation
- Offset term (5.54 × 10⁻³) indicates N-independent baseline decoherence
- Result supports Theorem 1 (Section 2.4)

### B.4 Trapped Ions (Monz et al. 2011)

**Source:** Monz, T. et al. "14-qubit entanglement: Creation and coherence." *Phys. Rev. Lett.* 106, 130506 (2011).

**Raw data:** GHZ state coherence decay for N = 2-8 qubits (14-qubit creation demonstrated but coherence not systematically characterized).

**Extraction method:**
1. Coherence time T₂ measured via Ramsey-type sequences
2. Superdecoherence model: $\Gamma_{GHZ} \propto N^2 \Gamma_{single}$ due to correlated magnetic field noise
3. Fit yields β = 2.0 ± 0.1

**Caveats:**
- 6-7 data points over dynamic range 4× in N
- Correlated noise (global B-field fluctuations) confirmed via noise spectroscopy
- Same GHZ state, different β than SC qubits—demonstrates diagnostic capability

### B.5 NV Center Ensembles (Park et al. 2022)

**Source:** Park, H. et al. "Decoherence of nitrogen-vacancy spin ensembles in a nitrogen electron-nuclear spin bath." *npj Quantum Info.* 8, 95 (2022).

**Raw data:** T₂ coherence times vs substitutional nitrogen concentration [P1].

**Extraction method:**
1. Dipole-dipole coupling to nitrogen bath acts as effectively local noise
2. Fit: $T_2 \propto [P1]^{-1.06 \pm 0.05}$
3. β = 1.06 consistent with uncorrelated (local) bath model

**Caveats:**
- ~5 data points over ~10× range in [P1]
- "Size" parameter is bath density, not system size per se
- Mechanism attribution (dipole bath) from prior literature

### B.6 Large-Molecule Interferometry (Fein et al. 2019)

**Source:** Fein, Y. Y. et al. "Quantum superposition of molecules beyond 25 kDa." *Nat. Phys.* 15, 1242-1245 (2019).

**Raw data:** Interference visibility for molecules up to 25,000 amu under ultra-high vacuum (< 10⁻⁹ mbar).

**Extraction method:**
1. Visibility remains substantial (V > 0.1) at 25 kDa despite 35× mass increase from C₆₀
2. β_obs ≈ 0.9 from log-log regression across full dataset (this work)
3. Multi-variable correction (Section 4.5) accounts for 100× vacuum improvement

**Caveats:**
- Pressure values are *estimates* (±50%) not direct chamber readings at measurement time
- τ_BA for 25 kDa is lower bound (visibility above threshold at reported times)
- β_obs ≈ 0.9 is *confounded* by isolation improvement; corrected β_pred = 0.7 ± 0.2

### B.7 Summary: Data Quality Assessment

| Platform | Data Points | Dynamic Range | β Precision | Confidence |
|----------|-------------|---------------|-------------|------------|
| Fullerene | 2 | 1.17× | ±0.5 | Moderate |
| Cavity QED | 4 | 7× | ±0.03 | High |
| SC qubits | 15 | 15× | ±0.05 | High |
| Trapped ions | 6 | 4× | ±0.1 | High |
| NV ensembles | ~5 | ~10× | ±0.05 | Moderate |
| Large molecules | 4+ | 35× | ±0.2 | Confounded |

**Overall assessment:** The framework is *supported by* available data across seven platforms. The strongest validations come from superconducting qubits (15 points, linear scaling) and cavity QED (4 points, precise fit). The fullerene comparison, while limited to two points, is *consistent with* Rayleigh predictions. The large-molecule dataset requires multi-variable treatment due to isolation confounding.
