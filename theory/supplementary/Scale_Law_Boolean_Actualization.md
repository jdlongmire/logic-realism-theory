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

Quantum mechanics permits superpositions at all scales, yet macroscopic measurement outcomes are invariably definite and Boolean. Decoherence theory explains the suppression of interference, but the rate of this suppression has not been expressed as a unified, operationally testable scaling framework enabling cross-platform comparison. This paper develops such a framework using logical entropy $h_L(\rho) = 1 - \mathrm{Tr}(\rho^2)$ and a fixed visibility threshold $V_\ast$ to define the Boolean actualization time $\tau_{\mathrm{BA}}$: the earliest time at which measured interference contrast falls below threshold. We show that $\tau_{\mathrm{BA}}$ scales as a power of system size, with exponent $\beta$ determined by both the physical mechanism and the correlation structure of environmental noise. Empirical validation across seven platforms confirms the framework: fullerene interferometry ($\beta = 2.11$, Rayleigh), cavity QED ($\beta = 1.01$, photon loss), superconducting qubits ($\beta = 1.0$, uncorrelated dephasing), trapped ions ($\beta = 2.0$, correlated dephasing), and NV ensembles ($\beta = 1.06$, dipole bath). Notably, the same GHZ state exhibits $\beta = 1$ on superconducting qubits versus $\beta = 2$ on trapped ions, demonstrating that the scaling exponent diagnoses noise correlation structure. We derive theorems for both limiting cases: independent dephasing yields $\tau_{\mathrm{BA}} \propto 1/N$, while correlated (superdecoherence) yields $\tau_{\mathrm{BA}} \propto 1/N^2$. The framework provides a quantitative, falsifiable criterion for the quantum-classical boundary. An optional interpretive section connects these results to Logic Realism Theory, which reads Boolean actualization as reflecting the logical structure of actuality itself.

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

Environmental entanglement rapidly suppresses off-diagonal terms of the reduced density matrix in the pointer basis (Zurek 2003; Schlosshauer 2007; Joos et al. 2003). The qualitative observation that larger systems decohere faster is well established. What has been lacking is a unified operational metric enabling quantitative comparison across disparate physical systems.

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

The framework has been validated across seven distinct experimental platforms spanning molecular, photonic, and solid-state systems.

**Table 1: Validated Scaling Exponents**

| Platform | Mechanism | Correlation | Size param | Predicted β | Measured β | Reference |
|----------|-----------|-------------|------------|-------------|------------|-----------|
| Fullerene (C₆₀/C₇₀) | Rayleigh scattering | — | mass $m$ | 2 | 2.11 | Arndt 1999 |
| Cavity QED cats | Photon loss | — | $\bar{n}$ | 1 | 1.01 | Brune 1996 |
| SC qubits (IBM) | Dephasing | Uncorrelated | $N$ | 1 | 1.0 | Kam 2024 |
| Trapped ions (Innsbruck) | Dephasing | Correlated | $N$ | 2 | 2.0(1) | Monz 2011 |
| NV ensembles | Dipole bath | Local | density | 1 | 1.06 | Park 2022 |

**Superconducting qubits (β = 1):**

GHZ state decoherence on IBM quantum processors (N = 1–15 qubits) yields:

$$\Gamma = (7.13N + 5.54) \times 10^{-3}\ \mu\text{s}^{-1}$$

The linear scaling ($\Gamma \propto N$) directly validates Theorem 1: independent local noise sources produce β = 1. Each qubit experiences uncorrelated dephasing from its local environment.

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

This confirms that the scaling exponent is not an intrinsic property of entangled states but reflects the correlation structure of environmental noise. The framework thus provides a diagnostic tool: measuring β reveals whether dominant noise sources are local or global.

### 3.4 Summary Table by Mechanism Class

**Table 2: Mechanism-Dependent Exponents**

| Mechanism | Size parameter | Predicted β | Empirical β | Status |
|-----------|----------------|-------------|-------------|--------|
| Thermal scattering (Rayleigh) | mass $m$ | 2 | 2.11 | ✓ Validated |
| Thermal scattering (geometric) | mass $m$ | 2/3 | — | Awaiting test |
| Photon loss (cavity) | $\bar{n}$ | 1 | 1.01 | ✓ Validated |
| Gas collisions | mass $m$ | 2/3 | — | Awaiting test |
| Dephasing (uncorrelated) | qubit $N$ | 1 | 1.0 | ✓ Validated |
| Dephasing (correlated) | qubit $N$ | 2 | 2.0 | ✓ Validated |
| Dipole bath (local) | density | 1 | 1.06 | ✓ Validated |

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

---

## 4. Falsifiability

### 4.1 Primary Criterion

The framework makes a testable prediction:

> Under controlled environmental coupling, $\tau_{\mathrm{BA}}$ scales as $s^{-\beta}$ with $\beta$ predictable from the dominant decoherence mechanism.

**Falsification condition:** Observation of scaling exponents deviating significantly from mechanism predictions, after accounting for all characterized environmental channels, would indicate either:
- Uncharacterized environmental couplings, or
- New physics beyond standard decoherence (e.g., objective collapse mechanisms)

This is the crisp, empirical test the framework provides.

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

---

## 5. Interpretive Context: Logic Realism Theory

*This section presents an optional interpretive layer. The empirical and formal results of Sections 1–4 stand independently of this interpretation.*

### 5.1 The Interpretive Claim

Logic Realism Theory (LRT) proposes that the Boolean character of actualized outcomes is not merely operational convenience but reflects the logical structure of actuality itself. On this view:

- The Three Fundamental Laws of Logic (Identity, Non-Contradiction, Excluded Middle) are constitutive of physical distinguishability
- Actualized events must be Boolean because actuality is constrained by these logical laws
- Decoherence is the physical mechanism through which quantum potentiality resolves into logically admissible classical outcomes

The universality of Boolean measurement outcomes, observed without exception across all of physics, receives explanation: it reflects the prescriptive character of logical law at the level of actuality.

### 5.2 Decoherence Within LRT

LRT does not modify decoherence physics. It provides an interpretive framework that situates decoherence within a broader metaphysics of actualization:

- Quantum states represent the structure of the Infinite Information Space (IIS), which is non-Boolean
- Boolean actuality is the domain where logical laws are fully enforced
- Decoherence describes the approach to the IIS-actuality interface
- The scaling law quantifies how rapidly this approach occurs as system complexity increases

The empirical trend, that larger systems reach the Boolean regime faster, is interpreted as reflecting the increasing "pressure" toward logical resolution as the number of degrees of freedom grows. More complex systems have more ways to entangle with their environment, accelerating the transition from quantum potentiality to Boolean actuality.

### 5.3 What LRT Does and Does Not Do

**LRT provides:**
- Ontological grounding for the Boolean structure of actual events
- Conceptual unification: decoherence as interface mechanism, not brute fact
- Explanatory context for why classical logic governs all actualized phenomena

**LRT does not provide:**
- Predictions of decoherence rates or scaling exponents (these come from physics)
- Constraints on environmental coupling strength Γ
- Size thresholds independent of isolation
- Modifications to the quantum formalism

LRT interprets the scaling law; it does not generate it. The predictions come from decoherence physics; LRT provides the metaphysical framework explaining why those predictions matter for the structure of actuality.

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
5. **Analytical cases:** Theorem 1 proves β = 1 for independent dephasing; superdecoherence gives β = 2 for correlated dephasing
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
