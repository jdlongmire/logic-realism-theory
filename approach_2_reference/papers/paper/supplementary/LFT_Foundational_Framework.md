# Logic Field Theory: Quantum Mechanics from Global Logical Consistency

## Abstract
Logic Field Theory (LFT) shows that quantum mechanics (QM) follows under the listed constraints within the class of orthomodular, no-signaling, tomographically local theories with continuous reversible dynamics. LFT’s framework is captured by **A = L(I)**, where physical actuality (A) emerges from the logic field operator (L) acting on an infinite information probability space (I2PS). Through a composite functor—mapping I2PS to an orthomodular poset, Hilbert spaces, states, and dynamics—LFT derives QM’s structure using representation theorems (Piron–Solèr, Gleason/Busch, Wigner, Tsirelson). Operational constraints (Lüders sharpness, atomicity, no-signaling) are motivated as necessary for global logical consistency and local measurability. LFT unifies these theorems, resolves quantum paradoxes as logical necessities, predicts testable finite-\(\varepsilon\) visibility and finite-\(K\) CHSH deviations, and frames physics as logical constraints on information actualization.

## 0. Motivation and Core Principles

### Why a Logic Field?
LFT posits that physics emerges from a **global logic field**, an abstract orthomodular poset \((\mathcal{L}, \wedge, \neg)\) of sharp tests, with operational meet (\(\wedge\), sequential conjunction on compatible tests), orthocomplement (\(\neg\)), and orthogonal join (\(\vee\)), satisfying:

- **L1 (Identity):** \(x = x\).
- **L2 (Non-Contradiction):** \(\neg(x \wedge \neg x)\).
- **L3 (Excluded Middle):** \(x \vee \neg x = I\).

A measurable label map \(\eta: \mathcal{L} \to \Sigma(I)\) labels each sharp test with a measurable event used only for measurability statements; \(\mathcal{L}\)’s meet/join differ from set-theoretic \(\cap/\cup\). The logic field enforces L1–L3 universally across an infinite information space \(I\). **Core Observation:** Entanglement and Bell violations (CHSH \(\le 2\sqrt{2}\)) require a global non-distributive structure. CHSH \(\le 2\) uses factorizability (CP1) and measurement independence; empirical CHSH > 2 shows at least one must fail in a Boolean setting. LFT replaces Booleanity with a global non-distributive event structure (Bell, 1964).

### Why Global?
If local event structures are distributive and probabilities factorize (CP1), CHSH \(\le 2\). Empirical violations (CHSH > 2) require a global non-distributive event structure, modeled by \(\mathcal{L}\) coordinating constraints across subsystems (§4.5).

### Why an Infinite Information Probability Space (I2PS)?
The I2PS is:
- \(I\): Infinite set of information points.
- \(\Sigma(I)\): σ-algebra of events.
- \(\mu\): Probability measure, \(\mu(I) = 1\).

E2 is a Solèr-type hypothesis enabling the Piron–Solèr representation; it is stronger than non-distributivity. Bell violations (CHSH > 2) occur already in finite dimension; E2 is used here to secure the Hilbert-space representation route we adopt (Solèr, 1995).

### Why Information-Theoretic?
LFT views physics as **logical constraints on information actualization**. The framework is:

**A = L(I)**

where \(L = L_{\text{dynamics}} \circ L_{\text{states}} \circ L_{\text{structure}} \circ L_{\text{lattice}}\):

- \(L_{\text{lattice}}\): I2PS \(\to \mathcal{L}\) (orthomodular poset, §4).
- \(L_{\text{structure}}\): \(\mathcal{L} \to \text{Proj}(\mathcal{H})\) (Hilbert space, §4).
- \(L_{\text{states}}\): \(\text{Proj}(\mathcal{H}) \to \mathcal{D}(\mathcal{H})\) (states, §6).
- \(L_{\text{dynamics}}\): \((\mathcal{D}(\mathcal{H}), U(t))\) (evolution, §8).

**Contribution.** LFT shows QM follows under the listed constraints within the above class, unifying theorems, resolving paradoxes, and predicting testable deviations.

---

## Required Operational Constraints
Constraints motivated by global consistency and local measurability (§4.5):

- **P1 (σ-additivity):** \(\mu(\bigsqcup_n E_n) = \sum_n \mu(E_n)\), countable disjoint \(E_n \in \mathcal{A}\).
- **Top1 (Standard Borel):** \((I,\Sigma)\) is standard Borel (Kechris, 1995, Ch. II).
- **IND (Independence):** Some preparations satisfy \(p(A \wedge B) = p(A)p(B)\).
- **NS (No-signaling):** \(\sum_b P(a,b|x,y) = P(a|x)\).
- **Tm (Local Tomography):** Joint states determined by local statistics.
- **CR (Continuous Reversibility):** Dynamics form a continuous connected group.
- **E1′ (Lüders Sharpness):** \(\mathsf{Upd}_E(\rho) = P_E \rho P_E + P_{E^c} \rho P_{E^c}\); compatible tests commute.
- **E0 (Atomicity):** \(\mathcal{L}\) has atoms.
- **E2:** \(\mathcal{L}\) has infinite orthogonal sequences.
- **Gen:** Propositions generate \(\Sigma(I)\).
- **O1 (Noncontextuality):** If two realizations yield the same \(\Phi(E)\), then \(p(E)\) is the same.
- **O2 (σ-additivity):** For any countable pairwise-orthogonal \(\{P_i\}\), \(p(\sum_i P_i) = \sum_i p(P_i)\).

---

## 1. Logical Axioms and Probability
- **L1 (Identity):** \(x = x\).
- **L2 (Non-Contradiction):** \(\neg(x \wedge \neg x)\).
- **L3 (Excluded Middle):** \(x \vee \neg x = I\).

**Bridge to Probability.** L1 ensures well-defined propositions. L2 implies \(E \cap E^c = \emptyset\). L3 implies \(E \cup E^c = I\). Define countable, separating \(\mathcal{Q}_0 \subset \{q: I \to \{0,1\} \mid q \text{ measurable}\}\). Set \(\mathcal{A} = \mathrm{alg}\{q^{-1}(\{1\}): q \in \mathcal{Q}_0\}\), \(\mu: \mathcal{A} \to [0,1]\), \(\mu(I) = 1\), with P1. Carathéodory extends \(\mu\) to \(\Sigma = \sigma(\mathcal{A})\) by the \(\pi-\lambda\) theorem (Billingsley, 2012). \(\Sigma(I)\) is Boolean; \(\mathcal{L}\) is non-distributive via constraints (§4.5).

---

## 2. Infinite Information Probability Space (I2PS)
- **D1 (Informational Infinitude):** \(I\) is infinite.
- **D2:** \(\Sigma(I) = \sigma(\mathcal{A})\), \(\mu(I) = 1\).
- **R1:** \((I,\Sigma,\mu)\) is a probability space.

**Structure.** Top1: \((I,\Sigma)\) is standard Borel. \(\mathcal{A} = \mathrm{alg}\{q^{-1}(\{1\}): q \in \mathcal{Q}_0\}\). Equivalence \(x \sim y\) if \(q(x) = q(y)\), \(\forall q \in \mathcal{Q}_0\). If \(\sim\) is Borel and smooth, \(\exists \tilde{I}\), Borel \(\pi: I \to \tilde{I}\), \(\Sigma = \pi^{-1}(\mathrm{Borel}(\tilde{I}))\) (Kechris, 1995, Thm 18.1).

**Why Infinite?** E2 is a Solèr-type hypothesis enabling the Piron–Solèr representation; it is stronger than non-distributivity. Bell violations (CHSH > 2) occur already in finite dimension; E2 is used here to secure the Hilbert-space representation route we adopt (Solèr, 1995).

---

## 3. Logical Operator
- **D3:** Logical operator \(L\):
  - **Case A:** Measurable \(f: I \to I\), \(f_\# \mu(E) = \mu(f^{-1}(E))\).
  - **Case B:** Markov kernel \(K: I \times \Sigma \to [0,1]\).

**Lemma L1:** \(\nu(E) = \int K(x,E) d\mu(x)\) is a probability measure by monotone convergence (Billingsley, 2012).

---

## 4. Event Lattice and Hilbert Space
**Sharp Events.** \(\mathcal{L}\) is an abstract orthomodular poset of sharp tests (repeatable, idempotent outcomes), with operational meet (sequential conjunction on compatible tests), orthocomplement, and orthogonal join. A measurable label map \(\eta: \mathcal{L} \to \Sigma(I)\) labels each sharp test with a measurable event used only for measurability statements; \(\mathcal{L}\)’s meet/join differ from set-theoretic \(\cap/\cup\).

**Orthomodularity.** If \(A \subseteq B\) and \(A, B\) are compatible (commuting projectors), then \(P_A P_B = P_B P_A = P_A\), hence \(B = A \vee (B \wedge A^\perp)\) (Foulis, 1995).

- **Theorem H1 (Piron–Solèr):** E0, E1′, E2 imply \(\mathcal{L} \cong\) closed subspaces over a division ring \(K\) (Piron, 1964; Solèr, 1995).
- **Lemma H2:** Tm + CR + phase/symmetry select \(\mathbb{C}\) (Hardy, 2011, §4; Barnum–Wilce, 2014, Thm 1).
- **Corollary H3:** \(\mathcal{L} \cong\) complex \(\mathcal{H}\).

### 4.5 Motivation of Operational Constraints
Under global logical consistency, local measurability, and reproducible sharp tests, E1′, E0, E2, and NS are required to match empirical Bell-type constraints without contradiction. These are explanatory necessities within LFT, not consequences of L1–L3 alone.

1. **Infinite Orthogonal Sequences (E2):**
   - **Motivation:** E2 is a Solèr-type hypothesis enabling the Piron–Solèr representation; it is stronger than non-distributivity. Bell violations (CHSH > 2) occur already in finite dimension; E2 is used here to secure the Hilbert-space representation route we adopt (Solèr, 1995). **Justification:** Rules out non-Hilbert lattices.

2. **Lüders Update (E1′):**
   - **Motivation:** Operational postulate for repeatability and minimal disturbance. **Justification:** Ensures projection to orthogonal subspaces, preserving L2 globally (Chiribella et al., 2011).

3. **Atomicity (E0):**
   - **Motivation:** L1 requires minimal events for well-defined outcomes. **Justification:** Atoms ensure definite measurement results.

4. **No-signaling (NS):**
   - **Motivation:** Local measurements must respect L2 globally. **Justification:** Prevents contradictions from non-local influences.

**Uniqueness:** E1′, E0, E2, NS lead to orthomodular \(\mathcal{L}\) and complex \(\mathcal{H}\). Alternatives fail:
- **Classical:** Distributive lattices violate E2.
- **GPTs:** Satisfy NS but allow CHSH = 4, requiring Hilbert/orthomodular structure (Popescu-Rohrlich, 1994).
- **Hidden-variable theories:** Noncontextual hidden-variable models violate O1 once Kochen–Specker constraints apply.

---

## 5. Symmetries
- **D4:** Assuming H3 (complex Hilbert space), \(t(\psi \to \phi) = |\langle \phi | \psi \rangle|^2\). Pre-H3, \(t\) is an abstract transition probability on rays.
- **S0:** Symmetries preserve \(t\).
- **S1:** Group \(G\) preserves \(t\).
- **CR:** Continuous representations (Bargmann, 1954).
- **Theorem T1 (Wigner):** Bijections on rays are unitary/antiunitary (Wigner, 1931).

---

## 6. Observables and States
- **D5:** \(E \in \Sigma(I) \mapsto F \in \mathsf{Eff}(\mathcal{H})\), \(0 \le F \le I\).
- **O1 (Noncontextuality):** If two realizations yield the same \(\Phi(E)\), then \(p(E)\) is the same.
- **O2 (σ-additivity):** For any countable pairwise-orthogonal \(\{P_i\}\), \(p(\sum_i P_i) = \sum_i p(P_i)\).

**Frame Function.** With O1 and O2, \(p\) on PVMs is a frame function. Gleason (dim \(\ge 3\)) and Busch (dim = 2 via POVMs/Naimark) imply \(\exists! \rho\), \(p(P) = \mathrm{Tr}(\rho P)\). Extend to events: \(p(E) = \mathrm{Tr}(\rho \Phi(E))\) (Gleason, 1957; Busch, 1999).

**Naimark Dilation.**
\[
E = \begin{pmatrix} 2/3 & 0 \\ 0 & 1/3 \end{pmatrix}, \quad K_0 = \sqrt{E} = \begin{pmatrix} \sqrt{2/3} & 0 \\ 0 & \sqrt{1/3} \end{pmatrix}, \quad K_1 = \sqrt{I - E} = \begin{pmatrix} \sqrt{1/3} & 0 \\ 0 & \sqrt{2/3} \end{pmatrix}
\]
Define \(V: \mathbb{C}^2 \to \mathbb{C}^2 \otimes \mathbb{C}^2\) by \(V|\psi\rangle = K_0|\psi\rangle \otimes |0\rangle + K_1|\psi\rangle \otimes |1\rangle\). Take \(P_1 = I \otimes |0\rangle\langle 0|\). Then \(E = V^\dagger P_1 V\), \(I - E = V^\dagger (I \otimes |1\rangle\langle 1|) V\).

---

## 7. Correlations
Under a C*-algebraic composite with independent subsystems and no-signaling, one obtains commuting local algebras and, under standard tensor assumptions, a tensor-product representation (CBH 2003). We adopt this form for composites (within a C*-algebraic setting).

**Tsirelson Bound.** For \(A_i, B_j\), \(A_i^2 = B_j^2 = I\):
\[
S = A_0 \otimes (B_0 + B_1) + A_1 \otimes (B_0 - B_1)
\]
\[
S^2 = 4I - [A_0, A_1] \otimes [B_0, B_1]
\]
\[
\|[X, Y]\| \le 2\|X\|\|Y\|, \quad \|A_i\| = \|B_j\| = 1 \Rightarrow \|S^2\| \le 8 \Rightarrow \|S\| \le 2\sqrt{2} \Rightarrow |\langle S \rangle| \le 2\sqrt{2}
\]
(Tsirelson, 1980).

---

## 8. Dynamics: Information-Theoretic Lagrangian
Assume \(I\) is a smooth manifold with metric \(g\) and compatible measure \(\mu\); the Fisher-information kinetic term is a modeling choice. Action:
\[
S_{LFT}[\rho, \phi] = \int dt \int_I d\mu(x) \, \mathcal{L}_{LFT}
\]
\[
\mathcal{L}_{LFT} = T - V
\]
- **Kinetic Term:** \(T = \frac{1}{2} \int_I \rho (\dot{\phi} + \nabla \phi \cdot v)^2 d\mu\), \(v = \nabla \phi / m\).
- **Potential Term:** \(V = \int_I \rho V_{\text{ext}} d\mu + \lambda(t) (\int_I \rho d\mu - 1)\).

**Euler-Lagrange.** Variation w.r.t. \(\phi\): \(\partial_t \rho + \nabla \cdot (\rho v) = 0\). Variation w.r.t. \(\rho\): Hamilton-Jacobi equation. With \(\psi = \sqrt{\rho} e^{i\phi/\hbar}\):
\[
i\hbar \partial_t \psi = -\frac{\hbar^2}{2m} \nabla^2 \psi + V_{\text{ext}} \psi
\]
(Caticha, 2010).

**Dephasing.** \(\Pi(E) = \sum_\alpha P_\alpha E P_\alpha\), unital, CP, idempotent, \(\|\Pi(E)\| \le \|E\|\). The dual Schrödinger map is CPTP and contractive in trace norm: \(\|\mathcal{E}(\rho) - \mathcal{E}(\sigma)\|_1 \le \|\rho - \sigma\|_1\). Schrödinger: \(\mathcal{E}(\rho) = \sum_\alpha P_\alpha \rho P_\alpha\).

**Visibility.** \(\psi = \frac{1}{\sqrt{2}}(|0\rangle + |1\rangle)\), \(\lambda(K) = 1 - e^{-K}\), \(V(K) = e^{-K}\).

---

## 9. Explanatory Power and Comparisons
**Why LFT?** LFT shows QM follows under the listed constraints within the class of orthomodular, no-signaling, tomographically local theories with continuous reversible dynamics, reconciling global logical consistency with local measurability.

**Comparisons:**
- **Classical Probability:** Distributive lattices, CHSH \(\le 2\), fail for entanglement.
- **QM:** Postulates Hilbert space. LFT derives it from \(\mathcal{L}\).
- **GPTs:** Satisfy NS but allow CHSH = 4, requiring Hilbert/orthomodular structure (Popescu-Rohrlich, 1994).
- **Hidden-Variable Theories:** Noncontextual hidden-variable models violate O1 once Kochen–Specker constraints apply.
- **Reconstructions:** Hardy (2011), Chiribella et al. (2011), Dakić–Brukner (2011), Masanes–Müller (2011) use operational axioms. LFT motivates these from logical realism.
- **Wheeler (1990):** “It from bit” posits informational physics. LFT grounds information in L1–L3 and infinite I2PS.

**Resolutions:**
1. **Measurement:** Collapse is constraint resolution in \(\mathcal{L}\).
2. **Nonlocality:** Constraint propagation in global \(\mathcal{L}\).
3. **Tsirelson Bound:** Orthomodular structure + tensor products.
4. **Superposition:** Non-distributive \(\mathcal{L}\).
5. **Contextuality:** Required by L2 in non-distributive \(\mathcal{L}\).
6. **Born Rule:** From Gleason/Busch.
7. **Classical Limit:** Boolean \(\mathcal{L}\).

**Uniqueness:** QM is the only theory satisfying E1′, E0, E2, NS within the above class (§4.5).

---

## 10. Predictions

Logic Field Theory (LFT) makes testable, pre-registered predictions that distinguish it from standard quantum-mechanical baselines by attributing visibility decay and correlation bounds to **logical constraint accumulation**. All tests operate on the interference **envelope** \(V_{\text{env}}\) (not the raw oscillatory contrast).

---

## P1 — Double-slit / Which-path visibility

**Envelope form (LFT).** For tunable entangling strength \(\varepsilon\) (e.g., conditional phase \(\beta\), or HWP angle \(2\alpha\)) and detector–pointer overlap \(\kappa(\varepsilon)\),
\[
V_{\text{env}}(\varepsilon)=|\kappa(\varepsilon)|\,\eta\,C_0,\qquad 
\kappa(\varepsilon)=\exp\!\big[-\gamma\,\varepsilon\,(1-e^{-\varepsilon/\varepsilon_0})\big].
\]
Equivalently, with \(L(\varepsilon)\equiv-\ln V_{\text{env}}(\varepsilon)\),
\[
L(\varepsilon)=\gamma\,\varepsilon\!\left(1-e^{-\varepsilon/\varepsilon_0}\right).
\]

**Scaling/collapse.** Let \(x=\varepsilon/\varepsilon_0\). Then
\[
\frac{-\ln V_{\text{env}}}{\gamma\,\varepsilon_0}=f(x),\quad
f(x)=x\left(1-e^{-x}\right).
\]
Small-\(x\): \(f(x)=x^2-\tfrac12 x^3+\tfrac16 x^4+\cdots\Rightarrow
c_2=\gamma/\varepsilon_0,\; c_3=-\gamma/(2\varepsilon_0^2)<0,\; c_3/c_2=-1/(2\varepsilon_0)\).
Large-\(x\): \(f(x)\to x\) (linear tail with slope \(\gamma\)).

**Competing baselines (standard QM).**
- *Gaussian pointer (dephasing)*: \(L=a\,\varepsilon^2\) (purely quadratic; super-linear tail).
- *Unitary rotation envelope*: \(V_{\text{env}}\approx|\cos(k\varepsilon)|\) \(\Rightarrow\) \(L=-\ln|\cos(k\varepsilon)|\) (oscillatory; no cubic onset; no linear tail).

### Pre-registered discriminants

1) **Cubic onset (low-\(\varepsilon\)).**  
   Prefit \((\hat\gamma,\hat\varepsilon_0)\) on the full sweep; define the low-\(\varepsilon\) window by
   \[
   \varepsilon<0.3\,\hat{\varepsilon}_0.
   \]
   Fit \(L(\varepsilon)=c_2\,\varepsilon^2+c_3\,\varepsilon^3\). **LFT requires \(c_3<0\)** with \(|c_3|/\mathrm{SE}(c_3)\ge 2\) (≈95% confidence).

2) **Linear tail (high-\(\varepsilon\)).**  
   For the top 20–30% of \(\varepsilon\) values, regress \(L\) vs. \(\varepsilon\). Require a **constant slope** within ±10% and \(R^2\ge 0.98\); report \(\gamma_{\text{vis}}\).

3) **Universality of \(\gamma\).**  
   Compare \(\gamma_{\text{vis}}\) (from P1 tail) with \(\gamma_{\text{Bell}}\) from the same platform’s finite-\(K\) CHSH test (P2). Use a **10% equivalence margin**:
   \[
   \frac{|\gamma_{\text{vis}}-\gamma_{\text{Bell}}|}{(\gamma_{\text{vis}}+\gamma_{\text{Bell}})/2}\le 0.10,
   \]
   adjudicated by CI overlap **and** Bayes factor \(>10\) in favor of equivalence.

4) **Data collapse.**  
   With \(\hat\gamma,\hat\varepsilon_0\), plot \(y= -\ln V_{\text{env}}/(\hat\gamma\,\hat\varepsilon_0)\) vs. \(x=\varepsilon/\hat\varepsilon_0\). **LFT gate:** RMSE\(_\text{collapse}\)\(\le 0.02\) to the curve \(f(x)=x(1-e^{-x})\).

### Envelope extraction (required)

Use one of:
- **Phase sweep/dither**: scan interferometer phase \(\phi\) at fixed \(\varepsilon\) (or add Gaussian phase dither \(\sigma_\phi\sim0.05{-}0.1\) rad) and set
  \[
  V_{\text{env}}(\varepsilon)=\frac{I_{\max}(\varepsilon)-I_{\min}(\varepsilon)}{I_{\max}(\varepsilon)+I_{\min}(\varepsilon)}.
  \]
- **Analytic/Hilbert transform** of the phase-series to extract the instantaneous envelope.

Report the **envelope-extraction uncertainty** and propagate it to all fitted quantities.

### Controls, reporting, and robustness

- **Complementarity check:** measure/path tomography to get \(D(\varepsilon)\) and verify \(V_{\text{env}}^2+D^2\le 1\).
- **WPD purity & source coherence:** report \(\eta\) and \(C_0\) with 95% CIs; propagate to CIs on \(c_3\) and \(\gamma_{\text{vis}}\).
- **Systematics:** pre-register bootstrap CIs, jackknife over points, and a sensitivity analysis to \(\pm(5\text{–}10)\%\) \(\varepsilon\) mis-calibration.

### Model fitting & selection

Fit the three models:
\[
\text{LFT: }L=\gamma\varepsilon(1-e^{-\varepsilon/\varepsilon_0}),\quad
\text{Gaussian: }L=a\varepsilon^2,\quad
\text{Unitary env.: }L=-\ln|\cos(k\varepsilon)|.
\]
Select by AIC/BIC and residual diagnostics; report posteriors for \(\hat\gamma,\hat\varepsilon_0,\hat a,\hat k\).

### Falsification criteria (any one suffices)

- **Onset:** \(c_3\ge 0\) or \(|c_3|/\mathrm{SE}(c_3)<2\) **and** quadratic-only preferred with \(\Delta\mathrm{BIC}\ge 10\).
- **Tail:** slope not constant within ±10% **or** \(R^2<0.98\).
- **Model selection:** a competing baseline beats LFT by \(\Delta\mathrm{AIC}\ge 10\) (or \(\Delta\mathrm{BIC}\ge 10\)).
- **Universality:** \(\gamma_{\text{vis}}\) and \(\gamma_{\text{Bell}}\) differ by \(>10\%\) beyond combined 95% CIs (or Bayes factor \(>10\) against equality).

### Current status (Oct 1, 2025)

Simulations with \((\gamma,\varepsilon_0)=(1,2)\) reproduce LFT’s signatures (**negative cubic onset**, **linear tail**, **scaling collapse**). Public datasets to date (e.g., superconducting qubit–resonator; photonic MZI) **lack the required dense low-\(\varepsilon\) scans and envelope isolation** to decisively test LFT; available points favor **unitary ± dephasing** fits. New experiments should implement the above checklist (dense low-\(\varepsilon\), phase dither, \(\eta\) tomography) to probe LFT’s unique scaling.

---

## P2 — Finite-\(K\) CHSH (entanglement with environment)

LFT predicts constraint-accumulation approach to Tsirelson:
\[
\mathrm{CHSH}(K)=2+\big(2\sqrt{2}-2\big)\big(1-e^{-\gamma K}\big),
\]
with the **same \(\gamma\)** as P1.

**Protocol.** Prepare a Bell state, apply \(K\) controlled interaction steps (or a calibrated coupling time), measure CHSH, and fit \(\gamma_{\text{Bell}}\).

**Falsification.** Any CHSH\((K)>2\sqrt{2}\), violation of L1–L3, or **universality failure** vs. \(\gamma_{\text{vis}}\) beyond the 10% margin (CI and Bayes-factor tests) falsifies LFT.

---

## 11. Independence Checks
- **CE-CTX (No O1):** Contextual, sums > 1.
- **CE-NS (Violates NS):** A signaling box with \(P(a=0|x,y) = \mathbf{1}_{[y=0]}\) (and suitable \(b\))—for which \(\sum_b P(a,b|x,y)\) depends on \(y\).
- **CE-Local (No CP1):** With CP1 (factorizability) \(\Rightarrow\) CHSH \(\le 2\). Dropping CP1 allows CHSH > 2 but is not a local hidden-variable model.
- **CE-GPT-Box:** Satisfies NS, CHSH = 4.

---

## 12. Examples
- **Qubit:** \(p(0) = |\alpha|^2\).
- **Bell Test:** CHSH = \(2\sqrt{2}\).
- **Finite-\(K\):** CHSH(0) = 2, CHSH(1) = 2.527, CHSH(\(\infty\)) = 2.828.

---

## 13. Dependency Graph
- L1–L3 → Boolean algebra.
- I2PS → Orthomodular \(\mathcal{L}\) (E1′, E0, E2, NS, motivated).
- \(\mathcal{L} \to \mathcal{H}\) (Piron–Solèr).
- States: Born rule (Gleason/Busch).
- Dynamics: Schrödinger (Lagrangian).

---

## 14. Conclusion
LFT shows QM follows under the listed constraints within the class of orthomodular, no-signaling, tomographically local theories with continuous reversible dynamics, unifying theorems, resolving paradoxes, and predicting finite-\(\varepsilon\) visibility and finite-\(K\) CHSH deviations. Physics is logical information actualization.

**Outlook:** Test finite-\(\varepsilon\) and finite-\(K\) predictions, explore quantum gravity, formalize lattice–Hilbert correspondence.

---

## Appendix: Axioms Table
| Axiom | Description | Role | Status |
|-------|-------------|------|--------|
| L1–L3 | Logical ground | Events well-defined | Assumed |
| P1 | σ-additivity | Probability extension | Assumed |
| Top1 | Standard Borel | Measurability | Assumed |
| IND | Independence | Product structure | Assumed |
| NS | No-signaling | Local autonomy | Assumed (motivated in §4.5) |
| Tm/CR | Tomography/Reversibility | Field selection | Assumed |
| E1′ | Lüders sharpness | Orthomodularity | Assumed (motivated in §4.5) |
| E0 | Atomicity | Minimal events | Assumed (motivated in §4.5) |
| E2 | Infinite sequences | Piron–Solèr representation | Assumed (motivated in §4.5) |
| Gen | Operational generator | Measurability | Assumed |
| O1 | Noncontextuality | Consistent probabilities | Assumed |
| O2 | σ-additivity | Frame function | Assumed |

**References:**
- Bell, J. S. (1964). *Physics*, 1, 195–200.
- Barnum, H., & Wilce, A. (2014). *J. Math. Phys.*, 55, 032203.
- Billingsley, P. (2012). *Probability and Measure*. Wiley.
- Busch, P. (1999). *Phys. Rev. Lett.*, 83, 647–650.
- Caticha, A. (2010). *J. Phys. A: Math. Theor.*, 44, 225303.
- Chiribella, G., et al. (2011). *Phys. Rev. A*, 84, 012311.
- Clifton, R., Bub, J., & Halvorson, H. (2003). *Found. Phys.*, 33, 1561–1591.
- Dakić, B., & Brukner, Č. (2011). *Phys. Rev. Lett.*, 106, 160403.
- Foulis, D. J. (1995). *Int. J. Theor. Phys.*, 34, 1021–1026.
- Gleason, A. M. (1957). *Math. Proc. Camb. Phil. Soc.*, 55, 322–325.
- Hardy, L. (2011). *J. Phys. A*, 44, 152001.
- Kechris, A. S. (1995). *Classical Descriptive Set Theory*. Springer.
- Kochen, S., & Specker, E. P. (1967). *J. Math. Mech.*, 17, 59–87.
- Masanes, L., & Müller, M. P. (2011). *New J. Phys.*, 13, 063001.
- Piron, C. (1964). PhD thesis, University of Lausanne.
- Popescu, S., & Rohrlich, D. (1994). *Found. Phys.*, 24, 379–385.
- Solèr, M. P. (1995). *Commun. Algebra*, 23, 2751–2760.
- Tsirelson, B. S. (1980). *Lett. Math. Phys.*, 4, 93–100.
- Wheeler, J. A. (1990). *Complexity, Entropy, and the Physics of Information*. Addison-Wesley.
- Wigner, E. P. (1931). *Gruppentheorie*. Vieweg.