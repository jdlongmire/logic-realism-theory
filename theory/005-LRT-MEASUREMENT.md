# The Measurement Problem Reframed: Actualization and the Quantum-Classical Interface

**Logic Realism Theory, Paper V**

James (JD) Longmire
Northrop Grumman Fellow (unaffiliated research)
ORCID: 0009-0009-1383-7698

---

## Abstract

The quantum measurement problem persists across interpretations because each presupposes that measurement is a physical process requiring a dynamical account within quantum mechanics itself. Logic Realism Theory (LRT) reframes the problem by locating measurement at the interface between two ontological domains: the information space $I_\infty$, where quantum states evolve unitarily as superpositions, and the actualized domain $A_\Omega$, where the action primitive $A$ selects determinate configurations subject to logical admissibility ($L_3$). Measurement is not collapse, branching, or epistemic update. It is the completion of actualization: the transition from partial to full determinacy under $A$. This paper develops the partial actualization framework, demonstrates its application to the double-slit experiment, Stern-Gerlach apparatus, and delayed-choice scenarios, and contrasts LRT's account with the Many-Worlds, Bohmian, spontaneous collapse, and QBist programs. Within the Hilbert-space framework imported from Hardy-Masanes-Muller reconstruction theorems, the formal machinery connecting Boolean actualization to projection-valued measures and the Born rule (established in Papers II and IV) supplies the quantitative backbone. We identify the actualization threshold, the lawful condition under which a degree of freedom enters the scope of $A$, as the principal open problem and propose avenues for experimental discrimination between LRT and competing accounts.

**Keywords:** measurement problem, quantum foundations, information ontology, logical realism, actualization, wave-function collapse, Born rule, partial actualization, quantum-classical interface

---

## 1. The Measurement Problem Stated

The measurement problem is not one problem but three entangled difficulties, each of which must be addressed by any adequate interpretation.

### 1.1 The Problem of Outcomes

Unitary quantum mechanics describes a closed system evolving under the Schrodinger equation:

$$i\hbar \frac{\partial}{\partial t} \lvert \psi(t) \rangle = H \lvert \psi(t) \rangle$$

This evolution is linear and deterministic. A system prepared in a superposition $\lvert \psi \rangle = \sum_i c_i \lvert a_i \rangle$ relative to an observable $\hat{A}$ remains in superposition under unitary evolution. Yet measurement always yields a single definite outcome $a_k$. The formalism does not contain a mechanism for selecting $a_k$ from among the $\{a_i\}$.

### 1.2 The Problem of the Preferred Basis

Even granting that one outcome occurs, nothing in the Hilbert space formalism singles out which observable is measured. Every state vector admits decomposition in infinitely many bases. The basis in which definite outcomes appear requires specification from outside the unitary dynamics.

### 1.3 The Problem of Statistics

The Born rule assigns probability $p(a_k) = \lvert \langle a_k \lvert \psi \rangle \rvert^2$ to each outcome. This rule is extraordinarily well-confirmed. Yet it is an additional postulate, not a consequence of the Schrodinger equation. Its status within each interpretation remains contested.

### 1.4 Why the Problem Persists

The measurement problem persists because every mainstream interpretation attempts to solve it *within* quantum mechanics:

- **Copenhagen** invokes a classical-quantum cut without specifying where it lies.
- **Many-Worlds** eliminates collapse but transfers the problem to the preferred basis and the meaning of probability in a deterministic branching structure.
- **Bohmian mechanics** adds hidden variables and a guidance equation, producing definite trajectories at the cost of nonlocality and the "surreal trajectories" problem.
- **GRW/CSL** modifies the Schrodinger equation with stochastic terms, introducing new constants ($\lambda_{\text{GRW}}$, $r_C$) that must be determined empirically.
- **QBism** reinterprets probabilities as personal degrees of belief, dissolving the problem pragmatically but leaving the ontology of outcomes unaddressed.

Each approach either relocates the problem or introduces elements whose justification is as puzzling as the original difficulty. LRT takes a different path: the measurement problem, as traditionally formulated, rests on a category error. It arises from attempting to account for the transition from possibility to actuality using only the resources available within the domain of possibility. The problem does not disappear. It is reclassified: the outstanding question is no longer "how does collapse happen?" but "what is the lawful condition under which a degree of freedom enters the scope of actualization?"

---

## 2. The LRT Ontological Framework

Logic Realism Theory grounds physical reality in three irreducible primitives, established in Papers 0 and I:

$$\chi \equiv [L_3 : I_\infty : A]$$

where:

- $L_3$ denotes the three laws of classical logic (Identity, Non-Contradiction, Excluded Middle) understood as ontological constraints on what can obtain.
- $I_\infty$ denotes the complete information space: the domain of all logically admissible configurations, each a determinate, distinguishable specification of possible state-content.
- $A$ denotes the actualization primitive: the irreducible operation by which configurations in $I_\infty$ become physically manifest in the actualized domain $A_\Omega$.

The bridge equation (Paper I, Section 6):

$$\chi \vdash A_\Omega = L_3(I_\infty)$$

establishes that actuality is constituted by logical constraint operating on the full information space. This is not a definition but an argued metaphysical identity: the structure of actuality is determined by the interaction of the three primitives.

### 2.1 Two Ontological Domains

LRT distinguishes two domains that are not spatially separated but ontologically distinct:

**$I_\infty$ (Information Space).** The domain of all $L_3$-admissible configurations. Quantum states $\lvert \psi \rangle$ are descriptions of configurations in $I_\infty$. Superposition, interference, and entanglement are features of this domain. Evolution within $I_\infty$ is unitary: the Schrodinger equation governs the lawful transformation of configurations that have not yet been fully actualized.

**$A_\Omega$ (Actualized Domain).** The domain of physically manifest configurations. Every configuration in $A_\Omega$ is determinate, Boolean, and logically admissible. Measurement outcomes, detector clicks, pointer positions, and all empirically accessible data belong to $A_\Omega$.

### 2.2 The Action Primitive

$A$ is Boolean:

$$A(E, c) \in \{1, 0\} \quad \text{for every event } E \text{ and configuration } c$$

where $1$ denotes "actual" and $0$ denotes "non-actual." There is no intermediate value. This is not a simplifying assumption but a consequence of $L_3$: Excluded Middle requires that every well-formed event either obtains or does not obtain. Non-Contradiction forbids that it both obtains and does not obtain in the same respect.

The Boolean character of $A$ is the fulcrum of the entire measurement account. It is what forces measurement outcomes to be definite, projection operators to be idempotent, and the Born rule to emerge as the unique probability measure over projection-valued measures (Paper II, Steps 4-6).

---

## 3. Partial Actualization

The central innovation of LRT's measurement account is the concept of *partial actualization*: a configuration may be actualized with respect to some properties while remaining in $I_\infty$ with respect to others.

### 3.1 The Concept

Consider a photon emitted by an atom. At the moment of emission, certain properties become determinate:

| Actualized at emission | Remains in $I_\infty$ |
|------------------------|----------------------|
| Existence (photon, not vacuum) | Position during propagation |
| Frequency $\nu$ (energy $E = h\nu$) | Which slit (in a double-slit setup) |
| Polarization state | Detection location |
| Propagation direction | Arrival time at detector |

The photon is *partially actualized*: its energy and polarization are elements of $A_\Omega$, while its spatial degrees of freedom remain configurations in $I_\infty$ evolving unitarily under the free-field Hamiltonian.

### 3.2 Formal Statement

Let $\mathcal{P} = \{P_1, P_2, \ldots, P_n\}$ be the set of physical properties characterizing a quantum system. A configuration $c$ is *fully actualized* if $A(P_i, c) \in \{0, 1\}$ for all $P_i \in \mathcal{P}$. A configuration is *partially actualized* if there exists a proper subset $\mathcal{S} \subset \mathcal{P}$ such that $A(P_i, c)$ is determinate for $P_i \in \mathcal{S}$ and the remaining properties $P_j \in \mathcal{P} \setminus \mathcal{S}$ remain as superpositions in $I_\infty$.

The partition into actualized and unactualized properties is not arbitrary. It is governed by the following criterion:

**Actualization Partition Rule.** A property $P_i$ is actualized in an interaction if and only if the interaction Hamiltonian $H_{\text{int}}$ couples $P_i$ to a macroscopic degree of freedom in a manner that produces a stable, irreversible record. Properties not so coupled remain in $I_\infty$.

More precisely: an emission event actualizes the properties that are eigenvalues of operators commuting with $H_{\text{int}}$ and whose values are fixed by the conservation laws governing the interaction. A photon's frequency is actualized at emission because the atomic transition Hamiltonian fixes $\Delta E = h\nu$ via energy conservation. Position is not actualized because the emission Hamiltonian does not couple position to any conserved quantity of the emitting system. The remaining degrees of freedom continue their unitary evolution in $I_\infty$.

This criterion is programmatic rather than fully derived. A complete derivation from $L_3$, $I_\infty$, and $A$ remains an open target (Section 9.1). But the criterion is not ad hoc: it tracks the physical structure of the interaction rather than being tailored to fit experimental outcomes after the fact.

### 3.3 Measurement as Completion of Actualization

Measurement, under LRT, is the process by which $A$ completes the actualization of a partially actualized configuration. Specifically:

**Definition.** A *measurement* of property $P_j$ on a partially actualized system is an interaction (described by a Hamiltonian $H_{\text{int}}$) that brings $P_j$ into the scope of $A$'s Boolean selection. After measurement, $A(P_j, c) \in \{0, 1\}$ is determinate.

This is not a dynamical modification of the Schrodinger equation. Unitary evolution continues to govern the system's trajectory through $I_\infty$ right up to the point of actualization. The transition from superposition to definite outcome is not a process *within* $I_\infty$ but a transition *from* $I_\infty$ *to* $A_\Omega$ for the relevant property.

### 3.4 Why This Is Not Collapse

Standard collapse interpretations treat the transition $\lvert \psi \rangle \to \lvert a_k \rangle$ as a dynamical event: something happens to the quantum state at the moment of measurement. This generates the measurement problem because the dynamical event is incompatible with unitary evolution.

LRT does not modify the quantum state's evolution. The state $\lvert \psi \rangle$ in $I_\infty$ evolves unitarily at all times. What changes at measurement is not the state but the *ontological status* of the relevant property: it transitions from the domain of possibility ($I_\infty$) to the domain of actuality ($A_\Omega$). The state vector is a description of configurations in $I_\infty$; it is not a physical object that "collapses."

The apparent discontinuity between pre-measurement superposition and post-measurement definiteness is an artifact of conflating two ontological levels. Within $I_\infty$, evolution is continuous. Within $A_\Omega$, outcomes are Boolean. The discontinuity exists at the *interface*, not within either domain.

---

## 4. The Double-Slit Experiment

The double-slit experiment crystallizes every aspect of the measurement problem. LRT's resolution is correspondingly precise.

### 4.1 Setup

A source emits particles (photons, electrons, neutrons) one at a time toward a barrier with two slits, $S_1$ and $S_2$. A detection screen records arrival positions. Without which-path detection, an interference pattern forms. With which-path detection, the interference pattern vanishes and two single-slit distributions appear.

### 4.2 LRT Analysis: No Which-Path Detection

**At emission.** $A$ actualizes the particle's existence, energy, and propagation direction (toward the barrier). Position relative to the slits is not actualized: the spatial degree of freedom remains in $I_\infty$.

**At the barrier.** Because which-slit is not actualized, the particle's spatial configuration in $I_\infty$ includes both paths. The state in $I_\infty$ is:

$$\lvert \psi \rangle = \frac{1}{\sqrt{2}} \bigl( \lvert S_1 \rangle + e^{i\phi} \lvert S_2 \rangle \bigr)$$

This is not a claim about the particle being "in two places at once." It is a description of the spatial configuration's status in $I_\infty$: both slit-passages are $L_3$-admissible configurations, and $A$ has not yet selected between them because no interaction has brought which-slit into the scope of Boolean selection.

**Propagation to the screen.** The state evolves unitarily in $I_\infty$. The two path-amplitudes acquire position-dependent phases, producing the interference structure:

$$\psi(x) = \psi_1(x) + e^{i\phi} \psi_2(x)$$

The probability distribution over detection positions follows from the Born rule:

$$p(x) = \lvert \psi(x) \rvert^2 = \lvert \psi_1(x) \rvert^2 + \lvert \psi_2(x) \rvert^2 + 2\,\text{Re}\bigl[\psi_1^*(x)\, e^{i\phi}\, \psi_2(x)\bigr]$$

The cross-term is the interference contribution. It exists because position remains in $I_\infty$, where superposition is the natural mode of existence.

**At detection.** The interaction between the particle and the detector screen brings position into the scope of $A$. The detector's interaction Hamiltonian $H_{\text{det}}$ couples the particle's spatial degree of freedom to macroscopic detector states. $A$ completes the actualization: one position $x_k$ is selected, and $A(\text{position} = x_k, c) = 1$.

Over many trials, the distribution of actualized positions reproduces the interference pattern. Interference is a feature of $I_\infty$; detection is a feature of $A_\Omega$. The Born rule mediates between them.

### 4.3 LRT Analysis: With Which-Path Detection

Now place a which-path detector at the slits.

**At the barrier.** The which-path detector's interaction Hamiltonian couples the particle's slit-passage to a macroscopic detector state. This interaction brings which-slit into the scope of $A$. The spatial degree of freedom is now actualized at the barrier rather than at the screen.

The state after which-path detection is:

$$A(\text{slit} = S_k, c) = 1 \quad \text{for some } k \in \{1, 2\}$$

The particle passes through one definite slit. The subsequent propagation to the screen is that of a single-slit diffraction pattern. No interference cross-term arises because there is no superposition of paths in $I_\infty$: which-path has already been actualized.

### 4.4 The Complementarity Principle Grounded

Bohr's complementarity principle states that wave and particle behaviors are mutually exclusive but jointly exhaustive descriptions. LRT grounds this principle ontologically:

- **Wave behavior** (interference) manifests when the relevant degree of freedom remains in $I_\infty$, where superposition and phase coherence obtain.
- **Particle behavior** (definite trajectory) manifests when the relevant degree of freedom has been actualized into $A_\Omega$, where Boolean definiteness obtains.

The two behaviors are mutually exclusive because a property cannot simultaneously be in $I_\infty$ (superposed) and in $A_\Omega$ (definite). They are jointly exhaustive because every property is in one domain or the other. Complementarity is not a philosophical gloss on the formalism; it is a structural consequence of the $I_\infty / A_\Omega$ distinction.

---

## 5. Stern-Gerlach

The Stern-Gerlach experiment measures spin, a property with no classical analogue. It is the paradigm case for the preferred basis problem.

### 5.1 Setup

A beam of spin-$\frac{1}{2}$ particles (e.g., silver atoms) passes through an inhomogeneous magnetic field oriented along $\hat{z}$. The beam splits into two components, detected at spatially separated positions corresponding to $\lvert +z \rangle$ and $\lvert -z \rangle$.

### 5.2 LRT Analysis

**Before the magnet.** The atom is partially actualized: its existence, mass, charge, and momentum (toward the apparatus) are in $A_\Omega$. Its spin projection along $\hat{z}$ is not actualized. If the atom was prepared in a general spin state $\lvert \psi \rangle = \alpha \lvert +z \rangle + \beta \lvert -z \rangle$, this superposition describes the spin configuration in $I_\infty$.

**In the magnetic field.** The interaction Hamiltonian $H_{\text{SG}} = -\mu \cdot B(z)$ couples the spin degree of freedom to the atom's spatial trajectory. The gradient $\partial B_z / \partial z$ produces spin-dependent forces, entangling spin with position:

$$\lvert \Psi \rangle = \alpha \lvert +z \rangle \otimes \lvert \text{up} \rangle + \beta \lvert -z \rangle \otimes \lvert \text{down} \rangle$$

At this stage, the spin-position entanglement is a configuration in $I_\infty$. No actualization of spin has occurred.

**At the detector.** The detector interaction brings spin-correlated position into the scope of $A$. Since spin and position are entangled, actualizing position simultaneously actualizes spin:

$$A(\text{position} = \text{up}, c) = 1 \implies A(\text{spin} = +z, c) = 1$$

The outcome is Boolean: one definite spin value, one definite position. The probability is $p(+z) = \lvert \alpha \rvert^2$, given by the Born rule.

### 5.3 Preferred Basis Resolved

The preferred basis problem asks: why does the measurement yield outcomes in the $\hat{z}$-basis rather than some other basis?

LRT's answer: the interaction Hamiltonian $H_{\text{SG}}$ determines which observable is coupled to macroscopic degrees of freedom. The magnetic field gradient along $\hat{z}$ makes $\hat{z}$-spin the observable whose eigenstates correlate with spatially separated detector positions. $A$ selects outcomes from the PVM determined by the interaction, not from an arbitrary basis.

Rotate the magnet to $\hat{x}$: the interaction Hamiltonian changes, the PVM changes, and outcomes appear in the $\hat{x}$-basis. The preferred basis is physically determined by the apparatus, not metaphysically imposed by interpretation.

---

## 6. Delayed-Choice Experiments

Wheeler's delayed-choice experiment and its quantum eraser variants pose a sharpened challenge: the "choice" of what to measure can be made after the particle has passed through the slits. This has been taken to imply retrocausation or the absence of any objective reality prior to measurement.

### 6.1 Wheeler's Delayed Choice

A photon passes through a beam splitter toward two paths. After the photon has entered the interferometer, the experimenter decides whether to insert a second beam splitter (wave test, producing interference) or leave it out (particle test, producing which-path information).

**LRT analysis.** The photon's which-path property is not actualized at the first beam splitter. It remains in $I_\infty$ throughout propagation. The "delayed choice" determines which interaction Hamiltonian governs the detector stage:

- **Second beam splitter inserted:** The detection interaction preserves superposition of paths, and $A$ actualizes an interference-pattern position. Which-path was never actualized.
- **No second beam splitter:** The detection interaction brings which-path into the scope of $A$, and a definite path is actualized.

No retrocausation is required. The photon's path was never actualized prior to detection. The delayed choice determines *which property* enters the scope of $A$, not the photon's past. The past is not rewritten because there was no fact of the matter about which-path to rewrite.

### 6.2 Quantum Eraser

In the quantum eraser (Scully and Druhl, 1982; Kim et al., 2000), which-path information is first encoded in an ancillary system and then "erased" by measuring the ancilla in a complementary basis. Post-selection on the ancilla measurement recovers the interference pattern.

**LRT analysis.** Encoding which-path information in the ancilla entangles the two systems, creating a joint configuration in $I_\infty$:

$$\lvert \Psi \rangle = \frac{1}{\sqrt{2}} \bigl( \lvert S_1 \rangle \lvert \text{mark}_1 \rangle + \lvert S_2 \rangle \lvert \text{mark}_2 \rangle \bigr)$$

At this stage, which-path is potentially actualizable: measuring the ancilla in the $\{\lvert \text{mark}_1 \rangle, \lvert \text{mark}_2 \rangle\}$ basis would actualize which-path and destroy interference. Measuring the ancilla in a complementary basis (the "eraser" measurement) brings a different observable into the scope of $A$, one that does not distinguish paths. Post-selection on the eraser outcome recovers the interference subensemble because, for those particles, which-path was never actualized.

The "erasure" does not undo a fact. It prevents a fact from being established. No which-path information was actualized; it was merely *available for actualization* in $I_\infty$.

---

## 7. Contrasts with Other Interpretations

### 7.1 Many-Worlds Interpretation

**MWI claim.** All outcomes occur; the universe branches at every measurement. There is no collapse.

**LRT contrast.** LRT agrees that unitary evolution is not interrupted. But LRT denies that all branches are actualized. $A$ selects one outcome: the one that obtains in $A_\Omega$. The other branches remain as configurations in $I_\infty$, which is to say they remain as possibilities that were not actualized. LRT preserves the deterministic evolution of $\lvert \psi \rangle$ without the ontological extravagance of universal branching.

MWI faces two problems that LRT does not:
1. **The probability problem.** In a deterministic branching universe, the meaning of $p(a_k) = \lvert c_k \rvert^2$ is obscure. Decision-theoretic derivations (Deutsch, Wallace) require substantive assumptions about rational agents. LRT grounds the Born rule ontologically: within the admitted Hilbert-space framework, $A$'s Boolean character forces projection structure, and Gleason's theorem yields the Born rule as the unique measure (Paper II, Step 6), without invoking agents or decisions.
2. **The preferred basis problem.** MWI typically appeals to decoherence to select the branching basis. But decoherence is a dynamical process within unitary evolution; it does not produce outcomes. LRT locates basis selection in the interaction Hamiltonian that determines which PVM enters the scope of $A$.

### 7.2 Bohmian Mechanics

**Bohmian claim.** Particles always have definite positions, guided by the wave function via the guidance equation $\dot{q}_k = \frac{\hbar}{m_k} \text{Im} \frac{\nabla_k \Psi}{\Psi}$.

**LRT contrast.** LRT agrees that measurement outcomes are definite. But LRT does not privilege position as the only always-definite observable. In LRT, *which* properties are actualized depends on the physical interaction history. A photon's energy may be actualized while its position is not. A spin may be actualized while momentum is not. The ontology is property-specific, not position-privileged.

Bohmian mechanics also faces the "surreal trajectories" problem (Englert, Scully, Sussmann, Walther, 1992): the Bohmian trajectories in certain interferometric setups do not match the paths the particles "seem" to follow. LRT avoids this because it does not posit hidden trajectories. A particle's position is either actualized (in $A_\Omega$, definite) or not (in $I_\infty$, no trajectory to be surreal about).

### 7.3 Spontaneous Collapse (GRW/CSL)

**GRW/CSL claim.** The Schrodinger equation is approximate. Stochastic terms cause spontaneous localization with rate $\lambda_{\text{GRW}} \approx 10^{-16}$ s$^{-1}$ per particle and localization width $r_C \approx 10^{-7}$ m.

**LRT contrast.** GRW/CSL modifies the fundamental dynamics. LRT does not. Unitary evolution is exact in LRT; the appearance of "collapse" is a feature of the $I_\infty \to A_\Omega$ interface, not a correction to the Schrodinger equation. LRT therefore predicts that no experiment will detect deviations from unitarity in isolated quantum systems, regardless of system size.

GRW/CSL also introduces two free parameters ($\lambda_{\text{GRW}}$, $r_C$) whose values are chosen to match observation rather than derived from principle. LRT's quantitative predictions depend on identifying the actualization threshold (Section 9), but the qualitative account requires no free parameters: $A$ is Boolean, and the interaction Hamiltonian determines the PVM.

### 7.4 QBism

**QBist claim.** Quantum states represent an agent's personal degrees of belief. Measurement "outcomes" are experiences of the agent, not objective events.

**LRT contrast.** LRT is realist. Measurement outcomes are objective configurations in $A_\Omega$, not agent-relative experiences. The Born rule probabilities are objective dispositional properties of states in $I_\infty$ with respect to $A$'s selection (Paper II, Section 4.2):

$$p(E \mid \psi) = \text{Tr}(\rho P_E)$$

is the objective disposition of configuration $\psi$ toward outcome $E$ under actualization. This is not a betting coefficient, not a frequency over an ensemble, and not a personal credence. It is a feature of the ontology.

QBism dissolves the measurement problem by denying that there is an objective problem to solve. LRT renders it intelligible by providing the ontological structure within which objective outcomes are categorically distinct from the superpositions that precede them.

### 7.5 Summary of Contrasts

| Feature | Copenhagen | MWI | Bohm | GRW | QBism | **LRT** |
|---------|-----------|-----|------|-----|-------|---------|
| Definite outcomes | Postulated | All occur | Always (position) | Dynamical | Agent-relative | $A$-selected |
| Collapse | Postulated | None | None | Modified dynamics | Belief update | Ontological transition (thesis under evaluation) |
| Preferred basis | Classical cut | Decoherence + environment | Position | Localization width | N/A | Interaction $H$ |
| Born rule status | Postulate | Derived (debated) | Postulate | Approximately derived | Normative | Grounded (Gleason, given $\mathcal{H}$) |
| Free parameters | Cut location | None (basis problem open) | None | $\lambda$, $r_C$ | None | Threshold (open) |
| Unitarity | Approximate | Exact | Exact | Approximate | N/A | Exact |
| Realist? | Ambiguous | Yes (branches) | Yes (particles) | Yes | No | Yes (configurations) |

*Table 1. Interpretive comparison. Each entry compresses substantial internal debate. "Grounded" for LRT's Born rule means: ontologically motivated within an imported Hilbert-space framework, not derived from LRT primitives alone. "Ontological transition" is LRT's thesis, not a settled result.*

---

## 8. The Formal Backbone

The qualitative account of Sections 3-6 rests on formal results established in Paper II and verified in Lean 4. This section summarizes the chain from $A$'s Boolean character to the Born rule.

### 8.1 Boolean Actualization Forces Projection Structure

From the Boolean character of $A$ and $L_3$:

1. **All events are sharp.** $L_3$ (Excluded Middle) requires that every event $E$ applied to any configuration $c$ has a determinate truth value. There are no fuzzy events in LRT.

2. **Event evaluation is binary.** $A(E, c) \in \{1, 0\}$ for all events $E$ and configurations $c$.

3. **Eigenvalue restriction.** If an event operator $\hat{E}$ represents the observable corresponding to event $E$, its eigenvalues must lie in $\{0, 1\}$ (since eigenvalues correspond to possible measurement outcomes, and $A$ permits only Boolean outcomes).

4. **Projection operators.** A self-adjoint operator with spectrum $\subseteq \{0, 1\}$ satisfies $\hat{E}^2 = \hat{E}$: it is a projection. Therefore, event operators are projection operators.

5. **PVM structure.** A complete set of mutually exclusive events $\{E_i\}$ satisfying $\sum_i \hat{E}_i = \mathbb{I}$ constitutes a projection-valued measure (PVM).

This chain (Paper II, Steps 4-5; Lean files `Step4/Boolean.lean`, `Step5/EigenvalueRestriction.lean`) is verified in Lean 4.

### 8.2 PVM Structure Forces the Born Rule

Given PVM structure over a complex Hilbert space of dimension $d \geq 3$:

6. **Frame function axioms from $L_3$.** Normalization from Excluded Middle (completeness: $\sum p(P_i) = 1$). Basis independence from Identity (physical state is independent of descriptive basis). Additivity from Non-Contradiction (orthogonal projectors represent exclusive outcomes).

7. **Gleason's theorem.** The unique probability measure over PVMs on $\mathcal{H}$ with $\dim \geq 3$ is $\mu(P) = \text{Tr}(\rho P)$ for some density operator $\rho$.

8. **Born rule.** For a pure state $\rho = \lvert \psi \rangle \langle \psi \rvert$:

$$p(a_k) = \text{Tr}(\lvert \psi \rangle \langle \psi \rvert P_k) = \lvert \langle a_k \lvert \psi \rangle \rvert^2$$

Within the Hilbert-space framework imported from Hardy-Masanes-Muller reconstruction theorems, the Born rule is not an independent postulate. It is the unique probability assignment consistent with the projection structure that $A$'s Boolean character forces onto the admitted Hilbert space, via Gleason's theorem (Paper II, Step 6; Lean file `Step6_BornRule.lean`). The ontological grounding is LRT's contribution; the Hilbert-space machinery on which Gleason's theorem operates is imported, not derived from the primitives alone.

### 8.3 Unitarity and Dynamics

Unitary evolution (Paper II, Steps 7-8) governs configurations in $I_\infty$. Stone's theorem yields the Schrodinger equation from the requirement that evolution forms a strongly continuous one-parameter group of unitary operators:

$$U(t) = e^{-iHt/\hbar}$$

Unitarity is exact. $A$ does not interrupt or modify unitary evolution. The Schrodinger equation governs the evolution of configurations in $I_\infty$; $A$ governs the transition from $I_\infty$ to $A_\Omega$.

---

## 9. Open Problems and Experimental Signatures

### 9.1 The Actualization Threshold

The principal open problem in LRT's measurement account is quantitative: *what determines when a property enters the scope of $A$?*

The qualitative answer is clear: the interaction Hamiltonian couples the quantum degree of freedom to macroscopic detector states, bringing the relevant observable into the domain where $A$ operates. But the threshold, if one exists, is not yet derived from the primitives.

**Candidate criteria:**

1. **Entanglement threshold.** Actualization occurs when the entanglement entropy $S(\rho_{\text{sys}})$ between the quantum system and the measuring apparatus exceeds a critical value $S_c$. This would make actualization a function of the system-environment coupling strength.

2. **Information-theoretic criterion.** Actualization occurs when the mutual information $I(\text{sys} : \text{env})$ becomes sufficient to distinguish outcomes at the macroscopic level.

3. **Irreversibility criterion.** Actualization occurs when the interaction has produced sufficient decoherence that the interference terms are suppressed below a threshold related to the precision of any feasible reversal operation.

Each candidate must satisfy two constraints: (a) it must be derivable from or at least consistent with $L_3$, $I_\infty$, and $A$; (b) it must reproduce the empirically observed timescales of quantum-to-classical transition.

### 9.2 Avenues for Experimental Discrimination

LRT's commitments generate empirical expectations, some of which overlap with standard quantum mechanics plus decoherence, and some of which produce sharper forks against specific competitors. The following are ordered by discriminating power.

**Fork 1: Exact unitarity (discriminates against GRW/CSL).**
Unlike GRW/CSL, LRT predicts that no deviations from unitary evolution will be found in isolated quantum systems, regardless of system size. Experiments testing spontaneous collapse models (e.g., LISA Pathfinder bounds, optomechanical oscillators, molecular interferometry) should find null results. This is the cleanest experimental fork: detection of spontaneous collapse signatures falsifies LRT's measurement account; continued null results increasingly constrain GRW/CSL while leaving LRT unaffected.

**Fork 2: Interaction-dependent basis (discriminates against pure-decoherence accounts).**
The preferred measurement basis is always determined by the physical interaction Hamiltonian, not by decoherence alone. In principle, an experiment could prepare a system in a regime where decoherence selects one basis but the interaction Hamiltonian selects another, testing whether outcomes follow the decoherence basis or the interaction basis. This is sharper in principle than in current experimental practice, but it identifies a genuine point of divergence.

**Consonance 1: No hidden variables.**
LRT expects Bell-inequality violations, Kochen-Specker contextuality, and Leggett-Garg inequality violations, since unactualized properties are genuinely indeterminate (not merely unknown). These results are consonant with LRT but not distinctly diagnostic of it: standard quantum mechanics without hidden variables produces the same expectations.

**Consonance 2: State-dependent decoherence consistency.**
If the actualization threshold is related to entanglement entropy, then the decoherence timescale $T_2$ should scale predictably with the system-environment coupling strength across different physical platforms (superconducting qubits, trapped ions, NV centers, molecular systems). Cross-platform consistency in the relationship between $T_2/T_1$ ratios and coupling parameters would support an information-theoretic actualization threshold. This is a research avenue, not yet a sharp discriminator.

### 9.3 Discriminating LRT from GRW/CSL

The sharpest experimental contrast is with spontaneous collapse models. GRW/CSL predicts measurable deviations from unitary evolution: an excess heating rate proportional to $\lambda_{\text{GRW}}$, anomalous diffusion in free particles, and a mass-dependent collapse rate. Current bounds (Vinante et al., 2020; Donadi et al., 2021) are approaching the GRW parameter space.

LRT predicts none of these effects. If spontaneous collapse signatures are detected, LRT's measurement account is falsified. If they are not, GRW/CSL is increasingly constrained while LRT remains unaffected. This is a clean experimental fork.

---

## 10. Discussion

### 10.1 What LRT Achieves

The measurement problem, as traditionally formulated, asks: how does a definite outcome emerge from a superposition? The question presupposes that the superposition and the outcome exist in the same ontological domain and that some dynamical process must connect them.

LRT denies the presupposition. Superposition and definite outcome belong to different ontological domains: $I_\infty$ and $A_\Omega$, respectively. The transition between them is not a dynamical process but an ontological one: the completion of actualization under $A$. The measurement problem is rendered intelligible, not by producing a new dynamical mechanism, but by reclassifying the question: the remaining burden is not "how does collapse happen?" but "what is the lawful condition under which a degree of freedom enters the scope of $A$?"

This is a genuine reclassification, not merely a relabeling. The distinction between dynamical collapse (a process within the Schrodinger evolution) and ontological transition (a change in the domain-membership of a property) is substantive: it eliminates the formal contradiction between unitary evolution and definite outcomes, which is the core of the measurement problem. What it does not yet eliminate is the need for a triggering condition. That residual burden is addressed in Section 9.1 as an open problem.

### 10.2 What LRT Does Not Achieve

**The relabeling objection.** A critic will say: "You have not dissolved measurement. You have renamed collapse as actualization and relocated it into a metaphysical primitive." This objection has force, and the paper must answer it directly. The answer is that LRT's ontological transition differs from collapse in a specific structural way: collapse is a modification of the quantum state within a single domain (interrupting unitary evolution), while actualization is a change in domain-membership that leaves unitary evolution intact. The formal contradiction between Schrodinger dynamics and definite outcomes, which is the measurement problem proper, does not arise under LRT. What does arise is a new question: what governs the scope of $A$? That question is open. But it is a different question from the one the measurement problem poses, and its answer need not violate unitarity. Whether this structural difference is sufficient to count as more than relabeling is a judgment the community must make. This paper argues that it is.

**The actualization threshold.** LRT does not yet specify the quantitative condition under which a degree of freedom enters the scope of $A$. The qualitative account is complete: partial actualization, interaction-determined PVMs, Boolean selection, Born-rule statistics. The quantitative account awaits either a derivation of the threshold from the primitives or an empirical determination that constrains the candidates (Section 9.1).

**Hilbert-space import.** LRT does not derive the specific Hilbert-space structure (complex field, dimensionality) from its primitives alone. These are imported from the Hardy-Masanes-Muller reconstruction theorems (Paper II, Step 4), which LRT grounds in the primitives but does not independently derive. Claims about the Born rule throughout this paper should be read accordingly: LRT supplies ontological grounding for why the relevant measure must be Born-type, given the admitted Hilbert-space framework.

### 10.3 The Ontological Economy

LRT introduces no new dynamical equations, no hidden variables, no additional physical constants, and no branching universes. It introduces three ontological primitives ($L_3$, $I_\infty$, $A$) and the distinction between two domains ($I_\infty$ and $A_\Omega$). Given the Hilbert-space framework imported from reconstruction theorems, the measurement formalism, including projection structure, the Born rule, and basis selection, follows from these primitives without further postulates specific to measurement.

Whether this counts as more or less economical than the alternatives depends on one's tolerance for metaphysics. LRT trades a physics problem (the measurement problem as dynamical contradiction) for a metaphysical framework (the primitives) plus a new open problem (the actualization threshold). The framework is argued, not arbitrary (Paper I). Whether the trade is worth making is a question for the community.

---

## 11. Conclusion

The measurement problem has resisted solution for nearly a century because each interpretation has sought a dynamical resolution within the quantum formalism itself. LRT reframes the problem by recognizing that measurement is not a dynamical process but an ontological transition: the completion of actualization under the Boolean action primitive $A$, mediated by the interaction Hamiltonian that determines the relevant projection-valued measure. This reframing eliminates the formal contradiction between unitary evolution and definite outcomes. It does not eliminate the need for a lawful account of when actualization occurs.

Partial actualization, the possibility that a configuration may be actualized with respect to some properties while remaining in $I_\infty$ with respect to others, provides a unified account of interference, which-path complementarity, delayed choice, and quantum erasure. Within the Hilbert-space framework imported from reconstruction theorems, the Born rule is grounded as the unique probability measure over PVMs via Gleason's theorem, ontologically motivated by $A$'s Boolean character. Unitarity is exact. The preferred basis is physically determined by the interaction Hamiltonian.

The principal open problem is the actualization threshold: the lawful condition under which a degree of freedom enters the scope of $A$. Resolving this problem, whether by derivation from the primitives or by empirical determination, is the natural next step. Until it is resolved, LRT offers a coherent ontological interpretation of measurement rather than a completed dissolution. That is still a contribution: it reclassifies the remaining burden and renders the measurement problem intelligible within a realist framework that preserves exact unitarity.

---

## References

Bennett, C.H. (2003). Notes on Landauer's principle, reversible computation, and Maxwell's Demon. *Studies in History and Philosophy of Modern Physics*, 34(3), 501-510.

Bohm, D. (1952). A suggested interpretation of the quantum theory in terms of "hidden" variables. *Physical Review*, 85(2), 166-193.

Chiribella, G., D'Ariano, G.M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Deutsch, D. (1999). Quantum theory of probability and decisions. *Proceedings of the Royal Society of London A*, 455(1988), 3129-3137.

Donadi, S., Piscicchia, K., Curceanu, C., et al. (2021). Underground test of gravity-related wave function collapse. *Nature Physics*, 17, 74-78.

Englert, B.-G., Scully, M.O., Sussmann, G., and Walther, H. (1992). Surreal Bohmian trajectories. *Zeitschrift fur Naturforschung A*, 47(12), 1175-1186.

Everett, H. (1957). "Relative state" formulation of quantum mechanics. *Reviews of Modern Physics*, 29(3), 454-462.

Fuchs, C.A. and Schack, R. (2013). Quantum-Bayesian coherence. *Reviews of Modern Physics*, 85(4), 1693-1715.

Ghirardi, G.C., Rimini, A., and Weber, T. (1986). Unified dynamics for microscopic and macroscopic systems. *Physical Review D*, 34(2), 470-491.

Gleason, A.M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885-893.

Hardy, L. (2001). Quantum theory from five reasonable axioms. *arXiv:quant-ph/0101012*.

Kim, Y.-H., Yu, R., Kulik, S.P., Shih, Y., and Scully, M.O. (2000). Delayed "choice" quantum eraser. *Physical Review Letters*, 84(1), 1-5.

Masanes, L. and Muller, M.P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Scully, M.O. and Druhl, K. (1982). Quantum eraser: A proposed photon correlation experiment concerning observation and "delayed choice" in quantum mechanics. *Physical Review A*, 25(4), 2208-2213.

Vinante, A., Mezzena, R., Falferi, P., Carlesso, M., and Bassi, A. (2020). Improved noninterferometric test of collapse models using ultracold cantilevers. *Physical Review Letters*, 125(10), 100404.

von Neumann, J. (1932). *Mathematische Grundlagen der Quantenmechanik*. Berlin: Springer.

Wallace, D. (2012). *The Emergent Multiverse: Quantum Theory According to the Everett Interpretation*. Oxford: Oxford University Press.

Wheeler, J.A. (1984). Law without law. In J.A. Wheeler and W.H. Zurek (Eds.), *Quantum Theory and Measurement* (pp. 182-213). Princeton: Princeton University Press.

Zurek, W.H. (2003). Decoherence, einselection, and the quantum origins of the classical. *Reviews of Modern Physics*, 75(3), 715-775.
