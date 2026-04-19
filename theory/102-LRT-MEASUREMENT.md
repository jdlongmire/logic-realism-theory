# The Measurement Problem Reframed: Actualization and the Quantum-Classical Interface

**Logic Realism Theory, Paper V**

James (JD) Longmire
Northrop Grumman Fellow (unaffiliated research)
ORCID: 0009-0009-1383-7698

---

## Abstract

The quantum measurement problem persists across interpretations because each presupposes that measurement is a physical process requiring a dynamical account within quantum mechanics itself. Logic Realism Theory (LRT) reframes the problem by locating measurement at the interface between two ontological domains: the information space $I_\infty$, where quantum states evolve unitarily as superpositions, and the actualized domain $A_\Omega$, where the action primitive $A$ selects determinate configurations subject to logical admissibility ($L_3$). Measurement is not collapse, branching, or epistemic update. It is the completion of actualization: the transition from partial to full determinacy under $A$. This paper develops the partial actualization framework, demonstrates its application to the double-slit experiment, Stern-Gerlach apparatus, and delayed-choice scenarios, and contrasts LRT's account with the Many-Worlds, Bohmian, spontaneous collapse, and QBist programs. Within the Hilbert-space framework imported from Hardy-Masanes-Muller reconstruction theorems, the formal machinery connecting Boolean actualization to projection-valued measures and the Born rule (established in Papers II and IV) supplies the quantitative backbone. We identify the actualization threshold as the pointer-basis stability condition determined by the system-environment interaction Hamiltonian $H_{SE}$: the decoherence timescale $\tau_D \sim \gamma_{SE}^{-1}$, calculable from coupling constants and environmental spectral density, fixes when a degree of freedom becomes $L_3$-evaluable. LRT contributes no free parameters to this determination: a feature, not a gap. We propose avenues for experimental discrimination between LRT and competing accounts.

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

Each approach either relocates the problem or introduces elements whose justification is as puzzling as the original difficulty. LRT takes a different path: the measurement problem, as traditionally formulated, rests on a category error. It arises from attempting to account for the transition from possibility to actuality using only the resources available within the domain of possibility. The problem does not disappear. It is reclassified: the outstanding question is no longer "how does collapse happen?" but "under what lawful condition does a degree of freedom enter the scope of actualization?", a question to which LRT provides a definite answer (Section 9.1)

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

A clarification on the role of irreversibility: "stable, irreversible record" is an *empirical marker* of scope-entry, not the metaphysical ground of actualization. The ground is $A$ itself, operating under $L_3$ constraint. Irreversibility is how we recognize that a degree of freedom has entered $A$'s scope; it is not what makes actualization occur. The distinction matters: the metaphysical primitive is $A$; the physical criterion tracks the conditions under which $A$ operates.

This criterion is not ad hoc: it tracks the physical structure of the interaction rather than being tailored to fit experimental outcomes after the fact. The quantitative content is supplied by standard decoherence theory: the interaction Hamiltonian $H_{SE}$ determines which basis is stable (the pointer basis), the decoherence timescale $\tau_D \sim \gamma_{SE}^{-1}$ determines when coherence is suppressed, and the coupling constants and environmental spectral density determine how irreversibly. LRT identifies this pointer-basis stability condition as the lawful condition under which a degree of freedom enters the scope of $A$ (Section 9.1).

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

At this stage, the entangled configuration remains in $I_\infty$ with a disposition toward multiple admissible actualizations under differing interaction contexts. Measuring the ancilla in the $\{\lvert \text{mark}_1 \rangle, \lvert \text{mark}_2 \rangle\}$ basis would bring which-path into the scope of $A$ and destroy interference. Measuring the ancilla in a complementary basis (the "eraser" measurement) brings a different observable into the scope of $A$, one that does not distinguish paths. Post-selection on the eraser outcome recovers the interference subensemble because, for those particles, which-path was never actualized.

The "erasure" does not undo a fact. It prevents a fact from being established. No which-path information was actualized; the configuration in $I_\infty$ retained its dispositional structure toward multiple admissible outcomes, and the eraser measurement resolved a different observable.

---

## 7. Contrasts with Other Interpretations

### 7.1 Many-Worlds Interpretation

**MWI claim.** All outcomes occur; the universe branches at every measurement. There is no collapse. The universal wave function evolves unitarily forever, and what we experience as a definite outcome is the result of observers becoming entangled with one branch of a superposition.

**LRT contrast.** LRT agrees that unitary evolution is not interrupted. But LRT denies that all branches are actualized. $A$ selects one outcome: the one that obtains in $A_\Omega$. The other branches remain as configurations in $I_\infty$, which is to say they remain as possibilities that were not actualized. LRT preserves the deterministic evolution of $\lvert \psi \rangle$ without the ontological extravagance of universal branching.

The disagreement between MWI and LRT is not merely interpretive: it is grounded in a direct conflict with $L_3$ and in multiple independent problems that MWI has not resolved. Six distinct points of divergence follow.

**Point 1: Direct conflict with $L_3$ as ontological constraint.**

$L_3$ (the law of Excluded Middle) requires, as an ontological constraint rather than a logical convention, that for any well-formed event $E$, $A$ delivers a Boolean verdict: $A(E, c) \in \{1, 0\}$. For any specific measurement outcome $E_k$ (for example, "spin-up is detected"), either $E_k$ obtains or it does not. Non-Contradiction forbids that both $E_k$ and $\neg E_k$ obtain in the same respect at the same time.

MWI asserts that both $E_k$ (spin-up) and $\neg E_k$ (spin-down) obtain in the actual world, differentiated only by being in distinct branches. The MWI branching is not a separation into a "real" and a "merely possible" domain; on MWI, every branch is equally real. Therefore MWI asserts:

$$A(E_k, \text{world}) = 1 \quad \text{and} \quad A(\neg E_k, \text{world}) = 1$$

This is precisely the conjunction that $L_3$'s Non-Contradiction forbids. MWI is not merely in tension with LRT; it is logically incompatible with $L_3$ understood as a constraint on what can obtain, not merely on what we say.

**Point 2: MWI relativizes $L_3$ to a perspectival status, demoting it from ontological to epistemic.**

The standard MWI response to Point 1 is that $L_3$ holds *within each branch*: relative to any observer in a branch, exactly one outcome obtained. On this view, Excluded Middle is observer-relative -- "E obtains, relative to this branch" -- not a constraint on the world as a whole.

This response concedes exactly what LRT asserts is at stake. If Excluded Middle governs only *appearances within branches* rather than *what is the case*, then $L_3$ has been reduced from an ontological constraint to an epistemic one: it governs how things seem to observers, not what is. LRT's $L_3$ is constitutive of reality. An $L_3$ that is branch-relative is not the same constraint; it is a weaker, perspectival principle masquerading under the same name. Accepting the MWI response requires abandoning the claim that logic governs ontology, not merely epistemology.

**Point 3: The probability problem.**

In a deterministic branching universe where all outcomes obtain, the meaning of $p(a_k) = \lvert c_k \rvert^2$ is not obvious. If spin-up and spin-down both occur, in what sense does spin-up occur with probability $\lvert \alpha \rvert^2$? There are not more spin-up branches than spin-down branches; there are exactly two branches (for a two-outcome measurement), regardless of amplitudes.

Decision-theoretic derivations (Deutsch 1999; Wallace 2012) attempt to recover Born statistics from rational-agent axioms applied within the Everett framework. These derivations are contested and require substantive assumptions about how rational agents should weight branches -- assumptions whose justification is circular if the goal is to *derive* the Born rule. The probability problem in MWI is unsolved.

LRT has no probability problem. The Born rule is grounded as the unique probability measure over PVMs on the admitted Hilbert space, via Gleason's theorem, motivated by $A$'s Boolean character (Paper II, Step 6). The argument does not invoke agents, decisions, or branch-weighting. The probability $p(a_k) = \lvert \langle a_k \lvert \psi \rangle \rvert^2$ is the objective disposition of configuration $\psi$ in $I_\infty$ toward outcome $a_k$ under $A$'s Boolean selection. One outcome obtains; the Born weights are the measure over which one.

**Point 4: The preferred basis problem.**

Even granting that branches are real, MWI must explain in which basis the universe branches. The wave function of the universe does not come pre-branched in any preferred decomposition. Every state vector admits infinitely many decompositions; nothing in unitary evolution selects one.

MWI typically appeals to decoherence: the environment selects a preferred pointer basis. But decoherence is a process entirely within unitary evolution. It suppresses off-diagonal terms in a particular basis but does not produce definite outcomes within that basis. Decoherence explains *apparent* classicality for observers within branches; it does not explain why there are branches rather than a single continuing superposition. The preferred basis problem for MWI is: decoherence narrows the options but does not complete the selection.

LRT locates basis selection in the interaction Hamiltonian $H_{\text{int}}$ that determines which PVM enters the scope of $A$. The pointer basis is the physically determined eigenbasis of the observable that the apparatus interaction couples to macroscopic degrees of freedom. There is no underdetermination: the Hamiltonian specifies the basis, the decoherence timescale $\tau_D$ specifies when, and $A$ provides the Boolean selection that decoherence alone cannot.

**Point 5: Ontological extravagance.**

MWI posits an uncountably large branching multiverse as the cost of avoiding collapse. Every quantum event -- every particle interaction, every environmental perturbation of every degree of freedom in the universe -- produces new branches. The ontological posit is not merely "many worlds" but a continuous, vast ramification of actual physical reality, each branch as real as any other.

LRT posits three primitives ($L_3$, $I_\infty$, $A$) and a two-domain distinction ($I_\infty$ vs. $A_\Omega$). The domain $I_\infty$ contains all logically admissible configurations as possibilities; the domain $A_\Omega$ contains one actual world. The configurations in $I_\infty$ that were not actualized are not additional actual worlds; they are possibilities that did not obtain. The ontological economy is substantial: one world governed by $\chi$, not an unlimited proliferation of equally actual branches. Parsimony favors LRT.

**Point 6: Empirical inertness vs. LRT's falsifiability.**

MWI makes no empirical prediction that distinguishes it from standard quantum mechanics without the many-worlds interpretation. No experiment can detect the other branches: they are, by construction, inaccessible to any observer in any branch. MWI is empirically inert -- not falsifiable, not confirmable by any physical measurement.

LRT is falsifiable. It predicts that no spontaneous collapse event will ever be detected ($\lambda = 0$ exactly as a structural consequence of the ontology), directly testable against GRW/CSL (Section 10). LRT also makes discriminating predictions about basis selection relative to the interaction Hamiltonian (Section 9.2, Fork 2). The methodological contrast is significant: MWI purchases empirical immunity at the cost of testability, while LRT makes specific predictions that ongoing experiments address. A framework that can be falsified stands epistemically above one that cannot.

### 7.2 Bohmian Mechanics

**Bohmian claim.** Particles always have definite positions, guided by the wave function via the guidance equation $\dot{q}_k = \frac{\hbar}{m_k} \text{Im} \frac{\nabla_k \Psi}{\Psi}$.

**LRT contrast.** LRT agrees that measurement outcomes are definite. But LRT does not privilege position as the only always-definite observable. In LRT, *which* properties are actualized depends on the physical interaction history. A photon's energy may be actualized while its position is not. A spin may be actualized while momentum is not. The ontology is property-specific, not position-privileged.

Bohmian mechanics also faces the "surreal trajectories" problem (Englert, Scully, Sussmann, Walther, 1992): the Bohmian trajectories in certain interferometric setups do not match the paths the particles "seem" to follow. LRT avoids this because it does not posit hidden trajectories. A particle's position is either actualized (in $A_\Omega$, definite) or not (in $I_\infty$, no trajectory to be surreal about).

### 7.3 Spontaneous Collapse (GRW/CSL)

**GRW/CSL claim.** The Schrodinger equation is approximate. Stochastic terms cause spontaneous localization with rate $\lambda_{\text{GRW}} \approx 10^{-16}$ s$^{-1}$ per particle and localization width $r_C \approx 10^{-7}$ m.

**LRT contrast.** GRW/CSL modifies the fundamental dynamics. LRT does not. Unitary evolution is exact in LRT; the appearance of "collapse" is a feature of the $I_\infty \to A_\Omega$ interface, not a correction to the Schrodinger equation. LRT therefore predicts that no experiment will detect deviations from unitarity in isolated quantum systems, regardless of system size.

GRW/CSL also introduces two free parameters ($\lambda_{\text{GRW}}$, $r_C$) whose values are chosen to match observation rather than derived from principle. LRT introduces no free parameters at all: $A$ is Boolean, the interaction Hamiltonian determines the PVM, and the actualization threshold is fixed by the pointer-basis stability condition (the decoherence timescale $\tau_D \sim \gamma_{SE}^{-1}$, calculable from the coupling constants and spectral density of the environment). The quantitative content is inherited from standard decoherence theory, not invented by LRT.

### 7.4 QBism

**QBist claim.** Quantum states represent an agent's personal degrees of belief. Measurement "outcomes" are experiences of the agent, not objective events.

**LRT contrast.** LRT is realist. Measurement outcomes are objective configurations in $A_\Omega$, not agent-relative experiences. The Born rule probabilities are objective dispositional properties of states in $I_\infty$ with respect to $A$'s selection (Paper II, Section 4.2):

$$p(E \mid \psi) = \text{Tr}(\rho P_E)$$

is the objective disposition of configuration $\psi$ toward outcome $E$ under actualization. This is not a betting coefficient, not a frequency over an ensemble, and not a personal credence. It is a feature of the ontology.

QBism dissolves the measurement problem by denying that there is an objective problem to solve. LRT renders it intelligible by providing the ontological structure within which objective outcomes are categorically distinct from the superpositions that precede them.

### 7.5 Summary of Contrasts

| Feature | Copenhagen | MWI | Bohm | GRW | QBism | **LRT** |
|---------|-----------|-----|------|-----|-------|---------|
| Definite outcomes | Postulated | All occur in branches | Always (position) | Dynamical | Agent-relative | $A$-selected (one obtains) |
| Collapse | Postulated | None | None | Modified dynamics | Belief update | Ontological transition (thesis under evaluation) |
| Preferred basis | Classical cut | Decoherence (partial) | Position | Localization width | N/A | Interaction $H$ (fully determined) |
| Born rule status | Postulate | Derived (contested) | Postulate | Approximately derived | Normative | Grounded (Gleason, given $\mathcal{H}$) |
| Free parameters | Cut location | None (basis problem open) | None | $\lambda$, $r_C$ | None | None ($\tau_D$ from $H_{SE}$) |
| Unitarity | Approximate | Exact | Exact | Approximate | N/A | Exact |
| $L_3$ status | Implicit | Perspectival (per branch) | Implicit | Implicit | N/A | Constitutive of reality |
| Realist? | Ambiguous | Yes (all branches actual) | Yes (particles) | Yes | No | Yes (one actual world) |
| Empirically falsifiable? | Limited | No | Limited | Yes | No | Yes ($\lambda = 0$) |

*Table 1. Interpretive comparison. Each entry compresses substantial internal debate. "Grounded" for LRT's Born rule means: ontologically motivated within an imported Hilbert-space framework, not derived from LRT primitives alone. "Ontological transition" is LRT's thesis, not a settled result. "$\tau_D$ from $H_{SE}$" indicates that LRT's actualization threshold is the pointer-basis stability condition, with no free parameters beyond those in the interaction Hamiltonian. "Perspectival (per branch)" for MWI reflects that MWI can only claim Excluded Middle holds relative to observers within branches, not as a global ontological constraint, which is what LRT requires.*

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

## 9. The Actualization Threshold and Experimental Signatures

### 9.1 The Actualization Threshold

The actualization threshold is not an open parameter awaiting determination. It is the pointer-basis stability condition, fully determined by the system-environment interaction Hamiltonian $H_{SE}$.

Standard decoherence theory establishes that $H_{SE}$ determines three things simultaneously: (1) *which* basis is stable (the pointer basis, selected by the commutativity condition $[H_{SE}, \hat{O}_{\text{pointer}}] \approx 0$ (Zurek's einselection)); (2) *when* coherence is suppressed — on the decoherence timescale $\tau_D \sim \gamma_{SE}^{-1}$, calculable from the coupling constants and spectral density of the environment; and (3) *how irreversibly* — determined by the number of environmental degrees of freedom that become correlated with the system. LRT identifies this condition as the lawful condition under which a degree of freedom enters the scope of $A$:

**The Zero-Gap Identity.** There is no temporal gap between decoherence completing and $A$ acting. Being decohered *is* being $L_3$-evaluable. Once the interaction Hamiltonian has suppressed off-diagonal coherences in the pointer basis, the degree of freedom satisfies the preconditions for Boolean evaluation: it has a determinate value or it does not (Excluded Middle), and it cannot both obtain and not obtain (Non-Contradiction). Decoherence is the physical *condition*; logical resolution under $A$ is the *consequence*. The two are not synonymous (Everettians accept decoherence without selection), but they are not temporally separated. LRT's $A$ provides the selection that decoherence alone does not.

**$L_3$ as constitutive precondition.** The Zero-Gap Identity might suggest that $L_3$ plays an optional interpretive role: one could accept the decoherence machinery and simply decline to invoke logical constraints on actuality. A reductio shows otherwise. Suppose $L_3$ does not hold as an ontological constraint. Then Identity ($a = a$) is not guaranteed for physical configurations, and without Identity, no configuration is self-identical, which is to say, no configuration is determinately *that* configuration rather than some other. But a measurement outcome is, by definition, a determinate result: the pointer reads $a_k$, not an indeterminate smear across the eigenvalue spectrum. Without Identity, the predicate "measurement outcome $= a_k$" does not refer, because there is no fact of the matter about what $a_k$ is. Non-Contradiction and Excluded Middle fail in turn: if configurations lack determinate identity, neither "$a_k$ obtains and $a_k$ does not obtain" nor "$a_k$ obtains or $a_k$ does not obtain" are well-formed, since the referent of $a_k$ is indeterminate. The cascade is: no Identity $\to$ no distinguishable outcomes $\to$ no measurement $\to$ no physics. The term "measurement outcome" presupposes that there exist determinate, distinguishable states to be measured; $L_3$ is the minimal condition under which that presupposition holds.

This is not a philosophical preference layered onto the physics. It is a transcendental condition on the intelligibility of measurement itself (cf. TAB $\S$2.4.0, where $L_3$ is established as constitutive of determinacy rather than descriptive of it). Every interpretation of quantum mechanics that produces definite outcomes tacitly relies on $L_3$: the eigenvalue $a_k$ returned by a PVM $\{P_k\}$ is a determinate value precisely because the projection operators $P_k$ are idempotent ($P_k^2 = P_k$, encoding Identity) and mutually orthogonal ($P_j P_k = \delta_{jk} P_k$, encoding Non-Contradiction and Excluded Middle). The formal structure of measurement already contains $L_3$. LRT makes this dependence explicit; other interpretations leave it implicit and therefore unexamined.

**The asymptotic objection and PPC.** Decoherence is technically asymptotic: off-diagonal terms approach zero but never strictly vanish. The Principle of Physical Completeness (PPC) handles this: once coherence is suppressed beyond the threshold of any operationally feasible detection — that is, below any measurement precision achievable by any physical apparatus, the property is functionally actualized. The residual coherence is not physically meaningful; the degree of freedom is in the scope of $A$. This is not a stipulation but a consequence of taking the operational content of $L_3$ seriously: a "superposition" that no physical interaction can distinguish from a definite state is not, in any $L_3$-relevant sense, a superposition.

**No free parameters.** LRT contributes no free parameters to the threshold determination. The coupling Hamiltonian $H_{SE}$ fixes the pointer basis, the timescale, and the irreversibility. The decoherence timescale $\tau_D$ is calculable from first principles for any given system-environment pair. This is a feature: LRT inherits the quantitative machinery of decoherence theory without adding adjustable constants.

**Microscopic systems.** Even an isolated microscopic system (a photon in a double-slit experiment) reduces to this framework. The detector *is* the environment supplying the interaction variables. When the photon strikes the detection screen, $H_{SE}$ (the photon-detector coupling) determines the pointer basis (position), the decoherence timescale (effectively instantaneous for macroscopic detectors), and the irreversibility (the detector's $\sim 10^{23}$ degrees of freedom). There is no separate "measurement" process: every actualization is an instance of environment-induced pointer-basis stabilization followed by $A$'s Boolean selection.

### 9.2 Avenues for Experimental Discrimination

LRT's commitments generate empirical expectations, some of which overlap with standard quantum mechanics plus decoherence, and some of which produce sharper forks against specific competitors. The following are ordered by discriminating power.

**Fork 1: Exact unitarity (discriminates against GRW/CSL).**
Unlike GRW/CSL, LRT predicts that no deviations from unitary evolution will be found in isolated quantum systems, regardless of system size. Experiments testing spontaneous collapse models (e.g., LISA Pathfinder bounds, optomechanical oscillators, molecular interferometry) should find null results. This is the cleanest experimental fork: detection of spontaneous collapse signatures falsifies LRT's measurement account; continued null results increasingly constrain GRW/CSL while leaving LRT unaffected.

**Fork 2: Interaction-dependent basis (discriminates against pure-decoherence accounts).**
The preferred measurement basis is always determined by the physical interaction Hamiltonian, not by decoherence alone. In principle, an experiment could prepare a system in a regime where decoherence selects one basis but the interaction Hamiltonian selects another, testing whether outcomes follow the decoherence basis or the interaction basis. This is sharper in principle than in current experimental practice, but it identifies a genuine point of divergence.

**Consonance 1: No hidden variables.**
LRT expects Bell-inequality violations, Kochen-Specker contextuality, and Leggett-Garg inequality violations, since unactualized properties are genuinely indeterminate (not merely unknown). These results are consonant with LRT but not distinctly diagnostic of it: standard quantum mechanics without hidden variables produces the same expectations.

**Consonance 2: State-dependent decoherence consistency.**
Since the actualization threshold is the pointer-basis stability condition, the decoherence timescale $\tau_D$ should scale predictably with the system-environment coupling strength across different physical platforms (superconducting qubits, trapped ions, NV centers, molecular systems). Cross-platform consistency in the relationship between $\tau_D$ and coupling parameters confirms that the actualization threshold tracks the physical interaction, not an LRT-specific constant. This is already well-supported by existing decoherence experiments.

### 9.3 Discriminating LRT from GRW/CSL

The sharpest experimental contrast is with spontaneous collapse models. GRW/CSL predicts measurable deviations from unitary evolution: an excess heating rate proportional to $\lambda_{\text{GRW}}$, anomalous diffusion in free particles, and a mass-dependent collapse rate. Current bounds (Vinante et al., 2020; Donadi et al., 2021) are approaching the GRW parameter space.

LRT predicts none of these effects. If spontaneous collapse signatures are detected, LRT's measurement account is falsified. If they are not, GRW/CSL is increasingly constrained while LRT remains unaffected. This is a clean experimental fork.

### 9.4 Discriminating LRT from MWI

The contrast with GRW/CSL described in Section 9.3 represents a clean empirical fork: two theories predict opposite experimental outcomes, and experiments are actively probing the boundary. The contrast with MWI is structurally different.

MWI makes no prediction that distinguishes it from standard quantum mechanics. Since all branches are equally real and no physical measurement can access other branches, every experimental result is compatible with MWI. This is not a feature; it is a methodological defect. A framework that accommodates every possible outcome predicts none, and a framework that predicts none cannot be tested.

LRT is not empirically inert. Three distinct discriminating structures apply:

**Structural asymmetry on the Born rule.** LRT grounds the Born rule without invoking agents or branch-weighting. MWI must derive Born statistics from rational-agent axioms, which requires substantive assumptions whose independence from what is to be derived is contested. The two derivational structures differ in character: LRT's follows from Gleason's theorem applied to PVM structure motivated by $A$'s Boolean character; MWI's requires additional axioms about rational preference. The debate over decision-theoretic derivations in MWI (Deutsch 1999; Wallace 2012) is an open dispute that the LRT derivation sidesteps entirely.

**The ontological parsimony criterion.** While parsimony is not empirical in the strict sense, it is a methodological principle applied when theories are otherwise empirically equivalent. MWI posits an uncountably large multiverse of equally actual branches; LRT posits one actualized world governed by three primitives. If both are consistent with all observations, parsimony favors LRT's ontology.

**Indirect discriminating structure: basis selection.** Fork 2 (Section 9.2) identifies an in-principle discriminating experiment: a regime where decoherence selects one basis but the interaction Hamiltonian selects another. Under LRT, outcomes follow the interaction Hamiltonian. Under standard decoherence-based accounts (including the decoherence-based branch selection in MWI), outcomes follow the decoherence basis. This distinction is at the edge of current experimental capability, but it identifies a structural difference between the two frameworks that a sufficiently refined experiment could, in principle, resolve.

The methodological asymmetry is significant regardless of the experimental outcome. LRT can be falsified; MWI cannot. A realist framework that issues specific, falsifiable predictions stands epistemically above one that does not, even when both remain consistent with all current data.

---

## 10. Falsifiability and Empirical Predictions

A scientific framework's credibility rests not only on its explanatory coherence but on its capacity to be empirically distinguished from competitors. LRT makes a specific, falsifiable prediction that separates it from both the spontaneous collapse program (GRW/CSL) and the empirically inert interpretations (MWI/Everett, Copenhagen, QBism). This distinction is not incidental: it is a consequence of the ontological structure. Because LRT locates actualization in the interaction Hamiltonian and not in branching or stochastic modification of dynamics, its commitments are physically specific in ways that MWI's are not.

### 10.1 The Null Prediction

LRT predicts that no spontaneous collapse event will ever be detected. This prediction is not a contingent expectation but a structural consequence of the framework.

In GRW/CSL, collapse is a modification of the Schrodinger equation: stochastic terms produce spontaneous localization at rate $\lambda_{\text{GRW}}$ per particle, with localization width $r_C$. These are free parameters, chosen to reproduce macroscopic definiteness while preserving microscopic coherence. The parameter space is a two-dimensional region ($\lambda$, $r_C$) within which values are constrained by experiment but not determined by theory.

In LRT, no such parameter space exists. The actualization threshold is the pointer-basis stability condition, fully determined by the system-environment interaction Hamiltonian $H_{SE}$. The decoherence timescale $\tau_D \sim \gamma_{SE}^{-1}$ is calculable from the coupling constants and environmental spectral density. There are no free parameters to tune, no stochastic terms to add, and no collapse rate to measure. The GRW/CSL parameter space is not merely constrained by LRT; it is empty. Spontaneous collapse does not occur because actualization is not a dynamical modification of unitary evolution but an ontological transition governed entirely by the interaction variables that standard quantum mechanics already provides.

### 10.2 Confirming Evidence from Null Results

Every experimental bound that tightens the constraint on $\lambda_{\text{GRW}}$ is confirming evidence for LRT. Current bounds from LISA Pathfinder (Carlesso et al., 2022), underground radiation measurements (Donadi et al., 2021), and optomechanical oscillators (Vinante et al., 2020) have progressively excluded regions of the GRW/CSL parameter space. Under LRT, the entire parameter space is excluded in principle: $\lambda = 0$ exactly. Each null result is therefore not merely consistent with LRT but positively predicted by it.

This asymmetry is significant. A framework that predicts $\lambda = 0$ is confirmed by every null result and falsified by any positive detection. A framework that permits a range of $\lambda$ values (GRW/CSL) is constrained but never confirmed by null results, since the true value might lie below current sensitivity. LRT's prediction is sharp: the spontaneous collapse rate is identically zero, not approximately zero, not below current detection thresholds, but zero as a structural feature of the ontology.

### 10.3 Empirical Distinguishability and the MWI Contrast

Not all interpretations of quantum mechanics are empirically distinguishable from one another. Many are empirically inert: they agree on all observable predictions while differing only in ontological commitments. LRT occupies a distinctive position in this landscape, with a particularly sharp contrast to MWI on both empirical and ontological grounds.

**Table 2. Testability, falsifiability, and metaphysical commitment across interpretations.**

| Feature | LRT | MWI (Everett) | GRW/CSL |
|---------|-----|---------------|---------|
| **Novel empirical prediction** | $\lambda = 0$ exactly; basis follows interaction $H$ | None beyond standard QM | Spontaneous collapse at rate $\lambda$, width $r_C$ |
| **Falsifiable by** | Detection of any spontaneous collapse event; or basis selection contradicting $H_{\text{int}}$ | No known empirical test | Null results excluding full parameter space |
| **Confirmed by** | Every tightened bound on $\lambda$; continued null results | N/A (every result compatible) | Detection of collapse signatures |
| **Free parameters (measurement)** | Zero ($\tau_D$ from $H_{SE}$) | Zero (basis problem unresolved) | Two ($\lambda$, $r_C$) |
| **Unitarity** | Exact | Exact | Approximate (modified dynamics) |
| **$L_3$ as ontological constraint** | Yes -- constitutive of what obtains | No -- Excluded Middle holds per branch only | Not addressed |
| **One actual world?** | Yes | No -- all branches equally actual | Yes |
| **Born rule derivation** | Gleason (no agents required) | Decision-theoretic (contested, agents required) | Approximately derived |
| **Metaphysical commitment** | Three primitives ($L_3$, $I_\infty$, $A$); one actualized world | Universal wave function; uncountably branching multiverse | Modified Schrodinger equation; stochastic ontology |
| **Empirically distinguishable from standard QM?** | Yes (predicts $\lambda = 0$ against GRW/CSL; basis fork in principle) | No | Yes (predicts $\lambda > 0$) |

*Table 2. The three-way partition among interpretations with respect to empirical content. GRW/CSL modifies quantum dynamics and is testable by searching for the modifications. MWI preserves quantum dynamics but makes no prediction that differs from standard quantum mechanics, and cannot be falsified by any physical experiment. LRT preserves quantum dynamics, makes a specific prediction ($\lambda = 0$ exactly, as a consequence of the ontology rather than as a default assumption) testable against GRW/CSL, and offers a basis-selection fork against decoherence-only accounts in principle. The "$L_3$ as ontological constraint" row marks the deepest divergence between LRT and MWI: MWI requires reducing Excluded Middle to a branch-relative principle, which LRT treats as an unacceptable demotion of logic from constitutive to perspectival status.*

### 10.4 The Structure of LRT's Falsifiability

LRT's measurement account would be falsified by any of the following:

1. **Detection of spontaneous collapse.** Any confirmed observation of a collapse event not attributable to environmental decoherence would falsify LRT's claim that actualization is governed entirely by the interaction Hamiltonian.

2. **Violation of exact unitarity in isolated systems.** LRT predicts that isolated quantum systems evolve unitarily without exception. Detection of non-unitary evolution in a verified isolated system would falsify this commitment.

3. **Basis selection inconsistent with the interaction Hamiltonian.** If measurement outcomes were found to occur in a basis not determined by the physical interaction Hamiltonian (after accounting for all relevant environmental couplings), LRT's basis-selection mechanism would be falsified.

4. **Demonstration that $L_3$ cannot function as an ontological constraint.** If a rigorous argument established that the Excluded Middle cannot coherently constrain what obtains (rather than merely what is knowable or sayable), the metaphysical foundation of the actualization account would require revision.

These conditions are specific, experimentally addressable (in conditions 1-3), and independent of one another. LRT is not merely "consistent with" current data; it makes predictions that ongoing experiments are actively testing.

The contrast with MWI on falsifiability is structural, not contingent. MWI is immune to experimental refutation because it accommodates every possible experimental result: whatever is observed in any branch is compatible with all branches being equally actual. LRT accepts experimental risk. A framework that can be falsified and has not been stands on stronger methodological footing than one that cannot be.

---

## 11. Discussion

### 11.1 What LRT Achieves

The measurement problem, as traditionally formulated, asks: how does a definite outcome emerge from a superposition? The question presupposes that the superposition and the outcome exist in the same ontological domain and that some dynamical process must connect them.

LRT denies the presupposition. Superposition and definite outcome belong to different ontological domains: $I_\infty$ and $A_\Omega$, respectively. The transition between them is not a dynamical process but an ontological one: the completion of actualization under $A$. The measurement problem is rendered intelligible, not by producing a new dynamical mechanism, but by reclassifying the question: the remaining burden is not "how does collapse happen?" but "what is the lawful condition under which a degree of freedom enters the scope of $A$?"

The distinction between dynamical collapse (a process within the Schrodinger evolution) and ontological transition (a change in the domain-membership of a property) is substantive: collapse interrupts unitary evolution within a single domain, while actualization changes the domain-membership of a property and leaves unitary evolution intact. The formal contradiction between Schrodinger dynamics and definite outcomes, which is the core of the measurement problem, does not arise under this architecture. The residual question (what governs the scope of $A$?) has a definite answer: the pointer-basis stability condition determined by the interaction Hamiltonian $H_{SE}$ (Section 9.1). Decoherence fixes when a degree of freedom becomes $L_3$-evaluable; $A$ provides the Boolean selection that decoherence alone does not.

### 11.2 What LRT Does Not Achieve

**The relabeling objection.** A critic will say: "You have not dissolved measurement. You have renamed collapse as actualization and relocated it into a metaphysical primitive." This objection has force, and the paper must answer it directly. The answer is that LRT's ontological transition differs from collapse in a specific structural way: collapse is a modification of the quantum state within a single domain (interrupting unitary evolution), while actualization is a change in domain-membership that leaves unitary evolution intact. The formal contradiction between Schrodinger dynamics and definite outcomes, which is the measurement problem proper, does not arise under LRT. What does arise is a new question: what governs the scope of $A$? That question is open. But it is a different question from the one the measurement problem poses, and its answer need not violate unitarity. Whether this structural difference is sufficient to count as more than relabeling is a judgment the community must make. This paper argues that it is.

**The actualization threshold.** The actualization threshold is identified with the pointer-basis stability condition (Section 9.1): $H_{SE}$ determines when coherence is suppressed and $A$ acts. What remains open is a *derivation* of this identification from the primitives alone, that is, a proof that $L_3$, $I_\infty$, and $A$ jointly entail that the scope of $A$ coincides with decoherence completion. The identification itself is physically well-motivated and yields correct timescales, but its derivation from metaphysical first principles is a target for future work.

**Hilbert-space import.** LRT does not derive the specific Hilbert-space structure (complex field, dimensionality) from its primitives alone. These are imported from the Hardy-Masanes-Muller reconstruction theorems (Paper II, Step 4), which LRT grounds in the primitives but does not independently derive. Claims about the Born rule throughout this paper should be read accordingly: LRT supplies ontological grounding for why the relevant measure must be Born-type, given the admitted Hilbert-space framework.

### 11.3 The Ontological Economy

LRT introduces no new dynamical equations, no hidden variables, no additional physical constants, and no branching universes. It introduces three ontological primitives ($L_3$, $I_\infty$, $A$) and the distinction between two domains ($I_\infty$ and $A_\Omega$). Given the Hilbert-space framework imported from reconstruction theorems, the measurement formalism, including projection structure, the Born rule, and basis selection, follows from these primitives without further postulates specific to measurement.

Whether this counts as more or less economical than the alternatives depends on one's tolerance for metaphysics. LRT trades a physics problem (the measurement problem as dynamical contradiction) for a metaphysical framework (the primitives) that inherits its quantitative content from standard decoherence theory without adding free parameters. The actualization threshold is not an additional postulate but the pointer-basis stability condition already calculable from $H_{SE}$. The framework is argued, not arbitrary (Paper I). Whether the trade is worth making is a question for the community.

---

## 12. Conclusion

The measurement problem has resisted solution for nearly a century because each interpretation has sought a dynamical resolution within the quantum formalism itself. LRT reframes the problem by recognizing that measurement is not a dynamical process but an ontological transition: the completion of actualization under the Boolean action primitive $A$, mediated by the interaction Hamiltonian that determines the relevant projection-valued measure. This reframing eliminates the formal contradiction between unitary evolution and definite outcomes. It does not eliminate the need for a lawful account of when actualization occurs.

Partial actualization, the possibility that a configuration may be actualized with respect to some properties while remaining in $I_\infty$ with respect to others, provides a unified account of interference, which-path complementarity, delayed choice, and quantum erasure. Within the Hilbert-space framework imported from reconstruction theorems, the Born rule is grounded as the unique probability measure over PVMs via Gleason's theorem, ontologically motivated by $A$'s Boolean character. Unitarity is exact. The preferred basis is physically determined by the interaction Hamiltonian.

The actualization threshold is the pointer-basis stability condition determined by the interaction Hamiltonian $H_{SE}$: the decoherence timescale $\tau_D \sim \gamma_{SE}^{-1}$ fixes when a degree of freedom becomes $L_3$-evaluable, and the Zero-Gap Identity ensures no temporal separation between decoherence completing and $A$ acting. LRT contributes no free parameters to this determination, inheriting the quantitative machinery of standard decoherence theory. What remains open is a derivation of this identification from the primitives alone. LRT renders the measurement problem intelligible within a realist framework that preserves exact unitarity and requires no adjustable constants beyond those already present in the interaction Hamiltonian.

---

## Appendix A. Formal Dependency Map

This paper's claims rest on results established across the LRT paper series and the Lean 4 formalization. The following map identifies where each major claim originates.

**Established in this paper (Paper V):**

- Partial actualization framework (Section 3)
- Application to double-slit, Stern-Gerlach, delayed choice (Sections 4-6)
- Interpretive contrasts, including extended anti-MWI analysis (Section 7, especially 7.1)
- Actualization threshold as pointer-basis stability condition, Zero-Gap Identity (Section 9.1)
- Discriminating LRT from MWI: methodological and ontological asymmetries (Section 9.4)
- Falsifiability analysis and null prediction against GRW/CSL (Section 10)
- Four-way empirical distinguishability partition including MWI (Section 10.3, Table 2)
- MWI falsifiability contrast in Section 10.4

**Imported from Paper I (TAB v2.0):**

- Ontological primitives $L_3$, $I_\infty$, $A$ and their mutual constitution
- Bridge equation $\chi \vdash A_\Omega = L_3(I_\infty)$
- Two-domain distinction ($I_\infty$ vs. $A_\Omega$)

**Imported from Paper II (Core Physics) and Lean formalization:**

- Boolean actualization $\to$ projection structure (Steps 4-5, Lean verified)
- PVM structure $\to$ Born rule via Gleason (Step 6, Lean verified)
- Unitary evolution and Schrodinger equation (Steps 7-10, Lean verified)

**Imported from external reconstruction theorems (not derived by LRT):**

- Complex Hilbert-space structure (Hardy 2001, Masanes-Muller 2011)
- Local tomography (Hardy H1/H2, with LRT motivating derivation in Paper II Step 3)
- Gleason's theorem (Gleason 1957)
- Stone's theorem (mathematical, used in Paper II Step 10)

**Open (not yet established):**

- Derivation of threshold identification (scope of $A$ = decoherence completion) from primitives alone (Section 11.2)
- Complete derivation of Actualization Partition Rule from primitives (Section 3.2)
- $K = 2$ forcing from Boolean structure (OPN-005)

---

## References

Bennett, C.H. (2003). Notes on Landauer's principle, reversible computation, and Maxwell's Demon. *Studies in History and Philosophy of Modern Physics*, 34(3), 501-510.

Bohm, D. (1952). A suggested interpretation of the quantum theory in terms of "hidden" variables. *Physical Review*, 85(2), 166-193.

Carlesso, M., Donadi, S., Ferialdi, L., Paternostro, M., Ulbricht, H., and Bassi, A. (2022). Present status and future challenges of non-interferometric tests of collapse models. *Nature Physics*, 18, 243-250.

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
