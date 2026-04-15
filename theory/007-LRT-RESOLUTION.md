# The Resolution Thesis: Why Quantum "Collapse" Is a Category Error

## Logic Realism Theory, Paper VII

James D. Longmire
Northrop Grumman Fellow (unaffiliated research)
ORCID: 0009-0009-1383-7698
Correspondence: jdlongmire@outlook.com
Date: April 2026
Status: Draft
Series: LRT Paper 007
Upstream: 000-TRM-FOUNDATIONS, 001-LRT-TAB-PHILOSOPHY, 002-LRT-CORE-PHYSICS, 004-LRT-HOW-COME-THE-QUANTUM, 005-LRT-MEASUREMENT, 006-LRT-ENTANGLEMENT

---

## Abstract

The word "collapse" encodes an ontological assumption: that the wavefunction is the primary bearer of physical reality, and that measurement interrupts its evolution through some dynamical mechanism yet to be identified. This paper argues that the assumption is a category error and that the measurement problem, as traditionally formulated, is malformed. Under Logic Realism Theory (LRT), where reality is constituted by three co-primitives — logical constraint ($L_3$), an informational domain of possible configurations ($I_\infty$), and a primitive actualization principle ($A$) — there is no wavefunction to collapse. Quantum states are descriptions of configurations in $I_\infty$; measurement outcomes are actualized configurations in $A_\Omega$. The transition from superposition to definite outcome is not a dynamical interruption of unitary evolution but the completion of logical resolution: decoherence provides the physical conditions under which $L_3$ becomes operative, $L_3$ (specifically Excluded Middle) supplies the logical verdict that a determinate outcome must obtain, and $A$ delivers that outcome. The measurement problem asked for a physical mechanism behind what is, at bottom, a logical requirement. Once the question is corrected, the answer is already present in the primitive ontology. This paper develops the Resolution Thesis in full, demonstrates its application to the standard measurement scenarios, and contrasts it with the dynamical collapse, decoherence-alone, and Everettian programs.

**Keywords:** quantum measurement, wavefunction collapse, category error, logical resolution, decoherence, actualization, quantum foundations, information ontology, logic realism

---

## 1. The Collapse Assumption

### 1.1 What "Collapse" Presupposes

The standard quantum measurement narrative runs as follows. A system is prepared in state $\lvert \psi \rangle = \sum_i c_i \lvert a_i \rangle$. The system evolves unitarily under the Schrödinger equation. Then measurement occurs, and the state "collapses" to some $\lvert a_k \rangle$ with probability $\lvert c_k \rvert^2$. This narrative is so embedded in the pedagogy of quantum mechanics that its ontological presuppositions are rarely examined. They are:

1. **Wavefunction primacy.** The quantum state $\lvert \psi \rangle$ is the ontologically primary description of the system — what the system *is*, not merely what we know about it.
2. **Dynamical completeness.** Unitary evolution is the only lawful dynamics. Any departure from unitarity requires a dynamical account — a mechanism, a modification of the Schrödinger equation, or at minimum a specification of when and where the departure occurs.
3. **Collapse as event.** The transition from superposition to definite outcome is a physical event that happens to the wavefunction. Something changes the state of reality, and we need to explain what.

These presuppositions generate the measurement problem. If the wavefunction is all there is, and if unitary evolution is the only dynamics, then no measurement outcome should ever occur — the system-apparatus composite should remain in a superposition of all outcomes. The fact that definite outcomes do occur requires either a modification of the dynamics (GRW/CSL), an expansion of the ontology (Many-Worlds), additional variables (Bohmian mechanics), or a retreat to instrumentalism (Copenhagen, QBism).

### 1.2 The Category Error

LRT's diagnosis is that all three presuppositions are false — not because the quantum formalism is wrong, but because the formalism is being asked to do ontological work it was never designed for.

The category error is this: *the measurement problem treats a logical requirement as if it were a dynamical deficit*.

The demand for a "collapse mechanism" presupposes that the transition from possibility to actuality is a physical process within the domain of possibility. But possibility and actuality are ontologically distinct domains. No process *within* $I_\infty$ can produce actuality, because $I_\infty$ is the domain of possible configurations and $A_\Omega$ is the domain of actual ones. The transition is not a dynamical event; it is the operation of the actualization primitive $A$ under logical constraint $L_3$.

Asking "what mechanism causes collapse?" is like asking "what force makes a contradiction false?" The answer is: no force. Contradictions are false in virtue of the law of Non-Contradiction, not in virtue of some dynamical process that eliminates them. Similarly, definite outcomes obtain in virtue of Excluded Middle and the Boolean character of $A$, not in virtue of some physical mechanism that interrupts unitary evolution.

### 1.3 The Corrected Question

If the collapse question is malformed, what is the well-formed question?

It is not: *How does the wavefunction collapse?*
It is: *Under what conditions does a degree of freedom enter the scope of actualization?*

This is the question Paper V identified as the principal open problem. The present paper develops the positive account — the Resolution Thesis — that replaces the collapse narrative.

---

## 2. The Resolution Thesis

### 2.1 Statement

**Resolution Thesis.** Measurement is not the collapse of a wavefunction but the completion of logical resolution. When a quantum degree of freedom enters physical conditions sufficient for $L_3$ to become operative with respect to that degree of freedom, Excluded Middle requires a determinate verdict, and $A$ delivers it. The process has three components:

1. **Decoherence provides the conditions.** Environmental interaction selects a preferred basis by suppressing off-diagonal terms in the density matrix, rendering the system's reduced state approximately diagonal in the pointer basis. This is a physical process within $I_\infty$, governed by unitary evolution of the system-environment composite.

2. **$L_3$ provides the verdict.** Once decoherence has rendered the alternatives mutually exclusive and exhaustive within the pointer basis — that is, once the system is in a configuration where the alternatives are $L_3$-admissible propositions — Excluded Middle requires that one alternative obtains and the others do not. Non-Contradiction requires that exactly one obtains. This is not a physical process but a logical constraint.

3. **$A$ delivers the outcome.** The actualization primitive selects one of the $L_3$-admissible alternatives. The selected outcome enters $A_\Omega$ as a determinate configuration. The selection is governed by the Born rule, which (per Paper II, Steps 5-6, via Gleason's theorem) is the unique probability measure on the projection-valued measure structure that $A$'s Boolean character forces.

### 2.2 The Three Components Unpacked

#### Decoherence: Physical Conditions, Not Sufficient Cause

Decoherence is essential but incomplete. The decoherence program (Zurek 1981, 2003; Joos *et al.* 2003; Schlosshauer 2005, 2007) has demonstrated that environmental interaction:

- Selects a preferred (pointer) basis via einselection
- Suppresses interference terms on extraordinarily short timescales ($\sim 10^{-20}$ s for macroscopic objects)
- Produces an *improper mixture* — a reduced density matrix that is diagonal in the pointer basis

What decoherence does *not* do, and what its proponents have acknowledged (Zurek 2003; Schlosshauer 2005), is select one outcome from the mixture. The improper mixture represents the system's entanglement with the environment; it does not represent ignorance of a pre-existing definite outcome. The diagonal density matrix

$$\rho_S \approx \sum_i \lvert c_i \rvert^2 \lvert a_i \rangle \langle a_i \rvert$$

says that each outcome $a_i$ is weighted by $\lvert c_i \rvert^2$, but it does not say which one obtains. Decoherence explains the *absence of interference* between alternatives. It does not explain the *presence of a definite outcome*.

In LRT's vocabulary: decoherence is a process within $I_\infty$ that brings a configuration to the threshold of $L_3$-resolvability. It transforms a superposition (where the alternatives are not yet mutually exclusive propositions at the level of the pointer basis) into a decohered mixture (where they are). This is the physical work that decoherence does. It is necessary and substantial. But it is not the whole story.

#### $L_3$: The Logical Verdict

Once the alternatives are mutually exclusive and exhaustive — that is, once the configuration is such that the propositions "outcome $a_i$ obtains" and "outcome $a_j$ obtains" ($i \neq j$) are genuinely contradictory — $L_3$ becomes operative:

- **Identity:** Each alternative $a_i$ is what it is. The alternatives are determinate, distinguishable options.
- **Non-Contradiction:** It is not the case that both $a_i$ and $a_j$ ($i \neq j$) obtain. The system cannot be in two determinate states simultaneously.
- **Excluded Middle:** Either $a_i$ obtains or it does not. For the complete set of alternatives, exactly one must obtain.

This is not a physical mechanism. It is the application of the ontological constraints that constitute $L_3$ to a configuration that has been brought (by decoherence) into the scope where they apply. The "verdict" is the logical fact that a definite outcome is required.

#### $A$: Delivery

$A$ is the primitive that actualizes one alternative. It is Boolean:

$$A(a_i, c) \in \{1, 0\}$$

with exactly one $a_i$ receiving $A = 1$. The probability distribution over outcomes is the Born rule, forced by Gleason's theorem given the PVM structure that $A$'s Boolean character entails (Paper II, Steps 4-6).

$A$ is not a hidden variable. It does not carry information about which outcome will be selected prior to the conditions for selection being met. It is the irreducible operation by which one configuration among the $L_3$-admissible alternatives becomes actual. Its irreducibility is what makes the measurement problem *dissolve* rather than *be solved*: there is no further mechanism behind $A$ because $A$ is a primitive, and the demand for a mechanism behind it is the demand for a reduction that the ontology rejects.

### 2.3 Why This Is Not Just "Interpretation"

The Resolution Thesis differs from competing interpretations in a specific structural way: it does not add to the formalism, modify the formalism, or reinterpret the formalism. It *relocates the explanatory burden*.

| Program | What it does to the formalism | Status of "collapse" |
|---|---|---|
| Copenhagen | Adds a classical-quantum cut | Real but unexplained |
| GRW/CSL | Modifies Schrödinger equation | Real dynamical process |
| Many-Worlds | Takes formalism literally | Apparent (all branches real) |
| Bohmian mechanics | Adds guidance equation + hidden variables | Apparent (particle always has definite position) |
| QBism | Reinterprets probabilities as credences | Credence update, not physical |
| Decoherence-alone | No modification | Claimed to be explained; actually incomplete |
| **LRT Resolution** | **No modification** | **Category error: logical resolution, not dynamics** |

The key distinction is between LRT and the decoherence-alone program. Both deny that collapse is a dynamical process. But the decoherence-alone program has no account of why one outcome rather than none obtains from the decohered mixture. LRT supplies this: $L_3$ requires it, $A$ does it.

---

## 3. Applications

### 3.1 The Double-Slit Experiment

**Setup.** A particle passes through a double slit and is detected at a screen.

**Standard narrative.** Without which-path information, the particle "goes through both slits" as a superposition and interferes with itself. With which-path detection, the interference pattern disappears — the wavefunction "collapses" at the slit.

**Resolution account.** The particle's path degree of freedom is a configuration in $I_\infty$. Without which-path detection, the configuration remains unresolved with respect to path: the two-slit superposition evolves unitarily and produces interference at the screen. The interference pattern is a feature of the configuration's structure in $I_\infty$, not of a physical object passing through both slits.

When a which-path detector is introduced, it decoheres the path degree of freedom: the detector-particle interaction produces entanglement that suppresses interference between the two path alternatives. The path alternatives become $L_3$-resolvable — they are now mutually exclusive propositions about which slit the particle traverses. Excluded Middle requires a verdict. $A$ delivers one. The interference pattern disappears because the configuration is now resolved with respect to path, not because a wavefunction was interrupted.

The transition from "interference" to "no interference" is the transition from an unresolved configuration in $I_\infty$ to a resolved one — from a state where $L_3$ is not yet operative with respect to path to one where it is.

### 3.2 Schrödinger's Cat

**Standard narrative.** A cat in a sealed box is entangled with a radioactive atom. Until the box is opened, the cat is in a superposition of alive and dead. "Collapse" occurs upon observation.

**Resolution account.** The cat is a macroscopic system. Its degrees of freedom are decohered on timescales of order $10^{-20}$ seconds. The cat's viability (alive/dead) is resolved essentially instantaneously after the radioactive decay event — long before any observer opens the box.

What resolves the cat's state is not observation but the physical conditions of decoherence acting on the cat's macroscopic degrees of freedom. Once the decay has occurred and the lethal mechanism has been triggered, the cat's state is decohered into $L_3$-resolvable alternatives. Excluded Middle requires a verdict. $A$ delivers it. The cat is determinately alive or dead from the moment the physical conditions produce decoherence, regardless of whether anyone looks.

The "paradox" arises from treating the observer as necessary for collapse. Under the Resolution Thesis, the observer is irrelevant to resolution. What matters is decoherence — the physical conditions under which $L_3$ becomes operative. The cat is not in superposition, and never was, because the conditions for logical resolution are met almost instantaneously at macroscopic scales.

### 3.3 Wigner's Friend

**Setup.** Wigner's friend performs a measurement inside a sealed laboratory. Wigner, outside, describes the laboratory (friend included) as a quantum system in superposition.

**Standard narrative.** There is a tension between the friend's experience of a definite outcome and Wigner's description of the laboratory as being in superposition. Recent extended Wigner's friend scenarios (Frauchiger and Renner 2018; Brukner 2018) sharpen this into apparent contradictions.

**Resolution account.** The friend's measurement apparatus interacts with the quantum system within the sealed laboratory. This interaction produces decoherence of the measured observable relative to the apparatus pointer basis. Within the laboratory, the conditions for $L_3$-resolution are met: the alternatives become mutually exclusive and exhaustive. Excluded Middle requires a verdict. $A$ delivers it. The friend observes a definite outcome.

Wigner's description of the laboratory as "in superposition" is a description of the laboratory's configuration in $I_\infty$ relative to *Wigner's* accessible degrees of freedom. The information about which outcome the friend obtained is encoded in the laboratory-environment entanglement and is not available to Wigner without opening the laboratory. But the outcome is *resolved* — it belongs to $A_\Omega$ — regardless of Wigner's description. Wigner's superposition is not a statement about reality's indeterminacy; it is a statement about Wigner's informational access to a resolution that has already occurred.

The tension dissolves: there is no contradiction between "the friend has a definite outcome" and "Wigner describes the laboratory in superposition," because the first concerns $A_\Omega$ and the second concerns a configuration in $I_\infty$ relative to an external observer's informational perspective.

### 3.4 Delayed Choice and Wheeler's Smoky Dragon

**Setup.** In Wheeler's delayed-choice experiment, the decision to observe interference or which-path information is made after the particle has passed through the slits.

**Standard narrative.** The experimenter's later choice "retroactively determines" whether the particle went through one slit or both. The past seems to depend on the future.

**Resolution account.** No degree of freedom is resolved until the conditions for $L_3$-resolution are met. The path degree of freedom remains unresolved in $I_\infty$ as the particle traverses the slits — not because the particle is "in two places at once" but because no physical process has yet decohered the path alternatives into $L_3$-resolvable propositions. The decision to insert or remove the final beam splitter determines which degree of freedom is decohered at the detection stage: with the beam splitter, the which-path information is erased and interference is restored; without it, the path alternatives are decohered and resolved.

Nothing retroactive occurs. The configuration in $I_\infty$ evolves unitarily throughout. The timing of resolution depends on the timing of decoherence, which depends on the experimental arrangement. The "delayed choice" is delayed decoherence, and there is nothing mysterious about the conditions for resolution being established at a later time than the passage through the slits.

---

## 4. Why the Measurement Problem Was Malformed

### 4.1 Three Problems, Three Dissolutions

Paper V (§1) identified three sub-problems: the problem of outcomes, the preferred basis problem, and the problem of statistics. The Resolution Thesis addresses each:

**The problem of outcomes** asks: why does a definite outcome occur when unitary evolution predicts continued superposition? The Resolution Thesis answers: unitary evolution governs configurations in $I_\infty$. Definite outcomes belong to $A_\Omega$. The transition is not a failure of unitarity but the operation of $A$ under $L_3$ when decoherence provides the conditions. Unitarity is not violated because unitarity governs $I_\infty$ and resolution governs the $I_\infty \to A_\Omega$ interface.

**The preferred basis problem** asks: what determines which observable is measured? The Resolution Thesis answers: decoherence determines the pointer basis — the basis in which environmental interaction renders the alternatives $L_3$-resolvable. This is the einselection mechanism (Zurek 2003), adopted without modification. The preferred basis is not imposed by an observer or by an ad hoc postulate; it is selected by the physical dynamics of system-environment interaction.

**The problem of statistics** asks: why the Born rule? The Resolution Thesis inherits the answer from Papers II and IV: the Born rule is the unique probability measure on a Hilbert space equipped with projection-valued measures (Gleason 1957), and the PVM structure is forced by the Boolean character of $A$ under $L_3$. The statistics are not an additional postulate but a theorem given the ontological structure.

### 4.2 The Source of the Malformation

The measurement problem was malformed because it presupposed that all legitimate explanations must be dynamical. This presupposition is natural within a framework where the wavefunction is ontologically primary — if the wavefunction is all there is, then any change to the wavefunction must have a dynamical account.

But the wavefunction is not all there is. Under LRT, the wavefunction is a description of a configuration in $I_\infty$. The actualized domain $A_\Omega$ is ontologically distinct from $I_\infty$. The transition from $I_\infty$ to $A_\Omega$ is not a change within a single ontological domain; it is the interface between two domains.

Demanding a dynamical mechanism for this interface is like demanding a causal mechanism for the fact that contradictions don't obtain. The non-obtaining of contradictions is not caused by anything — it is constituted by $L_3$. Similarly, the obtaining of definite outcomes is not caused by a physical mechanism — it is constituted by $L_3$ acting through $A$ on configurations that decoherence has brought to the threshold of resolvability.

### 4.3 Decoherence Provides Conditions, $L_3$ Provides the Verdict, $A$ Delivers It

This three-part slogan captures the Resolution Thesis in a form that can be tested against every measurement scenario:

1. **Is there a decoherence mechanism?** Identify the physical interaction between system and environment that produces einselection and suppresses interference. If no such mechanism exists (e.g., in a perfectly isolated system), no resolution occurs and the configuration remains unresolved in $I_\infty$.

2. **Are the alternatives $L_3$-resolvable?** After decoherence, are the remaining alternatives mutually exclusive and exhaustive with respect to the pointer basis? If yes, $L_3$ requires a verdict.

3. **Does $A$ deliver a definite outcome?** Yes, by its Boolean character, with probability given by the Born rule.

The three-part structure explains why decoherence is necessary but not sufficient (it provides conditions but not the verdict), why $L_3$ is necessary but not independently operative (it provides the verdict but only when conditions are met), and why $A$ is necessary but not informative in isolation (it delivers the outcome but only when both conditions and verdict are in place).

---

## 5. Comparison with Competing Programs

### 5.1 Dynamical Collapse (GRW/CSL)

The GRW (Ghirardi, Rimini, and Weber 1986) and CSL (Pearle 1989; Ghirardi, Pearle, and Rimini 1990) programs modify the Schrödinger equation by adding stochastic terms that produce spontaneous localization. The modification introduces two free parameters: a collapse rate $\lambda_{\text{GRW}} \approx 10^{-16}$ s$^{-1}$ per particle and a localization width $r_C \approx 10^{-7}$ m.

**Agreement with LRT:** Both programs hold that definite outcomes are real, objective, and not observer-dependent. Both deny that unitary evolution alone is sufficient for definite outcomes.

**Disagreement:** GRW/CSL treats collapse as a genuine dynamical process — a physical event that modifies the state vector. LRT denies this. Under the Resolution Thesis, what GRW/CSL models as spontaneous collapse is better understood as the onset of decoherence-driven $L_3$-resolution. The GRW rate $\lambda$ parameterizes the *conditions* under which resolution occurs, but the resolution itself is logical, not dynamical.

**Empirical discrimination:** GRW/CSL makes specific predictions that differ from standard quantum mechanics at mesoscopic scales — anomalous heating of bulk matter, spontaneous radiation from charged particles, and deviations from unitarity in interferometric experiments (Adler 2007; Bassi *et al.* 2013). Current experiments constrain but have not yet confirmed or excluded the GRW parameters. LRT predicts no deviation from standard quantum mechanics at any scale: the formalism is not modified, only grounded differently. Detection of GRW-type anomalies would be evidence against the Resolution Thesis; their continued absence is consistent with it.

### 5.2 Decoherence-Alone

The decoherence program (Zurek 1981, 2003; Joos *et al.* 2003; Schlosshauer 2005, 2007) demonstrates that environmental interaction suppresses interference between pointer-basis alternatives on extremely short timescales. Some proponents have suggested that decoherence, by itself, solves the measurement problem.

**Agreement with LRT:** Decoherence is essential. The einselection mechanism correctly identifies the pointer basis. The timescales are correct.

**Disagreement:** Decoherence alone does not produce outcomes. The decohered density matrix

$$\rho_S \approx \sum_i \lvert c_i \rvert^2 \lvert a_i \rangle \langle a_i \rvert$$

is an *improper* mixture — it arises from tracing over the environment, not from ignorance of a pre-existing definite state. As Schlosshauer (2005) notes: "Decoherence tells us why we do not observe certain things (such as interference at the macroscopic level). It does not tell us why we observe particular things."

LRT supplies what decoherence lacks: the $L_3$-verdict that a definite outcome must obtain, and the $A$-primitive that delivers it. The Resolution Thesis can be understood as completing the decoherence program with the ontological resources it was missing.

### 5.3 Many-Worlds (Everett)

The Everettian program (Everett 1957; DeWitt 1970; Wallace 2012; Carroll 2019) takes the quantum formalism at face value: the wavefunction never collapses, all branches of the superposition are equally real, and the appearance of collapse is explained by decoherence-induced branching.

**Agreement with LRT:** Both deny that collapse is a dynamical process. Both take decoherence seriously as the mechanism that produces effective classicality.

**Disagreement:** Many-Worlds denies that a single definite outcome occurs. All outcomes occur, in different branches. The appearance of a single outcome is explained by the observer's location within one branch.

LRT denies the existence of branches as ontologically real. $A$ is Boolean: for every actualization event, exactly one outcome obtains ($A = 1$) and the rest do not ($A = 0$). There is no sense in which the non-actualized alternatives persist as real branches. The "other outcomes" are configurations in $I_\infty$ that were $L_3$-admissible but were not selected by $A$. They are *possible* but not *actual*.

The Many-Worlds program also faces the probability problem: in a deterministic branching universe, what does it mean to say that an outcome has probability $\lvert c_k \rvert^2$? Various proposals (decision-theoretic: Deutsch 1999, Wallace 2012; self-locating uncertainty: Vaidman 2012; branch counting: Kent 2010) remain contested. LRT faces no probability problem because the Born rule is derived from Gleason's theorem applied to the PVM structure forced by $A$'s Boolean character (Paper II).

### 5.4 Bohmian Mechanics

Bohmian mechanics (Bohm 1952; Dürr, Goldstein, and Zanghì 1992) adds definite particle positions and a guidance equation to the quantum formalism. Particles always have definite positions; the wavefunction guides their motion.

**Agreement with LRT:** Both insist that definite outcomes really occur. Both deny that measurement outcomes are observer-dependent.

**Disagreement:** Bohmian mechanics locates definiteness in hidden variables (particle positions) that exist at all times. LRT locates definiteness in the actualization primitive $A$ operating under $L_3$, with resolution occurring when decoherence provides the conditions. Bohmian mechanics requires a preferred basis (position) as primitive; LRT derives the preferred basis from einselection.

Bohmian mechanics is also explicitly nonlocal: the guidance equation couples all particles instantaneously. LRT's treatment of nonlocality (Paper VI) distributes nonseparability to $I_\infty$ and locality to $A_\Omega$, avoiding primitive nonlocal dynamics.

---

## 6. Objections and Responses

### 6.1 "This Just Relabels the Problem"

**Objection:** You have replaced "collapse" with "logical resolution" and "$A$ delivers it." The explanatory situation is unchanged: we still don't know why one outcome rather than another occurs.

**Response:** The objection conflates two questions. *Why does a definite outcome occur?* — this is answered: $L_3$ requires it once decoherence provides the conditions. *Why this outcome rather than that one?* — this is answered probabilistically: the Born rule gives the probability of each outcome, and $A$ is the primitive that selects one. The demand for a deeper answer to the second question is the demand for a deterministic explanation of an irreducibly probabilistic process. No interpretation provides this. The Resolution Thesis does not claim to explain why a particular outcome occurs; it claims to explain why a *definite* outcome must occur and why asking for a dynamical mechanism behind that definiteness is a category error.

### 6.2 "Decoherence Is Not Sharp Enough"

**Objection:** Decoherence suppresses off-diagonal terms but never exactly eliminates them. The density matrix is never exactly diagonal. So the alternatives are never *exactly* mutually exclusive, and $L_3$ never *exactly* applies.

**Response:** This objection has force and identifies a genuine open problem. The exact condition under which a degree of freedom enters the scope of $L_3$-resolution — the *actualization threshold* — is identified in Paper V as the principal open question of LRT's measurement account.

Two responses mitigate the concern. First, decoherence is not merely approximate in a worrying sense. For macroscopic systems, the off-diagonal suppression factor is of order $e^{-N}$ where $N$ is the number of environmental degrees of freedom — a number so astronomically small (for pointer-scale objects, typically $10^{-10^{20}}$ or smaller) that no physical process could ever detect the residual coherence. The $L_3$ threshold need not be mathematically exact to be physically operative.

Second, the threshold question is not unique to LRT. Every interpretation that appeals to decoherence faces the same issue. The Many-Worlds program must specify when branching occurs (the "branch structure problem"). The decoherence-alone program must specify when the mixture becomes "classical enough." GRW/CSL parameterize the threshold explicitly. LRT is transparent about the open problem rather than concealing it.

### 6.3 "The Primitives Are Doing No Work — Decoherence Already Explains Everything"

**Objection:** Decoherence explains the preferred basis, the timescales, and the emergence of classicality. Adding $L_3$ and $A$ is unnecessary metaphysical baggage.

**Response:** Decoherence does not explain why a definite outcome occurs (§5.2). This is not a controversial claim; it is acknowledged by the leading proponents of the decoherence program. Zurek (2003) explicitly notes that decoherence explains the selection of the pointer basis and the suppression of interference but does not by itself yield definite outcomes. Schlosshauer's (2005, 2007) comprehensive reviews reach the same conclusion.

$L_3$ and $A$ are not baggage; they are the missing components that complete the account. Without them, the decoherence program either (a) silently appeals to something else (the Born rule postulate, an observer, an Everettian branching structure) or (b) claims a solution it has not provided.

### 6.4 "$A$ Is Just God-of-the-Gaps for Quantum Mechanics"

**Objection:** Invoking an irreducible "actualization primitive" is no different from saying "and then a miracle happens."

**Response:** $A$ is not invoked to fill a gap in our knowledge. It is posited as a primitive — a terminus of explanation, like charge in electrodynamics or spacetime in general relativity. Every physical theory has primitives that are not further explained. The question is whether the primitives are well-motivated and whether they do explanatory work.

$A$ is motivated by the transcendental argument (Paper I): the denial of actualization is self-undermining, since denying that anything is actual is itself an actual claim. $A$ does explanatory work: together with $L_3$, it forces PVM structure, the Born rule, and definite outcomes. A primitive that generates this much structure from this little input is not a gap-filler; it is an economical foundation.

---

## 7. The Resolution Thesis and the Unity of LRT

### 7.1 Connections to Prior Papers

The Resolution Thesis is not a standalone proposal. It is the natural terminus of the LRT program as developed across Papers 0-VI:

- **Paper 0 (TRM Foundations):** Established the co-primitive ontology $\chi \equiv [L_3 : I_\infty : A]$ and the bridge equation $A_\Omega = L_3(I_\infty)$.
- **Paper I (Transcendental Argument):** Defended the transcendental necessity of $L_3$ and $A$, and the pragmatic necessity of $I_\infty$.
- **Paper II (Core Physics):** Derived the 13-step reconstruction chain from $\chi$ to the Schrödinger equation, establishing PVM structure (Step 4-5), the Born rule (Step 6), and unitary dynamics (Steps 7-10).
- **Paper IV (How Come the Quantum):** Showed that quantum structure is a downstream consequence of $\chi$, answering Wheeler's question.
- **Paper V (Measurement):** Developed the partial actualization framework, identifying the $I_\infty \to A_\Omega$ interface as the locus of measurement and the actualization threshold as the principal open problem.
- **Paper VI (Entanglement):** Demonstrated that nonlocality resides in $I_\infty$ (non-decomposable configurations) while locality resides in $A_\Omega$ (Boolean actualization is local).

The Resolution Thesis synthesizes these results. The "measurement problem" dissolves because:

1. The formalism is grounded, not brute (Paper IV).
2. The two-domain ontology ($I_\infty$ and $A_\Omega$) is motivated (Papers 0, I, II).
3. The interface between domains is characterized by partial actualization (Paper V).
4. Nonlocal correlations are consistent with local actualization (Paper VI).
5. The demand for a collapse mechanism is a category error — confusing a logical requirement for a dynamical deficit.

### 7.2 What Remains Open

The Resolution Thesis does not close all questions. Two principal open problems remain:

**The actualization threshold.** What is the precise, mathematically specifiable condition under which a degree of freedom enters the scope of $L_3$-resolution? Paper V identified this as open. The present paper has not resolved it. The most promising avenue is a formal characterization in terms of the decoherence factor: $L_3$ becomes operative when the off-diagonal suppression reaches a scale at which the residual coherence is below some threshold. Whether this threshold is sharp or itself admits of degrees is unknown.

**The relativistic extension.** The Resolution Thesis is developed within non-relativistic quantum mechanics. The extension to quantum field theory — where "measurement" is even less well-defined and the notion of a preferred time-slice is unavailable — remains open. Paper II (§8) identified this as the principal limitation of the current reconstruction.

---

## 8. Conclusion

The word "collapse" has haunted quantum mechanics for a century. It has generated an industry of interpretations, modifications, and philosophical perplexities — all because of an unexamined presupposition: that the wavefunction is ontologically primary and that any transition from superposition to definite outcome requires a dynamical account.

The Resolution Thesis rejects this presupposition. Under LRT, the wavefunction is a description of a configuration in $I_\infty$. Definite outcomes are configurations in $A_\Omega$. The transition is not a dynamical event but the completion of logical resolution: decoherence provides the physical conditions, $L_3$ provides the logical verdict, $A$ delivers the outcome.

The measurement problem was not unsolvable. It was malformed. It asked for a physical mechanism behind a logical requirement. Once the question is corrected, the answer is already present in the primitive ontology that LRT has been developing since Paper 0.

Quantum "collapse" is a category error. The correct term is *resolution*.

---

## References

Adler, S. L. (2007). Lower and upper bounds on CSL parameters from latent image formation and IGM heating. *Journal of Physics A*, 40(12), 2935–2957.

Aspect, A., Dalibard, J., & Roger, G. (1982). Experimental realization of Einstein-Podolsky-Rosen-Bohm Gedankenexperiment: A new violation of Bell's inequalities. *Physical Review Letters*, 49(25), 1804–1807.

Bassi, A., Lochan, K., Satin, S., Singh, T. P., & Ulbricht, H. (2013). Models of wave-function collapse, underlying theories, and experimental tests. *Reviews of Modern Physics*, 85(2), 471–527.

Bohm, D. (1952). A suggested interpretation of the quantum theory in terms of "hidden" variables. *Physical Review*, 85(2), 166–193.

Brukner, Č. (2018). A no-go theorem for observer-independent facts. *Entropy*, 20(5), 350.

Carroll, S. (2019). *Something Deeply Hidden: Quantum Worlds and the Emergence of Spacetime*. Dutton.

Deutsch, D. (1999). Quantum theory of probability and decisions. *Proceedings of the Royal Society A*, 455(1988), 3129–3137.

DeWitt, B. S. (1970). Quantum mechanics and reality. *Physics Today*, 23(9), 30–35.

Dürr, D., Goldstein, S., & Zanghì, N. (1992). Quantum equilibrium and the origin of absolute uncertainty. *Journal of Statistical Physics*, 67(5-6), 843–907.

Everett, H. (1957). "Relative state" formulation of quantum mechanics. *Reviews of Modern Physics*, 29(3), 454–462.

Frauchiger, D., & Renner, R. (2018). Quantum theory cannot consistently describe the use of itself. *Nature Communications*, 9, 3711.

Ghirardi, G. C., Pearle, P., & Rimini, A. (1990). Markov processes in Hilbert space and continuous spontaneous localization of systems of identical particles. *Physical Review A*, 42(1), 78–89.

Ghirardi, G. C., Rimini, A., & Weber, T. (1986). Unified dynamics for microscopic and macroscopic systems. *Physical Review D*, 34(2), 470–491.

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885–893.

Joos, E., Zeh, H. D., Kiefer, C., Giulini, D., Kupsch, J., & Stamatescu, I.-O. (2003). *Decoherence and the Appearance of a Classical World in Quantum Theory* (2nd ed.). Springer.

Kent, A. (2010). One world versus many: The inadequacy of Everettian accounts of evolution, probability, and scientific confirmation. In S. Saunders, J. Barrett, A. Kent, & D. Wallace (Eds.), *Many Worlds? Everett, Quantum Theory, and Reality* (pp. 307–354). Oxford University Press.

Longmire, J. D. (2026a). The Triadic Reality Model: Irreducible Foundations for Physics. Pre-print.

Longmire, J. D. (2026b). Logic Realism Theory: Part II — Physics Reconstruction from $A_\Omega = L_3(I_\infty)$ to the Schrödinger Equation. Pre-print.

Longmire, J. D. (2026c). The Transcendental Argument for Being. Zenodo. https://doi.org/10.5281/zenodo.19226396

Masanes, L., & Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Pearle, P. (1989). Combining stochastic dynamical state-vector reduction with spontaneous localization. *Physical Review A*, 39(5), 2277–2289.

Schlosshauer, M. (2005). Decoherence, the measurement problem, and interpretations of quantum mechanics. *Reviews of Modern Physics*, 76(4), 1267–1305.

Schlosshauer, M. (2007). *Decoherence and the Quantum-to-Classical Transition*. Springer.

Vaidman, L. (2012). Probability in the many-worlds interpretation of quantum mechanics. In Y. Ben-Menahem & M. Hemmo (Eds.), *Probability in Physics* (pp. 299–311). Springer.

Wallace, D. (2012). *The Emergent Multiverse: Quantum Theory According to the Everett Interpretation*. Oxford University Press.

Zurek, W. H. (1981). Pointer basis of quantum apparatus: Into what mixture does the wave packet collapse? *Physical Review D*, 24(6), 1516–1525.

Zurek, W. H. (2003). Decoherence, einselection, and the quantum origins of the classical. *Reviews of Modern Physics*, 75(3), 715–775.
