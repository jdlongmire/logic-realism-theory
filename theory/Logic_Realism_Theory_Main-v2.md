# It from Bit, Bit from Fit: Foundational Physics Logically Remastered

**James (JD) Longmire**\
ORCID: 0009-0009-1383-7698\
Northrop Grumman Fellow (unaffiliated research)

**Version:** 2.0 (December 2025)

---

## Abstract

Every physical measurement ever conducted has yielded exactly one outcome: self-identical, non-contradictory, determinate. This holds across all domains, scales, and epochs of physical inquiry, including a century of quantum mechanics where violations were actively sought.

This paper argues that the Three Fundamental Laws of Logic (Identity, Non-Contradiction, and Excluded Middle) are not cognitive conventions but ontological constraints constitutive of physical distinguishability. From this thesis, quantum mechanics emerges as the unique stable structure at the interface between non-Boolean possibility and Boolean actuality.

The framework derives rather than postulates: complex Hilbert space structure follows from interface constraints combined with the physical requirement of compositional consistency (local tomography); the Born rule follows from Gleason's theorem; unitary dynamics follows from information preservation requirements. These derivations are conditional on both logical (3FLL) and physical (continuity, local tomography) inputs, but this specific combination suffices to reconstruct the theory without independent postulation.

One structural prediction, that quantum mechanics requires complex amplitudes, has been experimentally confirmed (Renou et al., 2021). The framework specifies twelve explicit conditions that would falsify it, including fundamental information loss or underivable collapse parameters, and makes testable predictions about collapse mechanisms currently under experimental investigation.

Logic Realism Theory provides unified explanation for seventeen quantum phenomena that other interpretations treat as independent postulates, while maintaining realism, locality, and parsimony. The competing interpretations either refuse ontological commitment (Copenhagen, QBism), require massive ontological excess (Many-Worlds), or introduce unexplained nonlocal mechanisms (Bohmian, GRW).

The "unreasonable effectiveness of mathematics" in physics is revealed as an illusion caused by viewing physical laws as contingent. By strictly enforcing Global Parsimony, LRT shows that fundamental physical constraints—from the Born Rule to Special Relativity—are the unique mathematical solutions necessary to maintain the Three Fundamental Laws of Logic at the interface of possibility and actuality. There is no "Bit" without the "Fit" of logical consistency.

**Keywords:** quantum foundations, logic realism, Born rule, measurement problem, entanglement, falsifiability

---

## 1. Introduction

### 1.1 The Empirical Puzzle

Every physical measurement ever conducted has yielded exactly one outcome: self-identical, non-contradictory, determinate. No detector has simultaneously fired and not-fired. No particle has been measured in contradictory states. No experimental record has ever displayed P and ¬P.

This pattern holds universally. Across all of physics, chemistry, biology, and engineering, across all scales from Planck length to cosmological horizon, across all epochs from the early universe to the present, the Three Fundamental Laws of Logic (3FLL) have never been violated:

- **Identity:** Everything is what it is (∀x: x = x)
- **Non-Contradiction:** Nothing both is and is not in the same respect (∀x,P: ¬(P(x) ∧ ¬P(x)))
- **Excluded Middle:** Everything either is or is not (∀x,P: P(x) ∨ ¬P(x))

This is not for lack of trying.

Quantum mechanics appeared to offer violations. Superposition looks like "both A and not-A." Entanglement looks like instantaneous contradiction-propagation. The measurement problem looks like contradictory states persisting until observed. For nearly a century, physicists and philosophers actively sought to interpret quantum mechanics as requiring non-classical logic.

Birkhoff and von Neumann (1936) proposed quantum logic with non-distributive structure. Paraconsistent approaches attempted to formalize quantum states as true contradictions. The measurement problem generated interpretations explicitly designed to accommodate logical indeterminacy. Sophisticated formal tools were developed. Professional incentives favored finding violations; it would have been a major result.

Every attempt failed.

The failure was not for lack of formal resources. Paraconsistent logics, developed rigorously since the 1960s (da Costa 1963; Priest & Routley 1989), provide mathematical frameworks where contradictions do not entail everything. Dialetheism, the view that some contradictions are true, has been seriously defended by philosophers including Graham Priest, who argues that semantic paradoxes, vagueness, and even motion involve true contradictions (Priest 2006). Impossible worlds semantics models scenarios where classical logic fails (Berto & Jago 2019). Buddhist logic explored four-valued structures (catuṣkoṭi) for millennia before Western analytic philosophy engaged these questions.

These are not idle speculations. Paraconsistent logic has an official American Mathematical Society classification (03B53). Five World Congresses on Paraconsistency have convened since 1997. The formal apparatus for conceiving and reasoning about 3FLL violations is mature and mathematically rigorous.

Yet no physical observation has ever instantiated what these frameworks describe. The gap between formal conceivability and physical actuality is the core explanandum.

Upon careful analysis, every apparent violation dissolved. Superposition is indeterminacy prior to measurement, not contradiction in actuality. Entanglement produces correlations, not signals. Wave-particle duality reflects complementary experimental contexts, not contradictory properties. And measurement, always, without exception, yields one definite outcome.

The quantum case is decisive precisely because it represents our best opportunity to find violations. If 3FLL were going to fail anywhere in physics, quantum mechanics is where it would happen. The formalism practically invites the interpretation that contradictions are real. Yet the logical structure holds.

This pattern demands explanation.

The demand is not merely philosophical. Quantum mechanics is our most successful physical theory, yet we cannot say why it has its specific structure: why complex Hilbert space, why the Born rule, why unitary dynamics. This explanatory vacuum has consequences. Without agreed-upon criteria for what counts as explanation, quantum foundations tolerates speculation other fields would not: infinite unobservable branches, consciousness-caused collapse, retrocausality. "Interpretation" becomes license for speculation unconstrained by structural requirements. Meanwhile, practical developments (quantum computing, quantum gravity) require foundational clarity we do not have. The pattern demands explanation, and the explanation must be disciplined.

### 1.2 The Thesis

This paper defends a physical thesis:

> **The Three Fundamental Laws of Logic are ontological constraints constitutive of physical distinguishability itself.**

Distinguishability, the capacity for one thing to be different from another, is not discovered in the world. It is what 3FLL establish. Without Identity, there is no basis for a state to be determinately itself. Without Non-Contradiction, there is no basis for a state to exclude alternatives. Without Excluded Middle, there is no basis for exhaustive distinction.

The laws are not rules we impose on experience. They are conditions under which experience, and physical existence, are possible.

### 1.3 The Asymmetry of Burden

The claim that the Three Fundamental Laws of Logic are merely formal, cognitive, linguistic, or contingently emergent carries a precise and unmet evidential obligation:

> Any critic who denies their ontological and constitutive status must produce at least one verified instance of a well-defined physical observable actualizing a non-Boolean or contradictory outcome in the historical record of measurement.

No such instance exists.

Every detector click, every photographic plate spot, every CCD pixel, every gravitational-wave strain datum, every spectroscopic line, trillions of independent events across thirteen-plus orders of magnitude in energy and fourteen billion years, has been strictly self-identical, non-contradictory, and determinate. The conformity is not probabilistic; it is absolute.

Until a single counterexample is exhibited, the universality of 3FLL compliance stands as an unexplained brute fact on any view that treats the laws as optional. Logic Realism Theory removes the brute fact by elevating the laws from unexplained regularities to the constitutive conditions of physical distinguishability itself.

The burden therefore lies entirely with the objector. LRT discharges its burden by showing that quantum mechanics is the unique stable structure compatible with that constitutive role.

### 1.4 The Consequence

If 3FLL are constitutive of distinguishability, a structural consequence follows.

Define two domains:

- **Infinite Information Space (IIS):** The totality of distinguishable configurations, everything that can be distinguished from everything else. This space is constituted by 3FLL and contains both determinate and indeterminate states.

- **Boolean Actuality:** The domain where 3FLL are fully enforced, where every proposition has exactly one truth value. This is what we call physical reality.

IIS is richer than Boolean structure. It contains superpositions, indeterminate configurations, states not yet resolved to definite values. Boolean actuality permits only determinate states.

This creates an interface problem: what structure mediates between non-Boolean IIS and Boolean actuality?

The answer is quantum mechanics.

Quantum mechanics is not one option among many. Given the constraints that 3FLL impose on any transition from possibility to actuality, quantum mechanics is the unique stable interface structure. Classical probability satisfies formal interface requirements but produces no stable atoms, no chemistry, no observers. Real and quaternionic quantum theories fail compositional requirements. Generalized probabilistic theories exceeding quantum correlations permit signaling. Only complex Hilbert space quantum mechanics with the Born rule produces stable physical existence.

This is the central claim: quantum mechanics has its specific structure because that structure is uniquely selected by the requirements of the IIS-actuality interface.

### 1.5 What This Paper Establishes

The argument proceeds as follows:

**Section 2** develops the framework: IIS, Boolean actuality, the interface problem, and the Consistency Bridging Principle that constrains admissible dynamics.

**Section 3** presents the derivation chain: from 3FLL, interface constraints, and physical requirements (continuity, local tomography) to complex Hilbert space, the Born rule, and unitary dynamics. Key results are derived from this combined foundation, not postulated independently.

**Section 4** shows what the framework explains: seventeen quantum phenomena receive unified explanation from common resources.

**Section 5** compares Logic Realism Theory (LRT) to competing interpretations, evaluating each as a physical theory on common criteria.

**Section 6** presents predictions and falsifiers: what LRT implies, what has been confirmed, what is currently testable, and what would refute the theory.

**Section 7** addresses open questions and concludes.

### 1.6 What This Paper Claims and Does Not Claim

**LRT claims:**

- 3FLL are ontological, not merely cognitive or linguistic
- Quantum mechanics is the unique stable IIS-actuality interface
- This explains otherwise unexplained features of quantum structure
- The framework is empirically falsifiable

**LRT does not claim:**

- Quantum mechanics is logically necessary (it is structurally selected)
- All of physics derives from logic alone (physical constraints are also required)
- The measurement problem is dynamically solved (it is structurally dissolved)
- All open questions are answered (several are explicitly identified)

**Scope clarification:** LRT's constitutive claim targets the *actuality/record layer*—the domain where measurement outcomes are registered and information is stably propagated. The claim is that any physically implementable measurement architecture capable of carrying stable information must terminate in Boolean records, and therefore 3FLL are constitutive of the only layer at which physics is operationally defined. What lies "beneath" or "beyond" this layer—the metaphysics of IIS prior to actualization—is constrained by architecture but not directly accessed by experiment. This is not a retreat from ontological claims but a clarification of their scope: LRT makes strong claims about the structure of physical accessibility, not about inaccessible domains.

The distinction between derivation and selection is crucial. We do not derive quantum mechanics from pure logic. We show that quantum mechanics is the unique structure compatible with stable information-bearing existence given the interface requirements. This is a selection claim with empirical content, not a claim of logical necessity.

---

## 2. The Framework

### 2.1 Distinguishability and the Three Laws

Distinguishability is not a primitive feature of reality that we discover. It is what the Three Fundamental Laws establish.

For state A to be distinguishable from state B:

- **Identity** must hold: A = A and B = B. Each state must be determinately itself.
- **Non-Contradiction** must hold: It cannot be that A = B and A ≠ B simultaneously.
- **Excluded Middle** must hold: Either A = B or A ≠ B. No indeterminate middle.

Without these conditions, there is no basis for one state to differ from another. Distinguishability just *is* the application of 3FLL to a domain. The laws do not describe distinguishability; they constitute it.

This claim invites a circularity objection: are we defining distinguishability in terms of 3FLL, then claiming 3FLL are necessary for distinguishability? No. The argument is transcendental, not definitional. We ask: what must be the case for distinguishability to be possible at all? For state A to be distinguished from state B, A must be determinately A (Identity), A must not simultaneously be B and not-B (Non-Contradiction), and A must either be B or not be B (Excluded Middle). These are not stipulations about what "distinguishability" means; they are conditions without which distinction cannot obtain. The question is not "what do we mean by distinguishability?" but "what makes distinguishability possible?" The answer is 3FLL.

This is the foundational claim of Logic Realism Theory. The laws are not cognitive filters we impose, not linguistic conventions we adopt, not useful approximations we employ. They are the conditions under which anything can be distinguished from anything else. The Technical companion (Theorem 7.1) proves this claim is ontic rather than epistemic: the continuity structure of quantum mechanics excludes hidden non-Boolean tokens even at probability zero.

**The measurement-layer argument:** One might object that 3FLL are constitutive only of *our concept* of measurement, not of physics itself. But this objection, properly understood, supports rather than undermines LRT. If any coherent notion of "measurement outcome"—one that yields stable, propagatable records capable of grounding scientific inference—must be Boolean, then 3FLL are constitutive of the only layer at which physics becomes empirically accessible. The question is not whether some exotic non-Boolean "physics" might exist beyond measurement, but whether such a domain could ever manifest in any operationally meaningful way. If it cannot, then 3FLL constrain everything that physics can coherently describe. The "middle position" (3FLL are constitutive of measurement concepts) is not a rival to LRT but a special case of it.

### 2.2 The Infinite Information Space

**Definition:** The Infinite Information Space (IIS) is the totality of distinguishable configurations, every state that can be distinguished from every other state, as constituted by 3FLL. IIS is infinite in the sense that the space of distinguishable configurations is unbounded; there is no finite limit to the distinctions that can be drawn.

IIS is not:
- A Platonic realm of abstract objects
- A set-theoretic construction (which would face cardinality paradoxes)
- Merely epistemic (representing what we don't know)
- Exotic new ontology added to physics

**IIS is what physics already uses.** Consider what physicists routinely treat as real: Hilbert space (infinite-dimensional, not embedded in spacetime), configuration space (3N dimensions for N particles), Fock space (variable particle number), phase space (the arena for statistical mechanics). These mathematical structures are not "in" physical space, yet physics operates with them as describing something physically meaningful. IIS names what these structures represent: the space of distinguishable possibilities. The question for skeptics is not "how can IIS be real?" but "what do you think Hilbert space describes?" If the wavefunction is physically meaningful, it must represent something. IIS is explicit about what.

IIS is the structural space of what *can be distinguished*. Its existence is not the existence of a thing among things, but the existence of a structural condition, the condition under which distinct states are possible at all.

**Co-primitive with 3FLL:** IIS and 3FLL are mutually constitutive. Without 3FLL, IIS would be undifferentiated noise, no state distinguishable from any other. Without IIS, 3FLL would have nothing to structure. This parallels Borges' Library of Babel: IIS contains every possible informational configuration; 3FLL make the library navigable by constituting what makes one configuration distinguishable from another.

**Functional characterization:** IIS is characterized functionally rather than by stipulating a mathematical structure at the outset. Its properties are *derived*, not assumed. Premature mathematization would beg questions about which formalism applies.

What we can say prior to derivation:
- IIS is not Boolean (contains determinate states, indeterminate states, superpositions, classical mixtures)
- IIS is structured by distinguishability; the "metric" is how distinguishable states are from each other
- IIS contains all consistent Generalized Probabilistic Theories (GPTs) as substructures (Hardy, 2001; Chiribella et al., 2011)

**Mathematical characterization:** IIS can be formally defined as the maximal collection of states closed under distinguishability:

$$\mathcal{I} = \{s : D \text{ is defined on } s \times \mathcal{I}\}$$

The derivation chain (Section 3) shows that IIS, equipped with the inner product induced by distinguishability, has complex Hilbert space form at the interface with Boolean actuality. This result invokes the Masanes-Müller reconstruction theorem. The mathematical structure *emerges* from the framework rather than being imposed on it.

**Physical interpretation:** For familiar quantum systems, IIS takes concrete form. A single qubit's IIS is the Bloch sphere, with the distinguishability metric $D$ giving the trace distance between states. In a two-slit experiment, the superposition state resides in IIS with definite identity (it is determinately $|\psi\rangle$) while lacking definite which-path information. For composite systems, entangled states represent correlation structures in IIS not reducible to subsystem states. The Technical companion (§3.4) develops these examples in detail, showing how the abstract IIS definition maps onto the standard quantum formalism.

Crucially, IIS is richer than Boolean structure. It contains:

| State Type | Description |
|------------|-------------|
| Determinate states | Fully specified configurations |
| Indeterminate states | Distinguishable but not resolved to definite values |
| Superpositions | Specific indeterminate states with interference structure |
| Mixtures | Probabilistic combinations without interference |

Indeterminacy is not contradiction. A state can be distinguishable from other states without having definite values for all properties. This distinction is essential: IIS contains genuine indeterminacy; it does not contain contradictions.

### 2.3 Boolean Actuality

**Definition:** Boolean Actuality is the domain where 3FLL are fully enforced, where every proposition about the state of affairs has exactly one truth value.

When something becomes actual, when it manifests as a physical state of affairs, it must satisfy 3FLL completely:

- **Identity:** The state is determinately what it is
- **Non-Contradiction:** The state does not both have and lack any property
- **Excluded Middle:** For any well-defined property, the state either has it or does not

Actuality is Boolean. Every measurement outcome is definite. Every physical record is determinate. Every causal interaction involves states that are one way rather than another.

This is not an interpretation. It is what we observe. Every measurement, without exception, yields one outcome.

### 2.4 The Interface Problem

The asymmetry between IIS and Boolean actuality creates a fundamental structural problem:

| Domain | Structure | Content |
|--------|-----------|---------|
| IIS | Non-Boolean | Determinate and indeterminate states |
| Actuality | Boolean | Only determinate states |

IIS contains more than actuality can accommodate. Superpositions exist as elements of IIS but cannot exist as actualized facts. Something must connect these domains.

This is the **interface problem**: What structure mediates between non-Boolean IIS and Boolean actuality?

Any interface must satisfy three constraints derived from 3FLL:

1. **Totality** (from Excluded Middle): The interface must be defined for all IIS states. Every state must be capable of yielding a definite outcome.

2. **Single-valuedness** (from Non-Contradiction): No state may yield contradictory outcomes in the same context. The interface produces no contradictions.

3. **Distinguishability-preservation** (from Identity): If states are distinguishable in IIS, their actualization patterns must not collapse that distinction entirely.

Multiple mathematical structures satisfy these formal constraints: classical probability, quantum mechanics, real quantum mechanics, quaternionic quantum mechanics, various generalized probabilistic theories. The interface constraints alone do not uniquely determine the structure.

---

![Figure 1: LRT Ontological Architecture](figures/LRT_Fig-1.jpeg)

**Figure 1.** The ontological architecture of Logic Realism Theory. The Infinite Information Space (IIS), constituted by the Three Fundamental Logical Laws, contains non-Boolean structure including superpositions and indeterminate states. Quantum mechanics operates as the interface, characterized by complex Hilbert space, the Born rule, and unitary dynamics. Boolean Actuality, where 3FLL are fully enforced, contains only definite, self-identical, non-contradictory outcomes. The three laws (Identity, Non-Contradiction, Excluded Middle) run through the entire structure, constituting IIS and constraining actuality.

---

### 2.5 Structural Principle: Consistency Bridging

What constrains dynamics within IIS? Not every conceivable transformation can be physically admissible.

The answer follows from the structure itself:

> **Consistency Bridging Principle (CBP):** Admissible transformations on IIS are only those for which all reachable states can, in principle, participate in a consistent resolution to Boolean actuality.

**Status:** CBP is a *substantive structural principle*, motivated by (but not strictly derived from) the constitutive thesis. We adopt it because it is the formal expression of the requirement that IIS dynamics never strand states with no path to actuality. It is not an arbitrary postulate but a principled constraint: if IIS exists to enable actualization, transformations that sever this connection are inadmissible.

**Alternative considered:** A weaker principle might permit "dead-end" IIS regions—states that can never actualize. Such regions would constitute physically inaccessible structure: distinguishable configurations with no empirical consequences. This alternative (a) reintroduces brute facts about why such regions are never accessed, undermining explanatory unity; and (b) violates the parsimony principle (Section 2.6) by admitting structure with no actualizable consequences. LRT rejects this alternative.

**Comparison:** Other frameworks build in analogous constraints: "no signaling" in operational approaches, "no superdeterministic conspiracies" in Bell analyses, specific collapse postulates in GRW. CBP is not more ad hoc than these; it is the LRT-specific expression of a general requirement that physical structure be empirically accessible.

CBP constrains dynamics to preserve the possibility of consistent actualization. It does not specify *when* actualization occurs or *which* outcome obtains. It constrains what transformations are admissible in the first place.

**Key consequence:** CBP implies that fundamental dynamics must be reversible. Irreversible dynamics destroy information; they map distinct states to the same output. But information destruction requires a mechanism: something must absorb or erase the distinction. Any such mechanism would constitute additional structure beyond IIS and 3FLL. By parsimony (Section 2.6), no such surplus structure exists at the fundamental level. Therefore, fundamental IIS dynamics preserve information.

### 2.6 Structural Principle: Global Parsimony

A principle of parsimony follows from the constitutive role of 3FLL:

If 3FLL constitute distinguishability, and IIS is the space constituted by 3FLL, then actuality contains exactly what this constitutive base generates, no more, no less.

> **Global Parsimony:** Actuality contains exactly the propositions whose truth values are grounded in (3FLL + initial conditions) and their consequences. No surplus structure exists.

**Status:** Global Parsimony is a *substantive structural principle*, motivated by the constitutive thesis. While we present a derivation below, the principle functions as a strong metaphysical commitment: that there can be no distinct physical structure with no new distinguishable consequences. We adopt it because it is the natural closure condition on the constitutive claim—but acknowledge that this "naturalness" argument falls short of logical necessity.

**Derivation:** If 3FLL constitute distinguishability, and all physical structure presupposes distinguishability, then all physical structure must trace to 3FLL. Consider what surplus structure would require: structure not traceable to 3FLL would need distinguishability from outside the only source of distinguishability. But there is no such source available; distinguishability just is what 3FLL establish. Surplus structure is therefore incoherent. Global Parsimony is not an aesthetic preference or methodological heuristic; it is the closure condition on the constitutive claim itself.

**Alternative considered:** A weaker parsimony might allow hidden, irretrievable information—structure that is distinguishable in principle but never accessible in practice. This alternative would (a) undermine the derivation of reversibility by permitting information sinks at the fundamental level; (b) reintroduce unexplained brute facts (why is this information hidden?); and (c) lose the explanatory unity that makes LRT distinctive. LRT rejects this alternative in favor of the stronger principle.

This is a structural consequence of what "constitution" means. If 3FLL constitute the domain, the domain contains what they generate. Propositions requiring additional grounding sources have no truthmakers within the framework.

Global Parsimony has teeth:

- Irreversible fundamental dynamics would require surplus mechanisms → ruled out
- Free parameters not derivable from the constitutive base → ruled out at the fundamental level
- Ontological additions beyond IIS structure → require justification from the constitutive base

A clarification: Global Parsimony applies to *fundamental* structure, not to emergent or contingent physical content. The claim is not that everything is derived from 3FLL; specific particle masses, coupling constants, and gauge groups are empirical. The claim is that no *additional foundational principles* beyond 3FLL are required to ground the structure of physical law. Contingent physical content operates within the framework that 3FLL establish; it does not require independent metaphysical grounding.

### 2.7 Why Quantum Mechanics

Multiple structures satisfy the formal interface constraints. What selects quantum mechanics specifically?

**Stability.**

Classical mechanics satisfies interface constraints but produces no stable physics:
- Electrons spiral into nuclei (no stable atoms)
- No discrete energy levels (no chemistry)
- No quantum tunneling (no stellar fusion)
- No identical particles (no periodic table)

A classical universe contains no stable matter, no chemistry, no life, no observers to notice.

Real quantum mechanics (using ℝ instead of ℂ) fails local tomography: composite system states cannot be fully determined by local measurements. Quaternionic quantum mechanics fails compositional consistency. Generalized probabilistic theories exceeding the Tsirelson bound permit signaling.

Only complex Hilbert space quantum mechanics with unitary dynamics and the Born rule produces:
- Stable atoms (discrete energy levels from spectral properties)
- Chemistry (electron orbitals, bonding, molecular structure)
- Solid matter (Pauli exclusion prevents collapse)
- Stars (quantum tunneling enables fusion)
- Observers (stable structures capable of inquiry)

This is **stability selection**: among structures compatible with the interface constraints, only quantum mechanics produces stable physical existence.

Stability selection explains why we observe quantum mechanics: observers require stable physical structures, and only quantum mechanics produces them. This is an observability filter, not an ontological derivation. The uniqueness claim, that quantum mechanics is the *only* structure satisfying the interface constraints with stability, rests on the mathematical reconstruction theorems (Masanes-Müller, Hardy, Chiribella et al.), which demonstrate that complex Hilbert space quantum mechanics is uniquely selected by the relevant axioms. Stability selection explains why we are in a position to observe this; the reconstruction theorems establish that there is nothing else to observe.

Stability selection is not logical derivation. It does not claim quantum mechanics is necessary. It claims quantum mechanics is *observationally necessary*, necessary for there to be stable structures capable of observation.

### 2.8 The Framework Summarized

| Component | Role |
|-----------|------|
| 3FLL | Constitute distinguishability |
| IIS | Space of all distinguishable configurations |
| Boolean Actuality | Domain where 3FLL are fully enforced |
| Interface | Structure mediating IIS → Actuality |
| CBP | Constrains admissible IIS dynamics |
| Global Parsimony | No surplus structure beyond constitutive base |
| Quantum Mechanics | The unique stable interface |

The central formula:

$$\mathcal{A} = \mathfrak{L}(\mathcal{I})$$

Actuality equals logical filtering (3FLL enforcement + parsimony) applied to the Infinite Information Space.

### 2.9 The Circularity Objection

A natural objection arises: the operational framework used to define distinguishability presupposes classical measurement apparatus. Detectors yield discrete outcomes; laboratory equipment obeys 3FLL. Does this make the derivation circular?

**The objection stated precisely:** If we define the distinguishability metric $D$ in terms of measurement statistics, and measurements presuppose 3FLL-conforming apparatus, then haven't we assumed what we claim to derive?

**The response distinguishes observation from explanation.**

*Observation:* Measurement apparatus conforms to 3FLL. Detectors fire or don't fire. Outcomes are determinate.

*Explanation:* Why does apparatus conform? Two answers are available:

| Answer | Claim | Status |
|--------|-------|--------|
| **Brute fact** | Apparatus just happens to obey 3FLL | No explanation offered |
| **LRT** | 3FLL are constitutive of distinguishability; apparatus conformity follows | Explains the conformity |

The operational framework is not *evidence* for LRT; it is the *explanandum*. LRT explains why the operational framework has the structure it does. Alternatives treat this structure as unexplained background.

**The asymmetry argument:** Consider the conceivability-observability gap:

- We *can conceive* of detectors that fire and don't fire simultaneously
- We *can imagine* measurement outcomes that violate Excluded Middle
- We *can entertain* the proposition that a particle is both detected and not detected

These scenarios are mentally representable. Nothing in cognition prevents us from considering them.

Yet we *never observe* them. No detector in the history of physics has ever produced a 3FLL-violating outcome. This asymmetry requires explanation.

**Psychologism** (3FLL are cognitive constraints) cannot explain this: if 3FLL were merely how we think, we could not conceive of their violation. But we can.

**Conventionalism** (3FLL are linguistic rules) cannot explain this: we could define "outcome" to permit contradictions; we still would not observe them.

**LRT** explains this: 3FLL are constitutive of physical distinguishability itself. Violations are not observed because they cannot occur—not because we cannot think them or have defined them away, but because distinguishability presupposes logical structure.

**The conceivability claim deserves emphasis.** The assertion that we "can conceive" of 3FLL violations is not mere hand-waving. It is backed by rigorous formal development:

| Framework | Key Feature | Status |
|-----------|-------------|--------|
| Paraconsistent logic | Contradictions don't explode | AMS 03B53; five World Congresses |
| Dialetheism | True contradictions exist | Defended by Priest, Routley, Beall |
| Impossible worlds | Logical laws fail at some worlds | Standard in modal metaphysics |
| Buddhist catuṣkoṭi | Four truth values (T, F, both, neither) | 2000+ year tradition |

These frameworks are not conceptual errors waiting to be corrected. They are internally consistent formal systems with sophisticated metatheory. One can reason validly within paraconsistent logic; the inferences are well-defined; the semantics is rigorous.

The question is not whether such reasoning is *possible* (it manifestly is). The question is whether such reasoning describes *actuality*. And here the answer is uniformly negative. No detector, no measurement apparatus, no physical record has ever exhibited a paraconsistent outcome. The formal possibility is real; the physical instantiation is absent.

This is precisely what LRT predicts. Formal systems are not constrained by 3FLL because they are not physical systems; they are abstract structures that can be specified arbitrarily. Physical actuality *is* constrained by 3FLL because distinguishability constitutes it. The conceivability-actuality gap is not a puzzle to be explained away; it is the signature of 3FLL's constitutive role.

**The circularity dissolves:** Yes, the operational framework presupposes 3FLL. This is not a bug but a feature. The question is whether this presupposition is brute (unexplained) or constitutive (explanatory). LRT claims the latter: 3FLL conformity of apparatus is not coincidental background but consequence of what distinguishability requires.

The derivation proceeds as follows:

1. **Given:** Operational framework with 3FLL-conforming measurements (observation)
2. **Claim:** 3FLL are constitutive of distinguishability (hypothesis)
3. **Derivation:** From 3FLL + minimal physics → quantum mechanics (consequence)
4. **Test:** Framework must be consistent, predictive, and explanatorily superior to alternatives (verification)

The circularity objection mistakes the explanandum (3FLL conformity of measurements) for a hidden assumption. LRT does not assume 3FLL conformity—it explains it.

---

## 3. The Derivation Chain

This section shows that quantum mechanical structure follows from the framework established in Section 2. The derivations rely on established mathematical results (Masanes-Müller, Gleason, Stone) applied to the LRT axiom structure. What LRT contributes is not new mathematics but the grounding that explains why these axioms hold.

### 3.1 The Axioms

LRT rests on five axioms, organized by tier:

**Tier 0: Foundational (LRT-specific)**

| Axiom | Statement |
|-------|-----------|
| A1: Constitution | 3FLL constitute distinguishability |
| A2: Pairwise Structure | Distinguishability is a binary relation: D(x,y) compares two states |
| A4: Boolean Actuality | Interface map Φ produces Boolean outcomes satisfying totality, single-valuedness, exclusivity |
| A5: Non-Contextual Measure | Interface induces probability measure independent of measurement context |

**Grounding A5:** Why should the interface measure be non-contextual? Consider what contextuality of the interface measure would mean: the same IIS state would yield different probability distributions depending on which other measurements could have been performed. But this would violate Identity at the interface. A state's probability of actualization would not be a determinate feature of that state; it would depend on extrinsic factors. The interface would fail to map states to definite probability assignments. Non-contextuality is thus required by Identity: the interface must assign each state a determinate actualization probability that is a feature of that state itself.

**Clarification:** Contextuality of *values* (Kochen-Specker) is compatible with non-contextuality of *measure*. The distinction is essential. Values are generated at actualization; they need not pre-exist and need not be context-independent. But probabilities characterize the IIS state's disposition toward actualization. If probabilities were contextual, the IIS state would lack determinate actualization propensities, violating Identity for the state itself. The Kochen-Specker contextuality that quantum mechanics exhibits concerns outcome values, not the probability measure over those outcomes.

**Tier 1: Derived**

| Result | Derivation |
|--------|------------|
| Global Parsimony | From A1 + Constitutive Closure (Section 2.6) |
| Reversibility | From CBP + Global Parsimony (Section 3.2) |

**Tier 2: Physical (irreducible input)**

| Axiom | Statement | Status |
|-------|-----------|--------|
| A3a: Continuity | IIS admits continuous transformations | Motivated by parsimony |
| A3c: Local Tomography | Composite system states determined by local measurements | Irreducible physical content |

The physical axioms (A3a, A3c) represent genuine empirical input. They are not derived from 3FLL alone. What LRT provides is the framework within which these physical constraints yield quantum structure.

**Status clarification on local tomography (A3c):** Local tomography is a Tier-2 physical axiom, not a consequence of 3FLL. LRT does *not* derive local tomography from logical principles; it shows that *given* local tomography plus the 3FLL-based constraints, complex quantum mechanics is uniquely selected. This keeps the reconstruction in the same epistemic category as other GPT reconstructions (Masanes-Müller, Hardy, Chiribella et al.). LRT's distinctive contribution is not new mathematics but the *interpretation* and unification of these axioms within the IIS/actuality picture: showing why this specific axiom set yields the structure needed for stable, Boolean-actualizing physics.

Whether local tomography can be derived from deeper principles (perhaps Global Parsimony applied to compositional structure, ruling out "surplus" globally-distinct-but-locally-indistinguishable states) remains an open question listed in Section 7.

### 3.2 Deriving Reversibility

**Theorem (Reversibility):** Fundamental transformations on IIS are information-preserving.

*Proof:*

1. Let T be a fundamental transformation on IIS. Suppose T is irreversible: it maps distinct states s₁ ≠ s₂ to the same output T(s₁) = T(s₂).

2. Information destruction requires a mechanism. If T erases the distinction between s₁ and s₂, some physical process must absorb or dissipate that distinction.

3. Any such mechanism constitutes structure beyond the constitutive base (3FLL + initial conditions).

4. By Global Parsimony, no surplus structure exists at the fundamental level.

5. By CBP, states must admit consistent Boolean resolution. Irreversible dynamics produce states whose history becomes unrecoverable, generating propositions ("which original state led here?") with no truthmaker.

6. Therefore, T must be reversible: distinct inputs map to distinct outputs. ∎

This derivation is genuine. Reversibility is not assumed but follows from CBP and Global Parsimony. The physical consequence is that fundamental dynamics preserve information, a defining feature of quantum mechanics that other interpretations simply postulate.

### 3.3 Deriving Hilbert Space Structure

**Theorem (Complex Hilbert Space):** IIS, equipped with the structure required by Axioms A1-A5 and physical constraints A3a, A3c, admits representation as a complex Hilbert space.

*Proof:*

The proof applies the Masanes-Müller reconstruction theorem (2011).

**Step 1: Pairwise distinguishability implies inner product structure.**

Axiom A2 establishes that distinguishability is a binary relation D: IIS × IIS → [0,1]. This pairwise structure, combined with continuity (A3a) and reversibility (derived above), induces an inner product ⟨·|·⟩ on IIS.

**Step 2: Local tomography selects complex numbers.**

Three number fields could support Hilbert space structure: real (ℝ), complex (ℂ), or quaternionic (ℍ).

- Real quantum mechanics: Fails local tomography. Entangled states exist that cannot be distinguished by local measurements alone.
- Quaternionic quantum mechanics: Fails consistent tensor product composition. Quaternionic phases create compositional pathologies.
- Complex quantum mechanics: Uniquely satisfies both local tomography and compositional consistency.

Axiom A3c (local tomography) therefore forces ℂ.

**Step 3: Completeness from maximality.**

IIS is defined as the maximal space of distinguishable configurations. Maximality implies closure under limits: any Cauchy sequence of distinguishable states has a limit that is itself distinguishable. This gives completeness, the defining property that makes the space a Hilbert space rather than merely an inner product space. ∎

**Experimental confirmation:** Renou et al. (2021) tested complex vs. real quantum mechanics directly. The experiment confirmed that locally tomographic real quantum mechanics makes predictions distinguishable from complex quantum mechanics, and nature follows the complex predictions.

This was a structural prediction of any locally tomographic framework, including LRT. It has been confirmed.

### 3.4 Deriving the Born Rule

**Theorem (Born Rule):** The interface probability measure has the form P(φ|ψ) = |⟨φ|ψ⟩|².

*Proof:*

The proof applies Gleason's theorem (1957).

**Gleason's Theorem:** In a Hilbert space of dimension ≥ 3, the only probability measure on projection operators satisfying non-negativity, normalization, and finite additivity is:

$$\mu(P) = \text{Tr}(\rho P)$$

For pure states ρ = |ψ⟩⟨ψ| and rank-1 projections P = |φ⟩⟨φ|, this reduces to:

$$P(\phi|\psi) = |\langle\phi|\psi\rangle|^2$$

**Verification of premises:**

1. *Dimension ≥ 3:* IIS contains composite systems (entangled states). Any composite of two systems has dimension ≥ 4.

2. *Non-negativity:* From Axiom A5.

3. *Normalization:* From Axiom A5.

4. *Non-contextuality:* From Axiom A5: probability assigned to an outcome depends only on state and outcome, not on other possible outcomes in the measurement context.

All premises are satisfied. Gleason's theorem applies. The Born rule follows. ∎

**The bridge from distinguishability to probability:** The probability measure is not independently postulated. Given Hilbert space structure (derived via Masanes-Müller from distinguishability geometry) and non-contextual measure (A5, grounded in Identity), Gleason's theorem *forces* |ψ|² as the unique probability measure. The mapping from distinguishability to probability is mathematical necessity given the derived structure, not stipulation.

**Why the squared magnitude?**

The inner product ⟨ψ|φ⟩ is complex-valued. Probabilities must be real and non-negative. The squared magnitude |⟨ψ|φ⟩|² is:

- The unique non-negative quantity constructible from the inner product
- The unique power satisfying Gleason's additivity constraints
- Invariant under global phase transformations

The exponent 2 is not chosen. It is forced by the mathematics.

### 3.5 Deriving Unitary Dynamics

**Theorem (Schrödinger Equation):** IIS dynamics take the form:

$$i\hbar \frac{\partial}{\partial t}|\psi\rangle = H|\psi\rangle$$

*Proof:*

**Step 1: Reversibility implies unitarity.**

Section 3.2 derived that fundamental transformations preserve information. On Hilbert space, the information-preserving transformations are precisely the unitary (and antiunitary) operators. Wigner's theorem establishes this: any transformation preserving distinguishability (inner product structure) is implemented by a unitary or antiunitary operator.

Antiunitarity corresponds to time reversal. For continuous forward evolution, unitarity applies.

**Step 2: Continuity implies Stone's theorem.**

Axiom A3a requires continuous transformations. A continuous one-parameter family of unitary operators U(t) satisfies the premises of Stone's theorem (1932):

- There exists a unique self-adjoint operator H (the Hamiltonian)
- U(t) = e^(-iHt/ℏ)

The Schrödinger equation follows immediately. ∎

### 3.6 Hamiltonian and Lagrangian Structure

Stone's theorem yields more than the Schrödinger equation. The self-adjoint generator H is the **Hamiltonian**, the observable corresponding to total energy. From this, standard dynamical formalism follows.

**What Stone's theorem provides:**

- A unique self-adjoint operator H generating the unitary group U(t) = e^(-iHt/ℏ)
- The spectral decomposition of H giving energy eigenstates
- The Heisenberg picture: A(t) = U†(t)A(0)U(t)

**What follows from standard physics:**

Once unitarity and the Hamiltonian are established, LRT inherits rather than rederives the classical formalism:

| Structure | Status | Derivation |
|-----------|--------|------------|
| Hamiltonian mechanics | Inherited | Generator of time evolution (Stone) |
| Lagrangian mechanics | Inherited | Legendre transform of Hamiltonian |
| Action principle | Inherited | Path integral formulation; stationary action |
| Symplectic geometry | Inherited | Phase space structure from [q,p] = iℏ |
| Classical limit | Inherited | ℏ → 0 or decoherence + large quantum numbers |

**LRT's contribution:**

LRT does not provide new derivations of Lagrangian or Hamiltonian mechanics. What it provides is *grounding*: an explanation of why unitary dynamics holds in the first place (reversibility from CBP + Parsimony), which then generates the Hamiltonian via Stone's theorem.

The action principle (that physical trajectories extremize action) receives philosophical motivation from parsimony (extremal paths require minimal specification), but this is interpretive, not a replacement for the standard derivation from variational principles.

**Open: Quantum Field Theory**

Extension to quantum field theory remains an open problem. QFT requires:

- Infinite-dimensional field configurations in IIS
- Relativistic (Poincaré) invariance
- Renormalization and vacuum structure

LRT's framework is consistent with QFT but does not yet provide independent derivations of field-theoretic structure. This is acknowledged as a limitation and direction for future work.

### 3.7 The Complete Derivation Chain

![Figure 2: LRT Derivation Chain](figures/LRT_Fig2b.png)

**Figure 2.** The LRT derivation chain. Blue nodes indicate axioms (foundational assumptions). Gold/amber nodes indicate results derived within the framework, citing the external theorems employed. Dashed lines show additional inputs required at each derivation step. The four derived results (reversibility, complex Hilbert space, the Born rule, and unitary dynamics) follow from the foundational axioms plus physical constraints, without independent postulation.

### 3.8 What Is Derived vs. Assumed

| Element | Status | Source |
|---------|--------|--------|
| 3FLL are constitutive | Axiom (A1) | Core LRT thesis |
| Distinguishability is pairwise | Axiom (A2) | Structural |
| Reversibility | **Derived** | CBP + Parsimony |
| Complex numbers | **Derived** | Local tomography (A3c) |
| Hilbert space | **Derived** | Masanes-Müller |
| Born rule | **Derived** | Gleason |
| Unitary dynamics | **Derived** | Reversibility + Continuity |
| Continuity | Axiom (A3a) | Physical input (motivated) |
| Local tomography | Axiom (A3c) | Physical input (irreducible) |
| Non-contextual measure | Axiom (A5) | Interface structure |

The derivations are genuine but conditional. They show: *given* the LRT axioms and physical constraints, quantum structure follows. The physical constraints (A3a, A3c) are not derived from logic alone; they represent empirical input about our universe.

What LRT provides is the unified grounding. The axioms of reconstruction theorems receive explanation: they are features required for stable interface between IIS and Boolean actuality.

---

## 4. What This Explains

Standard quantum mechanics is empirically successful but explanatorily silent. It tells us to use Hilbert space but not why. It gives us the Born rule but not why |ψ|². It presents contextuality, entanglement, and the Tsirelson bound as mathematical facts without physical grounding.

LRT fills these gaps. The framework developed in Sections 2-3 provides unified explanation for phenomena that other approaches treat as independent postulates or unexplained theorems.

### 4.1 What This Framework Addresses

The following phenomena receive treatment from LRT resources, ranging from rigorous mathematical derivation to reconceptualization. The claim is *unified treatment from common principles*, not uniform derivation. All seventeen trace to the IIS/actuality interface structure, unlike competing interpretations that treat them as independent postulates or unexplained facts.

| Phenomenon | Status | LRT Account |
|------------|--------|-------------|
| Born rule is \|ψ\|² | **Derived** | Gleason's theorem + non-contextual interface |
| Hilbert space is complex | **Derived** | Local tomography forces ℂ |
| Unitary dynamics | **Derived** | Reversibility (CBP + Parsimony) + Continuity → Stone |
| Reversibility | **Derived** | CBP + Global Parsimony |
| Contextuality | **Explained** | Interface signature: values generated at interface, not pre-existing |
| Bell inequality violations | **Explained** | Global constraint satisfaction: 3FLL enforce consistency |
| Tsirelson bound (2√2) | **Interpreted** | Interface stability framework (formal derivation pending) |
| No-cloning | **Explained** | Distinguishability preservation in IIS |
| Uncertainty relations | **Explained** | Non-commuting observables = incompatible IIS partitions |
| Entanglement without signaling | **Explained** | Global 3FLL constraints; correlation without causal connection |
| Wave-particle duality | **Reframed** | IIS state (wave-like) vs. actualized outcome (particle-like) |
| Superposition | **Reframed** | IIS is non-Boolean; superposition is pre-actualization state |
| State collapse | **Reframed** | Category transition from IIS to actuality, not dynamical process |
| Measurement disturbance | **Reframed** | No pre-existing values to disturb; values generated at interface |
| Decoherence | **Reframed** | Interface approach: environmental entanglement transfers phase information |
| Identical particles | **Compatible** | Excitations of same distinguishability mode (requires further development) |
| Quantization | **Compatible** | Boolean grain of actuality (requires further development) |
| Quantum Zeno effect | **Compatible** | Repeated interface transitions (not derived) |
| Preferred basis | **Constrained** | Einselection + interface structure determines partition |

**Status categories:**
- **Derived:** Follows mathematically from LRT axioms via established theorems
- **Explained:** Receives substantive account from IIS/actuality framework
- **Interpreted:** LRT provides interpretive framework; formal derivation pending
- **Reframed:** Reconceptualized in LRT terms; puzzle dissolved rather than solved
- **Compatible:** Consistent with LRT; full derivation not yet developed
- **Constrained:** LRT narrows possibilities without fully determining

### 4.2 The Measurement Problem Dissolved

The measurement problem asks: how does deterministic, unitary evolution produce definite, random outcomes? When does collapse occur? What counts as a measurement?

LRT dissolves rather than solves this problem.

**The dissolution:** Measurement is not a dynamical process requiring special physics. It is the interface between IIS and Boolean actuality. The quantum state evolves unitarily in IIS. When it interacts with a context requiring Boolean outcomes, 3FLL are enforced. The state becomes determinate.

This is category transition, not collapse dynamics. The question "when does collapse occur?" presupposes that collapse is a dynamical process within a single domain. On LRT, measurement is a transition between domains, from IIS structure to Boolean actuality. Asking when this occurs is legitimate, but the answer is a physical criterion (Section 7.1), not a dynamical mechanism. The measurement problem is transformed, not evaded.

**The key distinction:** The measurement problem is dissolved as a *conceptual puzzle* (no special collapse dynamics needed, no Heisenberg cut, no observer-dependence) while remaining open as an *empirical question* (which physical criterion marks the interface). These are different issues. The conceptual puzzle (how can deterministic evolution produce single random outcomes?) is resolved by recognizing measurement as category transition rather than dynamical process. The empirical question (what physical conditions trigger interface transition?) is legitimate and tractable, not a residual form of the original puzzle.

**What LRT explains:**
- Why definite outcomes occur (3FLL enforcement at interface)
- Why outcomes are always Boolean (actuality is Boolean by definition)
- Why no special "measurement" dynamics is needed (interface, not mechanism)

**What LRT does not explain:**
- The precise physical criterion marking the interface (decoherence threshold, gravitational criterion, information-theoretic saturation; these are empirical questions)
- Why *this* outcome rather than *that* (this may be irreducibly stochastic)

The openness of the interface criterion is not evasion. LRT constrains the answer: by Global Parsimony, any collapse mechanism must be derivable from geometry or information capacity; it cannot introduce free parameters. This rules out theories with arbitrary collapse rates while remaining neutral between derivable mechanisms (gravitational self-energy, information-theoretic saturation, decoherence thresholds). The measurement problem is not relocated but transformed from "what causes collapse?" to "which derivable physical criterion marks the interface?", an empirically tractable question.

The second open point, why this particular outcome, is not a failure. No interpretation explains why a particular outcome occurs. What LRT explains is why *an* outcome occurs and why it is always determinate.

### 4.3 Entanglement and Non-Locality

Bell's theorem shows that quantum correlations cannot be explained by local hidden variables. This is often presented as "spooky action at a distance."

LRT reframes this entirely.

**The reframing:** There is no action at a distance because there is no action. Entangled particles are not two things mysteriously connected; they are one configuration in IIS with non-factorizable structure.

When measurement occurs, 3FLL enforce consistency across the entire configuration. The correlations are not caused by signaling between particles. They are **constraint satisfaction**: the joint state already satisfies 3FLL globally, and measurement reveals this structure.

**Why no signaling:** The marginal statistics at each location are unchanged regardless of what happens at the other location. Correlations appear only when results are compared. This is exactly what constraint satisfaction predicts: the constraints were already global; measurement reveals them without transmitting information.

**Constraints vs. hidden variables:** Bell's theorem rules out local hidden *variables* (pre-existing definite values). LRT does not posit such values. The IIS state is genuinely indeterminate until the interface. Constraints specify relationships between outcomes, not the outcomes themselves.

This distinction is crucial:

| Concept | Definition | LRT Status |
|---------|------------|------------|
| **Variable** | Has a value; "hidden" means we don't know it | NOT posited |
| **Constraint** | A rule specifying relationships (e.g., A + B = 0) | Posited (3FLL) |

In LRT:
- The entangled state is a single IIS configuration satisfying 3FLL constraints
- Measurement reveals which values satisfy the constraints
- No signal is needed because the constraint was constitutive of the state, not "communicated"

The correlations are not explained by hidden information traveling faster than light. They are explained by the unified structure of the IIS state, which does not have spatial parts that need to coordinate. The "non-locality" is in the wholeness of the state, not in any propagation. This explains why entanglement produces correlations but not signaling.

#### Worked Example: Bell State Correlations

To make this concrete, we work through the Bell state $|\Psi^-\rangle$ in complete detail, showing how LRT explains the correlations.

**1. The State in IIS**

Consider the singlet Bell state:
$$|\Psi^-\rangle = \frac{1}{\sqrt{2}}(|01\rangle - |10\rangle)$$

where $|0\rangle$ and $|1\rangle$ denote spin-up and spin-down along the z-axis.

**IIS representation:** This state is a single point in the composite IIS for the two-particle system. Its key properties:

- **Global purity:** $|\Psi^-\rangle$ is a pure state with $D(|\Psi^-\rangle, |\Psi^-\rangle) = 0$
- **Local mixedness:** The reduced density matrices are $\rho_A = \rho_B = \frac{1}{2}I$ (maximally mixed)
- **Global distinguishability:** $D(|\Psi^-\rangle, |\Phi^+\rangle) = 1$ (perfectly distinguishable from other Bell states)

The entanglement is manifest: the global state carries more information than the sum of local states. This is correlation structure built into IIS, not a dynamical connection between particles.

**2. Measurement Scenario**

Alice and Bob perform measurements at spacelike-separated locations:

- Alice measures spin along axis $\hat{n}_A = (\sin\theta_A\cos\phi_A, \sin\theta_A\sin\phi_A, \cos\theta_A)$
- Bob measures spin along axis $\hat{n}_B = (\sin\theta_B\cos\phi_B, \sin\theta_B\sin\phi_B, \cos\theta_B)$

Each measurement yields Boolean outcome $\pm 1$ (satisfying 3FLL at the interface).

**3. Correlation Calculation**

The correlation function is:
$$E(\hat{n}_A, \hat{n}_B) = \langle\Psi^-|\sigma_A \cdot \hat{n}_A \otimes \sigma_B \cdot \hat{n}_B|\Psi^-\rangle$$

where $\sigma = (\sigma_x, \sigma_y, \sigma_z)$ are the Pauli matrices.

**Explicit calculation:**

For the singlet state, we use the identity:
$$|\Psi^-\rangle\langle\Psi^-| = \frac{1}{4}(I \otimes I - \sigma_x \otimes \sigma_x - \sigma_y \otimes \sigma_y - \sigma_z \otimes \sigma_z)$$

Therefore:
$$E(\hat{n}_A, \hat{n}_B) = \text{Tr}\left[|\Psi^-\rangle\langle\Psi^-| \cdot (\sigma \cdot \hat{n}_A) \otimes (\sigma \cdot \hat{n}_B)\right]$$

Expanding $(\sigma \cdot \hat{n}_A) \otimes (\sigma \cdot \hat{n}_B)$ and using $\text{Tr}(\sigma_i) = 0$ and $\text{Tr}(\sigma_i \sigma_j) = 2\delta_{ij}$:

$$E(\hat{n}_A, \hat{n}_B) = -\hat{n}_A \cdot \hat{n}_B = -\cos\theta$$

where $\theta$ is the angle between the measurement axes.

**Special cases:**
- Parallel axes ($\theta = 0$): $E = -1$ (perfect anticorrelation)
- Antiparallel axes ($\theta = \pi$): $E = +1$ (perfect correlation)
- Orthogonal axes ($\theta = \pi/2$): $E = 0$ (no correlation)

**4. CHSH Violation**

The CHSH inequality for local hidden variable theories states:
$$|S| = |E(a,b) - E(a,b') + E(a',b) + E(a',b')| \leq 2$$

Choose axes:
- $a = \hat{z}$ (Alice's first setting)
- $a' = \hat{x}$ (Alice's second setting)
- $b = (\hat{z} + \hat{x})/\sqrt{2}$ (Bob's first setting, at 45°)
- $b' = (\hat{z} - \hat{x})/\sqrt{2}$ (Bob's second setting, at -45°)

Calculate each term using $E = -\cos\theta$:
- $E(a,b) = -\cos(45°) = -1/\sqrt{2}$
- $E(a,b') = -\cos(45°) = -1/\sqrt{2}$
- $E(a',b) = -\cos(45°) = -1/\sqrt{2}$
- $E(a',b') = -\cos(135°) = +1/\sqrt{2}$

Therefore:
$$S = -\frac{1}{\sqrt{2}} - \left(-\frac{1}{\sqrt{2}}\right) + \left(-\frac{1}{\sqrt{2}}\right) + \frac{1}{\sqrt{2}} = -\frac{2}{\sqrt{2}} - \frac{2}{\sqrt{2}} = -2\sqrt{2}$$

$$|S| = 2\sqrt{2} \approx 2.83 > 2$$

The CHSH inequality is violated. Bell's theorem concludes: no local hidden variable theory can reproduce quantum predictions.

**5. No-Signaling Proof**

Despite the correlations, Alice cannot signal to Bob:

**Alice's marginal probability:**
$$P(A = +1 | \hat{n}_A) = \text{Tr}_B\left[\langle +_A|\rho_{AB}|+_A\rangle\right] = \text{Tr}\left[\frac{1}{2}I \cdot |+_A\rangle\langle +_A|\right] = \frac{1}{2}$$

This is independent of:
- Bob's choice of measurement axis $\hat{n}_B$
- Bob's measurement outcome
- Whether Bob measures at all

**Why?** Alice's reduced state is $\rho_A = \frac{1}{2}I$ regardless of anything Bob does. The correlations appear only in the joint statistics $P(A,B)$, never in the marginals $P(A)$ or $P(B)$.

**LRT interpretation:** Each party's local measurement produces Boolean outcomes from the same global IIS structure. No information propagates because both parties access the same pre-existing correlation structure. The correlations were constitutive of the state, not communicated.

**6. LRT vs. Alternatives**

| Approach | Explanation of Correlations | Problem |
|----------|---------------------------|---------|
| **Classical (hidden variables)** | Pre-existing values determine outcomes | Bell's theorem rules this out |
| **Copenhagen** | "Shut up and calculate" | No explanation offered |
| **Many-Worlds** | All outcomes occur; correlations are branch structure | Preferred basis problem; probability problem |
| **Bohmian** | Nonlocal guidance equation | Explicit nonlocal dynamics required |
| **LRT** | Correlation structure in IIS; local actualization | None (explains without nonlocal dynamics) |

**The LRT advantage:** Correlations are not caused by anything propagating between Alice and Bob. They are revealed by measurements that independently actualize from the same IIS structure. The entangled state already encodes the correlations; measurement makes them manifest without transmitting them.

This worked example demonstrates the core LRT insight: entanglement is structure in IIS, not mysterious connection in spacetime.

**Relativistic considerations:** The "global constraint" picture works naturally in non-relativistic quantum mechanics, where simultaneity is well-defined. In relativistic contexts, the constraint is on the IIS state, not on spacetime events. The entangled state in IIS is a single configuration; it does not have spatial parts that need to coordinate. When measurement outcomes are registered at spacelike separation, each outcome is locally determinate and globally consistent. Different reference frames describe the ordering of measurements differently, but all frames agree on the correlations, which is exactly what we observe. A fully relativistic formulation of LRT would need to articulate how the IIS/actuality interface respects the causal structure of spacetime; this represents ongoing work for the framework.

### 4.4 The Tsirelson Bound

Quantum correlations violate Bell inequalities but only up to the Tsirelson bound of 2√2 for CHSH. Stronger correlations are mathematically possible (PR boxes achieve 4) but not physically realized.

**Why this bound?**

**LRT interpretation (not derivation):** LRT suggests interpreting the Tsirelson bound as marking the maximum correlation compatible with stable interface operation. PR boxes and other super-quantum correlations, while satisfying no-signaling at the single-use level, permit signaling when composed or permit computational trivializations that destabilize physical structure.

This interpretation places the bound as the stability limit of the IIS-actuality interface.

**Status clarification:** LRT does *not* derive the Tsirelson bound from 3FLL or the IIS framework. Rather, LRT provides an *interpretive framework* within which the bound's existence becomes conceptually natural: if actuality requires Boolean definiteness and the interface must operate stably, correlations exceeding certain limits would destabilize the interface. The specific value 2√2 is not derived but interpreted as the empirically observed stability threshold. A formal derivation connecting 3FLL to this specific value remains future work (see Section 7: Open Problems).

### 4.5 Contextuality

The Kochen-Specker theorem shows that quantum observables cannot all have definite, non-contextual values prior to measurement.

**Standard framing:** This is presented as a no-go theorem, a constraint on hidden variable theories.

**LRT framing:** Contextuality is not a constraint on theories. It is a signature of the interface. Boolean values do not exist in IIS waiting to be revealed. They are generated at the interface, in context. Different measurement contexts actualize different aspects of IIS structure.

Contextuality follows directly from the IIS/actuality distinction. Asking "what value did the observable have before measurement?" presupposes that Boolean values exist in IIS. They do not. They exist in actuality, which is produced at the interface.

### 4.6 Wave Function Status

Is the wave function real (ontic) or merely knowledge (epistemic)?

**LRT answer:** Neither, as traditionally framed. The wave function is **IIS structure**: real but not actual.

- **Real:** The wave function describes genuine structure in IIS, not mere ignorance.
- **Not actual:** It is not a thing in Boolean actuality until interface transition.

This ψ-structural position is compatible with the PBR theorem (which rules out ψ-epistemic interpretations where quantum states represent ignorance of underlying ontic states) while avoiding the claim that ψ is a physical substance in spacetime.

### 4.7 The Unification

These seventeen explanations are not independent. They follow from a single structural insight:

> Quantum mechanics is the interface between non-Boolean IIS and Boolean actuality, constrained by 3FLL.

Every phenomenon in the table traces to this structure:

- **Measurement** = interface transition
- **Superposition** = IIS indeterminacy
- **Collapse** = category change
- **Entanglement** = global IIS configuration
- **Correlations** = constraint satisfaction
- **Contextuality** = values generated at interface
- **Born rule** = unique interface probability
- **Tsirelson bound** = interface stability limit (interpretive; see 4.4)

This unification is the primary evidence for LRT. Competing interpretations explain some phenomena while leaving others as brute facts. LRT explains all seventeen from common resources.

### 4.8 Ontic Booleanity: The Epistemic Loophole

A sophisticated objection grants that *observed* outcomes obey 3FLL but suggests this might be epistemic rather than ontic: perhaps 3FLL are filters on *observation*, not constraints on *reality*. Hidden outcome tokens might violate 3FLL while remaining undetectable.

LRT addresses this loophole as follows.

**Conjecture (Ontic Booleanity).** Under the continuity and path-connectedness required by quantum mechanics, every actual outcome token satisfies 3FLL. No token—even one that never occurs with positive probability—can violate 3FLL.

**Status:** This is a *conjecture* with a proof sketch, not a completed theorem. The argument outline is provided below; a fully rigorous proof requires additional technical development.

**The argument sketch has two parts:**

*Part I (Positive-probability tokens):* Any token that occurs with positive probability must be Boolean. If a token $t_0$ violated 3FLL (say, by satisfying both $A$ and $\neg A$ simultaneously), then states assigning positive probability to $t_0$ would violate probability normalization: $\omega(A) + \omega(\neg A) > 1$. This contradicts the probability structure of quantum mechanics. (This part is relatively straightforward.)

*Part II (Hidden zero-probability tokens):* Hypothetical tokens with zero probability under all states cannot violate 3FLL either. Here path-connectedness is crucial: pure states with $\omega(A) = 1$ and $\omega(A) = 0$ are connected by continuous paths. Any hidden non-Boolean token would disrupt this continuity structure. More fundamentally, the token space is *defined* by what states can distinguish—a token outside all state supports is not a token of the theory. (This part requires rigorous formalization; the intuition is clear but the proof details remain to be worked out.)

**If established, the conclusion would be:** 3FLL are not observer-imposed filters but structural constraints on outcome tokens themselves. The epistemic loophole would be mathematically closed.

This conjecture, if proven, would strengthen LRT's core claim: the 3FLL would not merely describe how we observe reality but constitute what can be an actual outcome. Completing this proof is listed as future work (Section 7).

*For the proof sketch details, see Technical companion Section 7.*

---

## 5. Comparison with Alternatives

This section evaluates LRT against competing interpretations of quantum mechanics. Each is treated as a physical theory and assessed on common criteria: explanatory power, ontological commitments, predictions, and falsifiability.

### 5.1 The Competitors

Six interpretations warrant comparison:

1. **Copenhagen**: Operational approach; refuses ontological commitment
2. **Many-Worlds (MWI)**: Wave function realism; all branches actual
3. **Bohmian Mechanics**: Hidden particle positions; nonlocal pilot wave
4. **GRW/Objective Collapse**: Spontaneous localization with specified rates
5. **QBism**: Quantum states as agent beliefs
6. **Relational QM**: Facts relative to observers

### 5.2 Explanatory Power

| Theory | Structure | Born Rule | Context. | Bell | Tsirelson |
|--------|:---------:|:---------:|:--------:|:----:|:---------:|
| Copenhagen | No | Postulates | Accepts | Accepts | Accepts |
| MWI | No | Contested | Accepts | Accepts | Accepts |
| Bohmian | No | Partial | Accepts | Nonlocal | Accepts |
| GRW | No | Modified | Accepts | Accepts | Accepts |
| QBism | No | Coherence | Accepts | Agent | Accepts |
| Relational | No | Relational | Context | Relational | Accepts |
| **LRT** | **Yes** | **Gleason** | **Interface** | **Derived** | **Interprets** |

LRT is the only framework that explains *why* quantum mechanics has its structure rather than postulating that structure or remaining silent.

### 5.3 The Measurement Problem

| Theory | Approach | Mechanism | When? | Why This Outcome? |
|--------|----------|-----------|-------|-------------------|
| Copenhagen | Pragmatic dissolution | "Measurement" (undefined) | Unspecified | Fundamental randomness |
| MWI | All outcomes occur | Branching | Always | All occur; you're in one branch |
| Bohmian | Always definite | Hidden position | N/A | Determined by hidden variable |
| GRW | Spontaneous collapse | Stochastic hits | Random (rate λ) | Stochastic |
| QBism | No objective problem | Belief updating | Agent-relative | Agent's experience |
| Relational | Relative facts | Interaction | Relative | Relative |
| **LRT** | **Category transition** | **IIS → Boolean** | **At interface** | **Not explained (acknowledged)** |

**Assessment:**

- **Copenhagen** avoids the question by refusing ontology
- **MWI** "solves" it by accepting all outcomes, but then faces the probability problem: why does |ψ|² give correct weights if all branches exist equally?
- **Bohmian** solves it with hidden variables, but requires explicit nonlocality and doesn't explain why the guidance equation has its form
- **GRW** solves it with new physics, but introduces free parameters (λ, a) with no derivation
- **QBism** dissolves it by making QM subjective, but loses objectivity
- **LRT** dissolves it as category transition, honest that "why this outcome" is open, but explains why outcomes are Boolean

### 5.4 Ontological Cost

| Theory | Wave Function | Additional Ontology | Parsimony |
|--------|--------------|--------------------| ----------|
| Copenhagen | Calculational tool | Classical apparatus (unexplained) | Evasive |
| MWI | Real (all branches) | Infinite branching worlds | **Very Low** |
| Bohmian | Real + particles | Hidden positions, nonlocal dynamics | Low |
| GRW | Real (modified) | Collapse mechanism, free parameters | Low |
| QBism | Agent beliefs | Agents | High (anti-realist) |
| Relational | Relational | Observer-relative facts | Medium |
| **LRT** | **IIS structure** | **3FLL (already presupposed)** | **High** |

**The parsimony comparison:**

MWI's ontology is staggering: every quantum event spawns entire universes. Defenders respond that branches are not "added" but entailed by refusing to postulate collapse. However, the asymmetry with LRT is fundamental. MWI's branches are entailed by *denying* something observation suggests (single outcomes). LRT's 3FLL are *presupposed* by any coherent discourse, including MWI's own formulation. MWI adds branch realism to avoid accepting what every measurement displays; LRT makes explicit what every theory already assumes at the metalevel. The parsimony difference is not between "one world" and "many worlds" but between recognizing presuppositions and multiplying entities to evade observations.

Bohmian mechanics adds hidden variables that are in principle unobservable plus explicitly nonlocal dynamics.

GRW adds new physics with unexplained parameters.

LRT adds nothing beyond what is already presupposed. The 3FLL are assumed by every theory at the metalevel. Making them explicit and showing they do physical work is not adding ontology; it is recognizing what was already there.

### 5.5 Locality

| Theory | Bell Correlations | Locality Preserved? | Signaling? |
|--------|------------------|--------------------| -----------|
| Copenhagen | Accepts | Silent | No |
| MWI | Local in configuration space | Yes (no collapse) | No |
| Bohmian | Nonlocal dynamics | **No** | No |
| GRW | Nonlocal collapse | **No** | No |
| QBism | Agent experiences | N/A | No |
| Relational | Relative | Claims yes | No |
| **LRT** | **Constraint satisfaction** | **Yes** | **No** |

Bohmian mechanics and GRW explicitly embrace nonlocality. This is a significant cost; it conflicts with relativistic intuitions and requires careful treatment to avoid signaling.

LRT maintains locality: correlations arise from global constraint satisfaction, not causal influence. The constraints are structural features of IIS configurations, not signals propagating between locations.

### 5.6 Predictions and Falsifiability

| Theory | Novel Predictions | Confirmed | Currently Testable | Explicit Falsifiers |
|--------|------------------|-----------|-------------------|---------------------|
| Copenhagen | None | N/A | None | None |
| MWI | None (empirically equivalent) | N/A | None practical | None practical |
| Bohmian | None (empirically equivalent) | N/A | None practical | None practical |
| GRW | Collapse effects | Testing | Yes | Yes |
| QBism | None | N/A | None | None (by design) |
| Relational | None | N/A | None | None |
| **LRT** | **Structural** | **Yes (2021)** | **Yes** | **12 explicit** |

**Assessment:**

Copenhagen, MWI, Bohmian, QBism, and Relational QM make no predictions beyond standard quantum mechanics. They are empirically equivalent interpretations.

GRW makes testable predictions about collapse rates. This is a genuine virtue; GRW takes empirical risk.

LRT makes structural predictions:
- Complex numbers required → **Confirmed** (Renou et al., 2021)
- Collapse parameters must be derivable, not free → Currently testable
- No recoherence after actualization → Distinguishes from MWI

LRT specifies twelve explicit falsifiers. It takes empirical risk.

### 5.7 The Born Rule Problem

The Born rule deserves special attention.

| Theory | Born Rule Status | Derivation Quality |
|--------|-----------------|-------------------|
| Copenhagen | Postulated | None |
| MWI | Contested | Decision-theoretic (Deutsch-Wallace), disputed |
| Bohmian | Derived | Quantum equilibrium, but why equilibrium? |
| GRW | Built in | Part of collapse postulate |
| QBism | Coherence | Dutch book (normative, not physical) |
| Relational | Relational | Not fully addressed |
| **LRT** | **Derived** | **Gleason's theorem (mathematically rigorous)** |

**The MWI problem is severe.** If all branches are equally real, what does "probability" mean? The Deutsch-Wallace derivation uses decision-theoretic arguments: a rational agent *should* weight branches by |ψ|². But this is normative, not physical. It doesn't explain why |ψ|² tracks anything about reality.

**LRT's derivation is rigorous.** Gleason's theorem proves |ψ|² is the unique probability measure on Hilbert space satisfying minimal conditions. The derivation is mathematical, not normative. The conditions (non-negativity, normalization, non-contextuality) are grounded in the interface structure.

### 5.8 Direct Comparison: LRT vs. MWI

MWI is LRT's strongest competitor as a realist interpretation. Direct comparison:

| Criterion | MWI | LRT |
|-----------|-----|-----|
| Wave function real? | Yes (all branches) | Yes (IIS structure) |
| Single actuality? | No | Yes |
| Born rule | Contested | Derived |
| Matches observation | Must explain away one outcome | Directly predicts one outcome |
| Ontological cost | Infinite branches | None beyond 3FLL |
| Novel predictions | None | Complex QM confirmed |
| Falsifiable | Practically no | Yes (12 explicit) |

**The core difference:**

MWI: We observe one outcome because we're in one branch, but all branches are equally real. This requires explaining why Born rule gives branch weights, what "probability" means when all outcomes occur, and why we should believe in unobservable branches.

LRT: We observe one outcome because actuality is Boolean. Non-Contradiction and Excluded Middle enforce single, determinate outcomes. No additional explanation needed; single actuality follows from 3FLL.

The asymmetry is fundamental: MWI introduces branch realism to avoid accepting what every measurement displays (single outcomes), while LRT makes explicit what every theory already presupposes (3FLL). MWI and LRT thus differ not just in ontology but in methodology: one multiplies entities, the other recognizes presuppositions.

### 5.9 Summary Comparison

**Table 1.** Comparison of quantum mechanics interpretations across key theoretical criteria. Y = criterion satisfied; N = criterion not satisfied; P = partial or contested; ? = unclear.

| Criterion | Copen. | MWI | Bohm | GRW | QBism | Relat. | **LRT** |
|-----------|:------:|:---:|:----:|:---:|:-----:|:------:|:-------:|
| Explains structure | N | N | N | N | N | N | **Y** |
| Derives Born rule | N | P | P | N | P | N | **Y** |
| Parsimony | P | N | N | N | P | P | **Y** |
| Realism | N | Y | Y | Y | N | P | **Y** |
| Locality | ? | Y | N | N | ? | Y | **Y** |
| Testable predictions | N | N | N | Y | N | N | **Y** |
| Falsifiable | N | N | N | Y | N | N | **Y** |

LRT is the only interpretation that:
- Explains why QM has its structure
- Derives the Born rule rigorously
- Maintains realism, locality, and parsimony simultaneously
- Has confirmed predictions
- Specifies explicit falsification conditions

### 5.10 The Layer Structure: Unifying Interpretations

Rather than viewing interpretations as competitors, LRT reveals them as descriptions of different layers:

| Layer | Description |
|-------|-------------|
| **LAYER 4: BOOLEAN ACTUALITY** | **Frameworks:** Copenhagen (outcomes), QBism (agent's bets). **Math:** Boolean algebra, classical probability. **What happens:** Definite outcomes; one result per context |
| **LAYER 3: THE INTERFACE** | **Frameworks:** Decoherence, GRW (collapse statistics). **Math:** Lindblad equation, stochastic Schrödinger equation. **What happens:** Transition from quantum to classical |
| **LAYER 2: PROBABILITY FLOW** | **Frameworks:** Bohmian mechanics (guidance equation). **Math:** Probability currents, quantum equilibrium. **What happens:** \|ψ\|² distribution maintained; flow structure |
| **LAYER 1: IIS DYNAMICS** | **Frameworks:** Unitary QM, Many-Worlds (wave function realism). **Math:** Schrödinger equation, Hilbert space. **What happens:** Unitary evolution; all branches present |

**Domain assignments:**

| Framework | Layer | Mathematical Content | LRT Interpretation |
|-----------|-------|---------------------|-------------------|
| Unitary QM / MWI | 1 | Schrödinger: i∂ₜ\|ψ⟩ = H\|ψ⟩ | Evolution in IIS; all branches exist |
| Bohmian | 2 | Guidance: dQ/dt = (ℏ/m)Im(∇ψ/ψ) | Probability flow in IIS |
| Decoherence | 3 | Lindblad: ρ̇ = -i[H,ρ] + L[ρ] | Approach to interface threshold |
| GRW | 3 | Collapse rate: λ · N | Statistics of interface transitions |
| QBism | 4 | Dutch book coherence | Agent's rational bets on outcomes |
| Copenhagen | 4 | Born rule + collapse | Description of actualized outcomes |
| Relational | 2-4 | Perspectival states | Context-dependence across layers |

**Why interpretations seem to conflict:** MWI (Layer 1) says all branches are real. Copenhagen (Layer 4) says one outcome occurs. Both are correct *in their domains*. MWI correctly describes IIS dynamics; Copenhagen correctly describes Boolean actuality. The apparent conflict dissolves when we recognize they describe different layers.

---

## 6. Predictions and Falsifiers

A physical theory must make testable claims and specify conditions for its own refutation. This section catalogs what LRT predicts, what has been confirmed, what is currently testable, and what would falsify the framework.

### 6.1 Confirmed Predictions

| Prediction | Basis | Test | Status |
|------------|-------|------|--------|
| Complex amplitudes required | Local tomography (A3c) forces ℂ over ℝ | Renou et al. (2021) | **Confirmed** |
| Born rule exact | Gleason's theorem | Precision measurements | Confirmed to 10⁻⁵ |
| Tsirelson bound exact | Interpretive (not derived) | All Bell tests | No violations observed |
| Bell inequality violations | Global constraint satisfaction | Bell tests since 1982 | Confirmed |
| Contextuality | Interface signature | Kochen-Specker tests | Confirmed |

**The complex numbers result:**

LRT, via local tomography (A3c), requires that quantum mechanics use complex rather than real amplitudes. This structural requirement (independently established by reconstruction theorems) was experimentally confirmed by Renou et al. (2021), who designed an experiment distinguishing complex from real quantum mechanics. Nature followed the complex predictions. While LRT did not generate this prediction independently of reconstruction theorems, the experimental confirmation validates the framework's structural commitments.

### 6.2 Currently Testable Predictions

**Prediction 1: Collapse parameters must be derivable.**

If objective collapse occurs (as in GRW-type models), LRT constrains the mechanism:

> Any collapse parameter not derivable from geometry or information capacity would constitute surplus structure, violating Global Parsimony.

GRW introduces parameters λ (collapse rate) and a (localization width) as primitives. If collapse is confirmed with these as free parameters (not derivable from existing physical constants), LRT requires revision.

Conversely, if collapse rates follow from gravitational self-energy (Penrose-Diósi) or information-theoretic bounds, LRT is supported.

**Current experiments:**

| Experiment | What It Tests | Timeline |
|------------|---------------|----------|
| MAQRO (ESA proposal) | Macroscopic superposition in space | Under review |
| Optomechanical tests | Nanoparticle superposition limits | Ongoing |
| Large-molecule interferometry | Interference at increasing mass scales | Ongoing (Vienna) |
| GRW heating tests | Anomalous heating from collapse | Sensitivity improving |

**Quantitative context - decoherence timescales:**

For objects in thermal environments, the decoherence time τ_D depends on mass, temperature, and superposition separation:

| System | Superposition Δx | Decoherence Time τ_D |
|--------|------------------|---------------------|
| Electron in lab | 1 nm | ~ 10⁻¹³ s |
| Dust grain (10⁻⁵ g) | 1 nm | ~ 10⁻³¹ s |
| Bowling ball | 1 cm | ~ 10⁻⁴³ s |

For macroscopic objects, τ_D → 0 effectively. The interface transition is instantaneous at human scales. This resolves the "when does collapse happen?" concern; for macro systems, the question of precise timing becomes physically meaningless.

**GRW mass scaling (if collapse model applies):**

| System | N (nucleons) | Mean collapse time |
|--------|--------------|-------------------|
| Electron | 1 | ~ 10⁸ years |
| Protein | 10⁵ | ~ 10³ years |
| Virus | 10⁷ | ~ 10 years |
| Dust grain | 10¹⁴ | ~ 10⁻⁶ s |
| Cat | 10²⁷ | ~ 10⁻¹¹ s |

This scaling explains why microscopic systems exhibit quantum behavior while macroscopic systems appear classical. The interface transition rate scales with system complexity.

**Prediction 2: No recoherence after actualization.**

LRT treats measurement as category transition. Once an outcome has produced a stable macroscopic record, the other "branches" were never actual; there is nothing to recohere.

MWI permits recoherence in principle (given sufficient control). LRT forbids it for actualized outcomes.

This is difficult to test directly but represents a genuine ontological difference with empirical implications in extreme regimes.

**Prediction 3: Structural fine-tuning is exact.**

LRT predicts that perturbations to quantum structure destroy stable physics entirely:

- Remove complex numbers → No stable interference
- Alter unitarity → Probability non-conservation
- Change Born exponent → No valid probability measure
- Exceed Tsirelson bound → Signaling permitted

Any observation of stable physics with altered quantum structure would falsify LRT.

### 6.3 The Falsifiers

Twelve conditions would refute LRT:

| # | Falsifier | What It Would Refute |
|---|-----------|---------------------|
| 1 | Born rule violated (dim ≥ 3) | Gleason derivation; non-contextual interface (A5) |
| 2 | Tsirelson bound exceeded | Interface stability interpretation (shared with standard QM) |
| 3 | Locally tomographic real QM works | Local tomography → ℂ derivation |
| 4 | Locally tomographic quaternionic QM works | Compositional consistency claim |
| 5 | Physical dialetheia observed | Non-Contradiction as constitutive |
| 6 | Non-Boolean measurement outcome | Excluded Middle as constitutive |
| 7 | Local hidden variables succeed | Global constraint interpretation |
| 8 | Non-contextual hidden variables succeed | Interface interpretation |
| 9 | Superluminal signaling via entanglement | 3FLL as constraint (not signal) |
| 10 | Distinguishable "identical" particles | Identity as constitutive |
| 11 | Information exceeds Bekenstein bound | Distinguishability finitude |
| 12 | Collapse with underivable free parameters | Global Parsimony |

**Testability categorization:**

| Category | Falsifiers | Status |
|----------|------------|--------|
| **Already tested and passed** | 1-4, 7-8 | Born rule (10⁻⁵), Tsirelson bound, complex QM (2021), Bell/KS violations |
| **Currently testable** | 11-12 | Bekenstein bound tests, collapse mechanism experiments (active research) |
| **Foundational/in-principle** | 5-6, 9-10 | Would challenge empirical science itself; no observations exist or expected |

**Assessment of falsifier categories:**

**Already tested (1-4, 7-8):** Falsifiers 1-4 and 7-8 have been tested extensively. Born rule confirmed to 10⁻⁵. Tsirelson bound holds. Real QM ruled out (2021). Bell and Kochen-Specker violations confirmed. LRT passes.

**Currently testable (11-12):** Bekenstein bound tests and collapse mechanism experiments are active research areas. These represent genuine empirical risk for LRT.

**Foundational (5-6, 9-10):** These falsifiers concern logical structure presupposed by all empirical science. Observing a physical dialetheia or non-Boolean outcome would not merely refute LRT; it would challenge the foundations of scientific inquiry itself. These are "in principle" falsifiers that establish LRT's logical commitments, not practical test conditions. No such observations exist or are expected.

**Note on shared falsifiers:** Several falsifiers (Born rule, Tsirelson bound, no-signaling) are shared with standard quantum mechanics. This is appropriate: LRT *predicts* standard QM, so falsifiers of standard QM are falsifiers of LRT. What distinguishes LRT is that it *explains* what it predicts rather than postulating it. The distinctive LRT predictions concern structural requirements (complex numbers, derivable collapse parameters) and the impossibility of certain extensions.

**Critical falsifier: Fundamental information loss.** The derivation of unitary dynamics (Section 3.5) rests on the Consistency Bridging Principle and Global Parsimony, which require that fundamental dynamics preserve information. This explicitly stakes LRT on the resolution of the Black Hole Information Paradox. If Hawking radiation is confirmed to be truly thermal with fundamental information loss (non-unitary black hole evaporation), this directly falsifies LRT's derivation of the Schrödinger equation. Current theoretical evidence (AdS/CFT correspondence, Page curve derivations) favors information preservation, but this remains an open empirical and theoretical question. LRT's commitment to unitarity is principled, not evasive: information destruction would require a mechanism constituting surplus structure beyond the constitutive base, violating Global Parsimony.

### 6.4 What LRT Does Not Predict

LRT makes no predictions about:

- Specific particle masses or coupling constants
- Number of particle generations
- Gauge group structure
- Cosmological parameters
- Dark matter/energy nature
- Quantum gravity details

These lie outside LRT's scope. The framework addresses *why quantum mechanics has its structure*, not the specific content of the Standard Model or cosmology.

### 6.5 The Evidential Structure

**Strong evidence:**
- Universal 3FLL compliance across all physics (foundational observation)
- Complex QM confirmed over real QM (structural prediction)
- 17 phenomena unified under common explanation (explanatory power)
- All falsifiers tested to date have been passed

**Moderate evidence:**
- Reconstruction theorems independently confirm uniqueness of QM structure
- No competing interpretation matches LRT's combination of virtues

**Open tests:**
- Collapse mechanism constraints (5-20 year horizon)
- Precision tests of information-theoretic bounds

### 6.6 Comparison with Competing Theories

| Theory | Confirmed Predictions | Testable Predictions | Explicit Falsifiers |
|--------|----------------------|---------------------|---------------------|
| Copenhagen | N/A | None | None |
| MWI | N/A | None practical | None practical |
| Bohmian | N/A | None practical | None practical |
| GRW | Testing | Yes (collapse rates) | Yes |
| QBism | N/A | None | None (unfalsifiable) |
| Relational | N/A | None | None |
| **LRT** | **Complex QM (2021)** | **Yes (collapse, bounds)** | **12 explicit** |

Only LRT and GRW make testable predictions and specify falsification conditions. This is what distinguishes physical theories from interpretive frameworks.

LRT's advantage over GRW: LRT constrains collapse mechanisms rather than postulating specific parameters. If GRW's parameters are confirmed as free (not derivable), GRW is confirmed but LRT requires revision. If collapse parameters are derivable from geometry or information theory, both are supported but LRT's parsimony constraint is vindicated.

---

## 7. Open Questions and Conclusion

### 7.1 What Remains Open

LRT does not answer every question. Honest accounting requires identifying what is not yet resolved.

**The interface criterion:**

LRT establishes that measurement is category transition from IIS to Boolean actuality. It does not specify the precise physical criterion marking this transition.

Candidates include:
- Decoherence thresholds (environmental entanglement)
- Gravitational self-energy (Penrose-Diósi)
- Information-theoretic saturation (Bekenstein-type bounds)
- Thermodynamic irreversibility

These are empirical questions. Section 6.2 identified experiments currently testing them. LRT constrains the answer (no free parameters) but does not determine it.

**A working hypothesis (Saturated Entanglement Criterion):**

A concrete candidate has been developed that realizes the "information-theoretic saturation" option within the LRT framework. The *plateau-plus-pointer* criterion proposes that the interface transition completes when two conditions are jointly satisfied:

> **(C1) Entropy Saturation:** The von Neumann entropy of the reduced system state reaches a stable plateau near its maximum: $S(\rho_{\text{system}}) \geq \log(d) - \epsilon$.
>
> **(C2) Pointer-Basis Decoherence:** Coherences in the pointer basis are irretrievably suppressed, with no recoherence on operationally relevant timescales.

This criterion builds on standard decoherence theory (Joos & Zeh 1985, Zurek 2003) without adding new physics. C1 captures the global information export to the environment; C2 ensures this information exists as stable Boolean records compatible with 3FLL enforcement. Together, they specify when "all operationally accessible interference between outcome branches has vanished."

The hypothesis generates testable predictions: collapse time should scale as $\tau \propto 1/(g^2 N)$ where $g$ is coupling strength and $N$ is apparatus degrees of freedom; interference should vanish precisely when entropy reaches the plateau; quantum eraser effects should succeed only before C2 is satisfied.

**Status:** This is a *research program* consistent with LRT's axioms, not a theorem derived from them. LRT does not stand or fall with this specific criterion; LRT requires *some* physically specifiable interface rule, and the saturated-entanglement criterion is the current best proposal, pending theoretical and experimental scrutiny. Full development including equations, experimental data, and proposed tests is available in the companion document "Saturated Entanglement as the Interface Transition Criterion" (Longmire 2025).

**Why this outcome?**

LRT explains why measurement yields *a* definite Boolean outcome. It does not explain why *this particular* outcome rather than another.

This may be irreducibly stochastic. The Born rule gives probabilities; there may be no deeper fact about why a specific outcome occurs. If so, this is not a failure of LRT but a feature of physical reality.

No interpretation explains individual outcome selection. MWI claims all outcomes occur. Bohmian mechanics makes selection deterministic but with unknowable initial conditions. GRW makes it stochastic. LRT is honest that this question is open.

**The relativistic interface:**

LRT explains entanglement as global constraint satisfaction rather than causal signaling. This works naturally in non-relativistic quantum mechanics, where simultaneity is well-defined. However, a fully relativistic formulation requires articulating how the IIS/actuality interface respects the causal structure of spacetime.

The challenge: "global constraint" might appear to presuppose a reference frame, while Special Relativity has no universal "now." The resolution lies in recognizing that the constraint is on the IIS state itself (which is a single configuration without spatial parts needing coordination), not on spacetime events. Different reference frames describe measurement orderings differently, but all frames agree on the correlations.

A Lorentz-invariant formulation of the interface, likely using algebraic quantum field theory where local observables respect causal diamond structure, is required for full theoretical completeness. This represents ongoing work analogous in importance to the interface criterion problem.

**Quantum field theory:**

Section 3.6 noted that QFT extension remains incomplete. LRT's framework is consistent with quantum field theory but does not yet provide independent derivations of:

- Relativistic field structure
- Renormalization
- Vacuum properties
- Gauge symmetries

However, explicit derivation may not be required. If 3FLL function as a global constraint field rather than merely interface constraints, QFT inherits logical grounding directly. The quantum mechanical core of QFT (complex Hilbert space/Fock space, unitary S-matrix, Boolean measurement outcomes, the Born rule) operates within the same constraint structure that LRT establishes. The specifically field-theoretic features (which fields, which gauge groups, which particle content) represent contingent physical content operating within the constraint field, analogous to how specific triangles operate within Euclidean geometry without being derived from its axioms.

This perspective suggests that renormalization might be understood as constraint enforcement: the infinities arising in naive QFT calculations violate distinguishability (infinite quantities are not well-defined), and renormalization removes these violations to restore 3FLL compliance.

The implications of treating 3FLL as a global constraint field (for understanding gauge symmetries, for the relationship between logical and spacetime structure, and for quantum gravity) constitute a direction for future work.

**Quantum gravity:**

The relationship between LRT and gravity is undeveloped. Intriguing possibilities exist:

- Spacetime might emerge from distinguishability structure in IIS
- The holographic principle suggests information-theoretic foundations for geometry
- The Bekenstein bound connects entropy to area in Planck units

These connections are suggestive but not yet rigorous. Quantum gravity remains the major open problem in fundamental physics; LRT does not solve it.

**The action-complexity conjecture:**

The original development of LRT proposed a conjecture:

$$S = \hbar \cdot C$$

relating physical action S to informational complexity C, with ℏ as the conversion factor.

This conjecture is motivated by:
- The Bekenstein bound (entropy proportional to area in Planck units)
- Black hole thermodynamics
- The Margolus-Levitin quantum speed limit

However, the conjecture remains speculative. It has not generated testable predictions distinct from existing physics. If developed further, it might yield novel empirical content. Currently, it is a research direction, not an established result.

### 7.2 The Status of LRT

LRT is a physical theory that:

| Criterion | Status |
|-----------|--------|
| Explains quantum structure | Yes (uniquely among interpretations) |
| Derives key results | Yes (Born rule, reversibility, complex numbers) |
| Has confirmed predictions | Yes (complex QM, 2021) |
| Is currently testable | Yes (collapse mechanism constraints) |
| Specifies falsification conditions | Yes (12 explicit) |
| Resolves all open questions | No (interface criterion, QFT, gravity remain open) |

This is the status of a successful physical framework with acknowledged limitations, not the status of a complete final theory.

### 7.3 Honest Accounting: Derived vs. Fine-Tuned vs. Given

Clear accounting distinguishes what LRT establishes:

**What Is Derived:**

| Claim | Status | Basis |
|-------|--------|-------|
| Actuality is Boolean | Derived | 3FLL require determinacy |
| Distinguishability is constituted by 3FLL | Derived | Definition/analysis |
| Distinguishability is pairwise/quadratic | Derived | Structural analysis |
| The bit is the fundamental unit | Derived | Minimal distinguishability |
| Born rule (given Hilbert space) | Derived | Gleason's theorem |
| Measurement is category transition | Derived | IIS/actuality framework |
| Entanglement is global constraint | Derived | 3FLL as constraint field |
| Complex Hilbert space | Derived | Masanes-Müller from Axiom 3 |
| Global Parsimony | Derived | CCP + Truthmaker Requirement |

**What Is Fine-Tuned:**

| Feature | Status | Why |
|---------|--------|-----|
| Specific quantum fields | Fine-tuned | Which modes exist is contingent |
| Particle masses | Fine-tuned | Parameter-level tuning |
| Coupling constants | Fine-tuned | Parameter-level tuning |
| Spacetime dimension | Fine-tuned | Not addressed by LRT |
| Initial conditions (s₀) | Fine-tuned | Contingent starting point |

**What Is Given (Axiomatic):**

| Element | Status | Note |
|---------|--------|------|
| 3FLL | Primitive | Constitutive; not derived |
| IIS | Primitive | Co-constitutive with 3FLL |
| Physical constraints (continuity, local tomography) | Axiom 3 | Required for stable, compositional physics |
| Non-contextual measure | Axiom 5 | Required for consistent interface statistics |

**Refining the Status of "Physical Inputs":**

In the derivation of Quantum Field Theory (see QFT companion paper), we categorize features like Lorentz Invariance and Microcausality as "Tier 2/3 Inputs". It is crucial to distinguish the *methodological status* of these inputs from their *ontological status*.

**Methodologically**, we treat them as inputs to maintain rigor where a complete mathematical derivation from 3FLL is not yet finalized. We honestly acknowledge the current gap between the abstract logic of distinguishability and the specific geometry of spacetime.

**Ontologically**, however, LRT asserts that these are not independent variables. Under **Global Parsimony**, the universe cannot contain arbitrary symmetries. Thus, these inputs function as **pending derivations**: logical placeholders for constraints that are necessary to maintain 3FLL compliance.

- **Local Tomography** is not an arbitrary rule; it is the stability constraint that prevents the logical incoherence of "globally distinct but locally identical" states. Although real QM permits globally distinct states with identical marginals (e.g., |Φ⁺⟩ and |Φ⁻⟩ both give ρ_A = ρ_B = I/2), such states would violate Global Parsimony: the same local statistics would correspond to two metaphysically distinct global configurations with no additional distinguishable consequences—surplus ontological structure forbidden by the truthmaker requirement of 3FLL.

- **Lorentz Invariance** is treated as an input, but LRT conjectures that the Poincaré group will ultimately be shown to be the unique isometry group that preserves the distinguishability metric D across all physically admissible frames of reference.

The distinction is not between "logical" and "empirical," but between "derived now" and "derivable in principle."

**What LRT Does Not Explain:**
- Why there is something rather than nothing
- Why 3FLL rather than some other logical structure
- Why THESE quantum fields, masses, constants
- The arrow of time (beyond interface structure)
- The specific interface criterion (empirical question)

### 7.4 The Core Contribution

LRT's central contribution is answering a question other interpretations do not address:

> **Why does quantum mechanics have its specific structure?**

The answer:

> Quantum mechanics is the unique stable interface between the space of distinguishable configurations (IIS) and Boolean actuality, given that the Three Fundamental Laws of Logic are constitutive of physical distinguishability.

This explains:
- Why Hilbert space (pairwise distinguishability + physical constraints)
- Why complex numbers (local tomography)
- Why the Born rule (Gleason's theorem on the interface)
- Why unitary dynamics (reversibility from CBP + Parsimony)
- Why contextuality (values generated at interface)
- Why Bell correlations without signaling (global constraint satisfaction)
- Why the Tsirelson bound (interface stability limit)

Other interpretations postulate quantum structure and interpret it. LRT explains why that structure obtains.

### 7.5 The Wager

LRT offers a wager:

> The deepest structure of physical reality is not contingent but constrained: constrained by the conditions under which anything can be distinguished from anything else.

If this is correct:
- The "unreasonable effectiveness of mathematics" dissolves (mathematics and physics share logical roots)
- The structure of quantum mechanics is not arbitrary but necessary for stable physics
- The foundations of physics connect to the foundations of logic and information

If this is wrong:
- Quantum structure is brute contingency, not explained by deeper principles
- The success of 3FLL across all physics is coincidence or cognitive artifact
- Some alternative interpretation better accounts for the evidence

The wager is testable. Section 6 specified conditions that would refute LRT. The framework takes intellectual risk.

### 7.6 Structured Open Problems

The LRT framework raises precise mathematical and physical questions. These are organized by difficulty and approach:

**Foundational Problems:**

| Problem | Difficulty | Current Status |
|---------|------------|----------------|
| Can Local Tomography be derived from 3FLL? | Hard | Open; currently an axiom (A3c) |
| Can complex numbers be derived from more primitive assumptions? | Medium | Partial; depends on local tomography |
| What categorical structure describes the interface functor? | Medium | Open |
| Characterize representations of the 3FLL algebra | Medium | Open |

**Physical Problems:**

| Problem | Difficulty | Current Status |
|---------|------------|----------------|
| What physical criterion marks interface transition? | Empirical | Candidates identified; testable |
| Prove or refute S = ℏC (action-complexity conjecture) | Hard | Conjectural; motivated |
| How does Lorentz symmetry act on IIS? | Hard | Open; algebraic QFT approach suggested |
| Does gravity modify the interface? (Penrose-Diósi) | Very Hard | Experimentally testable |

**Structural Problems:**

| Problem | Difficulty | Current Status |
|---------|------------|----------------|
| Why do physical systems have specific finite dimensions? | Very Hard | Fine-tuning; not addressed |
| Why U(1) × SU(2) × SU(3) gauge symmetry? | Beyond LRT | Requires unification physics |
| Why three generations of fermions? | Beyond LRT | Parameter-level fine-tuning |

### 7.7 Research Program

**Near-term (tractable with current methods):**
1. Test S = ℏC in simple models (qubit systems)
2. Develop relativistic LRT using algebraic QFT
3. Formalize the interface category mathematically
4. Improve sensitivity of collapse mechanism experiments

**Medium-term (requires new developments):**
5. Derive local tomography from 3FLL (would strengthen foundations)
6. Connect LRT to quantum gravity proposals
7. Test Penrose-Diósi collapse predictions at increasing mass scales
8. Investigate tensor network structure of actualizable states

**Long-term (speculative):**
9. Derive specific field content from LRT + cosmological principles
10. Unify LRT with spacetime emergence
11. Resolve the arrow of time within LRT

### 7.8 Programmatic Elements: Explicit Status Summary

This section explicitly distinguishes what LRT has established from what remains programmatic (open, sketched, or in progress). Honest accounting requires this transparency.

**Established (derived or rigorously justified):**

| Element | Status | Basis |
|---------|--------|-------|
| 3FLL as constitutive of distinguishability | **Established** | Conceptual argument (Section 2) |
| Born rule (|ψ|²) | **Derived** | Gleason's theorem + non-contextual interface |
| Complex Hilbert space (ℂ over ℝ) | **Derived** | Local tomography (A3c); experimentally confirmed (2021) |
| Unitary dynamics | **Derived** | CBP + Parsimony + Stone's theorem |
| Measurement as category transition | **Established** | Conceptual framework (Section 4.2) |
| Contextuality | **Explained** | Interface signature (Section 4.5) |
| Bell correlations without signaling | **Explained** | Global constraint satisfaction (Section 4.3) |

**Programmatic (open, conjectural, or requiring further work):**

| Element | Current Status | What Would Resolve It |
|---------|----------------|----------------------|
| Interface criterion | **Open** | Physical/empirical: What marks IIS→actuality transition? |
| Ontic Booleanity | **Conjecture** | Rigorous proof of Part II (zero-probability tokens); see Section 4.8 |
| Tsirelson bound | **Interpretive** | Formal derivation from 3FLL/interface stability; see Section 4.4 |
| Local tomography | **Tier-2 axiom** | Derivation from 3FLL would strengthen foundations |
| Relativistic extension | **Open** | Full treatment in QFT Gravity Extension paper |
| Specific dimension emergence | **Open** | Why dim(H) = n for specific systems? |

**This distinction matters.** LRT's core contribution is the *framework* that unifies quantum phenomena from logical principles. Some elements within this framework are rigorously established; others are conjectural or require additional development. Failing to distinguish these would overstate the theory's current reach.

The programmatic elements are *tractable* open problems, not fundamental obstacles. Completing them would strengthen LRT; their current openness does not undermine the established results.

### 7.9 Conclusion

Every physical measurement ever conducted has yielded exactly one outcome: self-identical, non-contradictory, determinate. This holds despite a century of quantum mechanics where violations were actively sought.

Logic Realism Theory explains this pattern. The Three Fundamental Laws of Logic are not cognitive conventions but ontological constraints constitutive of physical distinguishability. Quantum mechanics is the unique stable structure at the interface between non-Boolean possibility and Boolean actuality.

The framework derives rather than postulates: complex Hilbert space from local tomography, the Born rule from Gleason's theorem, unitary dynamics from information preservation. One structural prediction (that quantum mechanics requires complex amplitudes) has been experimentally confirmed.

Twelve explicit conditions would falsify the theory. Experiments currently underway test its predictions about collapse mechanisms. This is what physical theories do: explain, predict, and risk refutation.

The competing interpretations either refuse ontological commitment, require infinite unobservable worlds, introduce unexplained nonlocal mechanisms, or abandon objectivity. LRT maintains realism, locality, and parsimony while explaining what others postulate.

The "unreasonable effectiveness of mathematics" in physics is revealed as an illusion caused by viewing physical laws as contingent. By strictly enforcing Global Parsimony, LRT shows that fundamental physical constraints—from the Born Rule to Special Relativity—are the unique mathematical solutions necessary to maintain the Three Fundamental Laws of Logic at the interface of possibility and actuality. There is no "Bit" without the "Fit" of logical consistency.

It from bit. Bit from fit.

Wheeler's insight was that information is fundamental: physical reality emerges from yes/no questions. LRT adds: the bit itself, the fundamental unit of distinction, is not primitive. It emerges from the fit between logical structure (3FLL) and physical actuality. Quantum mechanics is the mathematics of that fit.

---

## References

Aspect, A., Dalibard, J., and Roger, G. "Experimental test of Bell's inequalities using time-varying analyzers." *Physical Review Letters* 49(25), 1982: 1804-1807.

Bell, J. S. "On the Einstein Podolsky Rosen paradox." *Physics* 1(3), 1964: 195-200.

Berto, F. and Jago, M. *Impossible Worlds.* Oxford University Press, 2019.

Borges, J. L. "The Library of Babel." In *Labyrinths*. New York: New Directions, 1962.

Birkhoff, G. and von Neumann, J. "The logic of quantum mechanics." *Annals of Mathematics* 37(4), 1936: 823-843.

Bohm, D. "A suggested interpretation of the quantum theory in terms of 'hidden' variables." *Physical Review* 85(2), 1952: 166-193.

Chiribella, G., D'Ariano, G. M., and Perinotti, P. "Informational derivation of quantum theory." *Physical Review A* 84(1), 2011: 012311.

da Costa, N. C. A. "On the theory of inconsistent formal systems." *Notre Dame Journal of Formal Logic* 15(4), 1974: 497-510.

Deutsch, D. "Quantum theory of probability and decisions." *Proceedings of the Royal Society A* 455, 1999: 3129-3137.

Diósi, L. "Models for universal reduction of macroscopic quantum fluctuations." *Physical Review A* 40(3), 1989: 1165-1174.

Everett, H. "Relative state formulation of quantum mechanics." *Reviews of Modern Physics* 29(3), 1957: 454-462.

Fuchs, C. A. and Schack, R. "Quantum-Bayesian coherence." *Reviews of Modern Physics* 85(4), 2013: 1693-1715.

Ghirardi, G. C., Rimini, A., and Weber, T. "Unified dynamics for microscopic and macroscopic systems." *Physical Review D* 34(2), 1986: 470-491.

Gleason, A. M. "Measures on the closed subspaces of a Hilbert space." *Journal of Mathematics and Mechanics* 6(6), 1957: 885-893.

Hardy, L. "Quantum theory from five reasonable axioms." arXiv:quant-ph/0101012, 2001.

Joos, E. and Zeh, H. D. "The emergence of classical properties through interaction with the environment." *Zeitschrift für Physik B* 59, 1985: 223-243.

Kochen, S. and Specker, E. P. "The problem of hidden variables in quantum mechanics." *Journal of Mathematics and Mechanics* 17(1), 1967: 59-87.

Longmire, J. D. "Logic Realism Theory: Technical Companion." [Available at: https://github.com/jdlongmire/logic-realism-theory/blob/master/theory/Logic_Realism_Theory_Technical.md]

Longmire, J. D. "Logic Realism Theory: Philosophical Foundations." [Available at: https://github.com/jdlongmire/logic-realism-theory/blob/master/theory/Logic_Realism_Theory_Philosophy.md]

Masanes, L. and Müller, M. P. "A derivation of quantum theory from physical requirements." *New Journal of Physics* 13, 2011: 063001.

Penrose, R. "On gravity's role in quantum state reduction." *General Relativity and Gravitation* 28(5), 1996: 581-600.

Priest, G. *In Contradiction: A Study of the Transconsistent.* Second edition. Oxford University Press, 2006.

Priest, G., Beall, J. C., and Armour-Garb, B. (eds.) *The Law of Non-Contradiction: New Philosophical Essays.* Oxford University Press, 2004.

Priest, G., Routley, R., and Norman, J. (eds.) *Paraconsistent Logic: Essays on the Inconsistent.* Philosophia Verlag, 1989.

Pusey, M. F., Barrett, J., and Rudolph, T. "On the reality of the quantum state." *Nature Physics* 8(6), 2012: 475-478.

Renou, M.-O., et al. "Quantum theory based on real numbers can be experimentally falsified." *Nature* 600, 2021: 625-629.

Rovelli, C. "Relational quantum mechanics." *International Journal of Theoretical Physics* 35(8), 1996: 1637-1678.

Stone, M. H. "On one-parameter unitary groups in Hilbert space." *Annals of Mathematics* 33(3), 1932: 643-648.

Tsirelson, B. S. "Quantum generalizations of Bell's inequality." *Letters in Mathematical Physics* 4(2), 1980: 93-100.

Wallace, D. "Quantum probability from subjective likelihood: Improving on Deutsch's proof of the probability rule." *Studies in History and Philosophy of Science Part B* 38(2), 2007: 311-332.

Wheeler, J. A. "Information, physics, quantum: The search for links." In W. Zurek (ed.), *Complexity, Entropy, and the Physics of Information*. Addison-Wesley, 1990.

Wigner, E. P. "The unreasonable effectiveness of mathematics in the natural sciences." *Communications on Pure and Applied Mathematics* 13(1), 1960: 1-14.

Zurek, W. H. "Decoherence, einselection, and the quantum origins of the classical." *Reviews of Modern Physics* 75(3), 2003: 715-775.

---

## Related Papers in This Series

Longmire, J. D. "Logic Realism Theory: Technical Foundations." Zenodo, 2025. DOI: [10.5281/zenodo.17778707](https://doi.org/10.5281/zenodo.17778707)

Longmire, J. D. "Logic Realism Theory: Philosophical Foundations." Zenodo, 2025. DOI: [10.5281/zenodo.17779030](https://doi.org/10.5281/zenodo.17779030)

Longmire, J. D. "LRT Constraints on QFT: Deriving Fock Structure and Interpreting Renormalization from Logical Foundations." Zenodo, 2025. DOI: [10.5281/zenodo.17779066](https://doi.org/10.5281/zenodo.17779066)

