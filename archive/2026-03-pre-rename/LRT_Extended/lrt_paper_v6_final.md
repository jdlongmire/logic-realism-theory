# Logic Realism and the Born Rule: Grounding Quantum Probabilities in Determinate Identity

James (JD) Longmire  
Northrop Grumman Fellow (unaffiliated research)  
ORCID: 0009-0009-1383-7698  
Correspondence: jdlongmire@outlook.com

---

## Abstract

Human cognition readily represents contradictions and impossibilities, yet physical reality appears never to instantiate them. This paper argues that this conceivability-instantiation asymmetry reflects an ontological constraint: the classical laws of logic—determinate identity, non-contradiction, and excluded middle—govern physical instantiation rather than merely description or inference. Developing the logical realism defended by Tahko (2009, 2021), the paper constructs a framework distinguishing representable configurations from those admissible for physical instantiation.

The central contribution is showing that the same Determinate Identity constraint governing instantiation also motivates the measure-theoretic assumptions underlying the Born rule. If a physical system's total weight cannot depend on how it is decomposed into components—a requirement of determinate identity—then the measure over admissible continuations must be additive and non-contextual. Under standard regularity assumptions, Gleason's theorem then yields the Born rule as the unique such measure. The paper thus offers a Tahko-style metaphysical grounding for quantum probabilities, embedding them in a logic-realist ontology of the physical world.

**Keywords:** logic realism, Born rule, quantum foundations, Determinate Identity, Gleason's theorem, ontology

---

## 1. Introduction

Minds and formal systems represent contradictions freely. We conceive round squares, prove theorems about impossible objects, and construct paraconsistent logics in which contradictions are tolerable. None of this strains our cognitive capacities. Yet physical reality, as far as we can determine, never instantiates genuine contradictions or failures of identity. Every quantum measurement yields a definite outcome. No physical system has been observed to both have and lack a property in the same respect. The empirical record is not merely extensive; it is without confirmed exception.

This asymmetry between conceivability and instantiation calls for explanation. The present paper proposes that the classical laws of logic—Determinate Identity, Non-Contradiction, and Excluded Middle—function as ontological constraints on what can be physically instantiated, not merely as constraints on coherent thought or language. This position extends the logical realism defended by Tahko (2009, 2021), who argues that the Law of Non-Contradiction is a metaphysical principle governing reality's structure rather than a semantic convention or psychological limitation.

The paper develops this logic-realist position into a concrete framework for physical instantiation and uses it to address a foundational question in quantum mechanics: why do quantum probabilities take the form they do? The Born rule, which assigns probability $|\langle\phi|\psi\rangle|^2$ to obtaining outcome $|\phi\rangle$ given state $|\psi\rangle$, is standardly treated as an independent postulate. Gleason's theorem (1957) shows that this is the unique probability measure satisfying certain additivity and non-contextuality conditions, but the question of why physical systems should satisfy those conditions remains open.

The central claim of this paper is that Determinate Identity provides a natural answer. If a physical system is determinately what it is, independent of how it is described, then the total measure associated with that system cannot vary with representational decomposition. This constraint motivates precisely the additivity and non-contextuality that Gleason's theorem requires. The Born rule thus emerges not as a brute postulate but as a consequence of logic-realist metaphysics applied to quantum systems.

The paper proceeds as follows. Section 2 develops the logic-realist framework, connecting Tahko's metaphysical position to a concrete admissibility structure on configurations. Section 3 bridges this framework to quantum theory, characterizing quantum states as representations of admissible structure and defining admissible continuations for measurement outcomes. Section 4 presents the core argument: Determinate Identity motivates the measure assumptions that yield the Born rule via Gleason's theorem. Section 5 addresses objections. Section 6 briefly indicates further applications. Section 7 concludes.

---

## 2. Logic Realism and Admissibility

### 2.1 Conceivable versus Instantiable

Let $I_\infty$ denote the space of all representable configurations, including inconsistent and impossible ones. This space is not a domain of entities or possible worlds; it carries no ontological commitment. It is simply the totality of what can be specified, described, or conceived, without restriction to coherence.

The key to understanding how representation of contradiction is possible without instantiated contradiction lies in the distinction between vehicles and contents. A representation has a physical vehicle (a brain state, inscription, or formal structure) and a representational content (what it is about). Vehicles are physical and must satisfy logical constraints. Contents are abstract and need not.

A brain state representing "round square" is a consistent neural configuration (vehicle) representing inconsistent content. The vehicle satisfies the logical constraints; the content does not need to. This distinction explains why minds can conceive impossibilities: the representing is always $L_3$-admissible, even when the represented is not.

### 2.2 $L_3$ as Ontological Constraint

Let $L_3$ denote the conjunction of three classical logical principles, understood as constraints on instantiation:

**Determinate Identity (Id):** Configuration $i$ is determinately the configuration it is, independent of description, distinct from every other configuration.

**Non-Contradiction (NC):** Configuration $i$ cannot instantiate both property $P$ and property $\neg P$ in the same respect at the same time.

**Excluded Middle (EM):** For any well-defined property $P$ applicable to configuration $i$, either $i$ instantiates $P$ or $i$ instantiates $\neg P$.

A configuration is *admissible* if it satisfies $L_3$. Physical reality, denoted $A_\Omega$, is identified with the admissible subset of $I_\infty$:

$$A_\Omega = \{ i \in I_\infty : L_3(i) \}$$

Physical instantiation is thus $I_\infty$ constrained by $L_3$. The claim is not that $L_3$ acts as a mechanism filtering configurations, but that "instantiated contradiction" is incoherent. Round squares are not excluded by a process; they are excluded by meaning.

**The argument against descriptivism.** A descriptivist holds that $L_3$ constrains how we describe reality, not reality itself. But this cannot explain the observed asymmetry. If $L_3$ constrained only description, conceiving violations should be difficult (since description requires $L_3$) while instantiating them should be possible (since reality would be unconstrained). Empirically, the reverse holds: conceiving violations is easy, instantiating them appears impossible. Logic realism explains this pattern; descriptivism does not.

**Connection to Tahko.** Tahko (2009, 2021) argues that the Law of Non-Contradiction is a metaphysical principle governing reality's structure. The present framework takes this metaphysical position and builds a concrete admissibility map from conceivable configurations to physically instantiable ones. Where Tahko establishes the metaphysical status of logical laws, LRT develops their structural consequences for physical instantiation.

### 2.3 Time and Ordering

The framework has nontrivial structural consequences beyond mere consistency. Consider two configurations $i$ and $j$ that are individually admissible but jointly inadmissible—for instance, the same particle at position $x_1$ and at position $x_2 \neq x_1$. Each satisfies $L_3$ alone, but their co-instantiation would violate Determinate Identity: the particle would not be determinately at one position.

If both configurations appear in a single history of an enduring system, they cannot be co-instantiated. They must be *ordered*: one before the other. Joint inadmissibility of individually admissible configurations yields a precedence structure. This is a sketch of how temporal ordering might emerge from admissibility constraints.

The point here is not to develop a full theory of time but to show that $L_3$ already shapes physical structure in substantive ways. If logical constraints yield temporal ordering, it is plausible that they also shape probabilistic structure. This sets up the main argument of Section 4.

---

## 3. Quantum States and Admissible Structure

### 3.1 Superposition as Representational

A quantum state $|\psi\rangle = \alpha|0\rangle + \beta|1\rangle$ does not represent a system that is "both 0 and 1." The state vector describes a region of admissible configurations in $L_3(I_\infty)$ consistent with preparation. The system has the determinate property of *being in state $|\psi\rangle$*. This is an element of $A_\Omega$. The outcome alternatives $|0\rangle$ and $|1\rangle$ are in $I_\infty$ pending resolution.

The claim is not that the quantum state is incomplete, but that it represents admissible structure rather than instantiated multiplicity. The admissibility of the quantum state itself is not in question; what is restricted is the co-instantiation of mutually exclusive outcome-specifications within a single identity-thread.

### 3.2 Admissible Continuations and Macroscopic Outcomes

A macroscopic object—a pointer, detector, or observer—has trans-temporal determinate identity: it is numerically one object persisting across time. When such an identity-bearing system becomes entangled with a quantum system, the situation changes.

Consider a measurement in which outcome $|0\rangle$ correlates with pointer state $|U\rangle$ (up) and outcome $|1\rangle$ correlates with pointer state $|D\rangle$ (down). A history containing the same pointer in both states $|U\rangle$ and $|D\rangle$ would violate Non-Contradiction for that pointer's trans-temporal identity. Such histories are inadmissible.

This provides a compact account of outcome definiteness:

1. Decoherence selects a stable pointer basis, making $\{|U\rangle, |D\rangle\}$ dynamically robust.
2. $L_3$ then requires that exactly one of the candidate histories—(pointer Up, observer sees Up) or (pointer Down, observer sees Down)—be included in $A_\Omega$.

Call each of these mutually exclusive, decohered outcome-histories an *admissible continuation* of the system's current state. The question that remains is: with what weights are the admissible continuations selected? This is where Determinate Identity enters.

---

## 4. Determinate Identity and the Born Rule

### 4.1 Identity Stability as a Constraint on Measures

Given a quantum system in state $|\psi\rangle$ and a set of mutually exclusive admissible outcome-configurations $\{|i\rangle\}$, we seek a measure $P(i \mid |\psi\rangle, \{|i\rangle\})$ weighting the admissible continuations.

The argument does not presuppose probabilistic interpretation. It concerns any measure intended to weight mutually exclusive admissible continuations. Only after the measure is fixed does it acquire probabilistic interpretation.

**The identity stability requirement.** For a physical system to satisfy Determinate Identity, its total measure cannot depend on how it is decomposed into components. If the total measure varied with choice of orthonormal basis, then the question "What is this system's total weight?" would have different answers in different decompositions. This violates Id: the system would not be determinately what it is, independent of how it is described.

This constraint motivates two properties:

1. **Additivity:** The measure over mutually exclusive outcomes must sum to a fixed total.
2. **Non-contextuality:** The weight assigned to a particular outcome cannot depend on which larger set of alternatives it is grouped with.

Non-Contradiction and Excluded Middle ensure that the set of outcome-configurations is partitioned into mutually exclusive and jointly exhaustive alternatives, making additivity meaningful. Determinate Identity then constrains how the total weight assigned to this partition can behave across decompositions. On this picture, rejecting non-contextuality for physical weights amounts to rejecting that a system's total weight is determinate and description-independent, and thus conflicts with Determinate Identity.

**Why probabilistic weight is physical, not merely representational.** A skeptic might reply: "The system is determinate, but its probabilistic description need not be. Basis-dependence is a feature of our representational scheme, not a failure of identity." This escape route must be blocked.

The measure in question is not an epistemic credence or a feature of how we choose to describe the system. It is the weighting over *which physical outcomes are admissible continuations* of the system's current state. These are candidate histories of actual physical events. If the total weight over such candidates varied with how we decomposed the system's state, then the physical situation itself—not merely our description of it—would be indeterminate. The system would not be determinately poised toward one distribution of outcomes rather than another.

An instrumentalist who treats probabilities as purely predictive tools may resist this framing. But the instrumentalist thereby abandons the project of giving an ontological account of quantum probabilities. For those who seek such an account, the measure over admissible continuations must be a feature of the physical situation, and Determinate Identity constrains it accordingly.

### 4.2 Excluded Middle and Macroscopic Outcomes

A clarification is needed regarding Excluded Middle in the quantum context. Quantum foundations includes extensive work on quantum logic, POVMs, unsharp observables, and many-valued semantics. Does EM apply to quantum systems?

The answer within LRT is: EM applies at the level of *instantiated macroscopic outcomes*, not at the level of all quantum propositions. A superposed system does not violate EM because the system is not "both spin-up and spin-down"; it is determinately in the superposition state $|\psi\rangle$. EM applies to instantiated configurations, and the superposed state is one such configuration.

When measurement occurs and macroscopic identity becomes engaged, the admissible continuations are the decohered outcome-histories. These are mutually exclusive and jointly exhaustive: the pointer is up or down, not both, not neither. EM governs this level—the level of what is actually instantiated in $A_\Omega$—not the level of quantum propositions about unmeasured systems.

This distinction allows LRT to maintain EM as an ontological constraint while acknowledging that quantum systems before measurement do not satisfy classical bivalence for all observables. The constraint applies to physical instantiation, not to the truth-values of counterfactual measurement claims.

### 4.3 Illustration: The Qubit Case

Consider a qubit with real coefficients:

$$|\psi\rangle = \cos\theta\,|0\rangle + \sin\theta\,|1\rangle$$

For illustration, restricting to real coefficients and assuming that the weight assigned to an outcome depends only on its amplitude coefficient, we write $P(0) = f(\cos\theta)$ and $P(1) = f(\sin\theta)$ for some function $f:[0,1]\to[0,1]$. Identity stability requires $f(\cos\theta) + f(\sin\theta) = 1$ for all $\theta$.

Test candidates:

- **Linear:** $f(x) = x$. Then $\cos\theta + \sin\theta = \sqrt{2}$ at $\theta = \pi/4$. Fails.
- **Cubic:** $f(x) = x^3$. Then $\cos^3\theta + \sin^3\theta \neq 1$ generally. Fails.
- **Quadratic:** $f(x) = x^2$. Then $\cos^2\theta + \sin^2\theta = 1$ for all $\theta$. Works.

The quadratic form is forced by the Pythagorean identity. This two-dimensional case illustrates the structural constraint; the general result relies on Gleason's theorem and does not depend on this example. The metaphysical constraint (identity stability) is dimension-independent; the mathematical theorem establishing uniqueness requires dimension $\geq 3$.

### 4.4 Connecting to Gleason and Busch

In Hilbert spaces of dimension $\geq 3$, Gleason's theorem (1957) establishes that any $\sigma$-additive, non-contextual probability measure on projections has the form:

$$\mu(P) = \langle\psi|P|\psi\rangle$$

For pure states and rank-1 projectors $P = |\phi\rangle\langle\phi|$:

$$\mu(P) = |\langle\phi|\psi\rangle|^2$$

This is the Born rule.

**Separating assumptions.** The derivation relies on two types of constraint:

*Metaphysically motivated by Determinate Identity:*
- Total measure fixed for a system (basis-independence)
- Non-contextuality of the measure

*Mathematically standard:*
- $\sigma$-additivity
- Hilbert space structure and dimension $\geq 3$
- Measurability of projections

**The contribution.** The paper does not replace Gleason's theorem or claim to derive the Born rule from logic alone. The contribution is the *ground*: Determinate Identity explains why it is natural—indeed, required for determinate physical systems—to assume a non-contextual, additive measure. Gleason then shows that the Born rule is the unique such measure.

This embeds quantum probabilities in a Tahko-style logic-realist metaphysics. The Born rule is not a brute postulate about nature; it is a consequence of what it means for physical systems to be determinately what they are.

---

## 5. Objections and Replies

**Objection 1: Instrumentalist non-contextuality.** "Non-contextuality is a feature of successful predictive schemes, not a constraint on physical reality. The Born rule works; why seek deeper grounding?"

*Reply.* This paper is addressed to those who seek an ontological account of quantum probabilities, not merely a predictive algorithm. For instrumentalists content with predictive success, no further grounding is needed. But instrumentalism is a methodological stance, not an explanation. Those who ask *why* the Born rule holds—why this measure rather than another—require the kind of grounding offered here.

**Objection 2: QBist rejection of system-intrinsic measures.** "Probabilities are agent-relative credences, not features of physical systems. There is no system-intrinsic measure to be grounded."

*Reply.* QBism relocates probability from world to agent, but it does not eliminate the question of why agents' credences, if they are to be coherent and successful, must satisfy Born-rule structure. LRT offers an answer: the physical situations agents encounter are structured by Determinate Identity, and coherent credences must respect that structure. QBism and LRT are not straightforwardly incompatible; they address different aspects of the probability question.

**Objection 3: Dialetheist pushback on LNC.** "Some contradictions may be true. Why assume Non-Contradiction governs physical instantiation?"

*Reply.* Dialetheists locate true contradictions in semantic, logical, or paradox-related domains, not in physical instantiation. No dialetheist claims that a particle is simultaneously at position $x$ and not at position $x$ in the same respect. The LRT claim—that physical instantiation satisfies $L_3$—is compatible with dialetheism about other domains. If a dialetheist wishes to extend true contradictions to physical instantiation, the burden is on them to produce an example. The empirical record provides none.

**Objection 4: Many-Worlds conflation.** "Admissible continuations sound like Everettian branches. Is this Many-Worlds in disguise?"

*Reply.* No. Admissible continuations are candidate histories, exactly one of which is included in $A_\Omega$. Everettian branches are all equally real and co-instantiated. LRT holds that macroscopic branching violates Determinate Identity: an object cannot have multiple successors while remaining numerically one object. The admissibility framework selects one history; Many-Worlds includes all. The disagreement is substantive, not verbal.

---

## 6. Further Applications and Future Work

The framework developed here has applications beyond the Born rule:

**Temporal structure and causality.** The same admissibility machinery yields a partial temporal order from joint inadmissibility of incompatible configurations (Section 2.3). A fuller development would connect logic realism to the emergence of time and causal structure.

**Measurement and macroscopic uniqueness.** Integration of decoherence theory with $L_3$ would provide a logic-realist account of why macroscopic observers always see determinate outcomes, complementing the probability measure with an account of outcome selection.

**Quantum gravity and singularities.** Admissibility and limits of individuation suggest interpretive alignments with Planck-scale structure and black hole thermality, viewed as breakdown and re-emergence of determinate identity. These remain conjectural.

**Dynamics and the kinetic term.** Under additional regularity assumptions (locality, isotropy, compositional additivity), identity stability may also favor a quadratic form for the "cost of motion" in configuration space, hinting at a metaphysical underpinning for the classical kinetic term. This is reserved for separate work.

---

## 7. Conclusion

Starting from Tahko-style logic realism about the Law of Non-Contradiction, this paper has articulated an admissibility-based picture of physical instantiation. The conceivability-instantiation asymmetry—the ease of representing impossibilities paired with the apparent impossibility of instantiating them—reflects ontological constraints on what can be physically real. Round squares are not excluded by a process; they are excluded by meaning. The same holds for instantiated contradictions generally.

The central contribution is showing that Determinate Identity, one of these ontological constraints, naturally motivates the measure assumptions that yield the Born rule. If physical systems are determinately what they are, their total weight cannot depend on representational decomposition. This requires additivity and non-contextuality. Gleason's theorem then yields the Born rule as the unique measure satisfying these constraints.

Quantum probabilities are thus embedded in a logic-realist metaphysics of the physical world. The Born rule is not a brute fact about nature but a consequence of what determinate physical existence requires.

---

## References

### Logic and Metaphysics

Priest, G. (2006). *In Contradiction: A Study of the Transconsistent*. Oxford University Press.

Tahko, T. E. (2009). The Law of Non-Contradiction as a Metaphysical Principle. *Australasian Journal of Logic*, 7, 32–47.

Tahko, T. E. (2021). *Unity of Science*. Cambridge University Press.

### Quantum Foundations

Busch, P. (2003). Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem. *Physical Review Letters*, 91(12), 120403.

Gleason, A. M. (1957). Measures on the Closed Subspaces of a Hilbert Space. *Journal of Mathematics and Mechanics*, 6(6), 885–893.

Pitowsky, I. (1998). Infinite and Finite Gleason's Theorems and the Logic of Indeterminacy. *Journal of Mathematical Physics*, 39(1), 218–228.

Wallace, D. (2012). *The Emergent Multiverse: Quantum Theory according to the Everett Interpretation*. Oxford University Press.

Zurek, W. H. (2003). Decoherence, Einselection, and the Quantum Origins of the Classical. *Reviews of Modern Physics*, 75(3), 715–775.
