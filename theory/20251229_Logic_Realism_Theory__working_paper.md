# Logic Realism and the Born Rule: Grounding Quantum Probabilities in Determinate Identity

James (JD) Longmire  
Northrop Grumman Fellow (unaffiliated research)  
ORCID: 0009-0009-1383-7698  
Correspondence: jdlongmire@outlook.com

---

## Abstract

Human cognition readily represents contradictions and impossibilities, yet physical reality appears never to instantiate them. This paper argues that this conceivability-instantiation asymmetry reflects an ontological constraint: the classical laws of logic (determinate identity, non-contradiction, and excluded middle) govern physical instantiation rather than merely description or inference. Developing the logical realism defended by Tahko (2009, 2021), the paper constructs a framework distinguishing representable configurations from those admissible for physical instantiation.

The central contribution is showing that Determinate Identity motivates the measure-theoretic assumptions underlying the Born rule. The argument proceeds via a vehicle/content distinction: a quantum state is a physical situation (vehicle) representing outcome-possibilities (content). The measure over admissible continuations characterizes how the physical situation is poised toward outcomes; it belongs to the vehicle, not the content. If this measure varied with choice of mathematical decomposition, the physical situation itself would be indeterminate, violating Determinate Identity. This constraint, combined with decoherence's selection of outcome bases, motivates the additivity and non-contextuality that Gleason's theorem requires. The Born rule thus emerges as the unique measure compatible with determinate physical identity.

Appendix A provides the complete formal derivation. Appendix B sketches how complex Hilbert space may be the unique arena capable of hosting determinate identity under composition (a research direction rather than a completed proof). Appendix C recasts Bell violations as failures of local identity factorization rather than failures of locality. Appendix D formalizes the derivation chain: Theorem D.1 shows that Determinate Identity forces intrinsic identity somewhere; Theorem D.2 establishes macroscopic self-sufficiency as a transcendental precondition of stable records; Theorem D.4 derives the Born rule from vehicle-weight invariance. The paper thus offers a Tahko-style metaphysical grounding for quantum probabilities and non-local correlations, embedding them in a logic-realist ontology of the physical world.

**Keywords:** logic realism, Born rule, quantum foundations, Determinate Identity, Gleason's theorem, Bell non-locality, Hilbert space, ontology

---

## 1. Introduction

Minds and formal systems represent contradictions freely. We conceive round squares, prove theorems about impossible objects, and construct paraconsistent logics in which contradictions are tolerable. None of this strains our cognitive capacities. Yet physical reality, as far as we can determine, never instantiates genuine contradictions or failures of identity. Every quantum measurement yields a definite outcome. No physical system has been observed to both have and lack a property in the same respect. The empirical record is not merely extensive; it is without confirmed exception.

This asymmetry between conceivability and instantiation calls for explanation. The present paper proposes that the classical laws of logic (Determinate Identity, Non-Contradiction, and Excluded Middle) function as ontological constraints on what can be physically instantiated, not merely as constraints on coherent thought or language. This position extends the logical realism defended by Tahko (2009, 2021), who argues that the Law of Non-Contradiction is a metaphysical principle governing reality's structure rather than a semantic convention or psychological limitation.

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

**Connection to Tahko.** Tahko (2009, 2021) argues that the Law of Non-Contradiction is a metaphysical principle governing reality's structure. The present framework takes this metaphysical position and builds a concrete admissibility map from conceivable configurations to physically instantiable ones. Where Tahko establishes the metaphysical status of logical laws, LRT develops their structural consequences for physical instantiation.[^1]

[^1]: The ontological extension here builds primarily on Tahko (2009), which argues directly for logical realism about the Law of Non-Contradiction. Tahko (2021), *Unity of Science*, concerns natural-kind monism and grounding relations; it informs the broader metaphysical framework (particularly the grounding structure of the derivation chain) but is not the direct source of the logical-realist premise.

The preceding considerations establish that $L_3$ constrains physical instantiation, not merely description. But how strong is this constraint? The following paragraphs defend the strongest defensible reading.

**The ontological status of Determinate Identity.** Physical reality is not a neutral arena onto which logic is later imposed. It is constituted such that only configurations satisfying Determinate Identity can be instantiated at all. A configuration without determinate identity is not a borderline or fuzzy entity; it is nothing. There is no "indeterminate thing" waiting to be instantiated and then made determinate by observation or description. To lack determinate identity is to fail to be a thing—not to be a vague thing, not to be a probabilistic thing, not to be a relational thing, but simply not to exist as a distinct entity in any respect whatsoever.

This is not a claim about how we must conceptualize reality. It is a claim about what reality can contain. The Law of Identity is not a law of thought imposed on an otherwise formless substrate. It is the minimal condition of ontological distinctness. Without it there are no entities, no properties, no relations, no events, no outcomes—only undifferentiated being, which is indistinguishable from non-being.

Empirical warrant for this claim comes from the complete absence of counterexamples: no physical process has ever been observed in which a genuine entity both is and is not determinately itself in the same respect. The apparent exceptions (superpositions, entangled subsystems) are not exceptions to Determinate Identity; they are situations in which local determinate identity has not yet emerged. Once decoherence produces a macroscopic pointer, determinate identity reappears exactly where the ontological constraint requires it. The pattern is consistent: where there is instantiation, there is determinate identity; where determinate identity is absent, there is no macroscopic instantiation.

Even readers who resist this direct ontological claim must accept a weaker transcendental version: any physical reality that admits determinate description, measurement, or record must satisfy Determinate Identity. The minimal precondition that makes determinate thought possible is also the minimal precondition that makes a determinate physical reality possible. If physical reality lacked Determinate Identity altogether, there would be no determinate configurations to instantiate, no determinate outcomes to measure, and no determinate records to read. This weaker claim suffices for the derivation that follows. But the intended interpretation is stronger: Determinate Identity is a constraint on being, not merely on knowability.

### 2.3 Time and Ordering (Programmatic)

The framework has nontrivial structural consequences beyond mere consistency. Consider two configurations $i$ and $j$ that are individually admissible but jointly inadmissible: the same particle at position $x_1$ and at position $x_2 \neq x_1$. Each satisfies $L_3$ alone, but their co-instantiation would violate Determinate Identity: the particle would not be determinately at one position.

If both configurations appear in a single history of an enduring system, they cannot be co-instantiated. They must be *ordered*: one before the other. Joint inadmissibility of individually admissible configurations yields a precedence structure.

*This observation is programmatic, not a completed derivation.* A full account would need to explain why the ordering is temporal rather than merely logical, how it acquires metric structure, and how it connects to relativistic spacetime. These questions are reserved for future work. The point here is only to illustrate that $L_3$ has structural consequences beyond filtering out contradictions; it shapes what configurations can coexist and in what relations. If logical constraints yield temporal ordering, it is plausible that they also shape probabilistic structure. This sets up the main argument of Section 4.

---

## 3. Quantum States and Admissible Structure

### 3.1 Superposition as Representational

A quantum state $|\psi\rangle = \alpha|0\rangle + \beta|1\rangle$ does not represent a system that is "both 0 and 1." The state vector describes a region of admissible configurations in $A_\Omega$ consistent with preparation. The system has the determinate property of *being in state $|\psi\rangle$*. This is an element of $A_\Omega$. The outcome alternatives $|0\rangle$ and $|1\rangle$ are in $I_\infty$ pending resolution.

The claim is not that the quantum state is incomplete, but that it represents admissible structure rather than instantiated multiplicity. The admissibility of the quantum state itself is not in question; what is restricted is the co-instantiation of mutually exclusive outcome-specifications within a single identity-thread.

### 3.2 Admissible Continuations and Macroscopic Outcomes

A macroscopic object (a pointer, detector, or observer) has trans-temporal determinate identity: it is numerically one object persisting across time. When such an identity-bearing system becomes entangled with a quantum system, the situation changes.

Consider a measurement in which outcome $|0\rangle$ correlates with pointer state $|U\rangle$ (up) and outcome $|1\rangle$ correlates with pointer state $|D\rangle$ (down). A history containing the same pointer in both states $|U\rangle$ and $|D\rangle$ would violate Non-Contradiction for that pointer's trans-temporal identity. Such histories are inadmissible.

This provides a compact account of outcome definiteness:

1. Decoherence selects a stable pointer basis, making $\{|U\rangle, |D\rangle\}$ dynamically robust.
2. $L_3$ then requires that exactly one of the candidate histories (pointer Up, observer sees Up) or (pointer Down, observer sees Down) be included in $A_\Omega$.

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

**Clarification on scope.** A potential circularity threatens here: does the argument assume basis-independence to derive basis-independence? The answer is no, because two distinct questions are in play.

*First question:* Which outcomes count as admissible continuations? This is answered by decoherence, which selects a dynamically stable pointer basis $\{|i\rangle\}$. The admissible continuations are fixed by physics, not by representational choice. There is no basis-independence assumption here; decoherence picks out a particular basis.

*Second question:* Given the fixed set of admissible continuations, how must the measure over them behave? Here Determinate Identity enters. The quantum state $|\psi\rangle$ can be decomposed into the pointer basis, but it can also be decomposed into infinitely many other orthonormal bases. These alternative decompositions do not change which outcomes are admissible (that is fixed by decoherence), but they do provide different mathematical representations of the same physical state.

The identity constraint is this: since these decompositions all represent the same physical situation, any measure that is intrinsic to that situation (rather than an artifact of representation) must be invariant across them. The measure cannot "know" which mathematical decomposition we happen to use.

This is not circular. Decoherence fixes the outcomes; Determinate Identity constrains the measure over those outcomes to be invariant under re-representation of the state. The two constraints operate at different levels.

Non-Contradiction and Excluded Middle ensure that the set of outcome-configurations is partitioned into mutually exclusive and jointly exhaustive alternatives, making additivity meaningful. Determinate Identity then constrains how the total weight assigned to this partition can behave across decompositions. On this picture, rejecting non-contextuality for physical weights amounts to rejecting that a system's total weight is determinate and description-independent, and thus conflicts with Determinate Identity.

**Why probabilistic weight is physical, not merely representational.** A skeptic might reply: "The system is determinate, but its probabilistic description need not be. Basis-dependence is a feature of our representational scheme, not a failure of identity." This escape route must be blocked.

The vehicle/content distinction introduced in Section 2.1 is crucial here; we now develop it further. A representation has a physical vehicle (the representing structure) and abstract content (what is represented). Vehicles must satisfy $L_3$; contents need not. Now consider: what kind of thing is the measure over admissible continuations?

The measure is not content; it is not what the quantum state represents. Rather, it characterizes the physical situation's disposition toward various outcomes. It belongs to the vehicle, not the content. The quantum state $|\psi\rangle$ is a physical configuration (vehicle) that represents a region of outcome-possibilities (content). The measure over those possibilities is a feature of *how the physical situation is poised*, not a feature of how we choose to describe that situation.

To see this more concretely: when we say the system has probability $p$ of yielding outcome $|i\rangle$, we are not describing an epistemic limitation or a representational choice. We are characterizing the physical situation's objective tendency. If this tendency varied with our choice of basis (if the system were "70% poised toward outcome A" in one decomposition and "50% poised toward outcome A" in another) then the physical situation itself would be indeterminate between these dispositions. The system would not be determinately poised toward any particular distribution of outcomes.

This is a failure of Determinate Identity at the level of the vehicle, not merely at the level of content. The physical situation would fail to be determinately what it is, independent of how we describe it.

An instrumentalist who treats probabilities as purely predictive tools may resist this framing. But the instrumentalist thereby abandons the project of giving an ontological account of quantum probabilities. For those who seek such an account, the measure over admissible continuations must be a feature of the physical situation (part of the vehicle, not the content) and Determinate Identity constrains it accordingly.

### 4.2 Excluded Middle, Quantum Logic, and Macroscopic Outcomes

A clarification is needed regarding Excluded Middle in the quantum context. Quantum foundations includes extensive work on quantum logic, POVMs, unsharp observables, and many-valued semantics. Does EM apply to quantum systems?

The answer within LRT is: EM applies at the level of *instantiated macroscopic outcomes*, not at the level of all quantum propositions. A superposed system does not violate EM because the system is not "both spin-up and spin-down"; it is determinately in the superposition state $|\psi\rangle$. EM applies to instantiated configurations, and the superposed state is one such configuration.

When measurement occurs and macroscopic identity becomes engaged, the admissible continuations are the decohered outcome-histories. These are mutually exclusive and jointly exhaustive: the pointer is up or down, not both, not neither. EM governs this level (the level of what is actually instantiated in $A_\Omega$) not the level of quantum propositions about unmeasured systems.

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

**Note on the dimension-2 case.** Gleason's theorem fails for $\dim \mathcal{H} = 2$: there exist non-Born measures satisfying additivity and non-contextuality in two dimensions. Does this undermine the metaphysical argument?

No. The dimension-2 pathology reflects the poverty of the two-dimensional projection lattice, not a failure of Determinate Identity. In dimension 2, every orthonormal basis contains only two elements, and the constraint structure is too weak to force uniqueness. But actual physical systems are never genuinely two-dimensional in isolation. A qubit is always embedded in a larger Hilbert space (the environment, the measurement apparatus, the rest of the universe). The relevant constraint is that the measure be consistent across *all* subsystems and compositions, not merely within an artificially isolated two-dimensional subspace.

Put differently: Determinate Identity is a global constraint on physical systems. The dimension-2 loophole exists only for mathematically idealized systems that cannot be physically instantiated in isolation. For any system embedded in a larger arena (which is to say, for any actual physical system) the constraint bites. This global embedding requirement is itself a consequence of the identity-preserving composition that Appendix B sketches: if subsystem identity must cohere with global identity under arbitrary decomposition, then the measure constraints propagate from the global arena (dimension $\geq 3$) to every embedded subsystem.

### 4.4 Connecting to Gleason and Busch

In Hilbert spaces of dimension $\geq 3$, Gleason's theorem (1957) establishes that any non-contextual probability measure on projections has the form:

$$\mu(P) = \langle\psi|P|\psi\rangle$$

**Technical note on additivity.** Gleason's original theorem assumes $\sigma$-additivity (countable additivity). Busch (2003) showed that finite additivity suffices in dimension $\geq 3$: the frame function argument extends without assuming countable additivity. The metaphysical argument of this paper motivates finite additivity directly (the total weight over any finite partition must be constant); $\sigma$-additivity is a mathematical strengthening that does not affect the conclusion. Appendix A uses finite additivity throughout.

For pure states and rank-1 projectors $P = |\phi\rangle\langle\phi|$:

$$\mu(P) = |\langle\phi|\psi\rangle|^2$$

This is the Born rule.

**Separating assumptions.** The derivation relies on two types of constraint:

*Metaphysically motivated by Determinate Identity:*
- Total measure fixed for a system (basis-independence)
- Non-contextuality of the measure
- Finite additivity over orthogonal projections

*Mathematically standard:*
- Hilbert space structure and dimension $\geq 3$
- Measurability of projections

**The contribution.** The paper does not replace Gleason's theorem or claim to derive the Born rule from logic alone. The contribution is the *ground*: Determinate Identity explains why it is natural (indeed, required for determinate physical systems) to assume a non-contextual, additive measure. Gleason then shows that the Born rule is the unique such measure. Appendix A provides the complete formal chain of reasoning from Determinate Identity through unitary invariance to the Born rule.

This embeds quantum probabilities in a Tahko-style logic-realist metaphysics. The Born rule is not a brute postulate about nature; it is a consequence of what it means for physical systems to be determinately what they are.

### 4.5 Bell Non-Locality as Global Identity Constraint

Bell-type correlations pose an apparent puzzle: spacelike-separated measurements exhibit correlations that cannot be reproduced by any locally factorizable model. The standard narrative frames this as a tension between locality and realism.

The admissibility framework offers a different diagnosis. Bell inequalities follow from three assumptions: (1) outcome definiteness, (2) local factorization of probabilities, and (3) measurement independence. Quantum mechanics violates the inequalities. Something must give.

The key observation is that local factorization implicitly assumes:

*Global identity is reducible to a product of independently individuated local identities.*

This assumption is stronger than locality and is not guaranteed by the 3FLL. From the Compositional Distinguishability Principle (Appendix B), every global distinction must admit a local, context-independent witness. But Bell violations show that certain global distinctions (correlation patterns between distant outcomes) do not decompose into independent local distinctions without violating identity constraints.

Thus Bell's theorem demonstrates: CDP cannot be simultaneously satisfied with local factorization. But CDP was required to preserve Determinate Identity under composition. Bell therefore forces a choice: abandon Determinate Identity, or abandon local factorization of identity.

Quantum mechanics chooses the latter. This is not "spooky action at a distance." No signal or influence travels between measurement sites. What changes is the set of *admissible global continuations* once outcomes are instantiated. Each local outcome is determinate and locally recorded, but which pairs of local outcomes are jointly admissible is globally constrained.

Bell's theorem can thus be restated: no theory can simultaneously satisfy (1) determinate outcomes, (2) decomposition-invariant identity, (3) local factorization of identity, and (4) empirical adequacy. Quantum theory preserves (1), (2), and (4) by rejecting (3).

Bell violations are experimental probes of identity structure, not spacetime causation. Appendix C develops this analysis in full detail.

---

## 5. Objections and Replies

**Objection 1: Instrumentalist non-contextuality.** "Non-contextuality is a feature of successful predictive schemes, not a constraint on physical reality. The Born rule works; why seek deeper grounding?"

*Reply.* This paper is addressed to those who seek an ontological account of quantum probabilities, not merely a predictive algorithm. For instrumentalists content with predictive success, no further grounding is needed. But instrumentalism is a methodological stance, not an explanation. Those who ask *why* the Born rule holds (why this measure rather than another) require the kind of grounding offered here.

**Objection 2: QBist rejection of system-intrinsic measures.** "Probabilities are agent-relative credences, not features of physical systems. There is no system-intrinsic measure to be grounded."

*Reply.* QBism relocates probability from world to agent, but it does not eliminate the question of why agents' credences, if they are to be coherent and successful, must satisfy Born-rule structure. LRT offers an answer: the physical situations agents encounter are structured by Determinate Identity, and coherent credences must respect that structure. QBism and LRT are not straightforwardly incompatible; they address different aspects of the probability question.

**Objection 3: Dialetheist pushback on LNC.** "Some contradictions may be true. Why assume Non-Contradiction governs physical instantiation?"

*Reply.* Dialetheists locate true contradictions in semantic, logical, or paradox-related domains, not in physical instantiation. No dialetheist claims that a particle is simultaneously at position $x$ and not at position $x$ in the same respect. The LRT claim (that physical instantiation satisfies $L_3$) is compatible with dialetheism about other domains. If a dialetheist wishes to extend true contradictions to physical instantiation, the burden is on them to produce an example. The empirical record provides none.

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

Starting from Tahko-style logic realism about the Law of Non-Contradiction, this paper has articulated an admissibility-based picture of physical instantiation. The conceivability-instantiation asymmetry (the ease of representing impossibilities paired with the apparent impossibility of instantiating them) reflects ontological constraints on what can be physically real. Round squares are not excluded by a process; they are excluded by meaning—and so too for instantiated contradictions of any kind.

The central contribution is showing that Determinate Identity, one of these ontological constraints, motivates the measure assumptions that yield the Born rule. The argument hinges on the vehicle/content distinction: a quantum state is a physical configuration (vehicle) representing outcome-possibilities (content). The measure over admissible continuations belongs to the vehicle; it characterizes how the physical situation is objectively poised toward various outcomes. If this measure varied with mathematical decomposition, the physical situation itself would fail to be determinate. 

Decoherence and identity constraints operate at different levels without circularity. Decoherence selects which outcomes are physically admissible continuations (fixing the pointer basis). Determinate Identity then constrains the measure over those fixed outcomes to be invariant under re-representation of the quantum state. Together, these constraints motivate additivity and non-contextuality. Gleason's theorem yields the Born rule as the unique measure satisfying these constraints in Hilbert spaces of dimension three or greater.

Quantum probabilities are thus embedded in a logic-realist metaphysics of the physical world. The Born rule is not a brute fact about nature but a consequence of what determinate physical existence requires.

Two extensions have been sketched. Appendix B outlines a research program showing how complex Hilbert space may be forced as the unique arena compatible with identity-preserving composition; this is a direction for future rigorization rather than a completed derivation. Appendix C recasts Bell non-locality as global identity coherence rather than superluminal causation: Bell violations probe identity structure, not spacetime causation.

The metaphysical commitment is explicit: logic governs instantiation, not merely description. Those who reject this commitment must explain the conceivability-instantiation asymmetry by other means. Those who accept it gain a unified framework in which quantum probabilities, the structure of state space, and non-local correlations all flow from a single source: the requirement that physical reality be determinately what it is.

---

## Appendix A: Proof that Determinate Identity Implies the Born Rule via Gleason's Theorem

This appendix collects and makes fully explicit the chain of reasoning that connects the metaphysical principle of Determinate Identity to the conclusion that the unique probability measure over admissible outcome-histories must be given by the Born rule (for pure states in Hilbert space dimension $\geq 3$).

We assume a complex separable Hilbert space $\mathcal{H}$ with $\dim \mathcal{H} \geq 3$. Let $\mathcal{P}(\mathcal{H})$ be the orthomodular lattice of orthogonal projections on $\mathcal{H}$. Let $\mu : \mathcal{P}(\mathcal{H}) \to [0,1]$ be a finitely additive probability measure on projections ($\mu(\sum P_i) = \sum \mu(P_i)$ for finite orthogonal sums, $\mu(I) = 1$). The measure is interpreted as assigning weights to admissible outcome-histories (rank-1 projections corresponding to mutually exclusive macroscopic continuations).

### A.1 Determinate Identity as Invariance of Total Weight

**Definition A.1 (Determinate total weight).** A physical system in a given state is determinately what it is, independent of how its set of mutually exclusive admissible continuations is decomposed into orthonormal bases. Therefore the total measure (weight) over any maximal orthonormal decomposition of the identity must be the same:

For every maximal orthonormal resolution of the identity $\{P_i\}_{i \in I}$ ($\sum P_i = I$, $P_i P_j = 0$ for $i \neq j$, each $P_i$ rank-1),

$$\sum_i \mu(P_i) = 1$$

(constant across all such decompositions).

This is the precise formal translation of the requirement that the system possess a determinate total weight independent of representational decomposition.

### A.2 Lemma 1: Transitivity of Maximal Orthonormal Decompositions

**Lemma A.1 (Transitivity of bases under unitary action).** For any two maximal orthonormal decompositions $\{P_i\}$ and $\{Q_j\}$ of the identity, there exists a unitary $U$ on $\mathcal{H}$ such that $\{Q_j\} = \{U P_{\sigma(j)} U^\dagger\}$ for some permutation $\sigma$.

*Proof.* The unitary group $U(\mathcal{H})$ acts transitively on the Grassmannian of ordered orthonormal bases (the Stiefel manifold). Since rank-1 projections are determined by their range (a one-dimensional subspace), any two orthonormal bases are related by a unitary, and hence so are their associated projection decompositions. $\square$

### A.3 Lemma 2: Unitary Implementation of Lattice Automorphisms

**Lemma A.2 (Wigner-Uhlhorn representation theorem).** Every lattice automorphism $\varphi$ of $\mathcal{P}(\mathcal{H})$ that preserves orthogonality is of the form $\varphi(P) = U P U^\dagger$ for some unitary or antiunitary $U$ on $\mathcal{H}$ (unique up to phase).

*Proof.* This follows from Wigner's theorem (1931) as extended by Uhlhorn (1963). The lattice $\mathcal{P}(\mathcal{H})$ determines the underlying Hilbert space up to unitary or antiunitary equivalence, and its orthogonality-preserving automorphism group is precisely the projective unitary-antiunitary group. For the complex case with continuous symmetries relevant here, the antiunitary case can be excluded, leaving $PU(\mathcal{H}) = U(\mathcal{H})/U(1)$. $\square$

### A.4 Lemma 3: Invariance under Unitary Conjugation

**Lemma A.3 (Unitary invariance of $\mu$).** If $\mu$ satisfies Definition A.1, then $\mu(U P U^\dagger) = \mu(P)$ for every unitary $U$ and every projection $P \in \mathcal{P}(\mathcal{H})$.

*Proof.* Fix an arbitrary rank-1 projection $P$. Extend $\{P\}$ to a maximal decomposition $D_1 = \{P, R_2, R_3, \ldots\}$. Then $\sum \mu = \mu(P) + \sum_{k \geq 2} \mu(R_k) = 1$.

Now take any unitary $U$. Let $Q = U P U^\dagger$ (another rank-1 projection). Extend $\{Q\}$ to a maximal decomposition $D_2 = \{Q, S_2, S_3, \ldots\}$ such that the orthogonal complement of $\text{span}\{\text{range}(P), \text{range}(Q)\}$ is the same in both decompositions (possible because $\dim \mathcal{H} \geq 3$).

By transitivity (Lemma A.1), there exists a unitary $V$ such that $D_2 = V D_1 V^\dagger$ up to reordering of the tail. But since $\mu$ is invariant under total weight across decompositions, and the tail can be matched (the codimension-2 difference allows the remaining infinite-dimensional subspace to be isometrically identified in a measure-preserving way), the only consistent assignment is $\mu(Q) = \mu(P)$.

The argument extends to finite-rank projections by finite additivity, and (under mild regularity, e.g., strong continuity) to all projections. $\square$

### A.5 Lemma 4: Unitarily Invariant Measures are Trace-like

**Lemma A.4 (Characterization of unitarily invariant measures).** Any finitely additive probability measure $\mu$ on $\mathcal{P}(\mathcal{H})$ ($\dim \mathcal{H} \geq 3$) that is invariant under unitary conjugation is of the form

$$\mu(P) = \text{Tr}(\rho P)$$

for a unique density operator $\rho \geq 0$ with $\text{Tr}(\rho) = 1$.

*Proof.* Define the sesquilinear form on finite-rank operators by

$$f(A) = \sum \lambda_k \mu(P_k)$$

for $A = \sum \lambda_k P_k$ in spectral form (well-defined by unitary invariance). This extends to a unitarily invariant linear functional on the finite-rank operators.

The conjugation action of $U(\mathcal{H})$ on trace-class operators $\mathcal{B}_1(\mathcal{H})$ is such that the invariant continuous linear functionals are precisely the multiples of the trace (irreducibility of the adjoint representation on the orthogonal complement of multiples of the identity; see Dixmier 1981 or Roberts 1977 for the relevant representation theory).

Normalization $\mu(I) = 1$ and positivity force the constant to be positive and yield a unique density operator $\rho$. For pure states (when $\mu$ vanishes on all projections orthogonal to a fixed one-dimensional subspace), $\rho = |\psi\rangle\langle\psi|$ and

$$\mu(|\phi\rangle\langle\phi|) = |\langle\phi|\psi\rangle|^2$$

(the Born rule). $\square$

### A.6 Conclusion

The chain is complete:

$$\text{Determinate Identity (Def. A.1)} \Rightarrow \text{invariance of total weight over all maximal decompositions}$$
$$\Rightarrow \text{invariance of } \mu \text{ under unitary conjugation (Lemma A.3)}$$
$$\Rightarrow \mu(P) = \text{Tr}(\rho P) \text{ for unique density operator } \rho \text{ (Lemma A.4)}$$
$$\Rightarrow \text{for pure states, } \mu(|\phi\rangle\langle\phi|) = |\langle\phi|\psi\rangle|^2 \text{ (Born rule)}$$

This establishes that the metaphysical demand for determinate physical identity, when imposed on the rich structure of the quantum projection lattice in dimension $\geq 3$, forces the measure over admissible continuations to be given by the Born rule. The argument relies on standard results from quantum logic and representation theory; no circularity is introduced, and no parameters are fitted.

The result holds under finite additivity and the assumption that physical instantiation respects Determinate Identity as an ontological constraint. If stronger regularity (e.g., countable additivity) is imposed, the conclusion is reinforced but not altered. In dimension 2 the argument fails, which is consistent with the known pathology of Gleason's theorem in that case.

---

## Appendix B: Derivation of the Hilbert-Space Arena from Logical Constraints

*Note: This appendix is programmatic. The Born rule derivation in Appendix A assumes Hilbert space structure and stands independently. Appendix B extends the argument by deriving constraints on the arena itself. Readers who accept Hilbert space as given may skip to the References.*

This appendix derives constraints on admissible physical structure, not the existence of structure itself. The aim is to show that complex separable Hilbert space is the unique arena capable of hosting determinate physical identity under unlimited decomposition, composition, and continuous transformation without violating the Three Fundamental Logical Laws (3FLL).

No probabilistic, quantum, or geometric postulates are assumed. The result is conditional:

*Any physical arena that preserves Determinate Identity under infinite refinement and composition must be isomorphic to complex Hilbert space.*

The argument proceeds in four stages:
1. Primitive distinguishability on the pre-ontological arena $I_\infty$
2. Compositional Distinguishability as a requirement of non-relational identity
3. Structural constraints mapped to reconstruction theorems
4. Phase stability and measure invariance as identity-preserving necessities

Conjectural extensions are explicitly labeled.

### B.1 Stage 1: Primitive Distinguishability on $I_\infty$

**Definition B.1 (Pre-ontological arena).** $I_\infty$ is the totality of all distinguishable configurations, constrained only by the Three Fundamental Logical Laws:
- Identity (Id): $\forall x (x = x)$
- Non-Contradiction (NC): $\neg (P(x) \land \neg P(x))$
- Excluded Middle (EM): $P(x) \lor \neg P(x)$

No topology, metric, probability, or algebraic structure is presupposed.

**Lemma B.1 (Irreflexivity of distinguishability).** $\forall c \in I_\infty, \neg D(c,c)$.

*Proof.* If $D(c,c)$, then $c$ differs from itself in some respect, implying both $P(c)$ and $\neg P(c)$ for that respect. This violates NC and contradicts Id. $\square$

**Lemma B.2 (Symmetry of distinguishability).** $D(c,c') \leftrightarrow D(c',c)$.

*Proof.* Difference indexed asymmetrically would make identity orientation-dependent. Identity must be intrinsic, not ordered by comparison. $\square$

**Lemma B.3 (Non-triviality).** $\exists c_1 \neq c_2 \in I_\infty$.

*Proof.* A singleton domain renders EM vacuous and NC untestable. Laws that cannot possibly constrain do not function as laws. Hence the domain must contain at least two distinguishable configurations. $\square$

**Lemma B.4 (Weak separation).** If $c \neq c'$, then $\exists m \in I_\infty$ such that exactly one of $D(c,m)$, $D(c',m)$ holds.

*Proof.* Take $m = c$. By irreflexivity $\neg D(c,m)$; by symmetry and $c \neq c'$, $D(c',m)$. $\square$

**Lemma B.5 (Discrete pseudo-metric).** There exists $\delta : I_\infty \times I_\infty \to \{0,1\}$ such that $\delta(c,c') = 0 \iff c = c'$, $\delta(c,c') = 1 \iff c \neq c'$, and $\delta$ is symmetric.

This is the weakest distance structure compatible with Id and NC.

**Lemma B.6 (At least countable infinity).** $|I_\infty| \geq \aleph_0$.

*Proof.* Let $R_n(x)$ denote "$x \in \{c_0,\dots,c_{n-1}\}$." By EM, either $\forall x\,R_n(x)$ or $\exists x\,\neg R_n(x)$. The former collapses the domain finitely and contradicts Lemma B.3 iteratively. Hence infinite extension is forced. $\square$

**Interim conclusion.** From the 3FLL alone, the pre-ontological arena admits a discrete, infinite, separable structure of distinguishability. No physical geometry has yet been assumed.

### B.2 Stage 2: Compositional Distinguishability Principle (CDP)

To preserve identity under composition, distinctions must localize.

**Definition B.2 (Local factor).** A configuration $m$ is a local factor of $c$ iff there exists a configuration $c'$ such that modifying only the aspect corresponding to $m$ suffices to remove a specific distinction between $c$ and $c'$.

"Local" means identity-preserving under variation elsewhere.

**Lemma B.7 (Compositional Distinguishability Principle).** If $D(c,c')$, then there exist local factors $m$ of $c$ and $n$ of $c'$ such that:
1. $D(m,n)$, and
2. $D(m,n)$ persists under variation of other subsystems.

*Motivation (not proof).* This principle is not derived from Determinate Identity alone. Theorem D.1 (Appendix D) shows that L₁ forces intrinsic identity *somewhere*—but that somewhere could be purely global. The move to *local* intrinsic identity requires empirical input: macroscopic systems exhibit self-sufficient identity under decomposition (M₁, Theorem D.2). CDP is the principled extension of this macroscopic self-sufficiency into the compositional regime, motivated by the pattern that self-sufficiency percolates downward as far as decoherence allows. See Appendix D.3 for the complete derivation chain.

**Corollary B.7.1 (Local tomography).** If CDP holds, then two global configurations that agree on all local factors of all subsystems are identical.

**Corollary B.7.2 (Subsystem independence).** If CDP holds, then local distinctions, once established, persist independently of unrelated subsystems.

These corollaries are consequences of accepting CDP; they inherit its motivated (rather than derived) status.

**Lemma B.8 (Infinite local depth).** For any configuration $c$, there exists an infinite descending chain of proper local factors.

*Proof.* Finite termination implies atomic identity. Atomicity blocks further refinement and collapses maximal permissiveness. This contradicts both $I_\infty$'s construction and CDP. $\square$

### B.3 Stage 3: Structural Constraints and Reconstruction

At this stage the structure satisfies:
- local tomography,
- subsystem independence,
- infinite refinement,
- compositional stability of identity.

These constraints align exactly with the non-probabilistic axioms used in operational reconstruction theorems.

**Lemma B.9 (Restricted reconstruction).** Any linear theory satisfying the above constraints must be representable on a Hilbert space over $\mathbb{R}$, $\mathbb{C}$, or $\mathbb{H}$.

This follows from standard reconstruction results (Hardy 2001; Chiribella et al. 2011; Masanes and Müller 2011).

**Lemma B.10 (Exclusion of real Hilbert space).** Real Hilbert space fails compositional discernibility: local tomography breaks for composite systems, making identity context-dependent.

*Elaboration.* Local tomography requires that the state of a composite system be fully determined by the statistics of local measurements on each subsystem. In real Hilbert space, this fails. Consider a two-qubit system in real Hilbert space. The transpose operation $T$ acts trivially on local density matrices (since $\rho^T$ has the same eigenvalues as $\rho$), but non-trivially on certain entangled states. This means two globally distinct states can be locally indistinguishable; their identity depends on global context rather than local facts.

Concretely: the real-valued state $|\psi\rangle = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$ and its "transpose" have identical local reduced density matrices but are globally distinguishable. The distinction between them cannot be witnessed locally. This violates CDP: what the global configuration *is* cannot be determined from what its local factors *are*.

This is not merely an epistemic limitation; it is a failure of intrinsic identity. If a configuration's identity depends constitutively on context rather than local facts, then identity is relational rather than intrinsic. Real Hilbert space thus violates Determinate Identity under composition.

**Lemma B.11 (Exclusion of quaternionic Hilbert space).** Quaternionic composition is non-commutative, making equivalence classes order-dependent. Identity under re-association fails.

*Elaboration.* Quaternionic Hilbert spaces have a richer structure than complex spaces due to the non-commutativity of quaternion multiplication. When composing subsystems, the order of composition matters: $\mathcal{H}_A \otimes \mathcal{H}_B$ is not canonically isomorphic to $\mathcal{H}_B \otimes \mathcal{H}_A$ in the quaternionic case.

This creates a problem for identity. Consider three subsystems A, B, C. The composite $(A \otimes B) \otimes C$ and $A \otimes (B \otimes C)$ are not canonically equivalent; their identification requires a choice of association. But Determinate Identity requires that what a system *is* be independent of how we choose to describe its composition. If the identity of ABC depends on whether we first compose A with B or B with C, then identity is representation-dependent.

Furthermore, quaternionic quantum mechanics lacks a consistent tensor product structure that preserves the quaternionic linearity of both factors. Physical composition of quaternionic systems forces a reduction to complex structure. The quaternionic option is thus not merely inconvenient; it is structurally incompatible with identity-preserving composition.

**Interim conclusion.** Complex Hilbert space is the only arena compatible with infinite refinement, local tomography, and identity-preserving composition.

### B.4 Phase Stability as an Identity Constraint

Complex phase is not optional structure. It is the minimal freedom required for continuous reversible transformations that preserve identity under composition.

**Lemma B.12 (Phase-stability requirement).** In a theory admitting continuous reversible transformations on pure states, preservation of identity under composition requires a continuous symmetry group whose action remains locally tomographic.

Real Hilbert space admits continuous rotations, but these fail to compose tomographically. Quaternionic space fails associativity. Only complex phase supports both.

Thus phase is forced not by continuity alone, but by identity-preserving continuity under composition.

### B.5 Measure Invariance and the Born Rule (Constraint, Not Postulate)

**Lemma B.13 (Conservation of admissibility weight).** For any system, the total admissibility weight assigned to a complete set of mutually exclusive outcomes must be invariant under choice of decomposition.

*Ground:* If total weight varies with basis, the system's "amount of being" becomes representation-relative, violating Determinate Identity.

This forces:
- additivity on exclusive outcomes,
- non-contextuality of weights.

Under standard regularity assumptions, Gleason's theorem (and Busch's extension) implies:

$$w(P) = \langle \psi | P | \psi \rangle$$

The Born Rule is thus the unique identity-preserving measure over admissible histories.

### B.6 Conjectural Extension: Identity Gradient and Dynamics

**Conjecture B.1 (Least-identity-strain principle).** Among all admissible continuations, realized histories minimize approach to joint-inadmissibility boundaries in configuration space.

This conjecture, if formalized, would recover variational principles (e.g., stationary action) as macroscopic shadows of NC.

This step is not required for the Born-rule result and remains testable future work.

### B.7 Conclusion of Appendix B

Complex separable Hilbert space is not assumed. It is forced as the only stable arena that prevents violation of the Three Fundamental Logical Laws under infinite decomposition and composition.

**Assessment of rigor.** The argument in this appendix has varying degrees of rigor across its stages:

- *Stage 1 (B.1):* The derivation of primitive distinguishability structure from the 3FLL is rigorous, though elementary.
- *Stage 2 (B.2):* The Compositional Distinguishability Principle is motivated but not derived from 3FLL alone. Appendix D provides the precise analysis: Theorem D.1 shows L₁ forces intrinsic identity *somewhere* (possibly only global); Theorem D.2 shows that macroscopic self-sufficiency (M₁) is a transcendental precondition of stable measurement records. CDP is the motivated extension of M₁ into the compositional regime.
- *Stage 3 (B.3):* The connection to reconstruction theorems is genuine but indirect. The operational axioms used by Hardy, Chiribella et al., and Masanes-Müller are not identical to CDP, though they overlap significantly. A fully rigorous derivation would require showing that CDP entails the relevant operational axioms, which is not done here.
- *Lemmas B.10-B.11:* The exclusion arguments are substantive but rely on known results from quantum information theory rather than being derived from first principles.

The appendix is thus best understood as a *research program* showing how complex Hilbert space *could* be forced by identity constraints, not as a completed proof. The full derivation of complex Hilbert space from L₃ alone remains open; the present argument shows only that no weaker structure is known to satisfy the required identity constraints. The Born rule derivation in Appendix A does not depend on this appendix and stands independently. Appendix D provides the formal chain clarifying exactly where logical constraints end and empirical/transcendental inputs begin.

Rejecting this conclusion requires rejecting at least one of:
- Determinate Identity as intrinsic,
- decomposition-invariant admissibility weight,
- local tomography,
- or compositional stability.

The metaphysical price is explicit. The chain is acyclic. The argument is falsifiable, but its full rigorization remains open work.

---

## Appendix C: Bell Non-Locality as a Constraint on Global Identity

This appendix applies the admissibility framework to Bell-type correlations. The central claim is not that quantum theory violates locality, but that local factorization of identity fails once Determinate Identity, outcome definiteness, and compositional admissibility are jointly enforced.

Bell's theorem is recast as a no-go result for locally factorizable identity, not a proof of superluminal causation.

### C.1 What Bell Actually Rules Out

Consider a standard Bell scenario with spacelike-separated measurement regions A and B, settings $a$, $b$, and outcomes $x$, $y$.

Bell-type inequalities follow from three assumptions:

1. **Outcome definiteness:** Each measurement yields a determinate outcome.
2. **Local factorization:** $P(x,y|a,b,\lambda) = P(x|a,\lambda) \cdot P(y|b,\lambda)$ where $\lambda$ is a complete specification of prior state.
3. **Measurement independence:** $\lambda$ is statistically independent of $a$, $b$.

Quantum mechanics violates Bell inequalities. Therefore, at least one assumption must fail.

Standard narratives pick: locality (non-local influence), or realism (outcomes not determinate), or measurement independence.

The admissibility framework offers a fourth option: *local factorization is not compatible with determinate identity under composition.*

### C.2 Identity, Not Influence, Is the Point of Failure

From Appendix B, two constraints are already fixed:
- Outcome definiteness is enforced by NC and EM at the level of macroscopic records.
- Determinacy of identity requires that admissible configurations be globally self-consistent under composition.

The Bell factorization condition implicitly assumes:

*Global identity is reducible to a product of independently individuated local identities.*

This assumption is stronger than locality and is not guaranteed by the 3FLL.

### C.3 Entangled Systems and Failure of Local Individuation

Consider an entangled pair prepared in a singlet state. Prior to measurement:
- The composite system has determinate global identity.
- No determinate local spin values exist.

After measurement:
- Each wing records a determinate local outcome.
- The pair of outcomes satisfies strict global constraints.

From the admissibility perspective:
- The global configuration is admissible.
- Certain local assignments, taken independently, are inadmissible because they cannot be jointly embedded into a single identity-preserving global configuration.

Thus the failure is not "spooky action," but *local identity underdetermination*.

### C.4 Bell Inequalities as a Test of Local CDP

Recall CDP from Appendix B: every global distinction must admit a local, context-independent witness.

Bell violations show that this fails if "local" is interpreted as spacetime-localized subsystem with independent identity.

More precisely:
- There exist global distinctions (correlation patterns) that do not decompose into independent local distinctions without violating identity constraints.
- The admissible witness is global, not local.

Bell's theorem therefore demonstrates:

*CDP cannot be simultaneously satisfied with local factorization.*

But CDP was not an arbitrary add-on. It was required to preserve Determinate Identity under composition.

Thus Bell forces a choice: abandon Determinate Identity, or abandon local factorization of identity.

Quantum mechanics chooses the latter.

### C.5 Why This Is Not Superluminal Causation

No signal, influence, or parameter travels between A and B.

What changes is the set of admissible global continuations once outcomes are instantiated.

Each local outcome is:
- determinate,
- locally recorded,
- uncontrollable by the distant setting.

But which pairs of local outcomes are jointly admissible is globally constrained.

This is analogous to a consistency condition, not a causal interaction.

### C.6 Relation to Parameter Independence and Outcome Independence

In standard terminology (following Bell 1976 and Jarrett 1984):
- Parameter independence holds (no signaling).
- Outcome independence fails.

In admissibility language:
- Local records are admissible.
- Certain combinations of local records are globally inadmissible.

Outcome independence presupposes local factorization of identity. Once that assumption is dropped, Bell violations are expected rather than paradoxical.

### C.7 Bell as a Theorem About Global Identity

Bell's theorem can be restated as:

*No theory can simultaneously satisfy:*
1. *determinate outcomes,*
2. *decomposition-invariant identity,*
3. *local factorization of identity,*
4. *empirical adequacy.*

Quantum theory preserves (1), (2), and (4) by rejecting (3).

In this sense, Bell inequalities are experimental probes of identity structure, not of spacetime causation.

### C.8 Consequence for the Hilbert-Space Arena

The necessity of complex Hilbert space from Appendix B now acquires physical bite:
- Complex structure allows globally constrained admissible amplitudes.
- The Born measure counts admissible global histories.
- Entanglement encodes non-factorizable identity constraints.

Bell violations are therefore not surprises layered on top of Hilbert space. They are direct manifestations of the same identity-preserving structure that forced Hilbert space in the first place.

### C.9 Summary

- Bell inequalities fail because local identity does not factorize, not because locality fails.
- The admissibility framework predicts this once Determinate Identity is taken seriously.
- Quantum non-locality is global identity coherence, not superluminal causation.

Rejecting this interpretation requires rejecting that identity is intrinsic and globally constrained. That is the metaphysical cost.

---

## References

### Logic and Metaphysics

Bell, J. S. (1964). On the Einstein Podolsky Rosen Paradox. *Physics Physique Fizika*, 1(3), 195–200.

Bell, J. S. (1976). The Theory of Local Beables. *Epistemological Letters*, 9, 11–24.

Jarrett, J. P. (1984). On the Physical Significance of the Locality Conditions in the Bell Arguments. *Noûs*, 18(4), 569–589.

Priest, G. (2006). *In Contradiction: A Study of the Transconsistent*. Oxford University Press.

Tahko, T. E. (2009). The Law of Non-Contradiction as a Metaphysical Principle. *Australasian Journal of Logic*, 7, 32–47.

Tahko, T. E. (2021). *Unity of Science*. Cambridge University Press.

Uhlhorn, U. (1963). Representation of Symmetry Transformations in Quantum Mechanics. *Arkiv för Fysik*, 23, 307–340.

Wigner, E. P. (1931). *Gruppentheorie und ihre Anwendung auf die Quantenmechanik der Atomspektren*. Vieweg.

### Quantum Foundations

Busch, P. (2003). Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem. *Physical Review Letters*, 91(12), 120403.

Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). Informational Derivation of Quantum Theory. *Physical Review A*, 84(1), 012311.

Dixmier, J. (1981). *Von Neumann Algebras*. North-Holland.

Gleason, A. M. (1957). Measures on the Closed Subspaces of a Hilbert Space. *Journal of Mathematics and Mechanics*, 6(6), 885–893.

Hardy, L. (2001). Quantum Theory from Five Reasonable Axioms. *arXiv:quant-ph/0101012*.

Masanes, L. and Müller, M. P. (2011). A Derivation of Quantum Theory from Physical Requirements. *New Journal of Physics*, 13(6), 063001.

Pitowsky, I. (1998). Infinite and Finite Gleason's Theorems and the Logic of Indeterminacy. *Journal of Mathematical Physics*, 39(1), 218–228.

Roberts, J. E. (1977). Mathematical Aspects of Local Cohomology. In *Algèbres d'opérateurs et leurs applications en physique mathématique* (pp. 287–302). CNRS.

Solèr, M. P. (1995). Characterization of Hilbert Spaces by Orthomodular Spaces. *Communications in Algebra*, 23(1), 219–243.

Varadarajan, V. S. (1968). *Geometry of Quantum Theory*, Vol. 1. Van Nostrand.

Wallace, D. (2012). *The Emergent Multiverse: Quantum Theory according to the Everett Interpretation*. Oxford University Press.

Zurek, W. H. (2003). Decoherence, Einselection, and the Quantum Origins of the Classical. *Reviews of Modern Physics*, 75(3), 715–775.

---

## Appendix D: Formal Strengthening of the Derivation Chain

This appendix provides formal theorems establishing the derivation chain from Determinate Identity through macroscopic self-sufficiency to the Born rule. The chain clarifies exactly where logical constraints end and empirical/transcendental inputs begin.

### D.1 Theorem: Necessity of Intrinsic Identity Terminus

**Definition D.1 (Purely relational identity).** A configuration $c$ has purely relational identity iff there exists a set $R_c$ of other configurations $\{d_1, d_2, \ldots\}$ and relations $\{\rho_1, \rho_2, \ldots\}$ such that $c$ is defined as the unique object satisfying $\forall i: \rho_i(c, d_i)$.

**Definition D.2 (Vicious relational structure).** A domain of configurations has a vicious relational structure iff every configuration has purely relational identity.

**Theorem D.1 (Grounding of intrinsic identity).** If Determinate Identity holds non-vacuously for all configurations in a domain, then the domain cannot have a vicious relational structure.

*Proof.* Assume for contradiction that the domain has a vicious relational structure.

Consider arbitrary $c$. By assumption, $c$'s identity is constituted by relations to configurations $\{d_1, d_2, \ldots\}$.

Apply Determinate Identity to $c$: $c$ is determinately $c$. But the right-hand side is well-defined only if each $d_i$ is itself determinately what it is (otherwise the relations $\rho_i$ cannot be meaningfully evaluated).

By the vicious assumption, each $d_i$ also has purely relational identity, so each $d_i$ depends on further configurations, and so on.

Three exhaustive cases arise:

*Case 1: Infinite descending chain (vicious regress).* There is no finite stage at which any configuration becomes determinate. But Determinate Identity requires that $c$ is determinate now. Contradiction.

*Case 2: Finite cycle (vicious circularity).* Suppose the chain closes: $c$ depends on $d_1$, $d_1$ on $d_2$, ..., $d_k$ on $c$. Then "$c = c$" is satisfied trivially by any $c$ fitting the cycle (tautological self-consistency). Determinate Identity becomes vacuously true but fails to be substantive. Contradiction to non-vacuity.

*Case 3: Global holism.* The entire domain is a single global relational fact with no proper parts having independent identity. The only locus of determinacy is the global whole $G$. Determinate Identity holds globally ($G$ is determinately $G$), but no local configuration $c \subset G$ has determinate identity independent of $G$. This case is not contradictory to Determinate Identity itself, but it is the only remaining possibility.

Therefore: either there exists at least one configuration with intrinsic (non-relational) identity, or the only determinate identity is global/holistic. $\square$

**Remark.** Theorem D.1 shows Determinate Identity forces intrinsic identity *somewhere*. It does not yet force *local* intrinsic identity for subsystems. That requires empirical input.

### D.2 Transcendental Precondition: Macroscopic Self-Sufficiency

**Definition D.2.1 (Stable macroscopic measurement record).** A macroscopic measurement record $R$ is stable iff:
1. $R$ is in one definite macroscopic configuration at time $t$ (pointer position, ink pattern, etc.),
2. The identity of $R$ persists through time ($R$ at $t + \Delta t$ is determinately the same record as $R$ at $t$),
3. The identity of $R$ is independent of the state of any other macroscopic system at arbitrary distance.

**Theorem D.2 (Transcendental necessity of macroscopic self-sufficiency).** If there exist stable macroscopic measurement records, then macroscopic identity is self-sufficient under decomposition and persistence.

*Proof.* Assume there exists at least one stable macroscopic measurement record $R$.

Suppose for contradiction that the identity of $R$ is not self-sufficient (i.e., $R$'s identity is relational with respect to some other macroscopic system $S$, possibly at arbitrary distance).

Then there exists some change in $S$ (or potential change in $S$) such that $R$ ceases to be determinately the same record. But then $R$ is not stable (condition 3 fails). Contradiction.

Hence the identity of every stable macroscopic record must be self-sufficient. Since macroscopic records are composed of macroscopic subsystems (pointers, dials, paper, etc.), macroscopic identity is self-sufficient under decomposition and persistence. $\square$

**Remark.** The antecedent is empirical: we possess such records. The consequent is therefore a transcendental precondition of empirical science. We denote this as **M₁**: Macroscopic identity is self-sufficient under decomposition and persistence.

### D.3 The Derivation Chain

The complete chain from logical floor to Born rule:

1. **Proto-distinguishability** (unavoidable): The registering of difference that any determinate thought presupposes.

2. **Determinate Identity (L₁)**: The first well-formed constraint. From L₁ alone, purely relational identity makes L₁ vacuous (Theorem D.1). Forces some intrinsic identity terminus somewhere.

3. **Macroscopic self-sufficiency (M₁)**: Empirical/transcendental input. Stable records exist (empirical). Therefore macroscopic identity is self-sufficient (Theorem D.2).

4. **Compositional Distinguishability Principle (CDP)**: Motivated extension of M₁. If macroscopic identity is self-sufficient, the natural hypothesis is that self-sufficiency percolates downward as far as decoherence allows. CDP is not derived from L₁ alone; it is the principled extension of macroscopic self-sufficiency into the compositional regime.

5. **Quantum mechanics as arena**: Complex Hilbert space is the mathematically cleanest structure that satisfies global intrinsic identity (the total state is determinately itself), allows local self-sufficiency after decoherence, and refuses local self-sufficiency before decoherence.

6. **Vehicle-weight invariance**: The measure over admissible macroscopic continuations belongs to the physical vehicle. If it varied with decomposition, the physical situation would not be determinately poised toward any distribution of outcomes, violating L₁ at the vehicle level.

7. **Born rule**: Vehicle-weight invariance implies additivity and non-contextuality. Gleason's theorem (Busch finite-additivity version) yields the Born rule as the unique such measure in dimension $\geq 3$.

### D.4 Vehicle-Weight Invariance → Born Rule

**Definition D.4.1 (Vehicle-weight invariance).** A physical situation in state $|\psi\rangle$ is determinately what it is (L₁ at vehicle level) only if the total weight it assigns to any complete set of mutually exclusive admissible continuations is independent of the mathematical decomposition chosen to represent that situation.

Formally: for every maximal orthonormal resolution of the identity $\{P_i\}$ ($\sum P_i = I$, orthogonal, rank-1),
$$\sum_i \mu(P_i) = 1 \text{ (constant across all decompositions)}$$

**Theorem D.4 (Vehicle-invariance implies Born rule).** Any finitely additive measure $\mu$ on $\mathcal{P}(\mathcal{H})$ ($\dim \mathcal{H} \geq 3$) satisfying vehicle-weight invariance is of the form $\mu(P) = \text{Tr}(\rho P)$ for a unique density operator $\rho$. For pure states, this yields the Born rule: $\mu(|\phi\rangle\langle\phi|) = |\langle\phi|\psi\rangle|^2$.

*Proof sketch.*

1. Vehicle-weight invariance implies $\mu$ is constant (=1) over every maximal orthonormal decomposition of $I$.

2. By transitivity of orthonormal bases under unitary action, any two maximal decompositions are related by some unitary $U$.

3. Therefore $\mu$ is invariant under arbitrary unitary conjugation: $\mu(UPU^\dagger) = \mu(P)$.

4. Any finitely additive probability measure on $\mathcal{P}(\mathcal{H})$ ($\dim \geq 3$) that is invariant under unitary conjugation must be of trace form: $\mu(P) = \text{Tr}(\rho P)$ for unique density $\rho \geq 0$, $\text{Tr}(\rho) = 1$. (This follows from representation theory: the adjoint representation of $U(\mathcal{H})$ on trace-class operators is irreducible on the orthogonal complement of multiples of $I$.)

5. For pure states ($\rho = |\psi\rangle\langle\psi|$), we recover the Born rule on rank-1 projectors. $\square$

**Circularity audit.** No premise contains the conclusion (Born rule). Unitary invariance is derived from vehicle-weight invariance plus standard Hilbert-space geometry. Gleason/Busch uniqueness is a theorem, not an assumption. The only non-logical inputs are $\dim \mathcal{H} \geq 3$ (empirically motivated) and the decoherence-selected pointer basis.

### D.5 Summary

The derivation is not purely a priori. It rests on:
- The unavoidable logical floor (L₁)
- The empirical/transcendental deliverance of macroscopic self-sufficiency (M₁)

Everything else follows with high internal consistency. No deeper non-vacuous foundation appears available. If someone claims one, ask them to speak a single determinate sentence about physical instantiation without implicitly relying on something at least as strong as L₁.
