# Logic Realism Theory: Grounding Reality as Logical, Informational, and Dynamic

**Author:** James D. Longmire
**Affiliation:** Northrop Grumman Fellow (unaffiliated research)
**ORCID:** 0009-0009-1383-7698
**Correspondence:** jdlongmire@outlook.com
**Date:** March 2026
**Status:** Publishable Draft
**Epistemic Discipline:** Each claim marked ESTABLISHED, ARGUED, or OPEN

**Notation note:** In prose, symbols appear as L₃, I∞, A_Ω, and X. In display and inline math blocks, the equivalent LaTeX forms are used: $L_3$, $I_\infty$, $A_\Omega$. On conversion to LaTeX or Word, all prose symbol instances convert to their math equivalents.

-----

Logic Realism Theory (LRT) proposes a single ground-level commitment: reality is logical, informational, and dynamic. Expressed formally as the primitive ontic state X ≡ [L₃ : I∞ : A], this commitment grounds a candidate derivation architecture for the full structure of non-relativistic quantum mechanics – complex Hilbert space, projection-valued measures, the Born rule, continuous time, and the Schrödinger equation – through a thirteen-step chain in which each step is explicitly marked by epistemic status: ESTABLISHED where peer-reviewed mathematics is imported, ARGUED where LRT-specific grounding arguments are defended, and OPEN where further work is identified.

LRT is not a competitor to prior interpretations in the usual sense. It inherits the determinacy of Copenhagen outcomes, the unitary structure of Everett without branch multiplication, the realism of Bohmian mechanics without the pilot wave, and the derivation methodology of operational reconstructions while grounding their axioms rather than postulating them. Each inheritance is specific and bounded within the quantum mechanical domain.

The central methodological claim is that the Three Fundamental Laws of Logic (L₃) are not constraints on reasoning about reality but constitutive conditions on what counts as a physical fact. Any proposition lacking operational distinguishability does not merely escape our access – it is not a physical proposition at all. This framing dissolves several standing problems in quantum foundations by relocating them: they are not puzzles about measurement or interpretation but consequences of what logical constraint on instantiation requires. Five steps in the derivation chain remain ARGUED rather than formally verified; Lean 4 formalization of those steps is the primary remaining technical agenda.

-----

## 1. The Ground-Level Commitment

### 1.1 What LRT Proposes

Logic Realism Theory begins with a commitment that is minimal but not empty: reality is logical, informational, and dynamic.

These three terms are not metaphors. Each picks out a distinct primitive aspect of what it means for anything to be real:

*Logical* means that the Three Fundamental Laws of Logic – Identity, Non-Contradiction, and Excluded Middle – are not rules governing how we reason about reality. They are constitutive conditions on what counts as a physical fact. A configuration that violates them is not a strange or impossible thing; it is not a thing at all.

*Informational* means that the domain of possible configurations is unbounded and structured by distinguishability. Any two configurations that differ in some respect are distinct. There is no upper bound on the space of representable distinctions.

*Dynamic* means that actuality is not static. There is a primitive binary operation – actual versus non-actual – that selects, from the informational domain, what is instantiated. This selection is not a one-time event but an ongoing process constituting the structure of actuality itself.

These three aspects are co-constitutive. None can exist without the others. Logic without information has nothing to constrain. Information without logic has no admissibility structure. Logic and information without the dynamic primitive produce no actuality – only a space of possibilities with no fact of the matter about what obtains.

### 1.2 The Formal Expression

The ground-level commitment is expressed formally as:

$$\mathbf{X} \equiv [L_3 : I_\infty : \mathbf{A}]$$

where:

|Symbol|Name                           |Role                                                               |
|------|-------------------------------|-------------------------------------------------------------------|
|L₃    |Three Fundamental Laws of Logic|Admissibility filter (Identity, Non-Contradiction, Excluded Middle)|
|I∞    |Infinite Information Space     |All representable configurations; structured by distinguishability |
|A     |Continuous Binary Action       |Instantiation primitive: actual vs. non-actual                     |

X is the primitive ontic state. It is the terminus of grounding chains – there is no ground for X, because any ground would itself require logical, informational, and dynamic structure to be statable. X is not derived; it is what any coherent account of reality already presupposes.

The co-constitutive notation [L₃ : I∞ : A] is deliberate. The colon is not conjunction. It marks mutual constitution: each aspect is what it is only in relation to the others. L₃ constrains the configurations of I∞; I∞ provides the domain that L₃ filters; A selects from the filtered domain what is actual. Remove any one aspect and the others collapse.

The core equation of LRT follows immediately:

$$A_\Omega = L_3(I_\infty)$$

where $A_\Omega$ is the actualized domain – the set of all configurations in $I_\infty$ that satisfy $L_3$. Actualization is inclusion, not creation: $A_\Omega \subseteq I_\infty$. X grounds this equation; the equation expresses what X produces. X answers *why* actuality obtains; $A_\Omega = L_3(I_\infty)$ answers *what* actuality is. The relationship between them is grounding, not causation.

### 1.3 The Status of L₃

The Three Fundamental Laws of Logic are not axioms of LRT in the ordinary sense – they are not propositions stipulated as true for the purposes of the theory. They are transcendentally necessary: any attempt to deny them already deploys them.

To assert “Non-Contradiction does not hold” requires using Identity (the assertion is what it is) and Excluded Middle (either it holds or it doesn’t). The negation is not false; it is unrealizable. This is not a rhetorical observation. It is a structural feature of L₃’s status as the framing condition for any coherent discourse about physical reality. The independence of logical laws from mind and language – their status as features of reality rather than conventions of reasoning – is a central theme in the logical realism literature; Tahko (2019) provides the most thorough recent survey of the position LRT presupposes here.

This transcendental status has a direct consequence for what counts as a physical proposition. A proposition P about a configuration is subject to L₃ – Identity, Non-Contradiction, Excluded Middle – or it is not a proposition about a physical configuration at all. For P to satisfy Identity, it must have determinate content: there must be something that P asserts. For P to satisfy Non-Contradiction, P-true and P-false must be distinct states of affairs. For P to satisfy Excluded Middle, there must be a determinate truth value. All three requirements entail operational distinguishability: without a possible measurement distinguishing P-true from P-false, there is no determinate content, no distinction, no truth value.

This inference is the governing bridge principle of the entire derivation chain. It is stated here explicitly as the **Physical Proposition Criterion (PPC):**

> *A claim Q counts as a physical proposition if and only if Q satisfies L₃. Satisfying L₃ requires that Q-true and Q-false are operationally distinguishable by some idealized physical interaction. Any claim lacking this operational signature is not a physical proposition – it is not a claim about a configuration in A_Ω at all.*

The PPC licenses every subsequent move from ontological condition to physical structure in the derivation chain. At Step 3, the PPC entails that all identity-making relations in a composite system must be operationally distinguishable, yielding local tomography. At Step 5, the PPC entails that event operators must have Boolean spectra, yielding PVM structure. At Step 8, the PPC entails that succession relations must be determinate, yielding the Unique Next State theorem. The PPC is not a new axiom introduced alongside X; it is a consequence of taking L₃’s constitutive status seriously as stated in the opening of this section. Its scope is all physical propositions; its failure condition is a physically real claim that satisfies L₃ but lacks any operational signature – which LRT holds to be unrealizable rather than merely unobserved.

*[Epistemic status of the PPC: ARGUED. The inference from “L₃ requires determinate content and distinct truth-value states” to “there must be a possible measurement distinguishing P-true from P-false” rests on the identification of distinct physical states of affairs with operationally distinguishable configurations. This identification is defensible but not logically compelled; a critic who holds that physical reality outstrips all possible operational access has a coherent position that LRT contests rather than refutes.]*

A proposition with no operational signature does not merely escape our access. It fails to satisfy L₃. It is not a physical proposition. It is a nothing – by the same reasoning that contradictions are no-thing in LRT.

This framing is not operationalism by stipulation. It is a consequence of taking L₃ seriously as a constitutive condition on physical facts rather than as a filter applied to propositions that are already formed.

A clarification on non-classical logics is warranted here. Paraconsistent logical systems formally reject Non-Contradiction; intuitionistic systems reject Excluded Middle. LRT does not claim these systems are formally incoherent – they are well-defined formal structures. The claim is narrower: such systems cannot be directly interpreted as describing physical configurations under LRT’s operational criterion. A physical configuration that violates Non-Contradiction has no determinate identity – there is no measurement that could distinguish it from its negation, and therefore no fact of the matter about what it is. It is not a strange kind of physical thing; it is not a physical thing at all. Non-classical logics may govern reasoning about incomplete information, counterfactual domains, or formal systems. They do not govern the structure of physical instantiation, which is what L₃ constrains in LRT.

### 1.4 Positioning Within the Landscape

LRT inherits specific gains from prior interpretations while avoiding their characteristic weaknesses. Each inheritance is bounded and stated precisely. The following table summarizes the position; the paragraphs below develop each entry.

|Source                          |Inherited                                   |Avoided                                             |
|--------------------------------|--------------------------------------------|----------------------------------------------------|
|Copenhagen                      |Boolean, determinate outcomes               |Observer-dependence; primitive measurement postulate|
|Everett                         |Unitary structure; branching geometry in I∞ |Branch multiplication; preferred basis problem      |
|Bohmian                         |Realism about state and outcomes            |Pilot wave; primitive nonlocality; preferred basis  |
|Reconstructions (Hardy; MM; CDP)|Derivation methodology; mathematical results|Ungrounded axioms                                   |
|Ontic structural realism        |Structural reading of physical identity     |Elimination of configurations                       |

From the Copenhagen interpretation, LRT inherits the insistence that measurement outcomes are Boolean and determinate. It grounds this in the action primitive A rather than leaving it as a postulate about observers or measurement contexts. The measurement problem does not arise in LRT because actualization is not a physical process requiring explanation – it is the primitive dynamic aspect of X itself. A brief pointer: the question of why unitary dynamics yields exactly one Boolean outcome per measurement event is addressed via the interface structure and the Born rule derivation in Sections 4 and 6.

From Everett’s relative-state formulation, LRT inherits the unitary structure and the branching geometry of the quantum state space. Branches exist in I∞ as representable configurations. But only one L₃-admissible outcome history is ever instantiated in A_Ω. This is one-world realism with Everettian mathematical structure – the branching without the ontological multiplication.

From Bohmian mechanics, LRT inherits realism about the quantum state and about outcomes. The quantum state is not a summary of knowledge; it is a structural feature of I∞. Outcomes are not relative to observers; they are determinate instantiations in A_Ω. But LRT requires no pilot wave, no preferred basis, and no nonlocality as a primitive.

From the operational reconstruction programs of Hardy (2001), Masanes and Müller (2011), and Chiribella, D’Ariano, and Perinotti (2011), LRT inherits the derivation methodology and imports their mathematical results directly. The difference is that LRT grounds the axioms of these programs in X rather than leaving them as operationally motivated postulates. LRT answers the question these programs leave open: why do the reconstruction axioms hold?

From ontic structural realism, LRT inherits the structural reading of physical identity. The identity of a configuration is constituted by its position in the distinguishability structure of I∞, not by primitive haecceity. But LRT does not eliminate the configurations themselves – the structure is real, and so are the states it distinguishes.

These inheritances are within the quantum mechanical domain. Extensions to cosmology, relativistic field theory, and quantum gravity remain open and are not claimed here.

### 1.5 Scope and Structure of This Paper

This paper presents the complete derivation chain from X to the Schrödinger equation and develops its consequences for quantum foundations. Each step in the derivation is marked with one of three epistemic statuses:

- **ESTABLISHED:** Definitionally immediate, or imported from peer-reviewed mathematics with explicit citation.
- **ARGUED:** Defended with explicit reasoning; not yet formally machine-verified.
- **OPEN:** Identified as requiring further work; not used as a premise in subsequent steps.

No step is presented as more secure than its status warrants. A distinction between what LRT originates and what it imports is maintained throughout. The mathematical results of Masanes and Müller (2011), Gleason (1957), Stone (1930), Debreu (1954), and Nachbin (1965) are imported with citation. LRT’s original contribution is the grounding argument: showing that the inputs these theorems require follow from X rather than standing as independent postulates. Steps marked ARGUED are where that original contribution lives. Lean 4 formalization of the argued steps is identified as the primary remaining work.

The paper is structured as follows. Section 2 develops the move from X to actuality: transcendental constitution, the core equation A_Ω = L₃(I∞), and Determinate Identity. Section 3 derives the structure of quantum theory: local tomography via the logical framing of L₃, complex Hilbert space via Masanes-Müller, and projection-valued measure structure via the eigenvalue restriction argument. Section 4 derives the Born rule via Gleason’s theorem applied to the PVM structure established in Section 3. Section 5 derives time and dynamics: the Unique Next State theorem, ordinal time, continuous time via Debreu-Nachbin, G-equivariance, Stone’s theorem, and the Schrödinger equation.

Section 6 addresses the resolution of standing problems in quantum foundations – the measurement problem, wave-particle duality, EPR and nonlocality, Schrödinger’s cat, the preferred basis problem, and the role of the observer – showing in each case that LRT dissolves rather than merely reinterprets the problem. Section 7 compares LRT systematically against the major interpretive positions: Copenhagen, Many-Worlds, Bohmian mechanics, GRW, Relational QM, and operational reconstruction programs. Section 8 addresses scientific status: Popperian falsifiability, the Lakatosian research program structure, the null hypothesis as standard QM, and the falsification hierarchy from categorical to empirical. Section 9 identifies open problems. Section 10 concludes. An appendix maps standard QM primitives to their LRT derivation origins for readers approaching from the physics side.

-----

## 2. From X to Actuality

### 2.1 Transcendental Constitution

**Claim:** X grounds A_Ω. *[Epistemic status: ESTABLISHED within LRT, given the grounding framework below.]*

X is the primitive ontic state. It does not cause A_Ω, nor does it precede A_Ω in time. The relationship is grounding in the sense of Fine (2012) and Schaffer (2009): A_Ω obtains *in virtue of* X. X is ontologically prior; A_Ω is what X produces at the level of actuality.

This is expressed formally as:

$$\mathbf{X} \vdash A_\Omega$$

Read: X transcendentally constitutes A_Ω. Three conditions hold. X is ontologically prior to A_Ω. A_Ω obtains in virtue of X. The grounding relation is non-causal and non-temporal.

Why transcendental rather than merely logical or causal? Because X is the condition under which any physical structure is possible at all. Any attempt to ask what grounds X already presupposes logical, informational, and dynamic structure – which is X. The grounding chain terminates at X not by stipulation but because no coherent question about X’s ground can be formed without X already being in play.

### 2.2 The Core Equation

From transcendental constitution, the core equation follows:

$$A_\Omega = L_3(I_\infty)$$

A_Ω is the actualized domain – the set of all configurations in I∞ that satisfy L₃. L₃ acts as an admissibility filter: configurations that violate Identity, Non-Contradiction, or Excluded Middle are not excluded from I∞ by an external rule. They are no-things. A contradiction is not a configuration that fails to be instantiated; it is the absence of any configuration at all. To be precise: configurations violating L₃ are formally representable in I∞ as surrogates – they can be written down – but they cannot be instantiated. A_Ω is exactly the L₃-admissible subset of I∞; the surrogates never enter it.

Actualization is inclusion, not creation:

$$A_\Omega \subseteq I_\infty$$

Nothing in A_Ω is manufactured. Every actual configuration was already representable in I∞. What A_Ω adds is the selection – via L₃ and A – of which configurations are instantiated. This framing has an immediate consequence for information preservation: information cannot be destroyed by actualization because actualization does not create the informational domain. Configurations that cease to be instantiated in A_Ω remain present as uninstantiated possibilities in I∞ – they never left it. The implications of this for black hole information – as a programmatic consequence to be developed in a companion paper, not a derived result of this paper – are noted in Section 6 and identified as an open research direction in Section 9.

### 2.3 Determinate Identity

**Claim:** Every actual configuration $c \in A_\Omega$ satisfies Determinate Identity. *[Epistemic status: ESTABLISHED – direct consequence of L₃ as admissibility filter.]*

**Definition:** A configuration $c \in A_\Omega$ has Determinate Identity if and only if:

$$c = c \quad \text{(Identity)}$$
$$\neg(P(c) \land \neg P(c)) \quad \text{for any property } P \text{ (Non-Contradiction)}$$
$$P(c) \lor \neg P(c) \quad \text{for any well-defined property } P \text{ (Excluded Middle)}$$

These three conditions are not independent constraints stacked on top of one another. They are three aspects of a single requirement: that a configuration be determinate. A configuration is determinate when it is self-identical, possesses no contradictory properties, and has definite status with respect to all applicable properties. Together they define what it means for a configuration to be instantiable.

**Qualitative and quantitative identity:** Determinate Identity admits a natural distinction. Qualitative identity concerns what kind of thing a configuration is – an electron rather than a photon, spin-up rather than spin-down. It is categorical. Quantitative identity concerns how much or where precisely – field magnitude, position along a continuum. It admits continuous variation while preserving qualitative type. This distinction grounds the continuity structure of physical configuration space: configurations of the same qualitative type form connected components in A_Ω.

**Determinate Identity applied to sequences:** Determinate Identity is not only a constraint on configurations at an instant. Applied to sequential instantiation – the ordered chain of configurations constituting a physical trajectory – it requires that each transition preserve the structural position of the state being transitioned. A transition that produced something with no determinate identity relation to its predecessor would violate DI at the sequence level. This sequential reading of DI is load-bearing in the derivation of continuous time in Section 5.

### 2.4 The Distinguishability Structure of I∞

I∞ is not an unstructured collection of configurations. It is structured by distinguishability: two configurations are distinct if and only if there exists some respect in which they differ. This is not merely a formal definition – it is a consequence of Identity. If two configurations were indistinguishable in every respect, Identity would require them to be the same configuration.

The distinguishability metric D is defined operationally:

$$D(s_1, s_2) = \sup_M |P_M(s_1) - P_M(s_2)|_{TV}$$

where the supremum is over all physically admissible measurement interactions M – as specified by the reconstruction axioms developed in Section 3 – and $|\cdot|_{TV}$ is the total variation distance. States are equivalence classes under D = 0. I∞ is the maximal D-closed, complete, rich set: closed under distinguishability, complete under D as a metric, and containing at least n mutually distinguishable states for any n.

This operational grounding of I∞ is not empiricism by stipulation. It is a consequence of L₃’s constitutive status established in Section 1.3: any configuration that lacks operational distinguishability fails to satisfy L₃ and is therefore not a configuration in I∞. The distinguishability metric D is the formal expression of what L₃ requires of I∞’s elements.

### 2.5 Summary of Steps 0-2

|Step|Content                             |Status     |
|----|------------------------------------|-----------|
|0   |X ≡ [L₃ : I∞ : A]                   |ESTABLISHED|
|1   |X ⊣ A_Ω; A_Ω = L₃(I∞)               |ESTABLISHED|
|2   |Determinate Identity for all c ∈ A_Ω|ESTABLISHED|

The foundation is secure. Steps 0-2 carry no argued gaps. Everything downstream inherits from this base.

-----

## 3. The Structure of Quantum Theory

### 3.1 From Determinate Identity to Local Tomography

**Claim:** Any theory describing actual configurations in A_Ω must satisfy local tomography. *[Epistemic status: ARGUED – see below.]*

**Definition:** A theory is *locally tomographic* if the state of a composite system is completely determined by the statistics of local measurements on its subsystems.

The argument proceeds in two stages. The first establishes metaphysical supervenience (H1); the second establishes operational local tomography (H2). The move from H1 to H2 is where LRT’s logical framing does its distinctive work.

**H1 (Metaphysical Supervenience):** Each subsystem of a composite system has determinate identity (Step 2). The composite is nothing over and above its subsystems relationally organized. No holistic facts float free of subsystem facts plus their relations. *[Epistemic status: ESTABLISHED – direct consequence of Determinate Identity.]*

**H2 (Operational Local Tomography):** The composite state is completely determined by local measurement statistics on subsystems. *[Epistemic status: ARGUED – follows from H1 given L₃’s constitutive status.]*

**The H1→H2 argument:** The apparent gap between H1 and H2 – that metaphysical supervenience does not automatically yield operational accessibility – closes under LRT’s logical framing. L₃ is not a filter applied to propositions that are already formed. It is the condition under which anything counts as a physical proposition at all.

For any relation R between subsystems to be a genuine physical relation – a real part of the composite’s identity under H1 – R must satisfy L₃. Identity requires R to have determinate content. Non-Contradiction requires R-holding and R-not-holding to be distinct states of affairs. Excluded Middle requires a determinate truth value. All three requirements entail operational distinguishability: without a possible measurement distinguishing R-true from R-false, there is no determinate content, no distinction, no truth value. R is not a hidden physical fact; it is a nothing.

Therefore every relation in H1’s supervenience base is operationally distinguishable. Subsystem states are locally measurable by definition. All identity-determining relations are locally accessible. The composite state is fully determined by local measurement statistics. This is H2.

The content of local tomography is not an empirical extra imported alongside the derivation. It is what you get when you insist that all identity-making relations in H1 must themselves count as physical propositions under L₃. Local tomography is the operational expression of Determinate Identity applied to composite systems – nothing more and nothing less.

The hidden variable objection – that there exist physically real but operationally inaccessible relations – fails at the point of formulation. To assert that a relation is physically real is to assert that it satisfies L₃. Satisfying L₃ requires operational distinguishability. The objection is not merely false; it is unrealizable under LRT’s framework.

A note on the generalized probabilistic theory literature: local tomography is not universally accepted as a foundational axiom. Real-vector-space quantum theories (Wootters, 1990; Hardy, 2012) and certain GPT constructions reject it, producing theories with different composite-system structure. LRT is consciously taking sides here. The commitment to local tomography is not empirical opportunism – it follows from the requirement that all identity-making relations satisfy L₃. That the resulting theory selects complex Hilbert space, confirmed by Renou et al. (2021), is a consequence, not a premise.

### 3.2 Complex Hilbert Space from Local Tomography

**Claim:** The state space of any locally tomographic theory satisfying standard reconstruction axioms is the complex Hilbert space ℂH. *[Epistemic status: ESTABLISHED – imported from Masanes and Müller (2011).]*

**Theorem (Masanes and Müller, 2011):** Among generalized probabilistic theories, the following axioms jointly and uniquely select complex Hilbert space quantum mechanics: local tomography, continuous reversible dynamics, the existence of entangled states, and no restriction on observables.

Local tomography is established at Step 3. The remaining three axioms – continuous reversible dynamics, entanglement existence, and no restriction on observables – are physical inputs to the Masanes-Müller reconstruction, imported alongside the theorem. They are not derived from X in this paper; they characterize the physical domain LRT is describing. Their satisfaction by the actual world is an empirical commitment, not a logical consequence of X alone.

Given these inputs, the state space is ℂH: a complex Hilbert space over ℂ. The field is complex, not real or quaternionic. This is not a free choice. Renou et al. (2021) demonstrated experimentally that real quantum theory makes different predictions from complex quantum theory in network scenarios. Local tomography, combined with the Masanes-Müller axioms, selects ℂ uniquely. Real and quaternionic alternatives are excluded.

**What this delivers:** Pure states are unit vectors in ℂH (up to global phase). Mixed states are density operators. Composite systems are represented by tensor products. The inner product structure is fixed. Everything downstream – measurement, probability, dynamics – operates within this arena.

### 3.3 Projection-Valued Measures from the Boolean Action Primitive

**Claim:** Every event operator on ℂH representing an actualization predicate is a projection operator. POVMs arise only as derived structure. *[Epistemic status: ARGUED.]*

The action primitive A is Boolean by definition:

$$\mathbf{A} : D \to {0, 1}$$

where D = L₃(I∞) is the domain of L₃-admissible configurations. For any configuration c and event predicate E, A assigns actuality status: A(E, c) = 1 if E is actual, A(E, c) = 0 if not. There is no intermediate actualization value. Excluded Middle ensures exactly one of {actual, not-actual} holds.

**The eigenvalue restriction argument:**

A distinction is required between the truth-value map and the probability map. The truth-value map A(E, c) ∈ {0,1} is ontological – it records what is actual. The probability map p(E|ψ) ∈ [0,1] is epistemic – it records the disposition of a state toward an outcome. The probability map taking values in [0,1] does not license event operators with eigenvalues in (0,1). Eigenvalues concern which outcomes are possible, not how probable they are.

Given this distinction:

1. A’s Boolean character entails Boolean actualization values for all events.
1. Measurement outcomes are eigenvalues of event operators (spectral theorem).
1. Therefore event operators have eigenvalues in {0,1}.
1. A bounded self-adjoint operator on ℂH has spectrum contained in {0,1} if and only if it satisfies P² = P.

*Proof of step 4:* If spec(P) ⊆ {0,1}, the spectral theorem gives P = 0·E₀ + 1·E₁ = E₁ where E₁ is the spectral projection onto the λ=1 eigenspace. Since E₁ is a spectral projection, E₁² = E₁, hence P² = P. Conversely, if P² = P, then for any eigenvalue λ with eigenvector |φ⟩: P²|φ⟩ = λ²|φ⟩ = P|φ⟩ = λ|φ⟩, giving λ² = λ, hence λ ∈ {0,1}. □

Therefore event operators in LRT are projections. The collection of projections associated with a complete measurement constitutes a projection-valued measure (PVM).

**On POVMs:** Positive operator-valued measures (POVMs) are not excluded from LRT – they are reinterpreted. By the Naimark dilation theorem, every POVM on ℂH arises as the reduction of a PVM on a larger Hilbert space ℂH ⊗ ℂK. POVMs describe measurements where the full system including apparatus has PVM structure, but the subsystem of interest shows effective POVM statistics after tracing out the environment. The fundamental events remain PVM; POVMs are epistemic reductions, not primitive ontological structure.

**Addressing weak measurements:** Weak measurement outcomes are statistical averages over many runs, each of which involves a Boolean actualization event. The continuous outcome is an ensemble property. Individual actualization events remain Boolean. No conflict with the eigenvalue restriction.

To be precise about the ontological commitment: LRT requires sharp event structure at the fundamental level. This is not a claim about idealized laboratory measurements. Realistic apparatus is noisy; coarse-graining produces effective POVM statistics. LRT’s position is that this noise and coarse-graining are epistemological features of the measurement process, not ontological features of the events themselves. At the level of what is actually instantiated in A_Ω, events are Boolean.

### 3.4 Summary of Steps 3-5

|Step|Content                                              |Status     |
|----|-----------------------------------------------------|-----------|
|3   |Local tomography from DI + L₃ framing                |ARGUED     |
|4   |Complex Hilbert space ℂH (Masanes-Müller)            |ESTABLISHED|
|5   |PVM structure from Boolean A (eigenvalue restriction)|ARGUED     |

The structure of quantum theory is now in place. Steps 3 and 5 are ARGUED – they depend on the logical framing of L₃ and the Boolean character of A respectively, both of which are framework commitments that a critic must engage at the level of X rather than at the level of these inferences. Step 4 is ESTABLISHED by imported peer-reviewed mathematics, conditional on the argued Step 3.

-----

## 4. Probability and the Born Rule

### 4.1 The Probability Problem in LRT

The actualization primitive A is Boolean: for any event E and configuration c, A(E,c) ∈ {0,1}. This is the ontological claim. But quantum mechanics assigns probability values p(E|ψ) ∈ [0,1] to events given states. The question is how a Boolean actualization structure generates a continuous probability measure.

This is not a version of the measurement problem. The measurement problem asks why unitary evolution yields definite outcomes at all. LRT dissolves that problem at Step 2: Determinate Identity guarantees definite outcomes for all c ∈ A_Ω; there is no collapse to explain. The probability question is distinct: given that each actualization event is Boolean, what constrains the probability distribution over possible outcomes? This separates LRT from both Everettian approaches – where the probability question is notoriously difficult because all branches are equally real – and from objective-collapse theories, where a physical mechanism must be specified to generate the distribution. In LRT, the distribution is fixed by the geometry of ℂH alone, via Gleason.

The answer is Gleason’s theorem. It is imported as an ESTABLISHED mathematical result and applied to the PVM structure derived at Step 5.

### 4.2 Gleason’s Theorem and the Born Rule

**Theorem (Gleason, 1957):** Let ℋ be a separable Hilbert space over ℝ or ℂ with dim(ℋ) ≥ 3. If μ is a frame function on the closed subspaces of ℋ – a function assigning non-negative reals to subspaces such that μ sums to 1 over any orthonormal basis – then there exists a unique density operator ρ on ℋ such that:

$$\mu(P) = \mathrm{Tr}(\rho P)$$

for every projection P. *[Epistemic status: ESTABLISHED – Gleason (1957), with the extension to dim = 2 and POVMs by Busch (2003).]*

**Application in LRT:** The PVM structure established at Step 5 consists of collections of projections summing to the identity. A probability assignment over a complete PVM is exactly a frame function in Gleason’s sense: non-negative, normalized, and defined on the projections of ℂH. Gleason’s theorem then entails that the unique consistent probability assignment is the Born rule:

$$p(E|\psi) = \langle \psi | P_E | \psi \rangle = \mathrm{Tr}(|\psi\rangle\langle\psi| P_E)$$

for pure states |ψ⟩, and p(E|ρ) = Tr(ρP_E) for mixed states.

The Born rule is not postulated in LRT. It is the unique probability measure consistent with the PVM structure that A’s Boolean character forces onto ℂH. Any other assignment would violate the frame function condition – it would fail to be a consistent probability measure over the projections of ℂH.

### 4.3 What Gleason’s Theorem Does and Does Not Establish

Gleason’s theorem establishes uniqueness conditional on the frame function requirement. It does not by itself explain why quantum probabilities should be interpreted as frequencies, propensities, or credences. LRT takes a specific position here.

Probabilities in LRT are objective dispositional properties of states in I∞ with respect to A’s selection. Given a state ψ and a measurement context M, p(E|ψ) = Tr(ρP_E) is the objective disposition of ψ toward outcome E – not a measure of ignorance, not a betting coefficient, not a frequency defined over an ensemble. The disposition is real and grounded in the structural relation between ψ and P_E within ℂH.

This is a propensity interpretation, but one grounded in the LRT framework rather than introduced as a further postulate. The grounding runs: A selects Boolean outcomes from I∞; the PVM structure of ℂH constrains what consistent probability assignments over those selections look like; Gleason’s theorem shows the Born rule is the unique such assignment; the Born rule therefore expresses the objective disposition of ψ toward A’s Boolean selection.

**The dim = 2 case:** Gleason’s original proof requires dim(ℋ) ≥ 3. For two-dimensional systems (qubits), the original theorem does not apply. Busch (2003) extended the result to all dimensions by working with POVMs rather than PVMs. In LRT, POVMs are derived via Naimark dilation from PVMs on extended spaces. The Busch extension is therefore available: the Born rule holds for qubits by treating the qubit measurement as a PVM on the extended system and tracing out the ancilla. *[Epistemic status: ARGUED – the Naimark bridge from Busch’s POVM result to LRT’s PVM ontology requires the dilation step to be physically grounded, which is argued but not formally verified.]*

**Hidden variable objection:** Could there be a finer-grained assignment that recovers deterministic outcomes without the Born rule? The Kochen-Specker theorem (1967) rules this out for any non-contextual hidden variable theory in dim(ℋ) ≥ 3: no assignment of definite {0,1} values to all projections simultaneously is consistent with the algebraic structure of ℂH. LRT does not require such an assignment – A selects one Boolean outcome per measurement event, not a global pre-assignment across all observables. Kochen-Specker is no objection to LRT; it is consistent with it. The non-decomposability results derived in the companion paper (Longmire, 2026) develop this connection further.

### 4.4 Summary of Steps 6-7

|Step|Content                        |Status                                                          |
|----|-------------------------------|----------------------------------------------------------------|
|6   |Frame function on PVM structure|ESTABLISHED                                                     |
|7   |Born rule via Gleason (1957)   |ESTABLISHED (dim ≥ 3); ARGUED (dim = 2 via Busch-Naimark bridge)|

The probability structure of quantum mechanics is now grounded. The Born rule is not a postulate in LRT; it is the unique consistent probability measure the PVM structure admits. Steps 6 and 7 are ESTABLISHED for the physically relevant case of dim ≥ 3. The dim = 2 extension is ARGUED, with the gap identified precisely at the Naimark bridge step.

-----

## 5. Time and Dynamics

### 5.1 The Problem of Time in LRT

X ≡ [L₃ : I∞ : A] contains no temporal primitive. Time is not built into the ground-level commitment. This is deliberate: treating time as a primitive would require grounding it in something prior, and LRT’s project is to derive physical structure from logical constraint rather than assume it. The question is whether temporal structure – ordinal ordering, continuous parameterization, and dynamical law – can be derived from what X does provide.

The answer is yes, in four stages. The Unique Next State theorem establishes that A’s Boolean character forces a well-defined successor relation on configurations. Ordinal time follows immediately. The Debreu-Nachbin theorem lifts that ordinal structure to a continuous real-valued parameter. G-equivariance and Stone’s theorem then fix the form of the dynamical generator. The Schrödinger equation follows.

### 5.2 The Unique Next State Theorem

**Claim:** For every actual configuration c ∈ A_Ω, there exists a unique next configuration c’ ∈ A_Ω such that A selects c’ as the successor of c. *[Epistemic status: ARGUED.]*

**Argument:** Determinate Identity (Step 2) requires every c ∈ A_Ω to be self-identical, non-contradictory, and determinate with respect to all applicable properties. Applied to sequential instantiation, DI requires that the transition from c to its successor preserve structural determinacy: the successor must itself be in A_Ω (DI cannot be violated on entry), and the transition relation must be determinate (DI at the sequence level, established in Section 2.3).

A’s Boolean character entails that for any candidate successor c’, A(c’ | c) ∈ {0,1}: either c’ is the actual next configuration or it is not. Excluded Middle rules out indeterminate succession. Non-Contradiction rules out two simultaneous successors. Identity rules out a successor with no determinate relation to its predecessor.

The result is a well-defined successor function S: A_Ω → A_Ω where S(c) = c’ is the unique actual next configuration. This is the Unique Next State theorem. To be precise about scope: UNS is defined relative to a given global dynamical law and interaction history. Conditional on the actual Hamiltonian and interaction structure of the system, there is a unique actual next state. UNS does not claim that the state alone fixes the entire future independent of physical laws – particular Hamiltonians are empirical inputs, as noted at Step 13. What UNS establishes is that given those laws, indeterminate or multiple succession is ruled out by DI and Boolean A.

**Objection – quantum superposition:** In standard QM, a system in superposition does not have a definite state until measurement. Does UNS conflict with this? No. The superposition |ψ⟩ = α|0⟩ + β|1⟩ is the unique next state – the superposition itself is the determinate configuration in ℂH. UNS does not require classical definiteness of observable values; it requires a determinate next element of A_Ω. The state |ψ⟩ is such an element. What is indeterminate is which measurement outcome A will select; what is determinate is the state from which that selection is made.

### 5.3 Ordinal Time

**Claim:** The successor function S induces a well-ordered discrete structure on A_Ω. *[Epistemic status: ESTABLISHED – direct consequence of UNS.]*

S is injective: if S(c₁) = S(c₂) then c₁ = c₂, by DI at the sequence level (two distinct predecessors would produce a configuration with indeterminate origin, violating Identity). S is therefore a well-defined ordering relation. The orbit of any c under iterated application of S:

$$c_0, c_1 = S(c_0), c_2 = S(c_1), \ldots$$

is a well-ordered sequence isomorphic to a subset of the ordinals. This is ordinal time: a discrete, well-ordered parameterization of configuration sequences. It has direction (S is not symmetric), it has a local structure (each configuration has a unique successor), and it has no primitive metric (distances between configurations are not yet defined).

Ordinal time is not physical time. It is the minimal temporal structure forced by UNS and DI. Physical time – continuous, metrizable, and identified with the real parameter in the Schrödinger equation – requires the further steps of Sections 5.4 and 5.5.

### 5.4 Continuous Time via Debreu-Nachbin

**Claim:** The ordinal temporal structure on A_Ω admits a continuous real-valued representation. *[Epistemic status: ARGUED – see below.]*

**The Debreu-Nachbin theorem** (Debreu, 1954; Nachbin, 1965): A totally ordered topological space (X, ≤, τ) admits a continuous order-preserving function f: X → ℝ if and only if (X, ≤) is separable in the order topology.

**Application:** The ordinal sequence (A_Ω, ≤_S) must be given a topology before the theorem applies. The topology comes from the Fubini-Study metric on the projective Hilbert space CP(ℋ): the space of pure states in ℂH carries a natural metric topology, and configuration sequences inherit this topology via the state representation established at Step 4.

**D2 (order-density):** The ordinal sequence is separable in the order topology – there exists a countable dense subset of configuration stages between any two non-adjacent stages – because trajectory continuity is grounded in Determinate Identity applied to sequential instantiation. A trajectory that failed to be dense in the order topology would contain a gap: two successive stages c_n, c_{n+1} with no configuration between them in the Fubini-Study topology. Such a gap would mean the transition from c_n to c_{n+1} produced a successor with no continuous identity relation to its predecessor – a violation of DI at the sequence level.

Given D2, the Debreu-Nachbin theorem applies: there exists a continuous, order-preserving function t: A_Ω → ℝ. This function is physical time. It is not a primitive of the theory; it is the unique continuous representation of the ordinal structure that DI and the Fubini-Study topology jointly force.

*[Epistemic status note: D2 rests on the sequential reading of DI established in Section 2.3 and the Fubini-Study topology from Step 4. It does not depend on Stone’s theorem or any downstream result. The dependency graph is acyclic.]*

### 5.5 G-Equivariance and the Dynamical Generator

**Claim:** The time evolution of states in ℂH is equivariant under the symmetry group G of A_Ω, and this equivariance fixes the generator of time evolution to be a self-adjoint operator H. *[Epistemic status: ARGUED.]*

The configuration space A_Ω carries a symmetry group G: the group of transformations of ℂH that preserve the distinguishability metric D and the PVM structure of Step 5. Any physically admissible time evolution must commute with these symmetries – evolution that broke G-symmetry would change the distinguishability structure of states, which would alter their identity under DI.

G-equivariance of time evolution means that for any g ∈ G:

$$U(t) \circ g = g \circ U(t)$$

where U(t) is the time evolution operator. Combined with the continuous time parameter established at Step 10 and the requirement that U(t) preserve the inner product structure of ℂH (since inner products encode the distinguishability metric D), U(t) must be a strongly continuous one-parameter group of unitary operators.

**Specifying G:** G is identified with the unitary group U(ℋ) acting on ℂH. This identification is physically motivated – U(ℋ) is the maximal group preserving the inner product structure of ℂH – but it is a physical input analogous to the auxiliary axioms of Masanes-Müller. The specific symmetry group of a physical system (rotation group, Poincaré group, gauge group) is determined by the system’s Hamiltonian, not by X alone. *[Epistemic status: the G-equivariance requirement is ARGUED; the identification of G with U(ℋ) is a physical input, not derived from X.]*

### 5.6 Stone’s Theorem and the Schrödinger Equation

**Claim:** The strongly continuous one-parameter unitary group U(t) has a self-adjoint generator H, and the resulting equation of motion is the Schrödinger equation. *[Epistemic status: ESTABLISHED – Stone (1930), imported.]*

**Theorem (Stone, 1930):** If {U(t)}_{t∈ℝ} is a strongly continuous one-parameter group of unitary operators on a Hilbert space ℋ, then there exists a unique self-adjoint operator H on ℋ such that:

$$U(t) = e^{-iHt/\hbar}$$

The operator H is the infinitesimal generator of the group.

**Application:** U(t) is the time evolution operator established by G-equivariance and continuous time (Steps 10-11). Stone’s theorem gives H immediately. The equation of motion for a state |ψ(t)⟩ follows by differentiation:

$$i\hbar \frac{d}{dt}|\psi(t)\rangle = H|\psi(t)\rangle$$

This is the Schrödinger equation. It is not postulated in LRT. It is the equation of motion that the logical-informational-dynamic structure of X forces on states in ℂH, via the chain: UNS → ordinal time → continuous time → G-equivariance → Stone → Schrödinger.

H is self-adjoint by Stone’s theorem. Its spectrum is real, ensuring real-valued energy eigenvalues. Its specific form – kinetic plus potential terms, or field-theoretic generalizations – is determined by the physical system, not by X. LRT derives the existence and self-adjointness of H; it does not derive the Hamiltonian of any particular system. That is a feature, not a gap: particular Hamiltonians are empirical inputs describing specific physical domains. The framework derived here is what constrains their form.

### 5.7 Summary of Steps 8-13

|Step|Content                           |Status                        |
|----|----------------------------------|------------------------------|
|8   |Unique Next State theorem         |ARGUED                        |
|9   |Ordinal time from UNS             |ESTABLISHED                   |
|10  |Continuous time via Debreu-Nachbin|ARGUED                        |
|11  |G-equivariance; U(t) unitary      |ARGUED                        |
|12  |Stone’s theorem; H self-adjoint   |ESTABLISHED                   |
|13  |Schrödinger equation              |ESTABLISHED (given Steps 8-12)|

The full derivation chain from X to the Schrödinger equation is now in place. Of the thirteen steps, seven are ESTABLISHED and six are ARGUED. The ARGUED steps – 3, 5, 8, 10, 11 – are precisely where LRT’s original contribution lives: grounding the inputs that the imported theorems require. Lean 4 formalization of these five steps is the primary remaining technical work, identified in Section 9.

-----

## 6. Resolution of Standing Problems

The standing problems of quantum foundations are not solved by LRT in the sense of providing new physical mechanisms. They are dissolved: each problem is shown to arise from a false presupposition that LRT’s framework does not share. This section works through six problems in sequence, showing in each case what presupposition generates the problem and why LRT does not inherit it.

### 6.1 The Measurement Problem

**The problem:** Unitary evolution is linear and deterministic. Measurement produces a single definite outcome. No unitary evolution takes a superposition to a definite outcome. Something – collapse, branching, decoherence, a new physical law – must be added to explain the transition.

**The presupposition:** Measurement outcomes require explanation in terms of physical dynamics. The definite outcome must be produced by some process.

**LRT’s dissolution:** Actualization is the primitive dynamic aspect of X, not a physical process occurring within A_Ω. A selects one Boolean outcome per measurement event not because a physical mechanism forces it but because that is what A is: the primitive binary operation distinguishing actual from non-actual. There is no collapse because nothing collapses – the superposition |ψ⟩ is the unique next state in A_Ω (UNS, Step 8), and A selects one outcome from its PVM decomposition. The unitary evolution of |ψ⟩ is the correct description of the state in ℂH; A’s selection is not a deviation from unitary evolution but an operation at a different level – the level of which configuration in I∞ is instantiated in A_Ω.

The measurement problem does not arise in LRT because LRT does not treat measurement as a physical process requiring a dynamical account. Measurement is an instance of A’s selection. The problem dissolves at the level of the framework, not at the level of the physics.

### 6.2 Wave-Particle Duality

**The problem:** Quantum systems exhibit wave-like behavior (interference) in some experimental contexts and particle-like behavior (definite position or momentum) in others. No classical description captures both simultaneously.

**The presupposition:** A quantum system must be either a wave or a particle, or some novel kind of thing that combines both natures. The puzzle is ontological: what kind of thing is it?

**LRT’s dissolution:** The wave-particle distinction maps directly onto the I∞/A_Ω distinction. The wave aspect – the full superposition |ψ⟩ with its interference structure – is the configuration in I∞ that evolves unitarily under the Schrödinger equation. The particle aspect – the definite outcome at detection – is the configuration in A_Ω selected by A. There is no tension because these are not competing descriptions of one thing. They are descriptions of the same configuration at two levels: as an element of I∞ (where it is the full quantum state) and as an element selected into A_Ω (where it is the definite outcome).

Interference is a feature of I∞ – the wave structure of uninstantiated configurations can contribute to the probability distribution over outcomes via the Born rule. Detection is a feature of A_Ω – what A selects is Boolean. The duality is not a mystery about a single thing’s nature; it is a consequence of the two-level structure of X.

### 6.3 EPR, Nonlocality, and Entanglement

**The problem:** Entangled systems exhibit correlations that violate Bell inequalities. No local hidden variable theory can reproduce these correlations. Something in quantum mechanics is nonlocal, but quantum mechanics does not permit faster-than-light signaling. What is the nature of this nonlocality?

**The presupposition:** Physical correlations between spatially separated systems must be explained either by local hidden variables or by some form of nonlocal causal influence.

**LRT’s dissolution:** Entangled states are non-decomposable configurations in I∞ – their identity cannot be decomposed into the product of subsystem identities without remainder. This is a consequence of L₃ applied to the composite system: the composite has determinate identity as a whole, and that identity is not fully captured by the identities of its parts. Non-decomposability is derived as a theorem in the companion paper (Longmire, 2026a) from the structure of A_Ω = L₃(I∞); Bell inequality violations and Kochen-Specker contextuality follow as downstream consequences.

LRT’s position is that Einstein’s locality is correct – there is no nonlocal causal influence. What is wrong is separability: the assumption that the composite system’s state is fully determined by the product of its subsystem states. Separability fails for entangled systems because their non-decomposable identity in I∞ is not a product. The correlations are not produced by a signal; they are a structural feature of how A_Ω instantiates non-decomposable configurations. Tsirelson’s bound – the upper limit on quantum correlations, $2\sqrt{2}$ for the CHSH inequality – follows from the Hilbert space structure of ℂH established at Step 4, and is thus an upper limit on LRT’s predicted correlations as well.

### 6.4 Schrödinger’s Cat

**The problem:** If unitary evolution is universal, a macroscopic superposition (cat both alive and dead) should exist before observation. This seems to contradict experience. Either unitary evolution breaks down at some scale, or macroscopic superpositions are real but unobserved, or measurement somehow selects a branch.

**The presupposition:** A superposition of macroscopic states must be either physically real in both branches or collapsed to one branch by some physical process.

**LRT’s dissolution:** The superposition |alive⟩ + |dead⟩ (suitably normalized) is a configuration in I∞ – it is representable, it evolves unitarily, it has interference structure. It is not in A_Ω as a superposition. A selects one L₃-admissible outcome: either |alive⟩ or |dead⟩ is instantiated, not both, not neither. Excluded Middle applies to what is in A_Ω.

The cat is not both alive and dead. It is not in an indeterminate state waiting for an observer. The superposition is the correct description of the configuration in I∞; A’s selection is the correct description of what is instantiated in A_Ω. There is no moment at which a macroscopic superposition is physically real in A_Ω, because superpositions of macroscopic states are configurations in I∞ that A never instantiates as composite configurations – A instantiates one L₃-admissible outcome from the PVM decomposition of the measurement interaction. The paradox arises from treating I∞ configurations as if they were A_Ω configurations. LRT’s two-level ontology dissolves it.

### 6.5 The Preferred Basis Problem

**The problem:** Unitary quantum mechanics does not single out a preferred basis in which to describe outcomes. Any observable can be diagonalized; any basis can be the “measurement basis.” What selects the basis in which actual outcomes occur?

**The presupposition:** Basis selection is a problem about dynamics or about the structure of the quantum state. Something in the physics must privilege one basis over others.

**LRT’s dissolution:** Basis selection is a consequence of A’s interaction with the physical system, not a property of the quantum state itself. A selects outcomes from the PVM decomposition of the interaction between the system and its environment or apparatus. The PVM is determined by the physical interaction Hamiltonian – the specific dynamical coupling between system and measuring device. That coupling is a physical fact about the interaction, not a feature of the state or of quantum theory in the abstract.

The preferred basis problem in LRT is not a problem about quantum mechanics. It is a question about which physical interaction is occurring. The interaction selects the relevant PVM; A selects one outcome from that PVM. There is no residual puzzle about why quantum states do not come pre-labeled with a preferred basis – they do not need to be, because A’s selection is always relative to a specific physical interaction structure.

### 6.6 The Role of the Observer

**The problem:** Many formulations of quantum mechanics assign a constitutive role to observers or measurement contexts: the quantum state is defined relative to an observer (relational QM), or the state represents an observer’s information (QBism), or observation collapses the wave function. This makes the observer a primitive of the theory.

**The presupposition:** Quantum mechanics requires observers as primitive elements because quantum states are defined in terms of their relation to observers.

**LRT’s dissolution:** A_Ω is defined by L₃ admissibility applied to I∞, not by any relation to observers. Observers are physical systems – configurations in A_Ω subject to the same Schrödinger dynamics and the same Boolean actualization as any other system. They have no constitutive role in the definition of physical reality. A selects outcomes independently of whether any observer is present to record them.

This is a strong realist commitment: quantum mechanics describes an observer-independent physical reality. LRT grounds this commitment not in a philosophical preference but in the structure of X. L₃ is not an epistemic norm governing observers’ reasoning; it is a constitutive condition on what counts as a physical configuration. A_Ω is not defined relative to any agent. The observer’s presence or absence is irrelevant to what A instantiates.

### 6.7 Black Hole Information – A Programmatic Pointer

The information-theoretic consequences of the A_Ω ⊆ I∞ framing extend, as a research program, to the black hole information problem. If actualization is inclusion rather than creation, then deactualization – a configuration ceasing to be instantiated in A_Ω – is not destruction. The configuration remains present in I∞ as an uninstantiated possibility. Applied to black hole evaporation: information that appears to be destroyed by the singularity is, in LRT’s framework, deactualized rather than annihilated. It remains in I∞.

This is a programmatic consequence, not a derived result of the present paper. Formalizing it requires connecting the deactualization operator D_sing (as a partial inverse of L₃) to Bekenstein-Hawking entropy and horizon thermodynamics – work identified as an open problem in Section 9. The modified Page curve prediction developed in the companion paper (Longmire, 2026b) is the current state of that program.

-----

## 7. LRT and the Interpretive Landscape

### 7.1 The Comparison Framework

LRT is not an interpretation of quantum mechanics in the standard sense. Interpretations take the formalism as given and ask what it means. LRT takes a prior commitment – X ≡ [L₃ : I∞ : A] – and derives the formalism. The comparison with other interpretive programs is therefore asymmetric: where interpretations differ on what quantum mechanics means, LRT differs on what quantum mechanics is and why it has the structure it has.

The comparison is nonetheless illuminating. Each major interpretive program makes commitments about measurement, ontology, the Born rule, nonlocality, and the observer. LRT’s positions on each are consequences of the derivation chain in Sections 2-5, not independent choices. The table below locates LRT in the landscape; the prose following it develops the most substantive contrasts.

|Program        |Measurement             |Ontology              |Born Rule            |Nonlocality               |Observer                      |Novel Prediction       |
|---------------|------------------------|----------------------|---------------------|--------------------------|------------------------------|-----------------------|
|Copenhagen     |Primitive postulate     |Agnostic              |Postulated           |Agnostic                  |Constitutive                  |None                   |
|Many-Worlds    |Branching; no collapse  |Universal wavefunction|Contested            |Structural                |None                          |None                   |
|Bohmian        |Effective collapse      |Particles + pilot wave|Quantum equilibrium  |Primitive (nonlocal)      |None                          |None beyond QM         |
|GRW            |Stochastic collapse     |Modified wavefunction |Postulated           |None                      |None                          |Collapse parameters    |
|Relational QM  |Relation-relative       |Relational facts      |Postulated           |None                      |Constitutive (relational)     |None                   |
|Reconstructions|Operationally defined   |Agnostic              |Derived (Gleason)    |Agnostic                  |Operational                   |None beyond QM         |
|**LRT**        |**A-selection; Boolean**|**I∞ / A_Ω**          |**Derived (Gleason)**|**Structural; not causal**|**None; observer-independent**|**Renou et al. (2021)**|

### 7.2 LRT and Copenhagen

Copenhagen’s virtues are its vices in a different light. Its insistence that quantum mechanics describes measurement outcomes rather than underlying reality has kept it empirically clean for a century. Its refusal to specify what the quantum state represents has immunized it against ontological objections. But the cost is explanatory inertness: Copenhagen cannot say why the Born rule holds, why measurement outcomes are Boolean, or why the Hilbert space is complex rather than real.

LRT inherits Copenhagen’s determinacy about outcomes – A selects one Boolean result per measurement event – and grounds it rather than postulating it. The measurement postulate is not a primitive in LRT; it is a consequence of A’s Boolean character (Step 5) and Gleason’s theorem (Step 7). Copenhagen’s empirical success is preserved; its explanatory gap is filled.

The key difference in register: Copenhagen says measurement produces a definite outcome and declines to explain why. LRT says A instantiates one L₃-admissible configuration and shows that this is the only structure consistent with X. The former is a postulate; the latter is a derivation.

### 7.3 LRT and Many-Worlds

The contrast with Everett’s relative-state formulation is the most structurally revealing comparison, because LRT and Many-Worlds share more formalism than any other pair in the table.

Both accept unitary evolution as exact and universal. Both treat the quantum state as physically real rather than merely epistemic. Both reject collapse as a physical process. Both work within the Hilbert space formalism established by Sections 3-5. The branching structure of Many-Worlds – the tree of possible histories generated by unitary evolution – exists in LRT as the structure of I∞: all representable configuration histories, unitarily evolved, are present in I∞ as uninstantiated possibilities.

The ontological difference is decisive. In Many-Worlds, all branches are equally instantiated; the universe splits at each measurement event and every outcome is realized in some branch. In LRT, branching structure is real in I∞ but only one L₃-admissible outcome history is ever instantiated in A_Ω. The Born rule weights in LRT are objective dispositional properties of states toward A’s Boolean selection – not measures of “how much” of reality each branch occupies. This is one-world realism with Everettian mathematical structure.

The Many-Worlds probability problem is well-documented: if all branches are equally real, it is unclear what probability means or why the Born rule should govern a rational agent’s credences. LRT has no such problem. Probability is the objective disposition of a state toward one Boolean outcome, grounded in the PVM structure of ℂH and fixed uniquely by Gleason’s theorem. There is one world; outcomes have determinate probabilities; the Born rule is derived.

The preferred basis problem in Many-Worlds – what selects the basis in which branching occurs – is dissolved in LRT by the same move as Section 6.5: A’s selection is always relative to a specific physical interaction, which determines the relevant PVM. No preferred basis is needed in I∞; the interaction selects it in A_Ω.

### 7.4 LRT and Bohmian Mechanics

Bohmian mechanics shares LRT’s realist commitment: the quantum state is physically real, outcomes are definite, and the observer plays no constitutive role. These are significant agreements. The disagreements are about what realism requires.

Bohmian mechanics achieves deterministic outcomes by adding particle positions as hidden variables guided by the pilot wave. The grounding direction is: quantum formalism first, then supplement with hidden structure to restore definiteness. The result is a theory with surplus ontology (pilot wave plus particles), primitive nonlocality (the guiding equation is holistic over all particle positions), and a preferred basis built in (position).

LRT’s grounding direction is reversed: logical constraints first, then derive the formalism. No pilot wave is required because definiteness is not achieved by a guiding mechanism but by A’s primitive Boolean selection. No preferred basis is required because the interaction structure determines the relevant PVM. And the nonlocality of entangled systems in LRT is structural – a consequence of non-decomposable identity in I∞ – not a primitive dynamical feature of the guiding equation.

The Bohmian can reasonably ask: what determines which L₃-admissible outcome A selects in any given measurement event? LRT’s answer is that A is a primitive of X; the specific outcome is not determined by any sub-X mechanism. This is not a hidden variable completion; it is a terminus of explanation at the level of the primitive. Whether this is satisfying depends on whether one requires mechanistic explanation at every level – a question that applies equally to Bohmian’s pilot wave, which is also not derived from anything more fundamental.

### 7.5 LRT and GRW

GRW and related objective collapse theories (CSL, Penrose-Diósi) make a genuine empirical bet: the Schrödinger equation is not exact, and stochastic collapse terms produce definite outcomes at a rate governed by free parameters. This is the only interpretive program besides LRT that makes novel empirical predictions distinguishable from standard QM.

LRT’s position on GRW is not dismissal but differentiation. GRW’s free parameters – collapse rate, localization width – are introduced ad hoc and must be fitted to experiment. LRT predicts that if physical collapse occurs, its parameters would need to be derivable from the logical-informational structure of X; underivable parameters would represent a failure of LRT’s grounding program. But LRT does not require collapse. A’s selection is not a modification of Schrödinger evolution; it operates at a different level. If GRW collapse parameters are eventually derived from more fundamental structure, LRT is compatible with that derivation. If they remain irreducibly free, LRT and GRW are empirically distinguishable and the experimental record will arbitrate.

### 7.6 LRT and Operational Reconstructions

The comparison with operational reconstruction programs – Hardy (2001), Masanes and Müller (2011), Chiribella, D’Ariano, and Perinotti (2011) – is the most technically precise, because LRT directly imports their results.

Reconstruction programs derive quantum formalism from operational axioms: local tomography, continuous reversibility, the existence of entangled states, no restriction on observables. The derivation is rigorous. What reconstruction programs do not provide is an answer to why these axioms hold. The axioms are operationally motivated – they describe features of any reasonable physical theory – but their grounding is left open.

LRT’s relationship to reconstruction programs is therefore this: LRT grounds the axioms. Local tomography is not an independent empirical postulate in LRT; it is the operational expression of Determinate Identity applied to composite systems under L₃ (Section 3.1). Continuous reversibility, entanglement existence, and no restriction on observables are physical inputs characterizing the domain – they are not derived from X but they are not in tension with X either. The Masanes-Müller result then delivers complex Hilbert space (Step 4), and LRT explains why the reconstruction axioms are what they are rather than some other set of operationally reasonable conditions.

This is LRT’s most precise claim to originality relative to the reconstruction tradition: not new mathematics, but a new grounding argument for the mathematics that reconstruction programs require. The question reconstruction programs leave open – why these axioms? – is what LRT answers.

-----

## 8. Falsification and Scientific Status

### 8.1 The Falsifiability Question

A theory grounded in logical necessity faces an immediate objection: if L₃ is transcendentally necessary and X is the terminus of grounding chains, is LRT falsifiable at all? A theory that cannot be wrong is not science.

The objection conflates two levels. L₃’s transcendental status means its negation is unrealizable – no coherent physical proposition can violate it. This is a claim about the structure of any possible physical theory, not a claim that LRT’s specific derivations are immune to error. LRT makes substantive claims at multiple levels, each of which is falsifiable in a different way. The falsification hierarchy runs from categorical to structural to empirical.

### 8.2 Popperian Falsifiability

LRT satisfies Popper’s falsifiability criterion. A single decisive falsifier exists at the categorical level: a completed physical record that violates L₃ – a measurement outcome that is both actual and not-actual, or a physical proposition with no determinate truth value in a completed experimental record – would falsify LRT’s central claim that A_Ω is the L₃-admissible subset of I∞.

This falsifier is categorical because it targets X itself rather than any downstream derivation. If L₃ is violated in a completed physical record, the entire framework fails, not merely one of its consequences. The falsifier is also practically meaningful: it specifies what kind of experimental result would constitute refutation, namely a stable, reproducible violation of Boolean outcome structure in a closed experimental record.

No such violation has been observed. The empirical track record of quantum mechanics – which inherits its Boolean outcome structure from LRT’s derivation – is the strongest available evidence that A_Ω is correctly characterized.

### 8.3 Lakatosian Research Program Structure

Popper’s criterion establishes minimal scientific status. Lakatos’s framework of scientific research programs gives a richer account of LRT’s structure and progressive character.

**Hard core:** The hard core of LRT is X ≡ [L₃ : I∞ : A] and the core equation A_Ω = L₃(I∞). These commitments are held fixed. Any anomaly is addressed by revising the protective belt, not the hard core. The hard core is falsifiable in principle – categorical L₃ violation would destroy it – but is protected from direct empirical contact by the belt.

**Protective belt:** The protective belt consists of the argued steps in the derivation chain: the H1→H2 argument for local tomography (Step 3), the eigenvalue restriction for PVMs (Step 5), the UNS theorem (Step 8), continuous time via Debreu-Nachbin (Step 10), and G-equivariance (Step 11). These are where LRT makes substantive commitments beyond the hard core. Anomalies at the level of quantum structure – failure of local tomography, violations of PVM structure, non-unitary dynamics – would require revision of one or more of these argued steps without necessarily touching X.

**Progressive predictions:** A research program is progressive when its protective belt generates novel predictions that are subsequently confirmed. LRT has one structurally selected result at this stage: the selection of complex over real Hilbert space. Local tomography, combined with the Masanes-Müller axioms, selects ℂH. Renou et al. (2021) demonstrated that real quantum theory makes different predictions from complex quantum theory in network scenarios and found results consistent with complex QM.

The precise status of this result warrants care. LRT does not claim to have pre-registered an empirical prediction in the ordinary physics sense prior to Renou et al.’s experimental design. What LRT supplies is a grounding architecture that selects complex QM structurally – via local tomography derived from Determinate Identity and L₃ – such that the Renou et al. result confirms the structure LRT requires rather than merely being compatible with it. This is retrodictive structural selection: stronger than post hoc compatibility, but not identical to an independently articulated pre-registered prediction. It is the appropriate category for a foundational grounding program rather than a standard empirical theory.

The companion papers extend the progressive character: the Non-Decomposability Theorem (Longmire, 2026a) derives Bell inequality violations and Kochen-Specker contextuality as downstream consequences of L₃ structure rather than independent postulates; the black hole information program (Longmire, 2026b) generates the modified Page curve prediction FC-2b. These extend the belt without modifying the hard core.

### 8.4 The Null Hypothesis: Standard QM

The null hypothesis for LRT’s empirical program is standard quantum mechanics without LRT’s grounding. Where LRT agrees with standard QM, the agreement is expected and uninformative about LRT specifically. Where LRT diverges, the divergence is the test.

**Agreement:** LRT reproduces standard QM predictions in all domains where the derivation chain is complete: non-relativistic quantum mechanics, Born rule statistics, unitary dynamics, entanglement structure, Bell inequality violations up to the Tsirelson bound. No deviation from standard QM is predicted within this domain.

**Structural divergence:** LRT makes structural claims that standard QM does not: that POVMs are derived rather than primitive, that the Born rule is the unique consistent probability measure given PVM structure, that complex Hilbert space is selected rather than postulated, that local tomography is a logical consequence rather than an axiom. These are not empirical divergences from standard QM’s predictions but claims about the status of its postulates. A referee can agree with every prediction LRT makes while disputing whether LRT’s grounding argument is correct.

**Empirical divergence:** Two domains generate genuine empirical divergence from what an ungrounded quantum theory would predict:

First, any theory in which Hilbert space is real rather than complex makes different predictions in network scenarios of the type tested by Renou et al. (2021). LRT predicts complex QM; ungrounded real quantum theories are empirically ruled out.

Second, the black hole information program generates the FC-2b prediction: a modified Page curve with a two-channel output structure. If black hole evaporation is observed to produce information return inconsistent with the standard Page curve but consistent with LRT’s two-channel model, this confirms FC-2b. The experimental access required for this test is not currently available; it is a long-range prediction.

### 8.5 The Falsification Hierarchy

Three levels of falsification are available, in descending order of severity:

**Categorical:** A completed physical record violating Boolean outcome structure – a stable, reproducible measurement with indeterminate or contradictory outcome. This falsifies X and destroys the entire framework.

**Structural:** A physical theory proven to require super-quantum correlations beyond the Tsirelson bound, or primitive POVMs that cannot be dilated to PVMs on any extended Hilbert space, or non-unitary dynamics irreducible to Hamiltonian evolution on an extended system. Each of these would require revision of a specific argued step in the derivation chain without necessarily falsifying X.

**Empirical:** A network-scenario experiment inconsistent with complex QM, or a black hole evaporation observation inconsistent with the two-channel FC-2b prediction. These test specific downstream consequences of the derivation chain.

The hierarchy is not a weakness. It is the expected structure of a foundational theory with a hard core and a progressive protective belt. Copenhagen has no such hierarchy because it makes no structural or grounding claims. Many-Worlds has no novel empirical predictions. LRT has both a categorical falsifier and empirically distinguishable predictions – which is the combination Lakatos identifies as the mark of a progressive research program.

-----

## 9. Open Problems

LRT is a research program, not a completed theory. This section identifies the open problems honestly, distinguishing those that are gaps in the current derivation chain from those that are extensions beyond its current scope. The distinction matters: a gap is a place where a claimed result is not yet secured; an extension is a direction where the framework may apply but has not yet been developed.

### 9.1 Lean 4 Formalization of Argued Steps

The five ARGUED steps in the derivation chain – Steps 3, 5, 8, 10, and 11 – are defended with explicit reasoning but have not been formally machine-verified. Lean 4 formalization of these steps is the primary remaining technical work.

**Step 3 (Local tomography from DI + L₃):** The H1→H2 argument requires formalizing the claim that L₃’s constitutive status entails operational distinguishability for all identity-making relations. The main challenge is making the notion of “physical proposition” precise enough for formal treatment while preserving the transcendental character of the argument.

**Step 5 (PVM structure from Boolean A):** The eigenvalue restriction argument is mathematically straightforward – the spectral theorem step is standard – but the connection from A’s Boolean character to the eigenvalue constraint needs formal grounding. The key lemma is that A(E,c) ∈ {0,1} for all E, c entails spec(P_E) ⊆ {0,1} for all event operators P_E.

**Step 8 (UNS theorem):** Formalizing UNS requires making the notion of “determinate succession” precise in terms of DI at the sequence level. The main challenge is that UNS is conditioned on a given Hamiltonian and interaction history – the formal statement must be conditional in the right way without becoming trivially true.

**Step 10 (Continuous time via Debreu-Nachbin):** The D2 (order-density) premise requires formal grounding in sequential DI and the Fubini-Study metric. The Debreu-Nachbin theorem itself is established mathematics; the formalization work is in establishing D2 from LRT’s commitments rather than as an independent axiom.

**Step 11 (G-equivariance):** The identification of G with U(ℋ) is a physical input rather than a derivation from X. The formal treatment needs to distinguish clearly between what LRT derives (the equivariance requirement) and what is physically specified (the particular group).

The companion non-decomposability paper (Longmire, 2026a) identifies three open Lean 4 formalizations in that domain; the present paper adds five more. Eight total open formalizations constitute the primary formal verification agenda.

### 9.2 Relativistic Extension

The derivation chain in Sections 2-5 is explicitly non-relativistic. The Schrödinger equation derived at Step 13 is the non-relativistic equation of motion. Extension to relativistic quantum mechanics and quantum field theory requires addressing two distinct challenges.

**Lorentz covariance:** The G-equivariance argument at Step 11 specifies G as the symmetry group of A_Ω. For relativistic systems, G must include Lorentz transformations. Whether the Lorentz group can be derived from X or must be specified as a physical input is an open question. The Poincaré group’s structure – including the role of mass as a Casimir invariant – may have a natural home in the distinguishability structure of I∞, but this has not been developed.

**Quantum field theory:** QFT introduces infinitely many degrees of freedom, vacuum structure, renormalization, and gauge symmetry. The I∞/A_Ω framework can in principle accommodate infinite-dimensional configuration spaces, but the treatment of UV divergences, renormalization group flow, and the ontological status of virtual particles within LRT’s framework requires dedicated development. This is a long-range extension, not a gap in the current derivation.

### 9.3 Specific Hamiltonians

Step 13 derives the existence and self-adjointness of the Hamiltonian H from Stone’s theorem. It does not derive the specific form of H for any physical system. The Hamiltonians of non-relativistic quantum mechanics – kinetic energy plus potential, spin-orbit coupling, the hydrogen atom Hamiltonian – are empirical inputs in LRT, not derived from X.

This is a feature of the framework’s scope, not a gap in the derivation. LRT derives that there must be a self-adjoint generator of time evolution; what that generator is for any particular system is a physical question answered by experiment and model-building. The question of whether any specific Hamiltonian can be derived from logical-informational structure alone is open, and almost certainly the answer is that most cannot – they encode contingent features of the physical world.

### 9.4 The Fine-Structure Constant

The fine-structure constant α ≈ 1/137 is a dimensionless physical constant governing the strength of electromagnetic coupling. It is currently a measured axiom: its value is determined empirically and inserted into the theory without derivation. Whether α can be derived as a theorem from LRT’s logical-informational structure is an open question and a long-range research goal.

The goal is not idle. If LRT’s grounding program is correct – if physical structure follows from logical constraint on information – then dimensionless constants that govern the coupling between physical degrees of freedom should in principle be derivable from the structure of I∞ rather than measured. Whether this is achievable for α in particular depends on whether electromagnetic coupling strength has a logical-informational characterization. No current approach within LRT addresses this. It is identified here as a research direction, not a near-term deliverable.

### 9.5 Bekenstein-Hawking Entropy and Horizon Thermodynamics

The black hole information program developed in the companion paper (Longmire, 2026b) introduces the deactualization operator D_sing as a partial inverse of L₃, and generates the FC-2b modified Page curve prediction. A confirmed open problem within that program is the connection between D_sing and Bekenstein-Hawking entropy.

Bekenstein-Hawking entropy S_BH = A/4G – where A is the horizon area and G is Newton’s constant – is a thermodynamic quantity associated with black hole horizons. If LRT’s information-preservation claim is correct (configurations cease to be instantiated in A_Ω but remain in I∞), then S_BH should have a characterization in terms of the count of deactualized configurations associated with a horizon. Establishing this connection requires showing that the Bekenstein-Hawking formula follows from, or is at least consistent with, D_sing’s action on configurations in I∞. This has not been done.

Until this connection is established, the black hole information program within LRT is programmatic in a double sense: it makes a prediction (FC-2b) without a complete derivation from the hard core to the thermodynamic quantities the prediction involves.

### 9.6 Cosmological Applications

The I∞/A_Ω framework has potential cosmological implications – the actualization primitive A operating at cosmological scales, the question of whether the universe as a whole is an element of A_Ω, the thermodynamic implications of deactualization – but none of these have been developed to the point of falsifiable prediction. Cosmological application is an open research direction. It is not a falsifiability criterion in the current state of the program.

### 9.7 Summary of Open Problems

|Problem                                        |Type                 |Priority                  |
|-----------------------------------------------|---------------------|--------------------------|
|Lean 4 formalization of Steps 3, 5, 8, 10, 11  |Gap                  |Primary                   |
|D_sing connection to Bekenstein-Hawking entropy|Gap (companion paper)|High                      |
|Relativistic extension / Lorentz covariance    |Extension            |Medium                    |
|Quantum field theory within I∞/A_Ω             |Extension            |Long-range                |
|Specific Hamiltonians from X                   |Extension            |Low (likely not derivable)|
|Fine-structure constant α as theorem           |Extension            |Long-range                |
|Cosmological application and prediction        |Extension            |Open                      |

-----

## 10. Conclusion

Logic Realism Theory begins with a single commitment: reality is logical, informational, and dynamic. Expressed formally as X ≡ [L₃ : I∞ : A], this commitment is not an axiom in the ordinary sense. It is the terminus of grounding chains – the condition that any coherent account of physical reality already presupposes. From X, through thirteen steps explicitly marked by epistemic status, the full structure of non-relativistic quantum mechanics follows: complex Hilbert space, projection-valued measures, the Born rule, continuous time, and the Schrödinger equation.

The derivation is not complete in the sense of having no remaining work. Five steps are ARGUED rather than ESTABLISHED; Lean 4 formalization of those steps is the primary remaining technical task. The relativistic extension, the connection to black hole thermodynamics, and the cosmological domain are open. LRT is a research program with a secure hard core, a progressive protective belt, and a well-defined agenda of open problems.

What the derivation does establish is a reorientation of the explanatory order in quantum foundations. The standing problems – measurement, wave-particle duality, EPR, Schrödinger’s cat, preferred basis, the observer – are not solved by new physical mechanisms. They are dissolved by showing that they arise from presuppositions LRT does not share. The measurement problem does not arise because actualization is a primitive, not a physical process. Wave-particle duality is not a puzzle about one thing’s nature but a consequence of the I∞/A_Ω distinction. EPR nonlocality is structural, not causal. The observer has no constitutive role.

The central methodological claim – that L₃ is not a constraint on reasoning about reality but a constitutive condition on what counts as a physical fact – distinguishes LRT from all previous quantum foundations programs. Prior programs move from physics to interpretation: they take the formalism and ask what it means. LRT moves from logic to physics: it takes the constitutive conditions on physical reality and derives the formalism. This reversal of grounding direction is what makes the dissolution of standing problems possible rather than merely rhetorical.

LRT’s original contribution is precisely located. The mathematical results imported – Masanes and Müller, Gleason, Stone, Debreu, Nachbin – are established. LRT’s contribution is the grounding argument: showing that the inputs these theorems require follow from X rather than standing as independent postulates. The question that reconstruction programs leave open – why these axioms? – is what LRT answers.

One result has been retrodictively structurally selected: complex over real Hilbert space, grounded in local tomography derived from Determinate Identity and L₃, subsequently confirmed by Renou et al. (2021). Further predictions extend the program into black hole information (FC-2b) and await experimental access. The categorical falsifier – a completed physical record violating Boolean outcome structure – remains unobserved.

The program is open. The foundation is secure.

-----

## References

Busch, P. (2003). Quantum states and generalized observables: A simple proof of Gleason’s theorem. *Physical Review Letters*, 91(12), 120403.

Chiribella, G., D’Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Debreu, G. (1954). Representation of a preference ordering by a numerical function. In R. M. Thrall, C. H. Coombs, and R. L. Davis (Eds.), *Decision Processes* (pp. 159-165). Wiley.

Fine, K. (2012). Guide to ground. In F. Correia and B. Schnieder (Eds.), *Metaphysical Grounding: Understanding the Structure of Reality* (pp. 37-80). Cambridge University Press.

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885-893.

Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.

Hardy, L. (2012). Limited holism and real-vector-space quantum theory. *Foundations of Physics*, 42(3), 454-473.

Kochen, S. and Specker, E. P. (1967). The problem of hidden variables in quantum mechanics. *Journal of Mathematics and Mechanics*, 17(1), 59-87.

Longmire, J. D. (2026a). LRT: Non-decomposability, entanglement, and Bell’s theorem derived from A_Ω = L₃(I∞). Zenodo. https://doi.org/10.5281/zenodo.18950181

Longmire, J. D. (2026b). LRT: Black hole information return – operator formalism and FC-2 prediction. Zenodo. https://doi.org/10.5281/zenodo.18950706

Masanes, L. and Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Nachbin, L. (1965). *Topology and Order*. Van Nostrand.

Renou, M.-O., Trillo, D., Weilenmann, M., Le, T. P., Tavakoli, A., Gisin, N., Acín, A., and Navascués, M. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600, 625-629.

Schaffer, J. (2009). On what grounds what. In D. Chalmers, D. Manley, and R. Wasserman (Eds.), *Metametaphysics: New Essays on the Foundations of Ontology* (pp. 347-383). Oxford University Press.

Stone, M. H. (1930). Linear transformations in Hilbert space III: Operational methods and group theory. *Proceedings of the National Academy of Sciences*, 16(2), 172-175.

Tahko, T. E. (2019). Logical realism. In E. J. Lowe and A. Rami (Eds.), *Truth and Truth-Making* (pp. 1-18). Routledge. [Survey available at PhilArchive: philarchive.org/archive/ETAASOv2]

Wootters, W. K. (1990). Local accessibility of quantum states. In W. H. Zurek (Ed.), *Complexity, Entropy, and the Physics of Information* (pp. 39-46). Addison-Wesley.

-----

## Appendix: QM Primitives to LRT Origins

This appendix maps the standard primitives of quantum mechanics – elements typically introduced as postulates in textbook presentations – to their origins in the LRT derivation chain. It is intended for readers approaching from the physics side who wish to locate where each standard postulate is derived or grounded.

|QM Primitive                         |Standard Status|LRT Origin                                   |Step|Epistemic Status|
|-------------------------------------|---------------|---------------------------------------------|----|----------------|
|Hilbert space ℂH                     |Postulated     |Masanes-Müller from local tomography         |4   |ESTABLISHED     |
|Complex field ℂ                      |Postulated     |Local tomography + MM axioms; Renou et al.   |4   |ESTABLISHED     |
|Pure states as unit vectors          |Postulated     |Follows from ℂH structure                    |4   |ESTABLISHED     |
|Mixed states as density operators    |Postulated     |Follows from ℂH structure                    |4   |ESTABLISHED     |
|Observables as self-adjoint operators|Postulated     |PVM structure + spectral theorem             |5   |ARGUED          |
|Measurement outcomes as eigenvalues  |Postulated     |Boolean A → eigenvalues in {0,1}             |5   |ARGUED          |
|Born rule p = Tr(ρP)                 |Postulated     |Gleason’s theorem on PVM structure           |7   |ESTABLISHED     |
|Composite systems as tensor products |Postulated     |Local tomography (Masanes-Müller)            |4   |ESTABLISHED     |
|Unitary time evolution               |Postulated     |G-equivariance + Stone’s theorem             |12  |ESTABLISHED     |
|Schrödinger equation                 |Postulated     |Stone’s theorem applied to U(t)              |13  |ESTABLISHED     |
|Collapse / definite outcomes         |Postulated     |A primitive; Determinate Identity            |2   |ESTABLISHED     |
|No-signaling                         |Postulated     |Structural: nonlocality in I∞, Boolean in A_Ω|6   |ARGUED          |

**Reading the table:** ESTABLISHED means the LRT derivation imports a peer-reviewed mathematical result that delivers this primitive given the prior steps. ARGUED means the LRT-specific grounding argument is defended but not yet formally machine-verified. In no case is the primitive simply re-postulated; in each case the derivation chain provides a grounding argument for why the primitive takes the form it does.
