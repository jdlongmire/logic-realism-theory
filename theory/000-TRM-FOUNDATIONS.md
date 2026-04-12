# The Triadic Reality Model: Irreducible Foundations for Physics

**James (JD) Longmire**
ORCID: 0009-0009-1383-7698
Northrop Grumman Fellow (unaffiliated research)
Correspondence: jdlongmire@outlook.com

**Version:** 1.1 (April 2026)
**Status:** Working Draft
**Related program:** Logic Realism Theory (Longmire, 2025a, 2025b, 2026a, 2026b). The TRM provides the primitive ontic architecture from which the LRT derivation chain proceeds. This paper develops the TRM as a self-standing foundational framework; the downstream derivations are pursued in the companion papers cited above.

---

## Abstract

Contemporary foundations of physics divides into two programs that address different questions and leave a third unanswered. Reconstruction programs derive quantum structure from operational axioms but do not explain why those axioms hold. Interpretational programs address what the quantum formalism describes but presuppose its mathematical structure. Neither program asks what the necessary conditions for any physically admissible theory are. This paper addresses that third question by proposing the Triadic Reality Model (TRM): the claim that any framework capable of coherently grounding physics must instantiate three irreducible co-primitives: L₃ (the classical laws of logic as an ontological constraint on actualized states), I∞ (an infinite configurability space of L₃-respecting informational structures), and A (a primitive actualization principle prior to and generative of temporal structure). The three are defended individually and shown to be irreducible: each pair without the third either fails to constitute a coherent formal object or fails specifically as a physical foundation. The TRM is not a rival dynamical theory but an ecumenical meta-framework: it provides the common meta-ontological backdrop that existing interpretations and reconstruction programs presuppose, specifying necessary conditions that any admissible physical theory must satisfy, represented as T ≡ ⟨L, S, D⟩ instantiating [L₃ : I∞ : A]. Classical mechanics and quantum mechanics are analyzed as triadic models. The double-slit experiment and Bell-type correlations are interpreted within the framework; analysis of the latter shows that all viable interpretations share the triadic structure. The primitives are defended at explicitly distinguished epistemic levels: L₃ and A are argued to be transcendentally necessary, their denials performatively self-undermining through distinct logical and ontic routes; I∞ is defended by pragmatic necessity and inference to best explanation, with its transcendental status left as an open problem. Falsifiability is addressed: the TRM excludes theories with actualized L₃-violations, unconstrained state spaces, and purely epistemic interpretations without ontic actualization. The bridge equation, $A_\Omega = L_3(I_\infty)$, is decomposed into three explicitly distinguished claims: grounding (the primitive ontology constitutes actuality), characterization (actuality cannot violate logic), and plenitude identity (the actualized domain coincides with the logically admissible domain). The first two are nearly uncontroversial given the primitives; the third carries the substantive philosophical weight and is defended via the constraint collapse argument.

**Keywords:** foundations of physics, logical realism, actualization, quantum reconstruction, philosophy of physics, triadic ontology, transcendental necessity, information

---

## 1. Introduction

### 1.1 The Gap in Existing Foundations Programs

Two research programs currently dominate the foundations of quantum mechanics, and between them they leave a significant question unaddressed.

The first program is quantum reconstruction. Hardy (2001), Chiribella, D'Ariano and Perinotti (2011), and Masanes and Müller (2011) have shown that the mathematical structure of quantum mechanics, including complex Hilbert space, the Born rule, and the tensor product rule for composite systems, can be derived from small sets of operational axioms. These results are technically significant: they demonstrate that quantum structure is not arbitrary but uniquely determined by certain informational and operational constraints. What they do not address is why those axioms hold. The reconstruction axioms are motivated operationally, by appeal to what agents can do, what experiments can distinguish, what composites can be tomographically characterized, but their deeper ground is left unexamined. The question "why these axioms rather than others?" is not answered within the reconstruction program; it is the question the program presupposes.

The second program is quantum interpretation. Everett (1957), Bohm (1952a, 1952b), Ghirardi, Rimini and Weber (1986), and the relational and epistemic approaches (Rovelli, 1996; Fuchs, Mermin and Schack, 2014) address a different question: what does the quantum formalism describe? These programs take the mathematical structure of quantum mechanics as given and argue about its ontological significance: whether the wavefunction is real, whether collapse is physical, whether there are hidden variables. They are indispensable for understanding what quantum mechanics means, but they presuppose the very formalism whose ground the reconstruction program is attempting to characterize.

Neither program asks what the necessary conditions for any physically admissible theory are. What must any framework satisfy, at the most primitive level, in order to be capable of grounding physics at all? This is a prior question, prior to the choice of formalism, prior to the choice of interpretation, prior to the operational axioms of reconstruction. It is the question the Triadic Reality Model addresses.

### 1.2 The Thesis

The TRM proposes that any framework capable of coherently grounding physics must instantiate three irreducible co-primitives, jointly denoted:

$$\chi \equiv [L_3 : I_\infty : A]$$

**L₃**, the classical triadic laws of logic (identity, non-contradiction, excluded middle), functions as an ontological constraint on what can be actual, not merely as an epistemic constraint on reasoning. Every physically actualized state must be L₃-conformant. No stable experimental record has ever instantiated a genuine violation of L₃ at the level of actualized outcomes, and the best explanation of that universality is that L₃-conformity is a constitutive condition on physical instantiation, not a contingent regularity.

**I∞**, an infinite configurability space of L₃-respecting informational structures, provides the domain over which physical theories range. Informational structure is immaterial in kind: individuated by L₃-respecting configuration rather than by physical substrate, as demonstrated by the multiple realizability of the same informational pattern across arbitrarily different physical media. I∞ is a modal space rather than an aggregate of simultaneously instantiated states; its infinite configurability is not bounded by holographic entropy constraints, which apply to actualized subsets of I∞ within bounded regions, not to I∞ as a representational space.

**A**, the primitive actualization principle, marks the distinction between what is actual and what is merely possible or admissible within I∞. A is not defined as temporal process; temporal succession is derived from A, not prior to it. A is transcendentally necessary: the assertion that nothing is actual is either itself actual, in which case something is actual and A is instantiated, or it carries no force as a denial. The denial of A is unsayable without self-defeat.

The three are irreducible co-primitives: none derives from the other two, and the removal of any one leaves the remaining pair insufficient as a physical foundation. The irreducibility argument proceeds through six pairwise-collapse cases, divided into two tiers: Tier 1 (the pair cannot ground a physical framework because a constitutive element is missing) and Tier 2 (the pair produces a formally coherent object that cannot perform the required physical function).

### 1.3 Scope and Method

The TRM is a meta-framework, not a rival dynamical theory, and it is ecumenical with respect to existing interpretations and reconstruction programs. It does not replace the formalisms of classical mechanics, quantum mechanics, or any future physical theory, nor does it adjudicate between Many-Worlds, Bohmian mechanics, collapse theories, or relational approaches. It provides the common meta-ontological backdrop that all of these presuppose: each requires L₃-conformant actualized outcomes, an informational state space, and some actualization principle, however differently they model these commitments. The TRM identifies what they share, not what distinguishes them. It specifies the necessary conditions those formalisms must satisfy. Any concrete physical theory T can be represented as a triple T ≡ ⟨L, S, D⟩ comprising logical layer, state space, and dynamics, where L instantiates L₃, S instantiates I∞, and D instantiates A. Different theories correspond to different specific choices of ⟨L, S, D⟩ within the constraints set by χ.

The method throughout is what might be called transcendental argument from physical practice: identify what physical inquiry presupposes at the level of experimental design, data recording, and theory testing; show that those presuppositions have ontological implications that cannot be discharged by purely epistemic or methodological readings; and codify those implications as primitive structural commitments. The move from practice to ontology is abductive, inference to the best explanation of physics' coherent success, except in the cases of L₃ and A, which are argued to be transcendentally necessary rather than merely inductively supported.

This paper is part of the Logic Realism Theory (LRT) program (Longmire, 2025a, 2025b, 2026a, 2026b), which develops the downstream derivation chain from χ: from the triadic primitives through admissibility conditions to Hilbert space structure, the Born rule, the Unique Necessary Successor theorem, and the Schrödinger equation. The TRM provides the primitive ontic architecture; the LRT papers develop what that architecture yields. The present paper establishes the TRM as a self-standing foundation; familiarity with the LRT companion papers is not presupposed.

### 1.4 Structure of the Paper

Section 2 defends each of the three axioms in turn (§§2.1-2.3), presents the complete triadic model with an explicit table of necessity levels claimed for each primitive (§2.4), and establishes irreducibility through the six pairwise-collapse cases (§2.5; full arguments in Appendix C). Sections 3 and 4 are exemplifications: §3 shows how classical and quantum mechanics instantiate the triadic template; §4 interprets the double-slit experiment and Bell-type correlations within the framework, including an analysis of why all viable interpretations share the triadic structure. These sections demonstrate compatibility, not confirmation; the evidential weight rests on the transcendental arguments of §2 and the bridge argument of §6. Section 5 addresses falsifiability. Section 6 derives the bridge equation, decomposing it into three explicitly distinguished claims (grounding, characterization, and plenitude identity), and argues for its status as a grounded characterization rather than stipulative definition. References and appendices follow.

---

## 2.1 Defense of the Axiom of Being (L₃)

**Epistemic Status:** ARGUED

**Axiom of Being (L₃).**
Being in χ is governed by the unified triadic laws of thought: identity, non-contradiction, and excluded middle (collectively L₃).

I defend the Being axiom on three levels: its implicit role in physical practice, the ontological implications of that practice, and responses to standard objections.

### (a) Implicit in physical practice

Physical theories presuppose L₃ in their core operations:

- **Identity:** A system or quantity is treated as self-identical across derivations and experiments; an electron's charge is not simultaneously "not-that-charge" in the same respect.
- **Non-contradiction:** Mutually exclusive outcomes are not jointly actual; a detector registering and not registering an event is not accepted as a legitimate empirical result.
- **Excluded middle:** Well-posed experimental questions yield determinate actual outcomes, not "neither A nor not-A."

These are not optional conventions. They underwrite experimental design, data recording, and theory testing. Denying them at the level of actuality would make empirical confirmation and falsification unintelligible.

### (b) From practice to ontology

The long-run success of physics suggests a tight coupling between the logical structure of our theories and the structure of what they describe. If actual states of reality frequently violated L₃, then mappings from theory to world would be systematically unreliable, contradictions could not be quarantined as modeling error or noise, and the distinction between spurious anomaly and genuine discovery would collapse. The best explanation of physics' coherent predictive and explanatory power is that reality's actualizations are themselves L₃-conforming. The Being axiom codifies this: logical structure is not merely an epistemic convenience but an ontological constraint on what can be actual in χ. Even an instrumentalist can grant that any deeper ontology must, at minimum, preserve L₃ at the level of actualized states if it is to underwrite law-governed, testable physics.

### (c) Objection and reply

**Objection.** Paraconsistent logics and some interpretations of quantum mechanics appear to tolerate contradictions or indeterminacy in the world, undermining the Being axiom.

**Reply.** Paraconsistent systems are formal tools for reasoning about inconsistent descriptions without triviality; they do not by themselves show that concrete physical states instantiate genuine A ∧ ¬A in the same respect. Dialetheist views (Priest, 1987, 2006) typically confine true contradictions to special semantic or conceptual domains, not to ordinary physical actualities. Quantum superpositions and contextuality enrich the formalism, but the outcomes delivered as actual, pointer readings, detector clicks, records, are still treated as self-identical and non-contradictory. Even in branching interpretations such as Many-Worlds, each realized branch is internally L₃-respecting.

Thus the Being axiom concerns actualized reality in χ, not the full space of formal descriptions or potentialities. Superpositions, probabilities, and alternative logics can be accommodated, provided no contradictory state is ever actualized in the same respect. By anchoring L₃ ontologically, the Triadic Reality Model secures the logical coherence within which the infinite configurability of I∞ and the principled actualizations of A can meaningfully unfold.

---

## 2.2 Defense of the Axiom of Information (I∞)

**Epistemic Status:** ARGUED

**Axiom of Information (I∞).**
Information in χ is immaterial in kind and admits, in principle, infinite configurability across L₃-respecting structures.

I defend I∞ by showing that physical practice presupposes a distinction between structure and substrate, that the success of highly abstract formalisms supports an ontology of information as such, and that common reductionist objections can be met.

### (a) Implicit in physical practice

Physics routinely treats the same informational structure as multiply realizable across different physical media. A single state description, say a Hamiltonian, a wavefunction, or a bit string, can be instantiated in ink on paper, voltages in a circuit, polarization states of photons, or neural patterns, without loss of its defining content. Error-correcting codes, symmetries, and conservation laws likewise operate over patterns that remain stable through changes of substrate, scale, or representation. This practice presupposes that what matters for explanation is not the particular material bearer but the structured configuration it realizes.

### (b) From practice to ontology

The extraordinary reach of abstract mathematical and informational formalisms suggests that reality is, at a deep level, amenable to description in terms of structure that is not tied to any one material realization. The same differential equations, group structures, or algorithmic schemas apply across wildly different physical systems once the relevant variables are appropriately identified. If information were nothing over and above a specific kind of matter, this cross-domain portability would be mysterious; on the Triadic Reality Model, it is expected. I∞ codifies the ontological claim that informational structure, configured under L₃, is a basic aspect of being in χ, with indefinitely extensible spaces of possible configurations, even though only a finite subset is ever physically realized at a time.

**Minimum characterization.** The TRM requires only this: I∞ is the space of L₃-individuated configurations over which any physically admissible theory's state-space can be represented. "L₃-individuated" means that configurations are distinguished by determinate identity conditions governed by L₃; "representable" means that any configuration specifiable within these conditions belongs to I∞. This floor is neutral among stronger ontological readings.

**Open question (OPEN):** Whether I∞ is best understood as a Platonic realm of abstract objects, a formal representational space with no independent ontological commitment beyond mathematical specifiability, or a third category is not resolved here. The minimum characterization above is all the TRM requires; stronger readings are available as options but are not argued. The precise ontological status of I∞ is left as an open problem for further development.

### (c) Objections and replies

**Objection 1.** "Information is always physical": every instance of information requires a physical carrier, so there is no need to treat information as immaterial or ontologically basic. Moreover, talk of "infinite configurability" seems idealized given finite resources.

**Reply.** That information requires a physical bearer does not collapse information into its bearer any more than the dependence of a melody on air and instruments collapses the melody into a particular violin. The same informational pattern can be realized in arbitrarily many, qualitatively different substrates; what is preserved across realizations is not the stuff but the structure. Calling information "immaterial" in I∞ marks this distinction of kind: informational entities are individuated by L₃-respecting configuration, not by their particular physical composition. As for infinite configurability, the claim is modal rather than aggregate: for any finite stock of realized informational states, further distinct configurations are in principle definable within the L₃-governed space (for example, by refinement, recombination, or extension of existing descriptions). This is no more problematic than treating the real numbers or possible solutions to a field equation as an infinite space, even though only finitely many can ever be written down or instantiated. I∞ thus secures an ontological role for information that is compatible with physical embodiment while irreducible to it, and prepares the ground for understanding how L₃-structured being can support the principled actualization of A in χ.

**Objection 2 (Landauer's Principle).** Landauer (1961) established that erasing one bit of information requires dissipating at least kT ln 2 of energy into the environment. This result, confirmed experimentally (Bérut et al., 2012), demonstrates that information has irreducible energetic cost. If information were immaterial in kind, it would be unclear why its manipulation carries thermodynamic consequences. Landauer's principle seems to show that information is not merely carried by physical substrates but is itself physical: it is the kind of thing that couples directly to energy and entropy. The "immaterial in kind" characterization of I∞ appears to sit in tension with this.

**Reply.** Landauer's principle governs the thermodynamic cost of instantiation and transition, specifically the cost of erasing a physically encoded bit, which requires driving the substrate from a two-state distribution to a single-state distribution and thereby increasing environmental entropy. This is a constraint on how A operates over physically instantiated configurations: it specifies the energetic conditions under which one actualized configuration gives way to another. It says nothing about the modal space of configurations that I∞ comprises.

The distinction is precise. Landauer's principle applies to the erasure of an instantiated bit, a configuration that has been selected as actual by A and encoded in a physical substrate. It does not apply to configurations in I∞ that have not been instantiated. The melody analogy holds here with additional precision: the energetic cost of playing and then silencing a melody (a transition between actualized states) does not constrain the space of melodies that could in principle be composed. Landauer constrains the thermodynamics of A's operation within the instantiated domain. It does not constrain I∞'s configurability as a modal space, because I∞ is not an aggregate of instantiated states but the space of what is in principle representable under L₃. Calling I∞ "immaterial in kind" marks exactly this distinction: I∞ is individuated by configuration structure, not by the thermodynamic properties of any particular physical realization.

**Objection 3 (Holographic Entropy Bounds).** Bekenstein (1973) and Hawking (1975) established that black holes carry entropy proportional to their horizon area, not their volume. The holographic principle, developed further by 't Hooft (1993) and Susskind (1995), generalizes this: the maximum information content of any bounded region of space is finite and proportional to its boundary area in Planck units. If the information content of physical regions is finite and bounded, the claim that I∞ admits "infinite configurability" appears to be ruled out by the physics of spacetime itself. The universe does not have infinite informational capacity; therefore I∞ as characterized is physically inadmissible.

**Reply.** The holographic bound constrains the number of distinguishable physical states that can be simultaneously instantiated within a bounded region, the cardinality of the actualized subset of I∞ within that region at a given moment. It does not constrain I∞'s configurability as a modal space for the same reason that a finite library does not constrain the space of sentences that could in principle be written. The bound is a constraint on A's actualization within physical spacetime regions, not a constraint on what is in principle representable under L₃.

The modal/aggregate distinction is critical here. I∞'s infinite configurability is the claim that for any finite collection of L₃-admissible configurations, further distinct configurations are definable by refinement, extension, or recombination. This is a claim about the structure of the representational space, not a claim that infinitely many configurations are simultaneously instantiated anywhere. The holographic bound addresses simultaneous instantiation within bounded regions; it is entirely silent on the modal extent of the representational space those regions draw from. The real numbers are not bounded by the fact that only finitely many can be physically encoded in any region of spacetime. I∞ is not bounded by holographic constraints for the same reason: the bound applies to the actualized, not to the representable.

A further point: the holographic principle itself is formulated using mathematical structures, including differential geometry, quantum field theory, and entropy functions, that are drawn from a space of representable configurations vastly larger than any finite bounded region can instantiate. The framework that generates and applies the holographic bound presupposes I∞'s configurability at the level of its own mathematical apparatus. The bound constrains what A can instantiate within a region; it cannot consistently be read as constraining I∞ without undermining the mathematical resources needed to state it.

---

## 2.3 Defense of the Axiom of Action (A)

**Epistemic Status:** ARGUED

**Axiom of Action (A).**
Action in χ is the primitive actualization principle by which L₃-structured informational configurations are selected from I∞ as actual, the irreducible ground from which temporal succession, directed change, and dynamical law are derived, not presupposed.

I defend A by showing that physical practice presupposes an underlying notion of directed actualization, that the success of dynamical theories supports an ontology of action as such, that A is irreducible to L₃ and I∞ jointly, and that timeless or purely static views do not undercut but presuppose this primitive.

### (a) Implicit in physical practice

Physical theories, as used in experiment and engineering, are centrally about transitions: how one state gives rise to another under specified conditions. Dynamical laws (equations of motion, evolution operators, transition amplitudes) are framed to tell us what will happen given an initial configuration, constraints, and interactions. Experimental protocols likewise presuppose that interventions, including preparations, couplings, and measurements, can reliably bring about changes from one regime of behavior to another. In practice, we distinguish mere description of a static configuration from the realization of a process that carries the system from one state to another. This pervasive focus on change and intervention tacitly assumes that action is not an illusion but a fundamental feature of how reality unfolds in χ.

### (b) From practice to ontology

The remarkable success of dynamical theories suggests that the world is not only structurally intelligible but processual: it is ordered in such a way that structured configurations can be reliably transformed according to stable principles. If change were merely apparent, or wholly reducible to a static totality without any genuine modality of "can bring about," it would be difficult to explain why interventionist reasoning, control theory, and causal modeling work so well. A codifies the ontological claim that there is a real fact of the matter about what follows from what under given conditions: action is the primitive by which L₃-respecting informational structures are selected into actuality and from which their succession is derived. Adding A to the framework does not add an extra "force" on top of being and information; A is the irreducible mode in which being and information enter into concrete actuality at all.

### (c) The irreducibility argument

L₃ and I∞ jointly specify what configurations are admissible and what configurations are representable. They do not, jointly or separately, specify which admissible configurations are actual. Without A, χ collapses to a static inventory of L₃-coherent possibilities in I∞, a space of candidates with no selection among them. Equally, A without L₃ is selection without admissibility criteria: arbitrary actuation with no principled constraint. And A without I∞ is selection over an empty domain. Each pair without the third is incoherent as a physical foundation. The three are therefore irreducible co-primitives: none is derivable from the other two, and the failure of any one renders the remaining two insufficient for grounding physics.

### (d) Objections and replies

**Objection 1.** On block-universe or timeless formulations, all events are equally real in a single four-dimensional structure; talk of "action" or "becoming" appears derivative or even illusory. If the universe is fundamentally static, why posit action as basic?

**Reply.** A accommodates such views precisely because A is not defined as temporal process. A is the primitive actualization principle, the ground from which temporal succession is derived, not a process occurring within time. Even in a block universe, there is an objective asymmetry between configurations that stand as input conditions and those that stand as outcomes under the dynamical equations. This asymmetry is not temporal in origin; it is the structural signature of A operating over I∞ under L₃. Timeless formalisms still encode lawful ordering relations among configurations, the ordering structure that supports counterfactuals and interventionist descriptions. A captures this modal, ordering aspect at the primitive level, prior to and generative of the temporal parameter that physics subsequently derives. In this sense, A is not a projection of human temporality onto a static world but the pre-temporal ground from which the very notion of temporal order emerges within χ.

**Objection 2.** The Wheeler-DeWitt equation of canonical quantum gravity (DeWitt, 1967) presents a sharper challenge. In that formalism, the wavefunction of the universe Ψ satisfies Ĥ|Ψ⟩ = 0 and has no time argument at all. Time is not merely derived; it is absent as a fundamental category. The Page-Wootters mechanism then recovers an effective internal time from entanglement correlations between a clock subsystem and the rest of the universe, entirely within the quantum formalism. If time emerges from internal correlations in I∞ without any appeal to A, the pre-temporal characterization of A appears to be doing no work. What does A contribute that the Wheeler-DeWitt formalism plus Page-Wootters does not already provide?

**Reply.** The Wheeler-DeWitt challenge is genuine and the sharpest live objection to A's pre-temporal characterization. The response turns on distinguishing two questions that the objection conflates: the question of temporal structure, and the question of actuality.

Wheeler-DeWitt removes external time. It does not remove the actual/non-actual distinction. The wavefunction Ψ that appears in Ĥ|Ψ⟩ = 0 is the wavefunction that obtains, not one among indefinitely many L₃-admissible solutions to that equation. The Wheeler-DeWitt equation, like any physical equation, has a solution space: a class of wavefunctions satisfying the constraint. That solution space is a subspace of I∞. But physics is not the study of the solution space in the abstract; it is the study of the configuration that is actual. The question of why this Ψ rather than another admissible Ψ, why this point in the solution space is instantiated, is precisely what A addresses. Wheeler-DeWitt is silent on this question. It specifies admissibility (via L₃ operating over I∞); it does not specify actuality. A is the primitive that closes that gap.

The Page-Wootters mechanism makes the point more precise, not less. Page and Wootters (1983) show that conditional on the clock subsystem registering a particular value, the remainder of the universe is in a definite state, and that scanning across clock values recovers an effective time-evolution. This is an internal relational structure derivable within I∞ from the entanglement geometry of Ψ. But notice what the mechanism presupposes: it presupposes that Ψ is actual. The entanglement correlations from which internal time is derived are features of the wavefunction that obtains. If no Ψ were actual, if the universe remained an undifferentiated space of admissible solutions, there would be no entanglement structure to derive time from. Page-Wootters derives temporal structure from A's output (the actual Ψ), not as a substitute for A. The mechanism is downstream of actuality, not prior to it.

A therefore operates at a level the Wheeler-DeWitt formalism does not reach: the distinction between the solution space of the constraint equation (a subspace of I∞ filtered by L₃) and the configuration that is actual (the output of A). Timeless quantum gravity removes external time and recovers internal relational time from correlations, both of which are operations within χ. It does not dissolve the actual/non-actual distinction that A marks. That distinction is presupposed by any physical formalism, including timeless ones, that claims to describe what the universe is rather than merely what it could be.

### (e) Modal status of A

**Epistemic Status:** ARGUED

Three modal categories present themselves as candidates for characterizing A's necessity: metaphysical necessity, nomological necessity, and transcendental necessity. The first two are inadequate. The third is the correct characterization, and it is the same modal category that governs L₃.

**Why not metaphysical necessity.** A claim is metaphysically necessary if it holds in all possible worlds, if its negation is impossible in the broadest modal sense. Establishing this for A would require showing that a world with no actualization primitive is not merely physically impossible but impossible in every sense. That is a stronger claim than the TRM requires and harder to defend, since the conceivability of a purely modal universe, a space of admissible configurations with none selected as actual, does not obviously generate a logical contradiction. Metaphysical necessity is available as a position but is not argued here.

**Why not nomological necessity.** A claim is nomologically necessary if it holds in all worlds sharing the laws of this world. This is too weak for A's foundational role. Nomological necessity subordinates A to physical law; it makes A necessary because the laws happen to require it. But A is supposed to be prior to and generative of physical law, not dependent on it. A foundation cannot be nomologically necessary without circularity: the laws would have to be in place before A, but A is what makes lawful actualization possible. Nomological necessity inverts the grounding direction.

**Transcendental necessity.** A claim is transcendentally necessary if its denial is performatively self-undermining, such that any coherent assertion of its negation already presupposes the claim. This is the modal category that governs L₃ in the TRM: one cannot coherently assert a contradiction without already invoking non-contradiction; the denial of L₃ presupposes L₃ at the level of the assertion itself.

The same structure applies to A. Consider any attempt to assert that the actual/non-actual distinction does not obtain, that nothing is actual rather than merely possible. That assertion is itself an actualization: it is the claim that this state of affairs (no actuality) is the case. But "being the case" just is being actual. The denial of A presupposes A at the level of the denial. The assertion that nothing is actual is either itself actual, in which case something is actual and A is instantiated, or it is not actual, in which case it is merely a possibility among others and carries no force as a denial. Either way, the denial fails. A's negation is not merely false; it is unsayable without self-defeat.

This is a third modal category stronger than nomological necessity and more precisely grounded than metaphysical necessity as standardly characterized. It does not require surveying possible worlds. It requires only attending to what any coherent assertion about the world presupposes. Any physical theory, any claim about what is or is not the case, any denial of A itself: all presuppose that something is actual rather than merely possible. A is transcendentally necessary in this sense: not because we cannot conceive of its absence, but because we cannot coherently assert its absence without instantiating it.

**Relation to L₃.** The parallel with L₃'s transcendental necessity is precise but not identical. L₃'s transcendental necessity runs through the structure of coherent assertion: denying non-contradiction presupposes non-contradiction in the denial. A's transcendental necessity runs through the structure of actuality itself: denying that anything is actual is itself an actual state of affairs or it is nothing. Both are cases where the denial is self-undermining, but through different routes. L₃'s route is logical; A's route is ontic. Together they establish that the two most basic primitives of χ, the admissibility condition and the actualization principle, are not contingent postulates but transcendentally necessary features of any framework that can coherently describe a world.

---

## 2.4 The Triadic Reality Model

**Epistemic Status:** ARGUED (co-primitivity formally developed in §2.5; individual axioms argued in §§2.1–2.3)

I take Triadic Reality to be characterized by the ordered triple

$$\chi \equiv [L_3 : I_\infty : A]$$

where each component is axiomatic, irreducible, and mutually co-constitutive.

The individual axioms have been defended in §§2.1-2.3. Their co-primitivity, that none derives from the other two and that the removal of any one leaves the remaining pair insufficient as a physical foundation, is established in §2.5 through six pairwise-collapse cases.

**Necessity levels.** The three primitives are not defended at the same epistemic strength, and conflating their modal statuses would be a philosophical error. The following table makes the distinctions explicit.

| Primitive | Pragmatic necessity | Inference to best explanation | Transcendental necessity |
|-----------|:---:|:---:|:---:|
| **L₃** | ✓ Presupposed in all experimental design, data recording, and theory testing (§2.1a) | ✓ Best explanation of universal L₃-conformity at the record level (§2.1b) | ✓ Denial of non-contradiction presupposes non-contradiction in the denial; self-undermining through logical route (§2.1c) |
| **I∞** | ✓ Physics presupposes distinguishable states and representable configurations (§2.2a) | ✓ Best explanation of cross-domain portability of informational structure (§2.2b) | — Modal status OPEN (§2.2b); minimum characterization established but transcendental argument not claimed |
| **A** | ✓ All dynamical theories presuppose transitions and actualization sequences (§2.3a) | ✓ Best explanation of interventionist success and causal modeling (§2.3b) | ✓ Denial that anything is actual is itself actual or carries no force; self-undermining through ontic route (§2.3e) |

Three points of clarification. First, pragmatic necessity (that coherent physical practice presupposes the primitive) is the weakest claim and is established for all three. Second, the abductive argument from practice to ontology (§§2.1b, 2.2b, 2.3b) is inference to the best explanation: strong but defeasible. Third, transcendental necessity, where the denial is performatively self-undermining, is the strongest claim and is argued only for L₃ and A, through distinct routes (logical and ontic respectively). I∞ is defended at the first two levels; its transcendental status remains an open problem. The paper does not claim that I∞ is transcendentally necessary, and a reader who accepts the pragmatic and abductive cases for I∞ while withholding judgment on its modal status loses nothing essential to the argument through §6.

---

## 2.5 Irreducibility of the Triad

**Epistemic Status:** ARGUED

The claim that L₃, I∞, and A are irreducible co-primitives requires more than asserting that each is necessary. It requires showing that no proper subset suffices, that each pair, taken without the third, either fails to constitute a coherent formal object at all or, where it does, fails specifically as a foundation for physics. The six cases divide into two tiers. The full arguments are developed in Appendix C; the results are summarized here.

| Case | Pair | Tier | Failure Mode |
|------|------|------|--------------|
| 1 | L₃ without I∞ | Tier 1: Cannot ground a physical framework | Constraint with no domain to range over |
| 2 | A without I∞ | Tier 1: Cannot ground a physical framework | Selection with no candidates |
| 3 | I∞ without L₃ | Tier 2: Cannot perform the required function | No admissibility: cannot distinguish physical from non-physical |
| 4 | I∞ without A | Tier 2: Cannot perform the required function | No actuality: static modal space, no dynamics or observables |
| 5 | L₃ without A | Tier 2: Cannot perform the required function | No selection among admissibles: candidacy without actuality |
| 6 | A without L₃ | Tier 2: Cannot perform the required function | No principled constraint: actuals produced arbitrarily |

The Tier 1 cases (Cases 1-2) show that I∞ is load-bearing for both L₃ and A: neither can ground a physical framework without a domain. A critic might object that constraint schemata or selection functions can be intensionally specified without a fully developed ontological domain; this is correct at the formal level, but the question is not whether a logician can write down a constraint without specifying its domain, but whether such a pairing can serve as a foundation for physics. It cannot: physics requires that constraints range over something determinately structured. The Tier 2 cases (Cases 3-6) show that each primitive performs a distinct, non-redundant function: L₃ provides admissibility, I∞ provides the configuration domain, A provides actualization. No two together suffice to perform the third's work.

To illustrate the argument's force, consider the representative case. **Case 4: I∞ without A.** A constrained possibility space, I∞ filtered by L₃, is a coherent formal object: the space of L₃-admissible configurations. But without A, nothing in that space is actual. Every admissible configuration is equally a candidate and equally unactualized. The result is a static modal structure: rich in possibility, empty of actuality. Physics is not a theory of what could be actual; it is a theory of what is actual and how actuality unfolds. No actualization principle means no dynamics, no observables, no empirical content. The formal object is coherent; it simply has nothing to say about the physical world.

The triad is therefore genuinely minimal: it cannot be reduced without loss, and it cannot be extended by decomposing any of its members into further primitives at the same level without either collapsing back into the triad or adding redundancy.

One further point deserves explicit statement. The irreducibility argument does not establish that the three primitives are metaphysically independent in every sense: it establishes that they are functionally irreducible as a physical foundation. Whether L₃ has a deeper modal status (transcendental necessity, as argued in §2.1) or whether A has an ontological ground beyond its role as actualization primitive are questions that remain open and are pursued in companion work. The irreducibility claim here is precisely scoped: within the framework of χ as a foundation for physics, no proper subset of {L₃, I∞, A} suffices.

---

## 3. Physical Theories as Triadic Models in χ

*Sections 3 and 4 are exemplifications, not confirmations. They show that existing physics is compatible with the triadic template and can be naturally redescribed within it. Compatibility is necessary for the TRM's credibility but does not by itself constitute evidence for the framework's necessity. The evidential weight comes from the transcendental arguments of §2 and the bridge argument of §6, not from the fact that known theories fit the template.*

### 3.1 The Triadic Template

**Epistemic Status:** ESTABLISHED (definitional template); ARGUED (claim that all admissible physical theories instantiate the template)

On the Triadic Reality Model, a physical theory is an organized way of instantiating the triad, not simply a set of equations.

$$\chi \equiv [L_3 : I_\infty : A]$$

More precisely, any concrete physical theory T can be schematically represented as a triple

$$T \equiv \langle \mathcal{L}, \mathcal{S}, \mathcal{D} \rangle$$

where each component corresponds to one aspect of χ.

- **L (Logical layer)** instantiates L₃. It comprises the theory's admissible statements, inference rules, and consistency conditions. Here we require that theoretical claims about states and observables be L₃-respecting: they obey identity, non-contradiction, and excluded middle in the sense articulated in §2.1. This layer fixes what counts as a well-formed question and a determinate answer within the theory.

- **S (State space)** instantiates I∞. It is the structured space of possible configurations: phase spaces, Hilbert spaces, configuration manifolds, or more abstract informational state spaces. These encode the theory's informational possibilities, including which distinct states it can represent, how finely it can distinguish them, and how they can be combined or refined. S is where the in-principle infinite configurability of I∞ shows up in concrete, mathematically regimented form.

- **D (Dynamics)** instantiates A. It collects the dynamical laws, evolution operators, transition rules, or update maps that specify how states in S are lawfully actualized and succeed one another. D captures the theory's instantiation of the action primitive: given a configuration (plus boundary conditions, interactions, or interventions), it determines which subsequent configurations are admissible and with what modal status (necessary, possible, probable).

Under this template, a physical theory is triadic by construction: L ensures logical coherence of description, S supplies a rich informational repertoire of possible states, and D encodes how those states are actualized and ordered. Different theories correspond to different specific choices of L, S, D within the general constraints set by [L₃ : I∞ : A].

---

## 3.2 Classical Mechanics in χ

**Epistemic Status:** ARGUED

Classical mechanics provides a clear example of a triadic model

$$T_{\text{CM}} = \langle \mathcal{L}_{\text{CM}}, \mathcal{S}_{\text{CM}}, \mathcal{D}_{\text{CM}} \rangle$$

realizing χ ≡ [L₃ : I∞ : A].

**Logical layer L_CM (instantiating L₃).** Classical mechanics is formulated in a classical logical framework: propositions about particle positions, momenta, energies, and trajectories are taken as either true or false for a given state, and contradictions are excluded. Standard presentations of Hamiltonian mechanics assume that each system has a well-defined state at each time and that mutually exclusive properties (e.g., being at different points in configuration space) are not jointly actual.

**State space S_CM (instantiating I∞).** The state space of an N-degree-of-freedom classical system is its 2N-dimensional phase space, with coordinates (qⁱ, pᵢ) specifying generalized positions and momenta. This phase space is typically taken as a smooth manifold supporting infinitely many distinct states and can be refined arbitrarily (e.g., by specifying values to higher precision). This realizes the I∞ idea: an in-principle infinite repertoire of logically well-formed configurations from which actual states are selected.

**Dynamics D_CM (instantiating A).** The dynamics are given by Hamilton's equations (or equivalently Lagrange's equations) specifying how a point in phase space evolves along a trajectory under the Hamiltonian H(q,p,t). For given initial data, these equations determine the actualization sequence, defining lawful ordering relations among configurations, an explicit formalization of A in χ. The flow on phase space, Liouville's theorem, and related structures encode how informational configurations are actualized and ordered under the theory's laws.

Classical mechanics exemplifies all three primitives: L₃-governed logic, I∞-like continuous state space, A-type actualization via Hamilton's equations.

---

## 3.3 Quantum Mechanics in χ

**Epistemic Status:** ARGUED

Quantum mechanics offers a more intricate, but still triadic, realization of

$$T_{\text{QM}} = \langle \mathcal{L}_{\text{QM}}, \mathcal{S}_{\text{QM}}, \mathcal{D}_{\text{QM}} \rangle$$

within χ ≡ [L₃ : I∞ : A].

**Logical layer L_QM (instantiating L₃).** At the formal level, propositions about all possible quantum measurements form a non-Boolean structure: the lattice of closed subspaces of Hilbert space is orthomodular rather than distributive, and "quantum logic" can be seen as a generalization or alternative to classical propositional logic in that arena. Nonetheless, the Triadic Reality Model locates L₃ at the level of actualized outcomes. Each concrete experimental context yields definite results, including particular detector clicks, pointer positions, or classical records, that are treated as unambiguously something-rather-than-nothing, never as both A and not-A in the same respect. In this sense, L_QM respects the Being axiom (§2.1): while the space of possible questions and projection operators may have a non-classical structure, the realized measurement outcomes are always registered and reasoned about in an L₃-governed way.

**State space S_QM (instantiating I∞).** The quantum state space is typically a complex Hilbert space (or a suitable generalization), with pure states represented by rays and mixed states by density operators (Masanes and Müller, 2011). This space is extraordinarily rich: superpositions, entangled states, and continuous degrees of freedom together provide an effectively unbounded repertoire of distinct informational configurations. From the standpoint of the Triadic Reality Model, S_QM is a canonical realization of I∞: it encodes an in-principle infinite space of L₃-well-formed possibilities (e.g., different wavefunctions, entanglement structures, or spectral decompositions), only a tiny subset of which are ever actualized in a given experiment. The immaterial character of information appears here as the structural role of the Hilbert space itself: what matters for quantum description are relational amplitudes and inner products, not the particular substrate in which they are represented.

**Dynamics D_QM (instantiating A).** Quantum dynamics is usually presented in two interconnected ways. Between measurements, the state evolves unitarily according to the Schrödinger equation (or its relativistic or field-theoretic counterparts), defining a continuous, law-governed actualization sequence on S_QM. At measurement, standard formulations introduce a stochastic transition rule, whether collapse, projection, or an effective update via decoherence and conditioning, that selects a definite outcome from among the available possibilities. Both aspects express A: they specify how informational configurations are lawfully ordered and how, under appropriate conditions, one configuration is actualized rather than another. Different interpretations of quantum mechanics vary in how they model this process, including branching worlds (Wallace, 2012), hidden variables, relational updates, and purely epistemic state changes, but on the present framework, they can all be read as competing accounts of how A operates over I∞ while preserving L₃-conformant outcomes.

Quantum mechanics fits the triadic template. It differs from classical mechanics not by abandoning L₃ but by enriching I∞ (Hilbert-space structure) and complicating A (probabilistic actualization).

---

## 4. Experimental Exemplifications

*The analyses below show how the TRM redescribes key quantum phenomena. They are interpretive exemplifications: they demonstrate compatibility and illustrative power, not derivation or confirmation. A rival meta-ontology might redescribe these same phenomena equally well. The TRM's claim to superiority rests on the arguments of §§2 and 6, not on these exemplifications alone.*

### 4.1 The Double-Slit Experiment in χ

**Epistemic Status:** ARGUED

The double-slit experiment is often taken to showcase quantum "weirdness": single quanta sent one by one build up an interference pattern, yet any attempt to determine which slit they pass through destroys that pattern. In the Triadic Reality Model, this behavior can be analyzed cleanly in terms of L₃, I∞, and A.

### (a) I∞: Informational structure of the setup

With both slits open and no which-path detector in place, the relevant informational state is a superposition of "through slit 1" and "through slit 2," represented as a single quantum state defined over a configuration space that includes both paths. The state encodes an extended pattern of amplitudes across many possible detection points on the screen, each corresponding to a distinct potential outcome. The interference fringes arise from the structured way these amplitudes combine, an informational property independent of any particular carrier.

### (b) A: Action as actualization sequence

Between source and screen, the state evolves unitarily according to D_QM (e.g., a Schrödinger-type propagation through the slits), implementing A as a lawful ordering of informational configurations. At the detector, this yields a single localized click: the point at which one of the many I∞-encoded possibilities is selected as actual. Over many runs, the pattern of these L₃-definite events approximates the squared amplitude distribution, revealing the underlying actualization structure of A without ever requiring an actually contradictory state.

When a which-path detector is introduced at the slits, A changes: the interaction entangles path information with the apparatus, effectively reconfiguring S_QM so that the interference-producing superposition is no longer available at the screen. The resulting actualization yields a different distribution of outcomes, two broad humps instead of fringes, reflecting a different lawful mapping from initial to final informational structures.

### (c) L₃: Actualized outcomes remain classical

Throughout, L₃ governs actualized reality in χ. Each detected event is recorded as "hit at position x" rather than "both a hit and not a hit at x," and each which-path measurement (when present) yields one slit or the other, not both in the same respect. The apparent paradox, that the particle goes through both slits and only one slit, arises from conflating the I∞-level superposed informational structure with the L₃-constrained actual outcomes delivered by A. On the triadic picture, the wavefunction encodes a rich, globally defined informational possibility structure, while the realized detection events remain strictly L₃-conformant.

---

## 4.2 Bell-Type Correlations in χ

**Epistemic Status:** ARGUED

Bell experiments involve pairs of entangled systems sent to distant measurement stations, where experimenters choose between different settings and record binary outcomes. Quantum mechanics predicts and experiments confirm correlations between these outcomes that violate Bell inequalities, ruling out any theory that combines locality with a classical-style hidden-variable realism.

### (a) I∞: Entangled informational structure

Before measurement, the joint system is described by an entangled state (for example, a spin singlet), represented as a vector or density operator in a tensor-product Hilbert space. This state encodes an intricate pattern of conditional probabilities for all combinations of measurement settings and outcomes at the two wings. The informational richness here is a paradigm instance of I∞: a single global quantum state compactly encodes an infinite family of possible outcome correlations across many measurement choices, none of which are yet actual.

### (b) A: Non-factorizable actualization

When Alice and Bob choose measurement settings and register outcomes, D_QM maps the prior entangled informational structure into a pair of definite results, with joint statistics given by the Born rule. From the χ-perspective, action here has two aspects: the local interactions at each detector (coupling system to apparatus) and the global constraint that these outcomes must jointly realize the correlations encoded in the initial entangled state. The resulting violation of Bell inequalities shows that no local hidden-variable dynamics, defined on a classical configuration space, can reproduce the same mapping from informational possibilities to outcome statistics. But A need not be conceived as superluminal signaling; it is the lawful, non-factorizable actualization of pairs of outcomes from a single, non-separable informational configuration, A operating globally over I∞, constrained by L₃.

### (c) L₃: Definite, non-contradictory outcomes

Despite the nonlocal-looking correlations, each run of a Bell experiment yields a pair of definite, classical records: "Alice measured +1 at setting aᵢ; Bob measured −1 at setting bⱼ," and never "both +1 and −1 at once in the same respect." The violation of Bell inequalities concerns the statistics of these L₃-respecting outcomes across many trials, not the logical status of any individual outcome. On the Triadic Reality Model, Bell's theorem constrains what forms I∞ and A can take, ruling out local hidden-variable realizations of the triad, but it does not require abandoning the Being axiom (§2.1). The actualized events remain strictly L₃-conformant; what changes is our understanding of the deep informational structure and actualization principles of χ that generate their correlations.

### (d) What TRM explains that interpretations take as brute

Every viable interpretation of Bell correlations shares three structural features: (i) definite, non-contradictory outcomes at each wing; (ii) a global informational state that encodes the full correlation structure prior to measurement; and (iii) an actualization mechanism that produces joint outcomes respecting those correlations. Many-Worlds achieves this through branching of a unitarily evolving state: the entangled state encodes correlations in $I_\infty$, decoherence-selected branches deliver $L_3$-conformant records, and branch realization instantiates $A$. Bohmian mechanics achieves it through a guiding field over configuration space: the wavefunction encodes correlations in $I_\infty$, particle positions deliver definite outcomes under $L_3$, and the guidance equation instantiates $A$. Collapse theories achieve it through stochastic reduction: the quantum state encodes correlations in $I_\infty$, collapsed outcomes are $L_3$-conformant, and the collapse mechanism instantiates $A$.

Each interpretation models these three commitments differently, but none can dispense with any of them. The TRM explains why: the triadic structure $[L_3 : I_\infty : A]$ is not interpretation-specific but a necessary condition on any framework capable of accommodating Bell correlations. The non-factorizability of quantum correlations constrains how $A$ operates over $I_\infty$, but the requirement that actualized outcomes be $L_3$-conformant is invariant across all interpretations. An interpretation that could dispense with any of the three, for example, by producing genuinely contradictory actualized outcomes, or by operating without a global informational state, would not be a competing interpretation of Bell correlations but a framework that cannot reproduce them.

---

## 5. Falsifiability and Empirical Traction

**Epistemic Status:** ARGUED

A transcendental foundation is not directly falsifiable by single experiment. That is not a defect peculiar to the TRM: it is a feature of any framework operating at the level of necessary conditions for physical inquiry rather than within physical inquiry. The relevant question is not whether χ can be falsified by a single experimental outcome but whether it makes substantive constraints on admissible theories, whether those constraints are checkable, and how the framework gains and loses empirical support indirectly. Three versions of the falsifiability challenge are addressed in turn.

### 5.1 The Accommodation Objection

**Objection.** The triadic template T ≡ ⟨L, S, D⟩ is so general that any physical theory can be mapped onto it. Classical mechanics fits. Quantum mechanics fits. Presumably any future theory will fit. A framework that accommodates everything rules out nothing and therefore says nothing.

**Reply.** The accommodation objection conflates scope with vacuity. That χ correctly maps all known physical theories is confirmation of a structural claim: that all physically admissible theories share the triadic form [L₃ : I∞ : A]. This claim has genuine content because it is not trivially true. A theory whose L-layer permitted actualized contradictions would not fit. A theory with no admissibility condition on its S-layer, no distinction between physically instantiable and non-instantiable configurations, would not fit. A theory whose D-layer described no actualization principle, only a static mapping between possibility structures, would not fit.

The accommodation objection would have force if the triadic template placed no constraints on the internal structure of L, S, and D. But it does. L must be L₃-respecting at the level of actualized outcomes; non-Boolean possibility structures are permitted in S, but actualized records must be Boolean. S must be a space of L₃-admissible configurations with genuine informational structure; arbitrary formal spaces without admissibility conditions do not qualify. D must instantiate A; it must specify an actualization principle, not merely a logical mapping. These are non-trivial structural requirements, and theories that violate them are excluded.

### 5.2 What χ Rules Out

The constraints χ places on admissible physical theories are precise enough to exclude recognizable theoretical positions.

**Theories with actualized L₃-violations.** Any theory that predicts stable, reproducible experimental outcomes that are simultaneously true and false in the same respect, where a detector both registers and does not register an event as a matter of physical fact rather than measurement error, is excluded by the Being axiom (§2.1). No such outcome has been experimentally confirmed. Every attempt to construct a dialetheist physics has either confined true contradictions to formal or semantic domains or has failed to produce experimentally distinguishable predictions. The empirical universality of L₃-conformant outcomes is the strongest ongoing confirmation of the Being axiom, and a confirmed L₃-violating outcome would falsify it directly.

**Theories with unconstrained state spaces.** Any theory whose state space carries no admissibility condition, in which no distinction is made between physically instantiable and non-instantiable configurations, is excluded by I∞ as characterized in χ. This rules out purely formal theories that treat all mathematical structures as equally physical without a selection principle. It also places a constraint on quantum gravity proposals: any approach that treats the full superspace of 3-geometries as equally actual, rather than as a possibility space from which actuals are selected, fails to instantiate A and is therefore inadmissible within χ.

Tegmark's Mathematical Universe Hypothesis (Tegmark, 2008) provides an instructive contrast. The MUH holds that all mathematical structures exist physically, that mathematical existence and physical existence are identical. This shares with χ the conviction that structure is fundamental, but diverges at precisely the point that matters: actualization. The MUH has no selection principle; every consistent mathematical structure is equally real. χ requires A as a primitive precisely because possibility alone, however structured, does not yield actuality. The MUH conflates I∞ with A_Ω, treating the space of possibilities as identical with what obtains. On the TRM, this is a category error: it mistakes the domain on which actualization operates for its output. Any framework that eliminates the actual/possible distinction in this way is excluded by χ's insistence on A as irreducible.

**Purely epistemic interpretations without ontic actualization.** Interpretations of quantum mechanics that treat the quantum state as purely a state of knowledge, with no ontic actualization event of any kind, are excluded by A as a primitive. This is not a prejudgment of the measurement problem. It is the claim that any adequate physical theory must distinguish what is actual from what is merely possible or probable, and that distinction requires an actualization principle at some level. Interpretations that deny any such principle, rather than relocating it, are excluded. QBism in its strongest form, where quantum states are purely subjective probability assignments with no ontic correlate (Fuchs, Mermin and Schack, 2014), falls into this class.

### 5.3 Indirect Empirical Support and Vulnerability

χ gains empirical support indirectly through two channels.

**Downstream derivations.** If the derivation chain grounded in χ, from the triadic primitives through admissibility conditions to Hilbert space structure, Born rule, and dynamical law, yields those structures as consequences rather than postulates, then every experimental confirmation of quantum mechanics is indirect confirmation of χ. The framework earns empirical credibility not by making novel first-order predictions but by showing that the confirmed structure of physics follows from its primitive commitments. A derivation chain that fails, that cannot recover quantum structure from χ without importing ungrounded additional postulates, would constitute evidence against χ as a sufficient foundation.

**Universal L₃-conformity at the record level.** Every experimental record produced by physics to date is L₃-conformant at the level of actualized outcomes. No stable, reproducible, publicly verifiable record has instantiated a genuine contradiction, a failure of identity, or a violation of excluded middle in an actualized result. This universality is not trivial: it spans wildly different physical regimes, energy scales, and experimental designs. Its best explanation, on the TRM, is that L₃-conformity is a constitutive condition on physical instantiation, not a contingent regularity. An alternative explanation, that L₃-conformity is a methodological artifact of how we design experiments and record results, is available but faces the objection that it cannot explain why no experimental design, however exotic, has ever produced a stable L₃-violating record.

**Vulnerability conditions.** χ would be undermined by any of the following: a confirmed, stable, reproducible experimental outcome that is genuinely L₃-violating at the actualized record level; a physical theory that is empirically superior to quantum mechanics and cannot be mapped onto ⟨L, S, D⟩ without forcing; or a demonstrated derivation of quantum structure from a strictly smaller primitive set, showing that one of {L₃, I∞, A} is eliminable without loss. None of these conditions has been met. Their continued non-occurrence is not proof of χ but is consistent with and supportive of it.

The TRM thus occupies the same epistemic position as other transcendental foundations in physics: not directly falsifiable by experiment, but constrained, non-trivial, and vulnerable to indirect disconfirmation through the failure of its downstream derivations or the confirmation of outcomes it structurally excludes.

---

## 6. The Bridge Argument

**Epistemic Status:** ARGUED

The preceding sections have established three irreducible co-primitives (§§2.1-2.3), their co-constitutive unity as $\chi \equiv [L_3 : I_\infty : A]$ (§2.4), their irreducibility (§2.5), their instantiation in known physics (§3), and the falsifiability conditions on the framework (§5). The question that remains is: what does $A$ produce when operating on $I_\infty$ under the constraints of $L_3$? This section derives the answer.

### 6.1 The Grounding Sequence

The core argument proceeds in three steps.

**Step 1: The Primitive Ontology**

$$\chi \equiv [L_3 : I_\infty : A]$$

This is not a postulate but the conclusion of §§2.1-2.5: these primitives are each transcendentally necessary (§§2.1, 2.3e), and they form a co-constitutive, irreducible unity (§§2.4-2.5).

**Step 2: The Grounding Relation**

$$\chi \vdash A_\Omega$$

From the primitive ontology, actuality follows. The turnstile ($\vdash$) signifies ontological grounding, not logical derivation in the narrow sense. Grounding here denotes constitutive dependence: actuality exists *in virtue of* the primitive ontology rather than being logically deduced from it.

$A_\Omega$ designates the actualized domain: the totality of what obtains. The subscript $\Omega$ marks actualization throughout, distinguishing configurations that obtain from those that are merely possible within $I_\infty$.

This step is secured by the argument of §2.3: $A$ is the primitive of obtaining, and its operation on $I_\infty$ under $L_3$ constitutes actuality.

**Step 3: The Bridge Equation**

$$A_\Omega = L_3(I_\infty)$$

The actualized domain coincides with the logically admissible informational configurations of the total possibility space. The identity has two inclusion directions, of sharply different difficulty.

**Direction 1 (easy): $A_\Omega \subseteq L_3(I_\infty)$**

Whatever is actualized is $L_3$-admissible. The argument:

1. $A$ operates on $I_\infty$ (there is nothing outside $I_\infty$ for $A$ to operate on; §2.2).
2. $L_3$ constrains which configurations are admissible (§2.1).
3. $A$ can only actualize configurations admissible under $L_3$ (contradiction cannot obtain; §§2.1b, 2.5 Case 6).
4. Therefore, every actualized configuration is in $L_3(I_\infty)$.

This direction is nearly uncontroversial. A reader who grants the three primitives and the irreducibility argument of §2.5 has already accepted it: actuality cannot violate logic.

**Direction 2 (hard): $L_3(I_\infty) \subseteq A_\Omega$**

Every $L_3$-admissible configuration of $I_\infty$ falls within the actualized domain. This is the plenitude direction, and it is where the substantive philosophical work occurs.

The argument for this direction proceeds as follows. $I_\infty$ is defined (§2.2) as the complete space of all representable configurations whose mutual distinguishability is $L_3$-admissible. $A$ operates over all of $I_\infty$; there is nothing outside it (§2.5, Cases 1-2). For any configuration $c \in L_3(I_\infty)$, $c$ satisfies the sole admissibility criterion, conformity with $L_3$, and inhabits the only domain over which $A$ operates. There is therefore no coherent ground on which $A$ could systematically exclude $c$ from the actualized domain. Exclusion would require some further constraint beyond $L_3$ that disqualifies $c$, but no such constraint exists within the primitive ontology $\chi$: $L_3$ is the complete admissibility criterion, and $I_\infty$ is the exhaustive possibility space.

The claim is not that all admissible configurations are simultaneously actual in the sense of concurrent physical instantiation; $A$ selects, and temporal or modal structure may distribute actualizations. The claim is structural: $A_\Omega$ and $L_3(I_\infty)$ coincide as domains because the two characterizations, "what can obtain" and "what is $L_3$-admissible in $I_\infty$," pick out the same totality. *[Epistemic status: ARGUED]*

### 6.2 Status of the Bridge Equation

The bridge equation compresses three distinct claims. Under pressure, they must be separated with precision, because a reader who accepts the first two may still resist the third, and the paper's argumentative integrity depends on knowing exactly where the weight falls.

**Claim 1: Grounding.** $\chi \vdash A_\Omega$ *[Epistemic status: ARGUED]*

The primitive ontology $\chi = [L_3 : I_\infty : A]$ grounds the actualized domain. This is the transcendental claim: actuality exists *in virtue of* the interaction of the three primitives. Without logical constraint, no admissibility conditions. Without the informational domain, nothing to constrain. Without actualization, no transition from possibility to obtaining. The turnstile ($\vdash$) signifies ontological grounding, not logical derivation: constitutive dependence, not deductive entailment.

This claim is secured by §§2.1-2.5. A reader who grants the necessity of the three primitives and their irreducibility has already accepted it. The remaining question is what the grounded domain looks like.

**Claim 2: Characterization.** $A_\Omega \subseteq L_3(I_\infty)$ *[Epistemic status: ARGUED, nearly uncontroversial given Claim 1]*

Whatever is actualized is $L_3$-admissible. This is the result of Direction 1 in §6.1: $A$ operates on $I_\infty$ (there is nothing else), $L_3$ constrains admissibility, and contradiction cannot obtain. Actuality cannot violate logic. A reader who grants the three primitives has, in effect, already accepted this: it says only that $A$ respects the sole constraint that governs it.

Characterization tells us the *form* of the actualized domain. It does not yet tell us its *extent*. A critic can accept both Claims 1 and 2 while maintaining that $A_\Omega$ is a proper subset of $L_3(I_\infty)$: actuality might be sparser than possibility.

**Claim 3: Plenitude Identity.** $A_\Omega = L_3(I_\infty)$ *[Epistemic status: ARGUED, conditional on the Plenitude Principle]*

The actualized domain coincides with the full set of $L_3$-admissible configurations. This is the substantive philosophical claim, and it is where the paper's argumentative burden concentrates. It adds Direction 2 (§6.1) to Direction 1: not only does actuality respect $L_3$, but $L_3$-admissibility exhausts the ground of actualization. What $L_3$ permits, $A$ does not selectively refuse.

This claim depends on the **Plenitude Principle** defended in §6.2.1 and the **Constraint Collapse Argument** of §6.2.2. A critic who rejects plenitude while accepting Claims 1 and 2 retains a coherent position (sparse actualism), but one that requires positing either a further constraint on $A$ beyond $L_3$ or brute selectivity. §6.2.1 argues that neither option is available within $\chi$; §6.2.2 argues that no such constraint can be coherently specified at the level where $A$ operates.

The claim is not that all admissible configurations are simultaneously actual in the sense of concurrent physical instantiation; $A$ selects, and temporal or modal structure may distribute actualizations. The claim is structural: $A_\Omega$ and $L_3(I_\infty)$ coincide as domains because the two characterizations pick out the same totality.

**The three claims together.** Grounding explains *why* actuality exists. Characterization specifies *what constraints* actuality satisfies. Plenitude determines *how much* of the admissible domain is actualized. A reader who accepts all three arrives at the bridge equation $A_\Omega = L_3(I_\infty)$. A reader who accepts only Claims 1 and 2 retains the core framework minus plenitude, a position the paper takes seriously as a live alternative (§6.2.1) while arguing against it.

The bridge equation is therefore:

- **Not a stipulative definition:** We are not merely defining $A_\Omega$ to mean $L_3(I_\infty)$. Claim 1 does substantive metaphysical work; Claims 2 and 3 follow from it under distinct argumentative pressures.
- **Not a formal theorem:** The argument is transcendental, not axiomatic. Formal verification can establish the internal consistency of the derivation chain, but the metaphysical warrant comes from the transcendental arguments of §§2.1-2.3.
- **A grounded characterization with a plenitude thesis:** Given the primitives and their transcendental necessity, the structure of $A_\Omega$ is characterized as $L_3(I_\infty)$, and its extent is argued to coincide with that characterization via plenitude.

### 6.2.1 Why Plenitude?

Call this the **Plenitude Principle (PP):** every $L_3$-admissible configuration of $I_\infty$ obtains. One might object: why should *all* $L_3$-admissible configurations obtain, rather than merely some? Could not $A$ select from the admissible without exhausting it?

The answer turns on $A$'s primitive status. Suppose $A$ systematically excludes some $L_3$-admissible configuration *k*. Then either:

1. *k* is not actually admissible: some constraint beyond $L_3$ rules it out. But then $L_3$ does not fully specify admissibility, and we have posited a hidden constraint not captured by the primitive framework. This violates the minimality of $\chi$.

2. $A$ is governed by a further principle that selects among admissibles. But then $A$ is not primitive; it is conditioned by something else. This violates the architecture in which $A$ marks the basic fact of obtaining.

Neither option is coherent with the framework. Therefore, if $A$ is primitive and $L_3$ is the complete logical constraint, no systematic exclusion of admissible configurations can be grounded. What $L_3$ permits, $A$ does not selectively refuse.

A subtler version of the objection concedes both points but insists that $A$ might be *primitively selective*: not governed by a rule, not violating $L_3$, simply a brute fact that some admissibles obtain and others do not. This move treats selectivity as a feature of $A$'s primitive character rather than a constraint imposed on it. The TRM's response is not that primitive selectivity is *incoherent* but that it is an *epistemic dead end*. A brute fact does not merely fail to explain; it terminates inquiry by fiat. Nothing follows from it, nothing can be tested against it, and it cannot constrain adjacent claims. If $A$ excludes configuration *k* without any property differentiating *k* from included configurations, the partition carries no structural information: there is nothing in virtue of which *k* falls on one side rather than the other. Differentiation, as §6.2.2 demonstrates, requires $L_3$-governed identity conditions, returning us to structured constraint. And structured constraint, within $\chi$, just is $L_3$. Primitive selectivity is therefore not a stable third option at the foundational level: it either acquires structure (collapsing into option 2) or remains a brute posit from which no downstream physical structure can be derived (see "Primitive modality" below).

**Primitive modality as a live position.** A critic might stand at a different point entirely and insist on *primitive modal facts*: brute, ungrounded facts about which possibilities obtain and which do not, not governed by any constraint, not explicable by any principle, simply given. This is a coherent metaphysical position. It is not self-contradictory, and a philosopher who holds it does not thereby commit any logical error. The TRM does not claim otherwise. The response operates at a different level: primitive modal facts are epistemic dead ends. They do not merely leave a question unanswered; they foreclose the possibility of answering it. Physics seeks to explain regularities among actualized configurations. If the distribution of actualization is itself brute, two consequences follow. First, the regularity of physical law has no ground: the uniformity of nature becomes a cosmic coincidence rather than a consequence of structural constraint. Second, no downstream structure can be derived, because a dead end generates no leverage for derivation. You cannot get from "it just is" to Hilbert space, Born rule, or dynamics. By contrast, the TRM's primitives are primitive but *generative*: the reconstruction chain from $\chi$ through $A_\Omega$ to quantum formalism runs through them precisely because they carry structural content rather than terminating it. Primitive modality is the right to stop explaining. The TRM argues that stopping here, before physical structure has been grounded, is stopping too early.

This does not commit the TRM to modal realism in the Lewisian sense. Lewis posits the actual existence of spatiotemporally isolated concrete worlds. The TRM claims that actuality is coextensive with logical admissibility within a single unified domain: a structural identity, not a plurality of worlds. The contrast with modal realism is preserved precisely because $A_\Omega$ is not carved into disconnected totalities but constitutes the single actualized domain constrained by $L_3$.

### 6.2.2 The Constraint Collapse Argument

A sophisticated objector might accept that $L_3$ governs *logical* admissibility while insisting that $A$ operates under additional *non-logical* constraints. On this view, some $L_3$-admissible configurations might nonetheless be excluded by principles orthogonal to logic.

The objection fails because no such constraint can be coherently specified at the level where $A$ operates.

A constraint on $A$ would be a rule partitioning $I_\infty$ into configurations that $A$ may actualize and configurations that $A$ may not. But partitioning requires distinguishability: the rule must identify which configurations fall on which side. Distinguishability requires determinate properties of configurations. And determinate properties require $L_3$-governed identity conditions.

The dependency chain is therefore:

1. To constrain $A$, a rule must evaluate configurations.
2. Evaluation requires determinate properties of configurations.
3. Determinate properties require $L_3$-governed identity conditions.
4. Therefore, any constraint on $A$ presupposes $L_3$.
5. A constraint that presupposes $L_3$ cannot be independent of $L_3$.

What about physical or causal constraints? These presuppose the very actuality that $A$ is supposed to ground. Physics describes regularities among actualized configurations; causation is a relation among obtaining states. Neither can constrain $A$ without circularity: they would invoke what $A$ produces in order to govern $A$'s operation.

The point is not that $A$ is "structurally indifferent" in some mysterious sense. The point is that the level at which $A$ operates is prior to any domain where non-logical constraints become available. $A$ is not a parameter within a model of reality; it is the condition for there being any model-relevant reality at all. At the primitive level, the only available constraint is $L_3$.

The objector's move therefore collapses. Any attempt to specify a non-logical constraint on $A$ either presupposes $L_3$ (and is therefore not independent of it) or presupposes actualization (and is therefore circular). No coherent constraint on $A$ can exclude $L_3$-admissible configurations from the actualized domain.

This transforms the plenitude argument. We are no longer claiming merely that $A$ "does not exclude." We are claiming that exclusion *cannot be coherently specified*. The equality $A_\Omega = L_3(I_\infty)$ holds because there is no coherent way to articulate a principle that would render it false. *[Epistemic status: ARGUED, the constraint collapse is a transcendental argument, not a formal proof; a critic who posits non-logical, non-physical constraints at the primitive level would reject it.]*

### 6.3 Burden on the Objector

Two challenges confront anyone who would reject the bridge equation:

1. **Demonstrate that physical reality is not logical, informational, and dynamic.** Any such demonstration must itself employ logical inference, informational content, and dynamical reasoning, thereby presupposing the very features it denies. This is not a rhetorical trick but a transcendental constraint: the conditions for coherent theorizing are the conditions $\chi$ identifies.

2. **Produce a physical configuration that obtains while violating $L_3$.** The objector must exhibit an actualized state that fails identity (something that is not what it is), violates non-contradiction (something that both obtains and does not obtain in the same respect), or escapes excluded middle (something for which a determinate property neither holds nor fails to hold). Apparent quantum counterexamples dissolve under scrutiny: superposition is a determinate state, not a violation of identity; entanglement involves determinate joint states with indeterminate marginals, not contradiction.

Until both challenges are met, the bridge equation stands: the primitives ground actuality, and the actualized domain is characterized as $L_3$-admissible configurations of $I_\infty$.

### 6.4 Consequences of Rejection

The burden just stated identifies what the objector must *do*. It is equally important to trace what the objector becomes *committed to* upon rejecting $\chi$.

**Rejecting $L_3$ as ontologically constitutive** eliminates the ground of determinate identity conditions for physical states. Without identity ($A = A$), no configuration is determinately itself; without non-contradiction, configurations both obtain and fail to obtain in the same respect; without excluded middle, determinacy of properties has no guarantee. The objector does not thereby simplify ontology; she inherits the same explanatory obligations with fewer resources. Moreover, the quantum phenomena sometimes cited against classical logic (superposition, entanglement) already satisfy $L_3$, as §§3.3 and 4.1-4.2 demonstrate. Rejecting $L_3$ does not resolve quantum puzzles; it renders them inarticulable.

**Rejecting $I_\infty$ as the possibility domain** requires an alternative account of why reality exhibits distinguishable states at all. Bare structure without an informational domain leaves differentiation unexplained: there would be "something" but no principled basis for "something *rather than something else*." Any bounded alternative to $I_\infty$ demands a boundary principle specifying which distinctions are available, and such a principle either presupposes a larger space of possible distinctions or posits a brute cutoff. The first generates regress; the second replaces one primitive with two (the bounded domain plus its boundary).

**Rejecting $A$ as primitive** collapses the actuality/possibility distinction. If actualization is not primitive, it must derive from something else. But derivation from logical constraint alone yields only admissibility, not obtaining: $L_3$ tells us *what can* be but not *that anything is*. Derivation from informational structure alone yields only possibility: $I_\infty$ specifies *what is distinguishable* but not *what is actual*. The objector must either accept that actuality is brute (which is what primitivity claims) or derive it from a source that itself presupposes actuality (which is circular).

**Rejecting the bridge equation while accepting the primitives** yields an ontology with three primitives whose interaction produces nothing. $L_3$ constrains, $I_\infty$ supplies, $A$ actualizes, but on this view, the result of their joint operation is left uncharacterized. The objector has the ingredients but refuses the recipe. §6.2.2 sharpens the point: no coherent non-logical constraint on $A$ can exclude $L_3$-admissible configurations, so the only alternative to the bridge equation is an unmotivated restriction: ontological waste posing as parsimony.

In each case, rejection does not yield a leaner ontology. It yields the same explanatory burdens with strictly fewer resources to discharge them.

**Result of §6:** Three claims compose the bridge argument. (1) The primitive ontology $\chi$ grounds the actualized domain ($\chi \vdash A_\Omega$). (2) The actualized domain respects $L_3$ ($A_\Omega \subseteq L_3(I_\infty)$). (3) Under the Plenitude Principle, the actualized domain coincides with the $L_3$-admissible configurations ($A_\Omega = L_3(I_\infty)$). Claims 1 and 2 are nearly uncontroversial given §§2.1-2.5. Claim 3 carries the substantive philosophical weight and depends on the arguments of §§6.2.1-6.2.2. The result is a grounded characterization with a plenitude thesis, not a stipulative definition.

### 6.5 The Bridge Lemma

The physics reconstruction in the companion LRT papers requires a specific connection between the ontological primitives established here and the operational constraints that generate quantum structure. This connection is summarized as the **Bridge Lemma**:

**Bridge Lemma.** *If $A_\Omega = L_3(I_\infty)$, then any proposition about a configuration $c \in A_\Omega$ satisfies $L_3$. Satisfying $L_3$ requires determinate content, which requires operational distinguishability. Therefore, every physical proposition is operationally distinguishable.*

This lemma licenses the transition from ontological grounding (the present paper) to physics reconstruction (LRT-MASTER). The Physical Proposition Criterion (PPC) stated in the companion paper is a direct consequence: a claim counts as a physical proposition if and only if it satisfies $L_3$, which requires that its truth-states be operationally distinguishable.

The lemma is not an additional assumption. It follows from the constitutive role of $L_3$ established in §2.1. Because $L_3$ is not a constraint *on* propositions but the condition *under which* anything counts as a proposition, the connection to operational distinguishability is internal to the framework rather than externally imposed.

---

## Open Issues for Development

**O1. Irreducibility section (§2.4).** COMPLETE. Six pairwise-collapse cases formalized across two tiers (strict incoherence / physical vacuity). Summary table included. Scope of irreducibility claim explicitly limited to functional role within χ as physical foundation.

**O2. Wheeler-DeWitt and Page-Wootters response (§2.3d).** COMPLETE. Two-objection structure: block-universe reply retained; Wheeler-DeWitt / Page-Wootters added as Objection 2 with explicit argument that A operates at the actual/non-actual level, which timeless formalisms presuppose but do not address.

**O3. Falsifiability (§5).** COMPLETE. Three-version structure: accommodation objection, what χ rules out, indirect empirical support and vulnerability conditions. Three explicit exclusions: actualized L₃-violations, unconstrained state spaces, purely epistemic interpretations without ontic actualization.

**O4. Relation to LRT derivation chain.** COMPLETE. Bridge argument added as §6: grounding sequence (§6.1), bridge equation status with plenitude and constraint collapse arguments (§6.2), burden on objector (§6.3), consequences of rejection (§6.4), bridge lemma licensing transition to LRT-MASTER (§6.5).

**O5. Modal status of A (§2.3e).** COMPLETE. Transcendental necessity established as the correct modal category. Metaphysical necessity declined as overclaim; nomological necessity declined as inverting the grounding direction. Parallel with L₃'s transcendental necessity made explicit, with the distinction between logical route (L₃) and ontic route (A) noted.

**O6. I∞ engagement with informational physics (§2.2c).** COMPLETE. Three objections addressed: information-is-physical (melody/substrate distinction), Landauer's principle (constrains A's thermodynamics, not I∞'s modal space), holographic entropy bounds (constrains instantiated subset of I∞, not I∞ as representational space). Modal/aggregate distinction is the load-bearing response to both Landauer and holographic objections.

**O7. Epistemic status tags.** COMPLETE. All sections tagged: §§2.1–2.3 ARGUED; §2.4 ARGUED; §2.5 ARGUED; §3.1 ESTABLISHED/ARGUED; §§3.2–3.3 ARGUED; §§4.1–4.2 ARGUED; §5 ARGUED; §6 ARGUED (grounding and characterization both ARGUED). OPEN tag placed on I∞ ontological status question in §2.2(b).

**O8. Register and citation pass.** COMPLETE. Body text citations inserted for Priest (1987, 2006), DeWitt (1967), Page and Wootters (1983), Wallace (2012), Masanes and Müller (2011). Full Harvard reference block added below. Confidence flags attached to each entry per source protocol.

---

## References

*Confidence flags: HIGH = verified primary source or direct quotation; MEDIUM = secondary source with publication details, appears reliable; LOW = paraphrase or tertiary; UNCERTAIN = attribution unverified.*

Bekenstein, J.D. (1973) 'Black holes and entropy', *Physical Review D*, 7(8), pp. 2333–2346. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Bohm, D. (1952a) 'A suggested interpretation of the quantum theory in terms of "hidden" variables, I', *Physical Review*, 85(2), pp. 166–179. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Bohm, D. (1952b) 'A suggested interpretation of the quantum theory in terms of "hidden" variables, II', *Physical Review*, 85(2), pp. 180–193. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Bérut, A., Arakelyan, A., Petrosyan, A., Ciliberto, S., Dillenschneider, R. and Lutz, E. (2012) 'Experimental verification of Landauer's principle linking information and thermodynamics', *Nature*, 483, pp. 187–189. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Chiribella, G., D'Ariano, G.M. and Perinotti, P. (2011) 'Informational derivation of quantum theory', *Physical Review A*, 84, 012311. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

DeWitt, B.S. (1967) 'Quantum theory of gravity. I. The canonical theory', *Physical Review*, 160(5), pp. 1113–1148. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Everett, H. (1957) '"Relative state" formulation of quantum mechanics', *Reviews of Modern Physics*, 29(3), pp. 454–462. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Fuchs, C.A., Mermin, N.D. and Schack, R. (2014) 'An introduction to QBism with an application to the locality of quantum mechanics', *American Journal of Physics*, 82(8), pp. 749–754. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Ghirardi, G.C., Rimini, A. and Weber, T. (1986) 'Unified dynamics for microscopic and macroscopic systems', *Physical Review D*, 34(2), pp. 470–491. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Hardy, L. (2001) 'Quantum theory from five reasonable axioms', arXiv:quant-ph/0101012. [MEDIUM — standard attribution; arXiv preprint widely cited; primary text not directly accessed for this draft]

Hawking, S.W. (1975) 'Particle creation by black holes', *Communications in Mathematical Physics*, 43(3), pp. 199–220. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Landauer, R. (1961) 'Irreversibility and heat generation in the computing process', *IBM Journal of Research and Development*, 5(3), pp. 183–191. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Longmire, J.D. (2025a) *Logic Realism Theory: Philosophical Foundations*. Working Draft v2.10. Independent research. [HIGH — primary author]

Longmire, J.D. (2025b) *Logic Realism Theory: Technical Foundations*. Working Draft. Independent research. [HIGH — primary author]

Longmire, J.D. (2026a) 'LRT: Non-Decomposability, Entanglement, and Bell's Theorem Derived from A_Ω = L₃(I∞)'. Zenodo. DOI: 10.5281/zenodo.18950181. [HIGH — primary author; deposited primary]

Longmire, J.D. (2026b) 'LRT: Black Hole Information Return — Operator Formalism and FC-2 Prediction'. Zenodo. DOI: 10.5281/zenodo.18950706. [HIGH — primary author; deposited primary]

Masanes, L. and Müller, M.P. (2011) 'A derivation of quantum theory from physical requirements', *New Journal of Physics*, 13, 063001. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Page, D.N. and Wootters, W.K. (1983) 'Evolution without evolution: dynamics described by stationary observables', *Physical Review D*, 27(12), pp. 2885–2892. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Priest, G. (1987) *In Contradiction: A Study of the Transconsistent*. Dordrecht: Martinus Nijhoff. [MEDIUM — standard primary source for dialetheism; primary text not directly accessed for this draft]

Priest, G. (2006) *In Contradiction: A Study of the Transconsistent*. 2nd edn. Oxford: Oxford University Press. [MEDIUM — expanded edition; primary text not directly accessed for this draft]

Rovelli, C. (1996) 'Relational quantum mechanics', *International Journal of Theoretical Physics*, 35(8), pp. 1637–1678. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Tegmark, M. (2008) 'The mathematical universe', *Foundations of Physics*, 38(2), pp. 101–150. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Susskind, L. (1995) 'The world as a hologram', *Journal of Mathematical Physics*, 36(11), pp. 6377–6396. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

't Hooft, G. (1993) 'Dimensional reduction in quantum gravity', in Ali, A., Ellis, J. and Randjbar-Daemi, S. (eds) *Salamfestschrift*. Singapore: World Scientific. Also available as: arXiv:gr-qc/9310026. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Wheeler, J.A. (1968) 'Superspace and the nature of quantum geometrodynamics', in DeWitt, C. and Wheeler, J.A. (eds) *Battelle Rencontres*. New York: Benjamin, pp. 242–307. [MEDIUM — standard attribution; primary text not directly accessed for this draft]

Wallace, D. (2012) *The Emergent Multiverse: Quantum Theory According to the Everett Interpretation*. Oxford: Oxford University Press. [MEDIUM — standard primary source for Many-Worlds / Everett interpretation; primary text not directly accessed for this draft]

---

**Reference verification status.** All third-party references are flagged MEDIUM: standard attributions with publication details, but primary texts have not been directly accessed for this draft. No third-party reference is cited at HIGH confidence. Before journal submission, each reference must be verified against the primary text for: (1) accurate page numbers/DOIs, (2) correct characterization of the cited claim, and (3) no misattribution of paraphrased content as direct quotation. Self-references (Longmire) are HIGH. This verification pass is a submission prerequisite, not an optional polish step.

---

## Appendix C: Full Pairwise-Collapse Arguments

The six cases establishing the irreducibility of the triad (summarized in §2.5) are developed here in full.

### Tier 1: Cannot Ground a Physical Framework

These pairs lack a constitutive element required for any physical foundation. The missing primitive is not merely useful; its absence leaves the remaining pair unable to range over, constrain, or select from a structured domain.

**Case 1: L₃ without I∞.**
L₃ is a set of constraints: identity, non-contradiction, excluded middle. Constraints are constraints on something; they presuppose a domain over which they range. Without I∞, there is no domain of configurations for L₃ to govern. The result is not a restrictive logic operating over an empty set; it is a constraint relation with no relata. No formal object results. This is not physical vacuity: it is the absence of any object of discourse whatsoever.

**Case 2: A without I∞.**
A is the primitive actualization principle, the selection of configurations as actual. Selection is a relation between a selector and a domain of candidates. Without I∞, there are no candidates. A without I∞ is not selection over an empty set, which is at least a coherent formal operation; it is a selection primitive with no domain specification. The operation is undefined. Again, no coherent formal object results.

### Tier 2: Cannot Perform the Required Physical Function

These pairs produce recognizable formal objects, objects that mathematicians and logicians can work with, but those objects cannot discharge the explanatory obligations a foundation for physics must meet. The failure is specific and precise.

**Case 3: I∞ without L₃.**
An unconstrained possibility space is a perfectly coherent formal object. Set theory, modal logic, and combinatorics all work with such spaces. The problem is that without L₃, there is no admissibility condition on I∞, no distinction between configurations that can be physically instantiated and those that cannot. Every configuration, including those that violate identity, non-contradiction, or excluded middle, is equally available. Physics requires that some configurations are inadmissible: that contradictory states are not actual, that a detector cannot simultaneously register and not register an event. Without L₃, that requirement has no ground. I∞ without L₃ is formally coherent but physically inert: it cannot distinguish physical from non-physical configurations, which is the first thing any foundation for physics must do.

**Case 4: I∞ without A.**
A constrained possibility space, I∞ filtered by L₃, is also a coherent formal object: it is precisely the space of L₃-admissible configurations. But without A, nothing in that space is actual. Every admissible configuration is equally a candidate and equally unactualized. The result is a static modal structure: rich in possibility, empty of actuality. Physics is not a theory of what could be actual; it is a theory of what is actual and how actuality unfolds. No actualization principle means no dynamics, no observables, no empirical content. The formal object is coherent; it simply has nothing to say about the physical world.

**Case 5: L₃ without A.**
Admissibility conditions over a configuration space, L₃ operating on I∞, yield the class of configurations that are candidates for actualization. But candidacy is not actuality. Without A, every admissible configuration has equal standing: nothing selects among them. One might object that L₃ itself performs a kind of selection by excluding inadmissible configurations. That is true, but it is selection at the wrong level: L₃ selects the admissible from the inadmissible, not the actual from the merely admissible. Physics requires the second selection. Without A, the admissible configurations sit inertly as an undifferentiated class of equally unactualized possibilities. L₃ without A is formally coherent: it defines a well-structured space. But it cannot say which configurations obtain, which is the central question of any physical theory.

**Case 6: A without L₃.**
A without L₃ is a selection principle operating over an unconstrained domain. It produces actuals, but arbitrarily. Without L₃, there is no admissibility filter on what A can select. Contradictory states, self-negating configurations, configurations that violate identity across successive actualizations: all are available as candidates. The result is not lawless in the sense of random; A could in principle select deterministically. But deterministic selection from an unconstrained domain is not physics. Physics requires that what is selected is coherent, that actualized states are self-identical and non-contradictory, that outcomes exclude their negations. Without L₃, A can produce a sequence of actuals, but that sequence has no logical structure and cannot be the subject of law-governed inquiry. The foundation is formally intelligible but physically unprincipled.
