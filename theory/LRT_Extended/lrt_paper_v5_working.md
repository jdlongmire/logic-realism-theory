# Logic Realism Theory: Physical Reality as Logical Filtering

**James (JD) Longmire**  
Northrop Grumman Fellow (unaffiliated research)  
ORCID: 0009-0009-1383-7698  
Correspondence: jdlongmire@outlook.com

---

## Abstract

Human cognition can represent configurations that physical reality does not instantiate. This paper argues that this conceivability-instantiation asymmetry reflects an ontological constraint: the classical laws of logic—determinate identity, non-contradiction, and excluded middle—govern physical instantiation rather than merely description or inference.

The framework distinguishes between the space of all representable configurations and the subset that can be instantiated under these logical constraints. Physical reality is identified with the latter. When configurations are individually admissible but jointly incompatible, instantiation requires exclusion or ordering rather than coexistence. The paper argues that this constraint structure is sufficient to ground temporal ordering, outcome definiteness in quantum measurement, and the form of probabilistic weighting in quantum theory.

In particular, the Born rule is shown to follow from the requirement that admissible weighting be invariant under equivalent decompositions, a condition imposed by determinate identity. Under additional regularity assumptions, the same identity constraints motivate the quadratic form of the kinetic term in classical dynamics. Further sections explore how this framework coheres with known physical regimes, including decoherence, Planck-scale limits on individuation, and black hole thermality, without claiming derivation of specific physical theories.

The framework is explicitly falsifiable. Persistent macroscopic superposition, interference between macroscopically distinct outcome histories, preservation of numerical identity through singularities, or the instantiation of completed physical infinities would refute its core claims.

**Keywords:** logic realism, ontology, quantum foundations, measurement problem, Born rule, Lagrangian mechanics, temporal structure

---

## 1. Introduction

Human minds can conceive what physical reality does not instantiate.

We can describe contradictory objects, indeterminate states, and logically impossible configurations without difficulty. Formal systems can represent inconsistency. Works of fiction routinely depict violations of classical logic. None of this strains our cognitive or representational capacities.

Physical instantiation is different. No observation has ever yielded an outcome that both is and is not the case in the same respect. No physical system has been observed to violate its own identity. Across all experimental domains, outcomes are determinate. The empirical record is exceptionless.

This asymmetry between conceivability and instantiation calls for explanation. If the classical laws of logic constrained only description or inference, then conceiving violations should be difficult, or instantiating them should be possible. We observe neither. The natural hypothesis is that classical logic constrains what can be instantiated, not what can be represented.

This paper develops that hypothesis into a framework: **Logic Realism Theory (LRT)**.

### 1.1 The Framework

The framework distinguishes three domains:

**$I_\infty$**: The space of all conceivable configurations. This includes inconsistent, indeterminate, and impossible specifications. It is unrestricted by logical admissibility.

**$L_3$**: The classical logical constraints of Determinate Identity, Non-Contradiction, and Excluded Middle, treated as ontological constraints on instantiation rather than rules of description.

**$A_\Omega$**: Physical reality, defined as the subset of conceivable configurations that satisfy these constraints.

The core structural claim is:

$$I_\infty \xrightarrow{L_3} A_\Omega$$

Physical reality is not coextensive with what can be conceived. It is what can be instantiated under classical logical constraints.

This framework does not attempt to derive the laws of logic or explain why they hold. They are taken as primitive constraints on determinate being. The project instead investigates what follows if physical instantiation is governed by them.

### 1.2 Central Thesis and Scope

The central thesis is that classical logical constraints actively structure physical instantiation. When configurations are individually admissible but jointly incompatible, instantiation requires exclusion or ordering rather than coexistence. The paper argues that this constraint structure is sufficient to ground temporal succession, measurement outcomes, and probabilistic structure in quantum theory.

In particular, the paper advances and defends the following claims:

- Temporal ordering arises from the exclusion of jointly inadmissible configurations.
- Quantum superposition reflects representational latitude within admissible configuration space, not co-instantiated contradiction.
- The Born rule follows from the requirement that identity be preserved across equivalent decompositions.
- The quadratic form of kinetic energy emerges from the same identity-stability constraints.

Further sections explore how this framework aligns with known physical scales and regimes, including Planck-scale structure and black hole physics. These latter claims are presented as conjectural alignments rather than derivations.

The framework is intended to be falsifiable. If physical reality were shown to instantiate genuine contradictions, persistent macroscopic superpositions, or completed actual infinities, the central hypothesis would fail.

### 1.3 Structure of the Paper

Section 2 develops the admissibility framework, the vehicle-content distinction, and addresses the circularity objection. Section 3 maps the regimes from Planck scale through black holes. Section 4 applies the framework to quantum mechanics, including derivation of the Born rule. Section 5 develops quantum gravity implications and dynamics from admissibility. Section 6 presents falsification criteria, limitations, and the selection problem. Section 7 situates LRT relative to alternative frameworks. Section 8 concludes.

---

## 2. The Admissibility Framework

### 2.1 Configuration Space

**Definition 2.1.** $I_\infty$ is the space of all conceivable configurations: whatever can be specified, described, or represented, without restriction to consistency.

$I_\infty$ includes:
- Contradictory specifications (round squares)
- Indeterminate states (neither $P$ nor $\neg P$)
- Impossible objects (Escher staircases)
- $L_3$-violating structures of all kinds

$I_\infty$ is not a physical space. It is the totality of what can be conceived. $I_\infty$ is not a domain of entities or worlds. It carries no ontological commitment. It is the space of specifications that can be represented, regardless of whether they can be instantiated.

### 2.2 Admissibility Constraints

**Definition 2.2.** $L_3$ is the conjunction of three constraints:

*Determinate Identity (Id)*: Configuration $i$ is determinately the configuration it is, independent of description, distinct from every other configuration.

*Non-Contradiction (NC)*: Configuration $i$ does not instantiate mutually exclusive determinations in the same respect at the same time.

*Excluded Middle (EM)*: For every property $P$ relevant to actualization, $i$ either has $P$ or lacks $P$.

**Definition 2.3.** Configuration $i$ is *admissible* iff $L_3(i)$ holds.

These constraints are not applied by a mechanism. They articulate what it is for a configuration to be determinate at all.

### 2.3 Physical Reality

**Definition 2.4.** $A_\Omega = \{i \in I_\infty : L_3(i)\}$. Physical reality is the $L_3$-admissible subset of $I_\infty$.

**Proposition 2.1.** $A_\Omega \subset I_\infty$ (proper subset).

*Proof.* $I_\infty$ contains $L_3$-violating configurations by construction. These are excluded from $A_\Omega$. $\square$

### 2.4 Time as Ordering

Temporal structure arises from admissibility constraints when individually admissible configurations cannot be jointly instantiated.

**Definition 2.5 (Joint Inadmissibility).** Two configurations $i$ and $j$ are *jointly inadmissible* iff each is individually admissible, but their logical co-instantiation is not:

$$L_3(i) \land L_3(j) \land \neg L_3(i \sqcup j)$$

The relation $i \sqcup j$ denotes logical co-instantiation, not temporal simultaneity. The question is whether a single determinate state of affairs could include both specifications, not whether they occur at the same time.

Joint inadmissibility applies only when $i$ and $j$ concern the same system in the same respect. A configuration may be represented as a tuple $\langle S, P, v, K \rangle$, where $S$ is a system-identifier, $P$ a property-type, $v$ a value, and $K$ the relevant contextual parameters (reference frame, measurement basis, coarse-graining). Joint inadmissibility applies only when the tuples match on $S$, $P$, and $K$, but differ in $v$.

*Example.* A particle at position $x_1$ is admissible. The same particle at position $x_2 \neq x_1$ is admissible. But the co-instantiation of both configurations for the same particle in the same spatial respect violates Determinate Identity: the particle would not be determinately *this* configuration. The joint configuration is inadmissible even though each component is admissible.

**Proposition 2.2 (Exclusion of Co-Instantiation).** Jointly inadmissible configurations cannot be co-instantiated in $A_\Omega$.

*Proof.* By definition, $i \sqcup j$ violates $L_3$ and is excluded from $A_\Omega$. Since both $i$ and $j$ are individually admissible, the exclusion applies only to their co-instantiation, not to either configuration taken alone. $\square$

*Remark (Exclusion-Ordering Trilemma).* If $i$ and $j$ are jointly inadmissible, three possibilities remain: (1) only $i$ occurs, (2) only $j$ occurs, or (3) both are included in a single history but not co-instantiated. The third case is relevant to change in an enduring system.

**Proposition 2.3 (Ordering Requirement).** If two jointly inadmissible configurations are both included within a single admissible history, then that history must impose an ordering relation between them.

*Proof.* Without such ordering, the history would amount to their logical conjunction, which is inadmissible. Admissibility requires that they be sequenced. $\square$

**Proposition 2.4 (Emergence of Temporal Structure).** Temporal succession is the ordering structure induced by joint inadmissibility among admissible configurations. Time is the precedence relation imposed by $L_3$ on configurations that cannot coexist.

No primitive temporal ordering is presupposed. The only primitive structure is admissibility; ordering appears as a requirement on histories containing mutually exclusive determinations of the same system. Metric time, duration, and relativistic structure belong to the protective belt and require auxiliary hypotheses.

*Remark (Partial Order).* The precedence relation need not be total. It applies along identity-threads of enduring systems and yields a causal-temporal partial order compatible with relativistic structure. Its universality follows from the fact that any two configurations of the same enduring system differing in $L_3$-relevant respects will be jointly inadmissible and therefore ordered if both are included.

### 2.5 Vehicle-Content Distinction

The framework explains why minds can conceive what reality cannot instantiate:

- **Vehicles** are physical systems, elements of $A_\Omega$. They satisfy $L_3$.
- **Contents** are what vehicles represent, drawn from $I_\infty$. They need not satisfy $L_3$.

A brain state representing "round square" is a consistent neural configuration (vehicle) representing inconsistent content. The vehicle satisfies $L_3$; the content doesn't need to.

This distinction applies to formal systems, artworks, quantum state vectors, and all representational structures. It explains how logical inconsistency can be represented without being instantiated, grounding the conceivability-instantiation asymmetry introduced in Section 1.

### 2.6 Against Descriptivism

A descriptivist holds that $L_3$ constrains how we describe reality, not reality itself. On this view, logic is a feature of language or thought, and the world is unconstrained by it. LRT denies this.

**Argument.** If $L_3$ constrained only description:
1. Conceiving violations should be difficult (description requires $L_3$)
2. Instantiating violations should be possible (reality unconstrained)

Empirically:
1. Conceiving violations is easy
2. Instantiating violations is impossible

The first point is established by the existence of paraconsistent logics, impossible fictions, and philosophical work on dialethism. Logicians routinely construct systems in which contradictions are tolerable. Artists depict impossible objects. Philosophers defend the view that some contradictions are true. None of this strains our cognitive capacities. The content of thought is not restricted to the $L_3$-admissible.

The second point is established by the empirical record. No confirmed empirical instance exists of a measurement yielding an outcome that was simultaneously $A$ and $\neg A$ in the same respect. No physical system has been observed violating its own identity. Every quantum experiment ever performed has produced a definite result. The record is not merely extensive; it is without confirmed exception across all domains, scales, and energies.

If $L_3$ were merely descriptive, this asymmetry would be inexplicable. We would expect either that conceiving violations is difficult (if logic constrains thought) or that instantiating them is possible (if logic doesn't constrain reality). We observe neither. The pattern is explained if $L_3$ constrains instantiation while leaving representation unconstrained.

**Engagement with specific alternatives.**

Several descriptivist positions deserve direct engagement:

*Logical pluralism* holds that different domains may require different logics. But this does not explain why the physical domain uniformly exhibits $L_3$-conformity while representation does not. The pluralist must explain the asymmetry, not merely permit it.

*Putnam's quantum logic* treats logic as empirical, revisable in light of quantum phenomena. But quantum experiments yield determinate outcomes; what is indeterminate is prediction, not instantiation. The empirical record supports $L_3$ for outcomes, not its revision.

*Dialethism* (Priest 2006) accepts true contradictions. But dialethists locate contradictions in semantic or logical domains, not physical instantiation. No dialethist claims a particle is simultaneously at position $x$ and not at position $x$ in the same respect. The position is compatible with LRT's core claim that physical instantiation is $L_3$-governed.

Each alternative either fails to explain the asymmetry or implicitly concedes that physical instantiation satisfies $L_3$.

Conclusion: $L_3$ constrains what can be physically instantiated, not merely what can be coherently described. $\square$

This argument is a central result of the paper. It establishes the key asymmetry on which LRT rests. The vehicle-content distinction (Section 2.5) explains how the asymmetry is possible; this argument establishes that it is actual.

The position aligns with logical realism as defended by Tahko (2009, 2021): the Law of Non-Contradiction is a metaphysical principle governing reality's structure, not a semantic convention or psychological constraint.

### 2.7 The Circularity Objection

An apparent circularity may be raised: if $L_3$ functions as the constraint determining what belongs to $A_\Omega$, must not the constraint itself be part of physical reality? And if so, does LRT not presuppose $L_3$ in order to explain why $L_3$ holds?

This objection rests on a category mistake. It conflates ontological constraints with physical mechanisms.

First, $L_3$ is not a process, entity, or structure that must itself be instantiated. It is a constraint on what instantiation *is*. Asking "what makes Non-Contradiction hold?" treats NC as a fact grounded in some further fact. But Non-Contradiction is constitutive of determinate being as such. A specification that both has and lacks property $P$ in the same respect is not a determinate configuration that fails a test; it is not a determinate configuration at all.

Second, the language of "constraint" or "admissibility" is not mechanistic. There is no literal sieve operating within ontological space. The claim is not that something prevents $L_3$-violating configurations from being instantiated, but that "instantiated contradiction" is incoherent. One does not ask what prevents round squares from existing, as though they were attempting to exist and being blocked. They are not excluded by a mechanism; they are excluded by meaning.

Third, LRT does not derive $L_3$ from anything within the framework. $L_3$ is explicitly taken as primitive. The aim of the theory is not to explain *why* the classical laws of logic hold, but to explore *what follows* if they constrain physical instantiation. This is standard practice in foundational inquiry: one begins with constitutive constraints and investigates their consequences.

The situation is directly analogous to logic's role in mathematics. Mathematics presupposes logic; logic is not derived from mathematical structures and then used to justify them. Logic is prior. In the same way, $L_3$ is prior to any physical structure.

If this leaves $L_3$ unexplained, that is correct. LRT offers no deeper account of why these constraints hold. The motivation for treating them as ontologically fundamental lies instead in the conceivability-actuality asymmetry (Section 1) and the failure of descriptivist alternatives (Section 2.6). This does not show that $L_3$ must govern reality; it shows that treating them as merely descriptive leaves the conceivability-instantiation asymmetry unexplained. The considerations justify taking the hypothesis seriously and examining its consequences.

Finally, primitiveness does not imply immunity from refutation. If physical reality were ever shown to instantiate genuine contradictions, indeterminacies, or identity failures, LRT would be falsified. The framework stands or falls on the claim that such instantiations do not occur.

---

## 3. The Regimes: Interpretive Alignments

Admissibility constraints operate differently at different scales. This section maps how the framework aligns with known physical regimes from Planck floor to black hole singularity. These alignments are interpretive, not derivations.

### 3.1 The Planck Scale: Individuation Limits

**Proposition 3.1 (Alignment Hypothesis).** The Planck scale ($\ell_P \approx 1.6 \times 10^{-35}$ m) plausibly corresponds to a lower bound on physical individuation, consistent with the requirements of determinate identity.

*Argument.* Attempts to individuate configurations below the Planck length require energies that would collapse the region into a black hole, preventing stable identity attribution. This suggests, though does not strictly entail, that the breakdown of classical spacetime structure at the Planck scale reflects limits on admissible individuation rather than merely technical failure of existing theories.

The Planck scale is not derived from $L_3$ alone. The alignment is that $L_3$ requires individuation, and known physics suggests individuation fails below this scale.

### 3.2 The Quantum Regime: Superposition

Between Planck scale and macroscopic scale, systems can exist in superposition.

**Proposition 3.2.** A quantum state vector $|\psi\rangle$ describes a region of $L_3(I_\infty)$: the admissible configurations consistent with preparation.

The superposition is not "both states at once." It is representational: the state vector describes which configurations could be instantiated given current constraints. The system is in $A_\Omega$; the state vector describes a region of possibility within the admissible.

The admissibility of the quantum state itself is not in question; what is restricted is the co-instantiation of mutually exclusive outcome-specifications within a single identity-thread.

EM applies to actualized outcomes, not to all predicates of the representation.

### 3.3 Measurement: Identity Engages

**Definition 3.1.** A macroscopic object has *trans-temporal determinate identity*: it is numerically one object persisting across time.

**Proposition 3.3.** When a quantum system entangles with a macroscopic object such that alternative outcomes would give the object incompatible macroscopic states, admissibility requires exactly one outcome.

*Proof.* A history containing the same macroscopic object in mutually exclusive states violates NC for that object's trans-temporal identity. Such histories are inadmissible. Only one outcome is included. $\square$

This is when "collapse" occurs: not a physical process, but the point at which admissibility becomes restrictive for that system. The threshold is macroscopic identity engagement.

The point at which trans-temporal identity becomes restrictive is not sharp and may depend on environmental coupling, decoherence timescales, and stability criteria. The framework requires only that such a regime exists, not that it be precisely defined a priori.

### 3.4 The Macroscopic Regime: Stable Identity

Macroscopic objects have stable trans-temporal identity. They persist as *this* object across time. Their configurations satisfy $L_3$ continuously.

This is the regime of tables, pointers, cats, and observers. Admissibility maintains single, definite histories for identity-bearing objects.

### 3.5 Loss of Determinate Identity at Singularities

**Proposition 3.4.** At a classical singularity, the conditions required for determinate identity are no longer satisfiable.

*Argument.* At a singularity, curvature and density diverge. Under such conditions, no stable criteria for individuation remain available. This suggests not that logical constraints cease to hold, but that no configuration satisfying them can be instantiated. The breakdown is ontological, not logical.

Structure that was in $A_\Omega$ is no longer individuable. In the language of the framework, it returns to $I_\infty$, the space of specifications without determinate instantiation.

### 3.6 Hawking Radiation: Interpretation

**Proposition 3.5 (Interpretive Alignment).** Within this framework, Hawking radiation is consistent with fresh admissible structure emerging rather than preserved identity.

The radiation is thermal (Planckian spectrum). Within LRT, this is consistent with the absence of preserved trans-temporal identity through the singularity. The radiation need not encode the original identity of infalling matter, because identity itself was not maintained.

This does not derive Hawking radiation or its thermality. It offers an ontological interpretation compatible with observed properties: information returns to $I_\infty$ at the singularity and emerges as fresh admissible structure, but the original trans-temporal identity cannot survive passage through conditions where determinate identity is unsatisfiable.

### 3.7 The Cycle

The full ontological cycle:

$$I_\infty \xrightarrow{L_3} A_\Omega \xrightarrow{\text{singularity}} I_\infty \xrightarrow{L_3} A_\Omega \ldots$$

Structure becomes admissible, persists while admissible, dissolves when individuation fails, and emerges as fresh admissible structure.

This schematic expresses a conceptual cycle of admissibility and breakdown, not a physical process occurring in time. Time itself is internal to admissible histories (Section 2.4).

---

## 4. Quantum Mechanics

### 4.1 Superposition as Representational

Quantum superposition does not violate $L_3$. A system in state $|\psi\rangle = \alpha|0\rangle + \beta|1\rangle$ is not "both 0 and 1." The state vector describes the region of $L_3(I_\infty)$ consistent with preparation.

The system has the determinate property of *being in state* $|\psi\rangle$. This is an element of $A_\Omega$. The alternatives described by $|0\rangle$ and $|1\rangle$ are in $I_\infty$ pending resolution.

The claim is not that the quantum state is incomplete, but that it represents admissible structure rather than instantiated multiplicity.

### 4.2 The Born Rule from Identity Stability

The Born rule is not an independent postulate. It is the unique probability assignment compatible with Determinate Identity.

**The constraint.** The argument does not presuppose probabilistic interpretation. It concerns any measure intended to weight mutually exclusive admissible continuations. Only after the measure is fixed does it acquire probabilistic interpretation.

For a physical system to satisfy Id, its total measure of admissible continuations cannot depend on how it is decomposed into components. If the total measure varied with choice of orthonormal basis, then the question "What is this system's total weight?" would have different answers in different decompositions. This violates Id: the system would not be determinately what it is, independent of how it is described.

**Proposition 4.1.** Any measure $P$ over admissible outcomes must satisfy:

$$\sum_i P(i\;|\;|\psi\rangle,\{|i\rangle\}) = 1$$

for any normalized state $|\psi\rangle$ and any orthonormal basis $\{|i\rangle\}$, with the total independent of basis choice.

This requires additivity on orthogonal subspaces and non-contextuality: the probability assigned to a projector cannot depend on which larger orthonormal family contains it.

**Two-dimensional illustration.** Consider a qubit with real coefficients:

$$|\psi\rangle = \cos\theta\,|0\rangle + \sin\theta\,|1\rangle$$

Suppose $P(0) = f(\cos\theta)$ and $P(1) = f(\sin\theta)$ for some function $f:[0,1]\to[0,1]$. Identity stability requires $f(\cos\theta) + f(\sin\theta) = 1$ for all $\theta$.

Test candidates:

- **Linear:** $f(x) = x$. Then $\cos\theta + \sin\theta = \sqrt{2}$ at $\theta = \pi/4$. Fails.
- **Cubic:** $f(x) = x^3$. Then $\cos^3\theta + \sin^3\theta \neq 1$ generally. Fails.
- **Quadratic:** $f(x) = x^2$. Then $\cos^2\theta + \sin^2\theta = 1$ for all $\theta$. Works.

The quadratic is forced by the Pythagorean identity. The two-dimensional case illustrates the structural constraint; the general result relies on Gleason's theorem and does not depend on this example.

**General result.** In Hilbert spaces of dimension $\geq 3$, Gleason's theorem (1957) establishes that any $\sigma$-additive, non-contextual probability measure on projections has the form:

$$\mu(P) = \langle\psi|P|\psi\rangle$$

For pure states and rank-1 projectors $P = |\phi\rangle\langle\phi|$:

$$\mu(P) = |\langle\phi|\psi\rangle|^2$$

This is the Born rule.

**Proposition 4.2.** The Born rule is the unique measure for weighting admissible continuations that preserves Determinate Identity across all basis decompositions.

*Proof.* Id demands that the total measure $\mathfrak{M}(\psi) = 1$ be independent of basis. NC and EM demand decomposition into mutually exclusive, jointly exhaustive alternatives. These constraints, formalized as additivity and non-contextuality, yield the hypotheses of Gleason's theorem. The Born rule follows. $\square$

Any alternative weighting rule would make the total admissible measure of a system depend on representational decomposition rather than on the system itself, violating determinate identity.

**Clarification on assumptions.** The derivation relies on two types of constraint:

- *Identity-mandated*: Total measure must be basis-independent. This follows from Determinate Identity: if the system's weight varied with representational decomposition, the system would not be determinately what it is.

- *Regularity assumptions*: σ-additivity, applicability to dimension ≥3, measurability of projections. These are standard measure-theoretic requirements not derived from $L_3$.

The contribution is not the derivation itself, which follows Gleason (1957) and Busch (2003). The contribution is the ground: identity stability explains *why* non-contextuality and additivity hold for physical systems, rather than taking them as unexplained axioms about nature.

### 4.3 Non-Locality

Bell correlations arise from global constraints on joint configuration space. When particles are prepared in entangled state $|\Psi\rangle$, the admissible region of *joint* configuration space is constrained globally from preparation onward.

$L_3$ constraints are not local. They apply to configurations, which can describe globally extended systems. The constraints do not propagate or signal; they structure the admissible region.

The global nature of admissibility constraints does not imply superluminal influence. Constraints structure which joint configurations are admissible; they do not transmit signals or causes.

### 4.4 Decoherence and Outcome Selection

Decoherence explains why certain macroscopic "pointer states" are dynamically robust under environmental interaction, but it does not by itself select a single outcome. LRT adds the claim that once macroscopic identity is engaged in a decohered basis, admissibility requires one outcome.

Decoherence explains basis stability but not outcome uniqueness. LRT supplies only the latter, not the former.

**The division of labor:**
- Decoherence selects the *basis* (which alternatives are macroscopically robust)
- $L_3$ selects the *outcome* (only one alternative is in $A_\Omega$)

**Minimal model.** Consider:
- System $S$: qubit with basis $\{|0\rangle, |1\rangle\}$
- Meter $M$: macroscopic pointer with position states $\{|U\rangle, |D\rangle\}$
- Environment $E$: large bath with many degrees of freedom

Initial state:
$$|\Psi_0\rangle = (\alpha|0\rangle + \beta|1\rangle) \otimes |R\rangle_M \otimes |e_0\rangle_E$$

where $|R\rangle_M$ is a "ready" pointer state.

Pre-measurement entangles $S$ and $M$:
$$|\Psi_1\rangle = \alpha|0\rangle|U\rangle_M|e_0\rangle_E + \beta|1\rangle|D\rangle_M|e_0\rangle_E$$

Environmental interaction correlates pointer with distinct environment states:
$$|\Psi_2\rangle = \alpha|0\rangle|U\rangle_M|e_U\rangle_E + \beta|1\rangle|D\rangle_M|e_D\rangle_E$$

with $\langle e_U|e_D\rangle \approx 0$. Tracing out $E$ yields a reduced density matrix for $S$-$M$ nearly diagonal in the $\{|U\rangle, |D\rangle\}$ basis.

Decoherence dynamically picks out $\{|U\rangle, |D\rangle\}$ as a robust pointer basis.

**Where $L_3$ acts.** At the level of global pure state $|\Psi_2\rangle$, nothing violates $L_3$: there is a single determinate quantum state. The problem arises if one reads $|\Psi_2\rangle$ as describing a single macroscopic pointer that is *both* Up and Down.

LRT's move:
- Before entanglement, candidate configurations in $I_\infty$ include pointer-Up and pointer-Down futures
- Decoherence narrows admissible macroscopic descriptions by selecting stable pointer basis $\{|U\rangle, |D\rangle\}$
- Once the pointer's trans-temporal identity as a single macroscopic object is engaged, a history in which that object is simultaneously in both positions violates NC
- Such a history is not in $A_\Omega$

For the decohered alternatives:
- Candidate histories: $h_U$ = (pointer Up, observer sees Up); $h_D$ = (pointer Down, observer sees Down)
- Decoherence makes $\{|U\rangle, |D\rangle\}$ dynamically stable
- Admissibility selects exactly one of $\{h_U, h_D\}$ into $A_\Omega$
- Born weights follow from identity stability (Section 4.2)

This complements Section 4.3: in Bell scenarios, $L_3$ forbids joint values for incompatible measurements; in decoherence, admissibility forbids a single macroscopic pointer from occupying mutually exclusive positions within the same history.

### 4.5 Interpretation Compatibility

LRT constrains interpretations. Compatibility here means ontological consistency with LRT's constraints, not derivability from them.

- **Copenhagen:** Compatible. Measurement triggers resolution to one outcome.
- **Bohm:** Compatible. Configurations always determinate; wave function guides.
- **GRW/Collapse:** Compatible. Collapse produces admissible outcomes.
- **QBism:** Compatible. Outcomes ontologically determinate.
- **Everett:** Conflict. LRT excludes branching for macroscopic objects.

---

## 5. Quantum Gravity Implications

### 5.1 Spacetime Not Fundamental

Spacetime emerges from $L_3$ constraints. Determinate Identity requires distinction; distinction requires separation structure; separation yields geometry (Section 5.2). At Planck scale, these constraints hit their limit. Spacetime dissolves because individuation dissolves.

### 5.2 Geometry from Identity

**Proposition 5.1.** Determinate Identity implies separation structure.

*Argument.* If $i \neq j$, there must be some basis for distinction. Distinction implies separation. Separation admits ordering. Under regularity assumptions (protective belt), this yields metric structure.

Geometry is not postulated. It emerges from the requirements of $L_3$-admissible configuration space.

### 5.3 No Actual Infinities

**Proposition 5.2.** Actual infinities cannot be instantiated.

*Argument.* An actual infinite collection requires completed infinite identity determinations. But admissibility cannot be established for infinite operations. Determinate Identity for infinitely many elements would require infinitely many completed identity facts, which is inadmissible.

Physical reality may approach infinity as limit (potential infinity) but cannot instantiate it (actual infinity). This explains why singularities are problematic: they involve actual infinities, which violate $L_3$.

### 5.4 The Singularity as $L_3$ Failure

The black hole singularity is not just extreme curvature. It is where Determinate Identity fails. Infinite density means configurations cannot be individuated. The "singularity" in the mathematics reflects a genuine ontological breakdown: $L_3$ cannot be satisfied.

This is why information "disappears": not because it's destroyed, but because it returns to $I_\infty$, where identity is not determined.

### 5.5 Testable Implications

The framework suggests:

1. **Planck-scale discreteness** with identity character, not arbitrary cutoff
2. **Black hole evaporation** thermal throughout, no late-time purification restoring original identity
3. **No trans-Planckian modes** in cosmological observations

These differ from some quantum gravity approaches and are in principle testable.

### 5.6 Dynamics from Admissibility

This section does not derive specific forces or equations of motion. It shows that, given minimal regularity assumptions, the form of classical dynamics is naturally aligned with the requirements of trans-temporal determinate identity. Full development is deferred to future work.

**Two sources of identity continuity constraint.**

An enduring object moving through configuration space faces two distinct constraints from $L_3$:

1. *Kinematic constraint*: The object at $t_1$ and the object at $t_2$ must be determinately the same object. Bridging configurations across time requires identity continuity. Rapid change places greater demand on this continuity than slow change.

2. *Boundary constraint*: Some configurations are closer to the boundary of $L_3$ admissibility. Occupying them carries higher "identity risk," independent of motion.

These correspond to kinetic and potential energy respectively. They are distinct and should not be conflated. These constraints are not physical forces. They are bookkeeping constraints on which histories are admissible given the requirement that an object be numerically identical across time.

**Kinematic constraint and the quadratic form.**

The problem is not to explain why motion has a cost, but why that cost must take a particular functional form.

Let $q(t)$ be a trajectory in configuration space, with a separation structure (Section 5.2) providing a notion of distance. The kinematic identity constraint at time $t$ is a function of the rate of configuration change:

$$\mathcal{I}_{\text{kin}}(t) = F(\|\dot{q}(t)\|)$$

The total constraint over a trajectory is $\int \mathcal{I}_{\text{kin}} \, dt$.

The following assumptions constrain $F$:

1. *Locality*: The total constraint along a trajectory decomposes into contributions from infinitesimal segments.
2. *Isotropy*: The constraint depends only on the magnitude of change, not its direction.
3. *Evenness*: Reversing direction does not alter the constraint.
4. *Compositional additivity*: Independent degrees of freedom contribute additively.

Two degrees of freedom are *independent* if jointly specifying both introduces no new $L_3$ constraints beyond the conjunction of each. Compositional additivity then becomes an identity accounting rule: the constraint from changing two independent respects equals the sum of the constraints from changing each.

Under these assumptions, the only continuous functional form compatible with identity continuity is a positive quadratic form on velocities. This is a standard characterization: continuous, rotation-invariant functions satisfying $F(v \oplus w) = F(v) + F(w)$ for orthogonal concatenation are proportional to the squared $L_2$ norm.

These assumptions are standard in physics, but here they are not taken as primitive symmetries of space. They arise from the requirement that identity accounting be consistent across decompositions of change. The structural parallel to Section 4.2 is exact: identity stability forces the $L_2$ norm in both probability measures and kinematic constraints.

Therefore:

$$\mathcal{I}_{\text{kin}} \propto \|\dot{q}\|_2^2$$

This yields the kinetic term in the Lagrangian.

No appeal is made to a principle of least action at this stage. The quadratic form emerges as a structural constraint on admissible histories, not as a variational principle. The action principle appears only once histories are globally evaluated under these constraints.

**Boundary constraint and potential energy.**

Unlike the kinetic term, no unique form for boundary constraints follows from admissibility alone. $L_3$ defines which configurations are admissible, but "distance to the boundary" requires additional geometric structure. Once the protective belt supplies a topology or metric on configuration space, an admissibility margin $\mu(q)$ becomes meaningful: how far configuration $q$ is from inadmissibility.

The boundary constraint is then:

$$\mathcal{I}_{\text{bdry}}(q) = G(\mu(q))$$

where $G$ is a decreasing function (lower margin → higher constraint). This yields a potential-like term $V(q) = G(\mu(q))$.

The existence of a potential-like term is motivated by admissibility considerations, but its specific form is empirically determined. This belongs to the protective belt.

**The resulting Lagrangian.**

Combining kinematic and boundary constraints:

$$\mathcal{L}(q, \dot{q}) = \frac{1}{2} m \|\dot{q}\|^2 - V(q)$$

The appearance of the classical Lagrangian reflects the bookkeeping structure required to track identity-preserving histories, not an independent postulate about nature's preferences.

The quadratic form of the kinetic term is derived from identity stability (given regularity assumptions). The parameters require calibration:

- *Mass* ($m$): An identity coupling constant specifying how costly velocity change is for this degree of freedom. LRT provides the quadratic form; physics provides species-dependent coefficients. A future goal is to connect mass to deeper admissibility geometry or to representation-theoretic invariants (e.g., mass as a Poincaré invariant for relativistic fields).

- *Potential* ($V$): Encodes local admissibility margin. For familiar forces, this is calibrated empirically. The conjecture is that gravitational potentials reflect gradients in admissibility slack, with black holes as the limiting case where margin vanishes entirely (Section 5.4). This is conjectural alignment, not derivation.

**Conservation laws.**

Once the admissibility-induced Lagrangian inherits homogeneity assumptions, Noether's theorem applies:

- If the Lagrangian has no explicit time-dependence (admissibility constraints are temporally homogeneous), energy is conserved.
- If no explicit position-dependence (spatially homogeneous), momentum is conserved.
- If no directional preference (rotationally invariant), angular momentum is conserved.

These conservation laws follow only if the admissibility constraints are homogeneous in the relevant respects. They are not guaranteed by logic alone.

**Derived versus calibrated.**

The quadratic kinetic form is derived from identity stability, conditional on regularity assumptions (continuity, isotropy, compositional additivity). The existence and form of a potential term requires additional geometric structure from the protective belt. Mass values and specific potentials are empirically calibrated, not derived. Conservation laws follow from Noether once the Lagrangian inherits the relevant symmetries.

**Stationary action.**

Among admissible histories, those that satisfy both identity continuity and boundary constraints form a restricted class. The principle of stationary action characterizes this class; it does not explain why it exists.

**Connection to flexible determinism.**

The link to Section 6.4 is direct. If stationary action constrains which histories are realized, and $L_3$ constrains which configurations are admissible, then the combination yields global determinacy with local flexibility: the complete history satisfies both constraints, but individual junctures retain latitude weighted by availability.

---

## 6. Falsification

### 6.1 What Would Refute LRT

**Criterion 1: Persistent Macroscopic Superposition.** A macroscopic object maintaining superposition of exclusive states indefinitely, despite macroscopic identity engagement. "Persistent" here means stable under arbitrary isolation and decoherence suppression, not merely long-lived relative to current experimental limits.

**Criterion 2: Macro Branch Interference.** Demonstrable interference between macroscopically distinct outcome histories, not merely recoherence at the microscopic level. This would show both branches in $A_\Omega$.

**Criterion 3: Identity Through Singularity.** Black hole evaporation that restores numerical identity rather than merely equivalent informational content. The original macroscopic object, not just a reconstruction with the same data, would need to emerge.

**Criterion 4: Sub-Planck Structure.** Empirical evidence of structure individuated below $\ell_P$, stable under interaction. Toy mathematical constructions do not count.

**Criterion 5: Instantiated Actual Infinity.** A completed, physically instantiated infinity, not merely an unbounded process or mathematical limit.

Unreachability of these criteria does not imply unfalsifiability. The criteria specify what would count as refutation; experimental feasibility is a separate question.

### 6.2 What Does Not Refute LRT

- Quantum superposition prior to macroscopic entanglement
- Decoherence dynamics
- Stochastic outcomes
- Contextuality of microscopic properties
- Indeterminacy in prediction (vs. outcome)

These phenomena concern representational structure or predictive limitation, not instantiated contradiction or identity failure.

### 6.3 Honest Limitations

**No specific physics derived.** LRT does not derive the Standard Model, GR, or constants. It constrains form, not content.

**Protective belt.** Geometry and specific dynamics rely on auxiliary hypotheses.

**Empirical distinguishability.** The framework does not currently distinguish empirically between some rival interpretations of quantum mechanics. It constrains which interpretations are compatible but does not uniquely select among them.

### 6.4 The Selection Problem and Flexible Determinism

LRT constrains which configurations are admissible, but it does not specify which admissible configuration is actualized at each juncture. The Born rule provides probabilities over outcomes (Section 4.2). What remains is often framed as the "selection problem."

The framework rejects the assumption that every outcome must be underwritten either by sufficient causal antecedents or by irreducible randomness. That assumption generates the selection problem. LRT suggests a third option: structured flexibility.

**The global picture.** Physical reality is a single, complete history satisfying $L_3$ and, plausibly, stationary action. This history is determinate: there is one world, one sequence of events, one set of facts about what occurs. In this sense, LRT is globally determinate. There are not many equally real branches; there is one actual history.

"Global determinacy" means that there is exactly one complete admissible history. It does not imply that every event is locally fixed by prior conditions.

This does not mean that the content of that history is fixed independently of the admissibility structure. Rather, it means that the framework does not license multiple completed histories as simultaneously actual.

**The local picture.** At any given point within that history, multiple continuations may be $L_3$-admissible. In a quantum measurement, several outcomes may each be consistent with all logical and physical constraints. The global history includes exactly one of them, but nothing in the local constraints uniquely fixes which one must occur in advance.

**Flexible determinism.** The resolution is that determinacy is global, while flexibility is local.

The framework guarantees the existence of a complete, admissible history, but it does not rigidly determine every branch point by sufficient causes. Instead, the system proceeds through the space of admissible continuations, with outcomes weighted by how much room they have within that space.

Born probabilities are not measures of ignorance, as in hidden-variable theories, nor expressions of fundamental chanciness, as in collapse models. They are measures of *availability*: a structural weighting over admissible continuations, not epistemic likelihood. Identity stability forces this measure to be quadratic in amplitudes (Section 4.2). The weighting is derived, not postulated.

This structure is analogous to variational principles in classical mechanics. The action principle fixes the realized trajectory globally, but intermediate variations are locally permitted. Likewise, LRT fixes the global admissible structure while allowing flexibility at individual resolution points.

**Predictability without rigidity.** If selection were unconstrained, prediction would be impossible. If it were rigidly fixed at every step, probabilistic structure would be inexplicable. Structured flexibility accounts for both:

- Logical and dynamical constraints are stable across experiments
- The measure over admissible continuations is fixed by identity preservation
- Repeated experiments sample from the same constrained space
- Statistical regularities emerge and converge

Physics is possible because flexibility is structured, not because outcomes are secretly fixed or utterly lawless.

**Reframing the selection question.** The question "Why this outcome rather than another?" receives a principled answer: this outcome was an admissible continuation within the globally constrained structure, and the system took it. The Born weight specifies how available it was relative to alternatives. There is no further structural fact available within the framework that would single out one admissible continuation over another.

This is not evasion. It is a rejection of a false demand. The selection problem presupposed that either causal sufficiency or brute chance must underwrite every outcome. LRT denies that presupposition. Selection is the actualization of one among the admissible paths, with availability measured by the uniquely identity-preserving rule.

The remaining flexibility is not a gap in the theory. It is a feature of how determinate reality emerges from constrained possibility.

### 6.5 Research Program Structure

LRT constitutes a research program in the Lakatosian sense, with a hard core protected by a belt of auxiliary hypotheses.

**Hard Core (non-negotiable):**

The following commitments define LRT. Abandoning any would collapse the framework.

1. *Conceivability-actuality asymmetry.* What can be conceived ($I_\infty$) exceeds what can be instantiated ($A_\Omega$). This asymmetry is structural, not epistemic.

2. *$L_3$ as ontological constraint.* The three classical laws (Identity, Non-Contradiction, Excluded Middle) constrain instantiation: $A_\Omega \subseteq L_3(I_\infty)$.

3. *Time as ordering.* Temporal succession is the ordering induced by joint inadmissibility. Time emerges from admissibility applied to configurations that cannot coexist.

4. *Trans-temporal determinate identity.* Macroscopic objects possess numerical identity across time. Histories containing the same object in mutually exclusive states are inadmissible.

5. *Vehicle-content distinction.* Physical vehicles satisfy $L_3$; represented contents need not.

If trans-temporal determinate identity is rejected, the framework collapses rather than adapts. This is the central metaphysical commitment.

**Protective Belt (adjustable):**

The following hypotheses support the framework but may be modified without abandoning the core. The belt is expected to change as the program develops.

1. *Metric structure.* The emergence of metric geometry from separation structure requires regularity assumptions (Section 5.2).

2. *Decoherence dynamics.* The specific mechanism by which pointer bases become robust is empirical, not derived from $L_3$.

3. *Temporal direction.* The arrow of time is not derived here. Admissibility yields precedence structure, not asymmetry.

4. *Spacetime unification.* Lorentzian structure and the integration of space with time require auxiliary hypotheses.

5. *Identity threshold.* The precise boundary at which macroscopic identity engages is empirical, not sharp.

**Programmatic Status:**

The hard core makes LRT falsifiable at the level of ontology (Section 6.1). The protective belt allows adjustment in response to empirical or theoretical pressure without abandoning the framework.

A research program is *progressive* if it predicts novel facts or unifies previously disparate phenomena. LRT claims progressiveness through unification: measurement, the Born rule, the Planck scale, black hole thermality, and temporal structure are all aligned with a single constraint structure. Whether this unification yields novel predictions distinguishable from standard physics remains open.

A research program is *degenerating* if it merely accommodates known facts post hoc. LRT's explicit falsification criteria (Section 6.1) and acknowledged limitations (Sections 6.3-6.4) are intended to prevent degeneration by keeping the framework empirically exposed.

---

## 7. Relation to Alternative Frameworks

LRT does not compete with established programs in quantum foundations and quantum gravity. It offers an ontological perspective that may illuminate their contributions. Each program has developed rigorous formalisms for one aspect of physical structure; LRT proposes a lens through which their achievements can be situated.

This section describes conceptual relations, not derivations or reductions.

**Tegmark's Mathematical Universe Hypothesis.**

Tegmark (2008) proposes that physical reality is mathematical structure. LRT accepts the intimate connection between physics and mathematics but offers an ontological distinction Tegmark's framework lacks: mathematical existence is not physical instantiation. $L_3(I_\infty)$ contains all consistent mathematical structures; $A_\Omega$ is the subset that is physically realized. LRT is compatible with Tegmark's insight that physics is structural while offering a different account of why not all structures are instantiated.

**Ontic Structural Realism.**

OSR (Ladyman and Ross 2007, French 2014) holds that relational structure is ontologically fundamental. LRT is sympathetic: the structures in $A_\Omega$ are individuated by their $L_3$-admissible relations, not by intrinsic haecceities. OSR's detailed work on structural individuation and its resolution of metaphysical puzzles about objects can be adopted within LRT. LRT does not challenge OSR's core claims about structure; it presupposes them. What LRT adds is a specific answer to "which structures?": those satisfying $L_3$.

**Causal Set Theory.**

Causal set approaches (Sorkin 2005) take discrete causal order as fundamental, deriving spacetime as an emergent approximation. LRT's derivation of temporal precedence from joint inadmissibility (Section 2.4) is conceptually compatible with this priority of order over metric structure. The causal set formalism, its results on Lorentz invariance from discreteness, and its approach to quantum dynamics on causal sets represent technical achievements LRT does not replicate. LRT offers a logical motivation for why causal structure might be fundamental; causal set theory provides the mathematics.

**Constructor Theory.**

Deutsch and Marletto (2015) reformulate physics in terms of which transformations are possible or impossible. LRT shares this constraint-first orientation. Constructor theory's formalism, its treatment of information, and its approach to thermodynamics could be read as detailed working-out of admissibility constraints. LRT does not provide the formal machinery constructor theory develops; it offers a metaphysical ground for the possible-impossible distinction constructor theory formalizes.

**Information-Theoretic Reconstructions.**

Programs deriving quantum formalism from information-theoretic axioms (Hardy 2001, Chiribella et al. 2011) demonstrate that quantum theory follows from constraints on information processing. These reconstructions are technical achievements LRT does not replicate. What LRT offers is an account of why information-theoretic axioms have ontological relevance: information processing presupposes $L_3$ (a bit is 0 or 1, not both, and is self-identical). The Born rule derivation (Section 4.2) exemplifies this connection: identity stability, an $L_3$ constraint, forces the probability measure.

**Many-Worlds Interpretation.**

Everett's relative-state formulation (1957) and its modern Many-Worlds descendants propose that all branches of the quantum state are equally real. There is no collapse; the universal wave function evolves unitarily, and what appears as measurement is branching into decohered sectors.

The disagreement between LRT and Many-Worlds is not empirical at present but metaphysical. Trans-temporal determinate identity (Section 3.3) requires that a macroscopic object be numerically one object across time. A history containing the same object in mutually exclusive macroscopic states conflicts with LRT's requirement of trans-temporal determinate identity. Such histories are inadmissible under LRT. Everett proponents deny this identity requirement; they hold that branching is ontologically unproblematic because each branch contains a determinate successor.

This is a substantive disagreement, not a difference of emphasis. Many-Worlds accepts the unrestricted reality of all branches; LRT holds that only one history is included in $A_\Omega$ at the macroscopic scale.

**The successor identity problem.** The Everettian response deserves direct engagement. Everettians may argue that post-branch successors are numerically distinct objects, so no single object occupies incompatible states. Branching is not contradiction but fission.

LRT's reply: the problem is relocated, not resolved. Consider the pre-branch object at $t_0$. After branching at $t_1$, there are two successors. Which is numerically identical to the original? Three options present themselves:

- If *both* successors are identical to the original, identity is not determinate: the original is "equally" each successor, violating the determinacy that Id requires.
- If *neither* successor is identical to the original, the original ceased to exist at branching, replaced by two new objects. But then macroscopic objects routinely cease to exist at every quantum interaction, which conflicts with the manifest persistence of ordinary objects.
- If *exactly one* successor is identical to the original, which one, and by what criterion? No physical fact distinguishes them.

Trans-temporal determinate identity requires that an object have at most one successor in any respect relevant to its identity. Branching violates this. The Everettian view treats identity as a pattern that can split; LRT treats it as a constraint that forbids splitting. This is a genuine metaphysical disagreement, not a verbal one.

However, LRT can acknowledge what Many-Worlds gets right. The universal wave function's unitary evolution is not denied; LRT treats the wave function as a representation of the admissible region of $I_\infty$ (Section 4.1). Decoherence dynamics are accepted as the mechanism selecting pointer bases (Section 4.4). What LRT rejects is the ontological reading that all branches are instantiated. The formalism is compatible; the interpretation is not.

The disagreement is empirically tractable in principle. If macro-branch interference were observed (Section 6.1, Criterion 2), Many-Worlds would be supported and LRT refuted. If persistent macroscopic superposition proves impossible despite increasingly sophisticated isolation, LRT's prediction stands. Current evidence does not discriminate, but the predictions diverge.

**Interpretive Relations.**

The following table summarizes conceptual compatibilities and points of disagreement, not derivations or reductions.

| Framework | Conceptual Compatibility | LRT's Distinct Contribution |
|-----------|--------------------------|----------------------------|
| Tegmark MUH | Physics-mathematics connection | Admissibility ≠ instantiation |
| Ontic Structural Realism | Structural individuation | $L_3$ as selection criterion |
| Causal Set Theory | Priority of order over metric | Logical ground for causal priority |
| Constructor Theory | Constraint-first orientation | Metaphysical ground for possible/impossible |
| Info-Theoretic | Axiomatic reconstructions | Why information axioms have ontological relevance |
| Many-Worlds | Unitary evolution, decoherence | Branching excluded by identity requirement |

LRT proposes that these programs, from different starting points, are characterizing structure compatible with $L_3$-admissibility. This is an interpretive hypothesis, not a demonstrated synthesis. Demonstrating genuine convergence would require showing that the formalisms are technically compatible when reinterpreted in LRT terms. That work remains to be done.

---

## 8. Conclusion

This paper has proposed Logic Realism Theory: the three classical laws of logic function as ontological constraints on physical instantiation.

**The framework:**

$$I_\infty \xrightarrow{L_3} A_\Omega$$

$I_\infty$ is all conceivable configurations. $L_3$ comprises the constraints (Identity, Non-Contradiction, Excluded Middle). $A_\Omega$ is physical reality.

**The central thesis:** Temporal ordering arises from the exclusion of jointly inadmissible configurations. Admissibility is continuous. Each moment is what currently satisfies the constraints.

**What this accounts for:**

| Phenomenon | Mechanism |
|------------|-----------|
| Measurement | Macro identity engages; admissibility selects one outcome |
| Born rule | Identity stability forces quadratic measure |
| Kinetic energy | Identity stability forces quadratic velocity dependence |
| Selection | Flexible determinism; structured availability, not brute chance |
| Planck scale | Minimum individuation resolution |
| Black holes | Identity conditions unsatisfiable; structure returns to $I_\infty$ |
| Hawking radiation | Fresh admissible structure; thermal because identity-uncommitted |
| No actual infinities | Completed infinite individuation inadmissible |
| Single history | Only one included at macro scale |

**Limitations acknowledged:** Specific physics not derived; protective belt requires auxiliary hypotheses; empirical distinguishability from some rival interpretations not established.

**Falsifiable:** Persistent macro superposition, branch interference, identity through singularity, sub-Planck structure, or instantiated infinity would refute the framework.

The framework stands on one claim: classical logical constraints, applied to the space of conceivable configurations, yield physical reality. Everything else follows from that.

Logic is not imposed on reality by minds. It is the constraint structure through which determinate being emerges from possibility.

---

## References

### Logic and Foundations

Frege, G. (1879) *Begriffsschrift*. Halle: Louis Nebert.

Priest, G. (2006) *In Contradiction*. 2nd edn. Oxford: Oxford University Press.

Tahko, T.E. (2009) 'The law of non-contradiction as a metaphysical principle', *Australasian Journal of Logic*, 7, pp. 32-47.

Tahko, T.E. (2021) 'A survey of logical realism', *Synthese*, 198, pp. 4775-4800.

### Philosophy of Science

Lakatos, I. (1978) *The Methodology of Scientific Research Programmes*. Cambridge: Cambridge University Press.

### Quantum Foundations

Bell, J.S. (1964) 'On the Einstein Podolsky Rosen paradox', *Physics Physique Физика*, 1(3), pp. 195-200.

Everett, H. (1957) '"Relative state" formulation of quantum mechanics', *Reviews of Modern Physics*, 29(3), pp. 454-462.

Schlosshauer, M. (2004) 'Decoherence, the measurement problem, and interpretations of quantum mechanics', *Reviews of Modern Physics*, 76(4), pp. 1267-1305.

Zurek, W.H. (2003) 'Decoherence, einselection, and the quantum origins of the classical', *Reviews of Modern Physics*, 75(3), pp. 715-775.

### Quantum Gravity

Bekenstein, J.D. (1973) 'Black holes and entropy', *Physical Review D*, 7(8), pp. 2333-2346.

Hawking, S.W. (1975) 'Particle creation by black holes', *Communications in Mathematical Physics*, 43(3), pp. 199-220.

Penrose, R. (1965) 'Gravitational collapse and space-time singularities', *Physical Review Letters*, 14(3), pp. 57-59.

Sorkin, R.D. (2005) 'Causal sets: discrete gravity', in *Lectures on Quantum Gravity*. New York: Springer, pp. 305-327.

### Philosophy of Physics

French, S. (2014) *The Structure of the World*. Oxford: Oxford University Press.

Ladyman, J. and Ross, D. (2007) *Every Thing Must Go*. Oxford: Oxford University Press.

Maudlin, T. (2019) *Philosophy of Physics: Quantum Theory*. Princeton: Princeton University Press.

Tegmark, M. (2008) 'The mathematical universe', *Foundations of Physics*, 38(2), pp. 101-150.

### Quantum Information

Chiribella, G., D'Ariano, G.M. and Perinotti, P. (2011) 'Informational derivation of quantum theory', *Physical Review A*, 84(1), 012311.

Deutsch, D. and Marletto, C. (2015) 'Constructor theory of information', *Proceedings of the Royal Society A*, 471(2174), 20140540.

Hardy, L. (2001) 'Quantum theory from five reasonable axioms', arXiv:quant-ph/0101012.

### Probability and Measurement

Gleason, A.M. (1957) 'Measures on the closed subspaces of a Hilbert space', *Journal of Mathematics and Mechanics*, 6(6), pp. 885-893.

Busch, P. (2003) 'Quantum states and generalized observables: a simple proof of Gleason's theorem', *Physical Review Letters*, 91(12), 120403.

### Historical Sources

Aristotle. *Metaphysics*. Book IV.

Parmenides. *On Nature*. [Fragments.]
