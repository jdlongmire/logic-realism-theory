# Logic Realism Theory: Physical Reality as Sequenced, Admissible Geometry

**James (JD) Longmire**  
Northrop Grumman Fellow (unaffiliated research)  
ORCID: 0009-0009-1383-7698  
Correspondence: jdlongmire@outlook.com

---

## Abstract

We propose Logic Realism Theory (LRT), a grounding framework for physical theory in which logical admissibility, rather than information, measurement, or dynamics, is taken as the most primitive constraint on physical reality. The theory is based on the compact relation

$$A^* = L_3(I_{\infty}),$$

where $I_{\infty}$ denotes an ontologically real space of possible configurations and $L_3$ denotes the constitutive constraints of identity, non-contradiction, and excluded middle. Physical reality $A^*$ consists only of those configurations of $I_{\infty}$ admissible under $L_3$. From this grounding, mathematics emerges as the formal articulation of admissible distinction, geometry as structured admissible relation, and spacetime as logically sequenced geometry. Time is identified with admissible ordering of actualization rather than a primitive dimension. Dynamics arise from admissibility constraints over histories, yielding a constraint action whose local representation is a Lagrangian, with the Hamiltonian as the generator of admissible temporal evolution. The framework provides unified, non-collapse explanations of quantum non-locality, no-signaling, and the measurement problem, achieving the structural advantages of Many-Worlds interpretations with strictly fewer ontological commitments. LRT is falsifiable at the level of physical admissibility and provides a principled resolution of the "unreasonable effectiveness" of mathematics in physics.

## 1. Introduction

Contemporary fundamental physics exhibits a persistent tension between formal success and ontological clarity. While physical theories achieve extraordinary predictive accuracy, their foundational interpretation remains fragmented across instrumentalist, information-theoretic, and observer-dependent accounts. Nowhere is this tension more evident than in the measurement problem of quantum mechanics (von Neumann, 1932; Albert, 1992), the status of spacetime in quantum gravity (Rovelli, 2004; Smolin, 2001), and the apparent "unreasonable effectiveness" of mathematics in describing physical law (Wigner, 1960).

A common strategy in recent foundational work is to treat information as primitive, often motivated by quantum information theory and operational reconstructions (Hardy, 2001; Chiribella et al., 2011; Fuchs et al., 2014). However, informational approaches presuppose the very structures they aim to explain: distinguishable states, non-contradictory outcomes, determinate actualization, and admissible sequencing. These presuppositions are rarely examined as ontological constraints.

This paper advances a different starting point. We argue that physical theory presupposes ontological admissibility conditions that are not themselves physical laws, but without which no physical law can be formulated. These conditions are captured by the classical logical constraints of identity, non-contradiction, and excluded middle (Frege, 1879; Russell & Whitehead, 1910-1913). Treated ontologically rather than syntactically, these constraints delimit the space of physically realizable configurations prior to dynamics, measurement, or information.

The resulting framework—Logic Realism Theory (LRT)—does not modify the mathematical formalism of physics. Instead, it grounds why physics must take the formal shape it does. Mathematics, geometry, spacetime structure, action principles, and Hamiltonian dynamics emerge as necessary representations of admissible actualization. The theory thereby explains structural features of modern physics that otherwise appear contingent or mysterious, while remaining falsifiable at the level of physical admissibility (Section 9).

## 2. Ontological Admissibility and the L_3 Constraint

### 2.1 Constitutive vs. Regulative Constraints

The constraints central to LRT are not physical laws in the usual sense. They do not govern the behavior of already-existing physical systems. Rather, they are constitutive constraints: conditions that must be satisfied for anything to count as a physically instantiated system at all.

We denote these constraints collectively as $L_3$:

1. **Identity** — a configuration must be determinately self-identical.
2. **Non-contradiction** — incompatible determinations cannot be simultaneously actualized in the same respect.
3. **Excluded middle** — for any determinate respect relevant to realization, a configuration must be actual or non-actual, not indeterminate at the level of actuality.

These principles are standard in logic, but LRT treats them as ontological admissibility conditions, not as rules of inference or linguistic conventions. A violation of $L_3$ does not describe an exotic physical phenomenon; it describes a configuration that cannot be physically instantiated.

### 2.2 The Space of Possible Configurations $I_{\infty}$

Let $I_{\infty}$ denote the space of all possible configurations—understood minimally as distinguishable arrangements or assignments, independent of physical realization. $I_{\infty}$ is not a physical space, a multiverse, or a collection of worlds. It is a modal space of possibility required to make sense of selection, restriction, and actualization.

Physical reality is not identical with $I_{\infty}$. Rather, it is a proper subset determined by admissibility:

$$A^* = L_3(I_{\infty}) = \{\, i \in I_{\infty} \mid L_3(i) \,\}.$$

This equation is the fundamental relation of LRT. It states that actuality is constrained possibility, not information made physical and not dynamics applied to an unconstrained state space.

### 2.3 Consequences for Physical Theory

Once ontological admissibility is made explicit, several consequences follow immediately:

* Physical states must be representable within a consistent state space.
* Physical evolution must preserve admissibility across time.
* Measurement outcomes must be determinate without invoking ad hoc collapse.
* Mathematical consistency becomes a necessary condition for physical realizability, not merely a representational convenience.

These consequences will be developed in subsequent sections. At this stage, the key point is methodological: physics already presupposes $L_3$. LRT makes this presupposition explicit and treats it as foundational.

### 2.4 Assumptions and Scope

While LRT grounds much of physical structure in $L_3$, not everything is derived from pure logic. To maintain clarity about what is established versus what is assumed, we distinguish:

**Derived from $L_3$ alone:**
- Mathematical consistency as a physical necessity (Section 4)
- Identity of indiscernibles and basic distinction structure
- Temporal ordering from logical incompatibility (Definition 3.5-3.6)
- Excluded middle requiring determinate actuality (no ontic contradictions)

**Physical regularity assumptions:**
- **Metric regularity** (Lemma 3.2): The triangle inequality on distinction function $\delta$ is a regularity condition, not a logical necessity. It reflects that physically realizable admissibility structures must be coherently organized.
- **Admissibility continuity** (Sections 5.4, 6.4): Smoothness and quasi-locality are stability requirements ensuring robustness under variation, not logical theorems.
- **Reversibility** (Lemma 3.8): $L_3$ constraints are temporally neutral; this is an ontological claim about admissibility, not purely logical.
- **Boundedness** (Lemma 3.11): The requirement that energy be bounded below is a physical realizability condition.

**Bridge postulates (Quantum Mechanics):**
- **Postulate 8.1**: Hilbert space admits representation as admissibility regions
- **Postulate 8.2**: Admissibility measure corresponds to Born rule

These are not derived but posited as the connection between LRT ontology and quantum formalism.

**Scope of current development:**
- LRT provides *grounding* for physical structure, showing why certain mathematical forms are necessary
- Single temporal dimension is derived necessarily (Proposition 6.1)
- Three spatial dimensions emerge as minimal admissible structure (Proposition 6.2), not brute empirical fact
- Specific dynamics (Einstein equations, gauge field equations, Standard Model) are not yet derived but are targets for future work
- Explicit parameterizations of admissibility microstructure $(A^*_\theta, d_{A,\theta}, \prec_\theta)$ remain to be developed

This framework distinguishes LRT from purely logical derivations (which would be too strong) and mere interpretation (which would be too weak). The theory makes substantive physical commitments while acknowledging what remains to be established.

## 3. Formal Structure of Logic Realism Theory

This section introduces the formal primitives and relations of Logic Realism Theory (LRT). No physical, geometric, temporal, or informational structure is presupposed beyond what is explicitly defined.

### 3.1 Ontological Possibility Space

**Definition 3.1 (Ontological Possibility Space).**  
Let $I_{\infty}$ denote a non-empty set whose elements $i$ are called configurations. Each configuration represents a fully specified but non-instantiated arrangement of distinguishable determinations.

No topology, metric, probability measure, causal structure, or temporal ordering is assumed on $I_{\infty}$.

### 3.2 Ontological Admissibility Predicate

**Definition 3.2 (Admissibility Predicate).**  
Define the admissibility predicate

$$L_3 : I_{\infty} \rightarrow \{\mathrm{True},\mathrm{False}\}$$

such that for any $i \in I_{\infty}$,

$$L_3(i) := \mathrm{Id}(i)\ \wedge\ \mathrm{NC}(i)\ \wedge\ \mathrm{EM}(i),$$

where:

* **Identity** $\mathrm{Id}(i)$: $i$ is determinate as itself (self-identical configuration).
* **Non-Contradiction** $\mathrm{NC}(i)$: $i$ does not entail mutually incompatible determinations in the same respect.
* **Excluded Middle** $\mathrm{EM}(i)$: For every determinate respect relevant to instantiation, $i$ is either actualizable or not actualizable; no third ontological state is permitted at the level of actuality.

These conditions are ontological constraints, not syntactic or epistemic principles.

### 3.3 Physically Actualized Reality

**Definition 3.3 (Physically Actualized Reality).**  
The set of physically actualized configurations is defined as

$$A^* \;\coloneqq\; L_3(I_{\infty}) \;=\; \{\, i \in I_{\infty} \mid L_3(i) \,\}.$$

The relation

$$\boxed{A^* = L_3(I_{\infty})}$$

is the fundamental equation of Logic Realism Theory.

### 3.4 Asymmetry of Possibility and Actualization

**Proposition 3.1 (Modal Asymmetry).**

$$A^* \subset I_{\infty}, \qquad A^* \neq I_{\infty}.$$

**Corollary 3.1.**

$$I_{\infty} \not\Rightarrow A^*, \qquad A^* \Rightarrow I_{\infty}.$$

Ontological possibility does not imply physical instantiation, whereas physical instantiation presupposes ontological possibility.

### 3.5 History Space and Sequencing

**Definition 3.4 (History Space).**  
Let $\Gamma$ denote the space of histories, where each history is a mapping

$$\gamma : \mathbb{O} \rightarrow A^*,$$

and $\mathbb{O}$ is an abstract ordering domain.

No metric, topology, or temporal interpretation is assumed on $\mathbb{O}$.

### 3.6 Time as Logical Ordering

**Definition 3.5 (Temporal Ordering).**  
For $i_1, i_2 \in A^*$, define the binary relation

$$i_1 \prec i_2 \iff L_3(i_1) \land L_3(i_2) \land \neg L_3(i_1 \sqcup i_2),$$

where $i_1 \sqcup i_2$ denotes the minimal configuration containing all determinations of $i_1$ and $i_2$; no algebraic closure is assumed beyond definability of joint determination.

The relation $\prec$ is a strict partial order induced by admissibility, not assumed a priori.

**Definition 3.6 (Time).**  
Time is the partial order $(\prec, A^*)$ induced by ontological admissibility. Temporal succession is logical incompatibility of joint actualization.

Time is therefore logical sequencing of admissible actualization, not a primitive dimension.

### 3.7 Admissibility Constraints over Histories

**Definition 3.7 (Constraint Functional).**  
Let

$$C : \Gamma \rightarrow \mathbb{R}^k$$

be a constraint functional encoding admissibility over histories. A history $\gamma$ is physically admissible iff

$$C[\gamma] = 0.$$

Specifically, $C[\gamma] = 0$ requires:

$$\forall o_1, o_2 \in \mathbb{O}: o_1 < o_2 \Rightarrow \gamma(o_1) \prec \gamma(o_2) \lor \gamma(o_1) \sim \gamma(o_2),$$

where $\sim$ denotes compatibility (joint actualization does not violate $L_3$). The constraint ensures histories respect the logical ordering structure of $A^*$.

**Lemma 3.1 (Distinguishability Measure).**  
For any $i_1, i_2 \in A^*$, the **Identity** constraint $\mathrm{Id}$ requires that configurations be determinately self-identical, which implies determinate distinction from non-identical configurations.

Define the **distinction function**:

$$\delta : A^* \times A^* \rightarrow [0,\infty)$$

such that for $i_1, i_2 \in A^*$:

$$\delta(i_1, i_2) = 0 \iff i_1 = i_2$$
$$\delta(i_1, i_2) > 0 \iff i_1 \neq i_2$$

The value $\delta(i_1, i_2)$ quantifies the degree of determination difference between configurations.

**Lemma 3.2 (Metric Compatibility).**  
If the distinction function $\delta$ satisfies:

1. **Non-negativity**: $\delta(i_1, i_2) \geq 0$
2. **Identity of indiscernibles**: $\delta(i_1, i_2) = 0 \iff i_1 = i_2$
3. **Symmetry**: $\delta(i_1, i_2) = \delta(i_2, i_1)$
4. **Triangle inequality**: $\delta(i_1, i_3) \leq \delta(i_1, i_2) + \delta(i_2, i_3)$

then $(A^*, \delta)$ forms a metric space.

Properties (1)–(3) follow directly from the definition and **Identity**. Property (4) is a regularity condition: physical realizability requires admissible configuration spaces to admit metric structure consistent with the triangle inequality. This establishes $(A^*, \delta)$ as a metric space.

**Definition 3.7a (Configuration Metric).**  
The metric on $A^*$ induced by $L_3$ is:

$$d_A : A^* \times A^* \rightarrow [0,\infty), \quad d_A(i_1, i_2) := \delta(i_1, i_2).$$

This metric structure arises necessarily from the **Identity** constraint without additional geometric postulates.

### 3.8 Constraint Action and Variational Principle

**Lemma 3.3 (Path Length in Configuration Space).**

For a history $\gamma : \mathbb{O} \rightarrow A^*$, define the path length:

$$\ell[\gamma] = \int_{\mathbb{O}} \|\dot{\gamma}\| \, do,$$

where $\|\dot{\gamma}\| = \lim_{\Delta o \rightarrow 0} d_A(\gamma(o), \gamma(o+\Delta o))/\Delta o$ is the rate of configuration change. This measures total distance traveled through $A^*$ along the history.

**Lemma 3.4 (Kinetic Term from Rate Penalization).**

Admissible sequencing via $\prec$ implies transitions require traversing intermediate states. Rapid configuration change (large $\|\dot{\gamma}\|$) increases proximity to inadmissibility. This admits a lowest-order rate-dependent cost:

$$T[\gamma] = \int \frac{1}{2} m(\gamma) \|\dot{\gamma}\|^2 \, do,$$

where $m(\gamma)$ is configuration-dependent inertial resistance. The quadratic form arises because cost scales with both speed and density of change. Higher-order terms are suppressed by admissibility regularity.

**Lemma 3.5 (Admissibility Gradient).**

Define the admissibility proximity function:

$$\phi : A^* \rightarrow [0,\infty), \quad \phi(i) = \inf_{j \notin A^*} d_A(i, j)$$

measuring minimal distance from $i$ to the boundary of inadmissible configurations.

**Lemma 3.6 (Potential Term from Configuration Cost).**

Actualization near low-$\phi$ regions (close to $L_3$ violation) carries higher ontological cost. Define:

$$V[\gamma] = \int V(\gamma(o)) \, do, \quad \text{where } V(i) = f(\phi(i))$$

with $f$ decreasing: lower admissibility proximity yields higher potential.

**Lemma 3.7 (Logical Neutrality of $L_3$).**

The constraints $\mathrm{Id} \wedge \mathrm{NC} \wedge \mathrm{EM}$ make no reference to temporal direction. They are purely structural, with no preferred time orientation.

**Lemma 3.8 (History Reversibility).**

If $\gamma : \mathbb{O} \rightarrow A^*$ satisfies $C[\gamma]=0$, then the reversed history $\gamma^{\text{rev}}(o) := \gamma(o_{\max} - o)$ also satisfies $C[\gamma^{\text{rev}}]=0$.

*Proof:* $L_3$ constraints are symmetric under sequence reversal. If configurations are ordered $i_1 \prec i_2$ to avoid contradiction, reversing gives $i_2 \prec i_1$, equally valid. $\square$

This reversibility holds at the level of admissibility constraints and does not preclude emergent temporal asymmetries introduced by boundary conditions or coarse-graining.

**Lemma 3.9 (Action Symmetry).**

Time-reversal symmetry requires $S[\gamma] = S[\gamma^{\text{rev}}]$, forcing the Lagrangian to depend only on even powers of velocity: $L(q, \dot{q}^2)$.

**Lemma 3.10 (Additivity and Dimensional Consistency).**

For independent subsystems $i = i_A \oplus i_B$:

$$L_3(i_A \oplus i_B) = L_3(i_A) \wedge L_3(i_B) \Rightarrow L(q_A \oplus q_B) = L_A(q_A) + L_B(q_B)$$

Both $T$ and $V$ have dimensions of energy. Consistent combination requires linear form: $L = \alpha T + \beta V$.

**Lemma 3.11 (Sign Determination from Boundedness).**

For $L = T + V$: conserved quantity $E = T - V$ is unbounded below (unphysical).
For $L = T - V$: conserved quantity $E = T + V \geq 0$ is bounded below (stable dynamics).

Physical realizability requires the latter.

**Proposition 3.2 (Existence and Form of Action Functional).**  
Physically admissible histories characterized by $C[\gamma]=0$ generate an action functional:

$$S[\gamma] = \int (T - V) \, do = \int L(q, \dot{q}) \, do$$

where $T = \frac{1}{2}m\dot{q}^2$ (Lemma 3.4) and $V = V(q)$ (Lemma 3.6), with sign structure determined by reversibility (Lemmas 3.7-3.9) and boundedness (Lemma 3.11).

The physically realized history satisfies:

$$\gamma^* = \arg\operatorname{ext}_{\gamma \in \Gamma} S[\gamma], \quad \text{subject to } C[\gamma]=0.$$

This form is uniquely determined up to admissibility-preserving reparameterizations.

### 3.9 Lagrangian as Local Admissibility Density

**Definition 3.8 (Lagrangian).**  
The Lagrangian $L$ is the local density whose extremization enforces admissibility constraints along a history.

The Lagrangian is not ontologically primitive; it is a local representation of a global admissibility condition.

### 3.10 Hamiltonian as Generator of Admissible Sequencing

**Definition 3.9 (Hamiltonian).**  
Given canonical variables $(q_i,p_i)$, define

$$p_i := \frac{\partial L}{\partial \dot q_i}, \qquad H(q,p,t) := \sum_i p_i \dot q_i - L.$$

The Hamiltonian generates admissible temporal evolution in phase space.

### 3.11 Constraint–Hamiltonian Duality

**Proposition 3.3 (Dual Representation).**  
Constraint-first admissibility implies Hamiltonian evolution on a restricted phase space. Gauge freedom corresponds to non-physical degrees of freedom in $I_{\infty}$ excluded from $A^*$ by $L_3$.

### 3.12 Structural Summary

Within LRT:

* **Ontology:** $A^* = L_3(I_{\infty})$
* **Geometry:** structured admissible relations on $A^*$
* **Time:** admissible ordering on $A^*$
* **Spacetime:** ordered geometry
* **Dynamics:** admissible sequencing
* **Measurement:** admissible actualization, not collapse

This section provides the formal backbone for all subsequent physical claims. All results in later sections are derived consequences of the structures defined here.

## 4. Mathematics as Formal Articulation of Admissible Distinction

### 4.1 The Unreasonable Effectiveness Problem

Eugene Wigner (1960) famously described the "unreasonable effectiveness of mathematics in the natural sciences" as a phenomenon requiring explanation. Why should abstract mathematical structures, developed independently of physical concerns, provide such precise descriptions of physical law? Standard responses fall into three categories:

1. **Instrumentalist**: Mathematics is merely a convenient language with no ontological import (van Fraassen, 1980).
2. **Platonist**: Mathematical structures exist independently, and physical reality somehow instantiates them (Balaguer, 1998).
3. **Structural realist**: Physics discovers mathematical structures that constitute physical reality (Tegmark, 2008; French, 2014).

LRT offers a fourth explanation: mathematics is not applied to physics from outside, nor is physics a subset of mathematics. Rather, mathematical structure is the formal articulation of distinctions that must hold for any physically realizable configuration.

### 4.2 Mathematics from Identity and Distinction

The **Identity** constraint $\mathrm{Id}(i)$ requires that each configuration $i \in A^*$ be determinately self-identical. This seemingly trivial requirement has profound consequences.

**Observation 4.1.** If $i_1 \neq i_2$, then the configurations differ with respect to at least one determination. The ability to distinguish configurations requires determinate difference.

The distinction function $\delta(i_1, i_2)$ (Definition 3.7a) quantifies this difference. But quantification itself presupposes:

- **Number**: distinctions can be counted or measured
- **Relation**: configurations can be compared
- **Structure**: patterns of distinction are reproducible

These are mathematical concepts, but they are not imported from abstract mathematical space. They emerge necessarily from the requirement that configurations be determinately distinguishable.

### 4.3 Mathematical Consistency as Physical Necessity

**Proposition 4.1 (Mathematical Consistency Requirement).**  
Any formal system used to represent configurations in $A^*$ must be logically consistent.

*Proof:* Suppose a formal system $\mathcal{F}$ representing $A^*$ contains a contradiction: both $P$ and $\neg P$ are theorems of $\mathcal{F}$.

By the principle of explosion, any proposition $Q$ is derivable in $\mathcal{F}$. Therefore $\mathcal{F}$ cannot distinguish between configurations, violating **Identity**.

Moreover, if $\mathcal{F}$ asserts $P \land \neg P$ about a configuration, this violates **Non-Contradiction** directly.

Therefore, any formal representation of $A^*$ must be consistent. This argument presupposes classical consequence relations, which are required for physical instantiation under $L_3$. $\square$

**Corollary 4.1.**  
Mathematics works in physics not because physical reality happens to be mathematical, but because mathematical consistency is required for physical realizability under $L_3$.

### 4.4 Distinction from Mathematical Platonism

LRT is not a variant of Tegmark's Mathematical Universe Hypothesis (MUH) (Tegmark, 2008), which claims physical reality *is* a mathematical structure. The distinction is crucial:

**MUH**: Mathematical structures exist abstractly and independently; physical reality is identified with one (or all) such structures.

**LRT**: Physical reality is $A^* = L_3(I_{\infty})$, a proper subset of possible configurations selected by admissibility constraints. Mathematics is the formal language that *must* be usable to describe $A^*$ because $L_3$ requires determinate distinction, which forces mathematical structure.

In MUH, mathematics is ontologically prior to physics. In LRT, admissibility is prior to both, and mathematics emerges as the necessary formal articulation of admissible distinction.

### 4.5 Why Mathematics Must Be Applicable

The "unreasonable effectiveness" dissolves once we recognize:

1. **Physical configurations must be determinately distinguishable** (from Identity).
2. **Distinguishability requires formal structure** (relations, ordering, measure).
3. **Formal structure consistent with $L_3$ is precisely what mathematics provides**.

Mathematics is effective in physics not by cosmic coincidence or Platonic correspondence, but because physics presupposes the very distinctions that mathematics formalizes.

**Observation 4.2.** When physicists discover a new mathematical structure that accurately describes physical phenomena, they are not finding a pre-existing abstract object. They are articulating the admissibility structure that was already constraining physical reality.

### 4.6 Scope and Limits

This account explains why mathematics must be applicable to physics and why it must be consistent. It does not explain:

- Why specific mathematical structures (groups, manifolds, Hilbert spaces) appear in particular physical theories (this is addressed in Sections 5-6).
- Why some mathematical structures remain physically unrealized (these correspond to configurations excluded from $A^*$ by $L_3$).

The emergence of specific geometric and algebraic structures from admissibility constraints is the subject of the following sections.

## 5. Geometry as Structured Admissible Relation

### 5.1 From Distinction to Relation

Section 4 established that mathematics arises as the formal articulation of admissible distinction. Distinction alone, however, is insufficient for physical instantiation. Physical reality requires not only that configurations be distinguishable, but that relations among configurations be coherently structured.

Relations such as proximity, continuity, symmetry, and transformation are not optional descriptive tools. They are required to represent how admissible configurations can vary without violating ontological constraints. The formal study of such relations is geometry.

Within LRT, geometry is therefore not imposed on physical theory as an external framework. It emerges as the minimal structure required to organize admissible configurations in $A^*$.

### 5.2 Metric Structure and Physical Representability

In Section 3, a distinction function $\delta$ was introduced and shown to be compatible with metric structure under admissibility regularity. When such a metric $d_A$ exists, $(A^*, d_A)$ forms a metric space.

This result has immediate physical significance. Without metric structure:

* continuity cannot be defined,
* limits cannot be taken,
* variation cannot be formalized,
* and stable evolution cannot be represented.

Accordingly, any physically realizable configuration space must admit a geometric structure compatible with admissibility. This requirement is not dynamical; it is ontological.

### 5.3 Geometry as Constraint, Not Representation

It is common to treat geometry as a representational choice: Euclidean for classical mechanics, pseudo-Riemannian for relativity, Hilbert-space geometry for quantum theory. LRT inverts this perspective.

On the LRT view:

**Geometry is the formal encoding of admissible relational structure.**

Different physical theories employ different geometries not because geometry is freely chosen, but because different domains of admissible configurations impose different relational constraints.

Thus:

* Configuration spaces are geometric because admissibility requires coherent relation.
* Phase spaces are geometric because admissible change must be structured.
* Hilbert spaces are geometric because admissible superposition requires inner-product structure to preserve distinguishability and normalization.

Geometry is therefore forced by admissibility, not selected by convenience.

### 5.4 Emergence of Manifolds and Continuity

Physical theories overwhelmingly employ smooth manifolds. Within LRT, this is not an assumption but a consequence of admissibility regularity.

**Plausibility argument (not proof):**  
If admissible configurations could vary only discontinuously, then arbitrarily small changes would risk violating admissibility constraints, undermining stable actualization. Smoothness provides robustness under variation, ensuring that nearby configurations remain admissible.

Accordingly, admissibility regularity *favors* (though does not logically necessitate):

* continuous configuration spaces,
* differentiable structure,
* local linear approximations.

These are precisely the defining features of manifolds. This is a stability and robustness argument: physically realizable admissibility structures will generically be smooth because discontinuous structures are fragile. Full mathematical derivation of manifold necessity remains an open question.

### 5.5 Symmetry as Admissibility Invariance

Symmetries play a central role in modern physics. In LRT, symmetry is not fundamental; it is derivative.

A symmetry corresponds to a transformation that preserves admissibility:

$$i \in A^* \;\Rightarrow\; g(i) \in A^*$$

for some transformation $g$.

Symmetry groups therefore encode invariances of admissibility, not deep metaphysical truths about reality. This explains why symmetry principles are powerful but defeasible: when admissibility changes, symmetry can break.

### 5.6 Why Geometry Precedes Dynamics

Dynamics presuppose geometry. Equations of motion require:

* a space of states,
* relations among states,
* measures of change.

All of these are geometric notions. For this reason, LRT insists on a strict ordering:

$$\text{Admissibility} \;\rightarrow\; \text{Mathematics} \;\rightarrow\; \text{Geometry} \;\rightarrow\; \text{Dynamics}$$

This ordering prevents a common foundational error: treating dynamical equations as primitive while leaving the structure of state space unexplained.

### 5.7 Summary

Within Logic Realism Theory:

* Geometry arises from the need to structure admissible relations among configurations.
* Metric and manifold structures are required for stable actualization.
* Symmetries encode invariances of admissibility, not fundamental laws.
* Geometry is ontologically prior to dynamics.

This prepares the ground for the next step: the incorporation of logical sequencing, yielding spacetime as an ordered geometric structure.

## 6. Spacetime as Logically Sequenced Geometry

### 6.1 The Status of Spacetime in Physical Theory

In standard approaches to fundamental physics, spacetime is treated as either:

1. **Primitive background structure** (classical field theory, special relativity) (Einstein, 1916; Minkowski, 1909)
2. **Dynamical field** (general relativity) (Einstein, 1916)
3. **Emergent from quantum degrees of freedom** (various quantum gravity proposals) (Rovelli, 2004; Sorkin, 2005)

Each approach faces foundational difficulties. Background spacetime is metaphysically suspect (what is it made of?). Dynamical spacetime requires pre-geometric structure to define dynamics. Emergent spacetime proposals often presuppose the very structures they aim to derive.

LRT offers a different grounding: spacetime is neither primitive nor emergent from more fundamental physical entities. It is the synthesis of geometric structure (Section 5) with logical ordering (Section 3).

### 6.2 Time as Logical Ordering (Recapitulation)

In Definition 3.6, time was identified with the partial order $(\prec, A^*)$ induced by ontological admissibility. Specifically, $i_1 \prec i_2$ when both configurations are individually admissible but their joint actualization violates $L_3$.

This grounding eliminates time as a primitive dimension. Temporal structure arises from the logical incompatibility of certain configurations being co-actualized. There is no "flow" of time, no objective "now," and no temporal becoming beyond the ordering of admissible actualization.

### 6.3 Spacetime as Ordered Geometry

Geometry provides relational structure on $A^*$. Temporal ordering $\prec$ provides sequencing structure on $A^*$. Their synthesis yields spacetime.

**Definition 6.1 (Spacetime Structure).**  
Spacetime is the ordered metric space $(A^*, d_A, \prec)$, where:

* $d_A$ provides geometric (relational) structure among configurations
* $\prec$ provides temporal ordering of actualization
* The combination structures both "where" and "when" admissible configurations can be realized

We call $d_A$ "spatial" only after restricting to compatibility classes (co-actualizable configurations under $\sim$), where $d_A$ functions as a distance on simultaneous relational degrees of freedom.

Spacetime is therefore not a container in which physics happens, but the formal representation of admissible relational and sequential structure.

### 6.4 Locality as Derivative

Locality (the principle that interactions occur at spacetime points and propagate continuously) is typically assumed in field theory. Within LRT, locality emerges as a regularity condition on admissibility structure.

**Proposition 6.1 (Locality as Admissibility Regularity).**  
Assume:
1. $d_A$ induces a topology under which admissibility constraints are continuous
2. The constraint functional $C[\gamma]$ is quasi-local: its value is determined by bounded neighborhoods in $d_A$

Then admissible influences propagate through bounded $d_A$-neighborhoods, yielding an effective locality principle.

*Justification:* Non-local interactions would require configurations at arbitrarily large $d_A$ separation to jointly determine admissibility in violation of quasi-locality. Configurations separated by large $d_A$ have independent determination structure when constraints are continuous and quasi-local.

These regularity conditions are not derived from more primitive principles in LRT, but represent consistency requirements on physically realizable admissibility structures.

### 6.5 Relativistic Structure Without Postulating Spacetime

The Minkowski metric of special relativity has signature $(-,+,+,+)$, distinguishing time from space. Within LRT, the qualitative origin of this signature can be understood through the fundamental distinction between temporal ordering and spatial relation.

The temporal ordering $\prec$ is fundamentally different from spatial relations $d_A$:

* **Spatial relations** are symmetric: $d_A(i_1, i_2) = d_A(i_2, i_1)$
* **Temporal ordering** is asymmetric: $i_1 \prec i_2$ does not imply $i_2 \prec i_1$

When these structures are combined into a unified geometric representation (the spacetime metric), the asymmetry of $\prec$ motivates a signature with opposite sign for temporal components.

**Observation 6.1 (Qualitative Origin of Temporal Sign).**  
The asymmetry of $\prec$, contrasted with the symmetry of $d_A$, motivates a pseudo-metric representation in which the ordered dimension enters with opposite sign. Recovering the specific Lorentzian form $(-,+,+,+)$ requires additional regularity and invariance assumptions: local linear structure, invariant causal cones, and spatial isotropy/homogeneity. These are addressed through the dimensionality and degrees of freedom analysis in Sections 6.6-6.7.

### 6.6 Dimensionality and Degrees of Freedom

Why does physical spacetime have three spatial dimensions and one temporal dimension, rather than some other configuration?

LRT does not derive the specific dimensionality 3+1, but it provides the framework for understanding why dimensionality matters. The number of spatial dimensions corresponds to the degrees of freedom required to specify distinguishable configurations in $A^*$. The single temporal dimension corresponds to the single ordering structure $\prec$.

If physical systems required more degrees of freedom to specify admissible distinctions, higher-dimensional spatial structure would emerge. If multiple independent ordering relations existed on $A^*$, multiple temporal dimensions could appear. The observed 3+1 structure is therefore an empirical constraint on the admissibility structure of our physical reality, not a metaphysical necessity.

### 6.7 Derivation of Minimal Spacetime Dimensionality

While LRT does not uniquely determine 3+1 dimensions from pure logic, it constrains dimensionality through admissibility requirements for stable, non-degenerate physical structure.

**Proposition 6.1 (Temporal Dimensionality).**  
Physical spacetime must have exactly one temporal dimension.

*Proof:* Time is defined as the ordering relation $\prec$ induced by admissibility (Definition 3.6). A second independent temporal ordering $\prec'$ would require independent admissibility constraints determining when configurations can be jointly actualized. However, $L_3$ provides a single global constraint structure: configurations either violate **Non-Contradiction** under joint actualization or they don't. Multiple independent orderings would require configurations to be simultaneously ordered and unordered with respect to different temporal dimensions, violating determinate identity. Therefore, exactly one temporal dimension is necessary. $\square$

**Proposition 6.2 (Minimal Spatial Dimensionality).**  
Physical spacetime requires at least three spatial dimensions for stable, non-degenerate admissible structure.

*Justification (admissibility regularity argument):*

**1-dimensional space:** No nontrivial relational structure. All configurations lie on a line; no structure for rotational degrees of freedom, no possibility of stable localized excitations that can avoid each other.

**2-dimensional space:** Topologically unstable. No knotting (all paths can be continuously deformed into each other), no stable localized field configurations (no non-trivial homotopy groups for gauge fields), gravitational dynamics degenerate (no propagating gravitational waves in 2+1 GR).

**3-dimensional space:** Minimal structure supporting:
- Nontrivial topology (knots exist)
- Stable localized excitations (particles)  
- Rich relational structure (arbitrary rotations)
- Non-degenerate gravitational dynamics

This is essentially Ehrenfest's stability argument (1917), reframed: admissibility regularity requires sufficient relational structure for stable, information-rich configurations. Three spatial dimensions provide the minimal such structure. $\square$

**Observation 6.2 (Higher Dimensions).**  
Spaces with more than three spatial dimensions are not excluded by $L_3$ but face stability challenges. Generic perturbations in $d > 3$ lead to:
- Gravitational instability (inverse-square force laws generalize to $r^{-(d-1)}$, affecting bound states)
- Dynamical degeneracy (many more degrees of freedom without corresponding stabilization)
- Compactification requirements (extra dimensions must be stabilized/hidden)

Higher-dimensional theories (string theory, Kaluza-Klein) address these by imposing additional constraints. LRT suggests such constraints are admissibility requirements for stable higher-dimensional structure.

**Summary:**  
LRT derives 1 temporal dimension necessarily and 3 spatial dimensions as the minimal admissible structure supporting stable, dynamically rich physical reality. The specific value 3 is selection-by-constraint rather than arbitrary empirical fact or unique logical necessity. Higher dimensions remain logically possible but require additional admissibility structure to avoid instability.

### 6.8 Quantum Spacetime and Discreteness

If admissibility at fundamental scales imposes discreteness (minimal distinguishable configurations), spacetime would exhibit discrete structure near the Planck scale. This would not contradict LRT, but rather specify the detailed form of $d_A$ and $\prec$ at extreme scales.

Proposals for discrete spacetime, quantum geometry, or causal sets can be understood within LRT as specific hypotheses about the fine structure of $(A^*, d_A, \prec)$ at scales where admissibility constraints become maximally restrictive.

### 6.9 Summary

Within Logic Realism Theory:

* Spacetime is not primitive, dynamical, or emergent from quantum degrees of freedom.
* Spacetime is the ordered geometric structure $(A^*, d_A, \prec)$.
* Locality follows from the requirement that admissibility be locally determined.
* Relativistic signature follows from the asymmetry of temporal ordering versus spatial relation.
* Dimensionality reflects the degrees of freedom in admissible configurations.

This completes the derivation chain:

$$L_3 \rightarrow \text{Mathematics} \rightarrow \text{Geometry} \rightarrow \text{Spacetime} \rightarrow \text{Dynamics}$$

The next section addresses how dynamics emerge from admissibility constraints over spacetime histories.

## 7. Dynamics from Admissibility Constraints

### 7.1 From Ordered Geometry to Admissible Histories

Section 6 defines spacetime as the ordered geometric structure $(A^*, d_A, \prec)$. A dynamical law in LRT is not primitive; it is a rule for selecting physically realized histories $\gamma \in \Gamma$ consistent with admissibility.

Let $\Gamma$ be the space of histories $\gamma : \mathbb{O} \to A^*$ (Definition 3.4). Let $C[\gamma]=0$ encode admissibility of histories (Definition 3.7). Dynamics, on this view, is a selection principle over admissible histories, i.e. a map

$$\mathcal{D}:\{\gamma\in\Gamma \mid C[\gamma]=0\}\to \Gamma^*\subseteq \Gamma.$$

In LRT, $\mathcal{D}$ is represented by a variational principle.

### 7.2 Constraint Action

**Definition 7.1 (Constraint Action).**  
A constraint action is a functional $S:\Gamma\to\mathbb{R}$ such that the realized history $\gamma^*$ satisfies

$$\gamma^* \in \arg\operatorname{ext}_{\gamma\in\Gamma} S[\gamma] \quad \text{subject to}\quad C[\gamma]=0.$$

When constraints admit a local representation, write $C[\gamma] = \int c(\gamma,\dot\gamma,o)\,do$ where $c$ is a local constraint density, and the admissibility condition becomes $c(\gamma,\dot\gamma,o)=0$ at each ordering parameter value. The augmented action can then be written:

$$S[\gamma,\lambda] \;=\; \int_{\mathbb{O}} \Big(L(\gamma,\dot\gamma)\;+\;\lambda\cdot c(\gamma,\dot\gamma)\Big)\,do,$$

where $\lambda$ is a multiplier field and "$\cdot$" denotes contraction over constraint components.

This expresses the core claim: admissibility is global; the action is its dynamical encoding.

### 7.3 Lagrangian as Local Density

Given sufficient regularity to express $S$ as an integral over the ordering domain $\mathbb{O}$, there exists a Lagrangian density $L$ such that

$$S[\gamma] \;=\; \int_{\mathbb{O}} L(\gamma(o),\dot\gamma(o),o)\,do.$$

Under the reversibility condition in Section 3 (Lemma 3.8) and action symmetry (Lemma 3.9), the lowest-order dependence is even in $\dot\gamma$. In local coordinates $q$ on the admissible configuration space, the minimal admissibility-compatible form is

$$L(q,\dot q,o) = T(q,\dot q) - V(q),$$

where $T$ is quadratic in $\dot q$ at lowest order and $V$ penalizes proximity to inadmissibility as encoded by $\phi$ (Lemma 3.5–3.6).

### 7.4 Euler–Lagrange Evolution as Admissible Sequencing

If $L$ is differentiable in $(q,\dot q)$, stationary histories satisfy the Euler–Lagrange equations:

$$\frac{d}{do}\Big(\frac{\partial L}{\partial \dot q_i}\Big) - \frac{\partial L}{\partial q_i} = 0,$$

together with the constraint equations enforcing $C[\gamma]=0$.

In LRT these equations do not define "what nature does" from nowhere; they define which histories are compatible with admissible sequencing in $(A^*, d_A, \prec)$.

### 7.5 Hamiltonian Formalism and Generator Interpretation

Define canonical momenta

$$p_i := \frac{\partial L}{\partial \dot q_i},$$

and Hamiltonian

$$H(q,p,o) := \sum_i p_i \dot q_i - L(q,\dot q,o).$$

When $L$ is regular (Legendre transform exists), evolution can be written as Hamilton's equations:

$$\dot q_i = \frac{\partial H}{\partial p_i},\qquad \dot p_i = -\frac{\partial H}{\partial q_i}.$$

**Interpretive claim:** In LRT, $H$ is the generator of admissible sequencing—the algebraic representation of permitted transitions within the admissible state structure, rather than an independently postulated "energy object."

#### 7.5.1 Energy as Conserved Admissibility Cost

The connection between the Hamiltonian and physical energy requires explicit derivation. We establish this through temporal translation symmetry and Noether's theorem applied to admissibility structure.

**Lemma 7.1 (Temporal Translation Invariance).**  
If the admissibility constraints $L_3$ do not depend explicitly on the ordering parameter $o$ (i.e., what is admissible does not change with temporal position), then the Lagrangian satisfies:

$$\frac{\partial L}{\partial o} = 0.$$

This is temporal homogeneity: the rules of admissibility are the same at all temporal positions along the history. The ordering parameter $o$ plays the role of a time parameter in the variational formulation, and invariance under the transformation $o \mapsto o + \epsilon$ (parameter translation) yields a conserved quantity via Noether's theorem.

**Proposition 7.1 (Energy Conservation from Temporal Symmetry).**  
When $\partial L/\partial o = 0$, the quantity

$$E := \sum_i p_i \dot q_i - L = H(q,p)$$

is conserved along admissible histories.

*Proof:* Consider the total time derivative of $L$:

$$\frac{dL}{do} = \sum_i \frac{\partial L}{\partial q_i}\dot q_i + \sum_i \frac{\partial L}{\partial \dot q_i}\ddot q_i + \frac{\partial L}{\partial o}.$$

By the Euler-Lagrange equations:

$$\frac{\partial L}{\partial q_i} = \frac{d}{do}\frac{\partial L}{\partial \dot q_i} = \frac{dp_i}{do}.$$

Substituting:

$$\frac{dL}{do} = \sum_i \frac{dp_i}{do}\dot q_i + \sum_i p_i \ddot q_i + \frac{\partial L}{\partial o}.$$

Therefore:

$$\frac{d}{do}\Big(\sum_i p_i \dot q_i - L\Big) = \sum_i p_i \ddot q_i + \sum_i \dot q_i \frac{dp_i}{do} - \sum_i \frac{dp_i}{do}\dot q_i - \sum_i p_i \ddot q_i - \frac{\partial L}{\partial o} = -\frac{\partial L}{\partial o}.$$

When $\partial L/\partial o = 0$:

$$\frac{dE}{do} = 0. \quad \square$$

This is Noether's theorem for temporal translation: temporal symmetry implies energy conservation.

**Corollary 7.1.**  
The Hamiltonian $H = T + V$ is the conserved energy when admissibility constraints are temporally homogeneous.

#### 7.5.2 Ontological Interpretation of Energy

What does energy *represent* in LRT?

Recall from Section 3:
- Kinetic term $T$ measures cost of rate of change through configuration space (Lemma 3.4)
- Potential term $V$ measures configuration-dependent proximity to inadmissibility (Lemma 3.6)

The conserved energy $E = T + V$ therefore represents:

**Total admissibility cost**: the sum of transition cost (kinetic) and state cost (potential) that remains constant along physically realized histories.

**Physical interpretation:**

1. **Energy is not primitive** - it emerges from admissibility structure
2. **Energy conservation** - reflects temporal homogeneity of $L_3$ constraints
3. **Energy transformation** - trading kinetic for potential is trading transition cost for state cost while preserving total admissibility burden
4. **Energy as generator** - $H$ generates temporal evolution precisely because it encodes how admissibility cost transforms under sequencing

This grounds energy in ontological admissibility rather than treating it as an unexplained primitive.

#### 7.5.3 Why Energy Must Be Additive

For composite systems with independent subsystems $A$ and $B$:

$$H_{\text{total}} = H_A + H_B + H_{\text{int}},$$

where $H_{\text{int}}$ captures interaction.

This additivity follows from the admissibility factorization established in Lemma 3.10: independent subsystems have additive admissibility costs. Energy additivity is therefore not a postulate but a consequence of how admissibility constraints compose.

**Summary of energy derivation:**

- Energy emerges from Noether's theorem applied to temporal homogeneity of $L_3$
- Energy equals total admissibility cost $E = T + V$
- Energy conservation reflects that admissibility rules don't change with temporal position
- Energy additivity follows from constraint factorization
- The Hamiltonian generates evolution because it represents how admissibility cost transforms under sequencing

### 7.6 Constrained Hamiltonian Systems

When constraints are present (as they are fundamentally in LRT), the correct dynamical object is a constrained Hamiltonian system on a restricted phase space (Dirac, 1964; Henneaux & Teitelboim, 1992):

$$\mathcal{C}_a(q,p)=0.$$

Gauge freedom corresponds to directions in phase space that do not change physical admissibility class (cf. Proposition 3.3).

This aligns the LRT dynamical picture with the standard structure of fundamental physics (gauge theory; GR in Hamiltonian form) (Arnowitt et al., 1962; Rovelli, 1991), while preserving the theory's grounding priority: constraints first, dynamics second.

### 7.7 Summary

Within LRT:

* Admissibility over histories $\Rightarrow$ constraint action $S$
* Local representability of $S$ $\Rightarrow$ Lagrangian $L$
* Dual representation $\Rightarrow$ Hamiltonian $H$ as generator of admissible sequencing
* Constraints persist as first-class structure

This completes the chain:

$$L_3 \rightarrow \text{Mathematics} \rightarrow \text{Geometry} \rightarrow \text{Spacetime} \rightarrow \text{Dynamics}.$$

The next section applies this framework to quantum mechanics, addressing non-locality, measurement, and the no-signaling theorem.

## 8. Quantum Mechanics: Non-locality, Measurement, and No-Signaling

### 8.1 The Quantum Interpretation Problem

Quantum mechanics presents three foundational puzzles that remain unresolved under standard interpretations:

1. **Non-locality**: Bell correlations (Bell, 1964) demonstrate that spatially separated measurements exhibit correlations inexplicable by local hidden variables.
2. **Measurement problem**: The transition from superposition to definite outcomes lacks a principled explanation without ad hoc collapse (von Neumann, 1932) or branching worlds (Everett, 1957; Wallace, 2012).
3. **No-signaling**: Despite non-local correlations, superluminal communication is impossible (Peres & Terno, 2004).

Copenhagen-style collapse interpretations resolve measurement by fiat. Many-Worlds interpretations (MWI) (Everett, 1957; DeWitt & Graham, 1973; Wallace, 2012) preserve unitarity but posit ontological branching. Bohmian mechanics (Bohm, 1952) introduces non-local hidden variables. Each approach adds structure beyond the formalism.

LRT provides unified explanations for all three puzzles without collapse, branching, or hidden variables, by grounding quantum formalism in admissibility structure.

### 8.2 Representation: Hilbert Space and Admissible Configurations

To connect standard quantum mechanics with LRT, we require an explicit bridge between Hilbert space states and admissible configuration regions.

**Postulate 8.1 (Representation Map).**  
There exists a representation map

$$\Pi : \mathcal{H} \to \mathcal{P}(A^*)$$

from quantum states (pure or mixed density operators) to subsets of admissible configurations, such that:

1. For a quantum state $\rho$, $\Pi(\rho) = \mathcal{A}_\rho \subseteq A^*$ is the region of configurations compatible with the constraints encoded in $\rho$.
2. For independent subsystems with states $\rho_A$ and $\rho_B$:
   $$\Pi(\rho_A \otimes \rho_B) = \mathcal{A}_{\rho_A} \Join \mathcal{A}_{\rho_B},$$
   where $\Join$ is an admissibility composition operator consistent with $L_3$.
3. A measurement described by POVM $\{E_k\}$ corresponds to constraint updates that partition $\mathcal{A}_\rho$ into outcome-specific regions $\mathcal{A}_{\rho,k}$.

This postulate does not derive quantum mechanics from pure logic, but provides the formal connection between standard QM formalism and LRT ontology.

### 8.3 Quantum Superposition as Admissibility Region

A quantum superposition $|\psi\rangle = \alpha|0\rangle + \beta|1\rangle$ does not represent simultaneous actualization of incompatible states (which would violate **Non-Contradiction**). Rather, $\Pi(|\psi\rangle)$ specifies a region of $A^*$ where multiple configurations remain admissible under the available constraints.

**Key distinction:** Superposition reflects constraint-based specification, not ontological indeterminacy. The configuration is determinate in $A^*$, but the quantum state $|\psi\rangle$ provides incomplete constraint information, leaving multiple configurations admissible.

**Clarification: LRT is not a hidden-variable theory.**  
LRT might appear to introduce hidden variables (the actual configuration $i \in A^*$ underlying the quantum state). However, LRT differs fundamentally from local hidden-variable theories (Bohm, 1952; Bell, 1964):

1. **Global constraints**: Admissibility structure is global, not factorizable into local subsystems. Bell correlations arise from global constraint geometry, not local hidden states.
2. **Non-classical measure**: The admissibility measure $\mu$ is constrained by Hilbert structure and satisfies Tsirelson bounds (Proposition 9.1), not arbitrary probability distributions over classical configurations.
3. **No additional dynamics**: There is no "guiding equation" or pilot wave. The actual configuration evolves according to standard unitary dynamics; admissibility constraints determine which configuration satisfies all constraints post-measurement.
4. **Contextual actualization**: What is actualized depends on the full constraint context (including measurement apparatus), not predetermined values independent of measurement choice.

LRT explains quantum phenomena through global admissibility structure while maintaining single actualization, avoiding both the ontological excess of Many-Worlds and the non-local dynamics of Bohmian mechanics.

### 8.4 Measurement and the Born Rule

Measurement does not "collapse" the wavefunction. Measurement adds constraints that determine which configuration within $\mathcal{A}_\rho$ is actualized.

**Postulate 8.2 (Admissibility Measure and Born Correspondence).**  
There exists a measure $\mu$ over admissible configuration regions such that outcome probabilities for a POVM $\{E_k\}$ satisfy:

$$p(k) = \mathrm{Tr}(\rho E_k) = \mu(\mathcal{A}_{\rho,k}),$$

where $\mathcal{A}_{\rho,k} \subseteq \mathcal{A}_\rho$ is the subset compatible with measurement outcome $k$.

This postulate establishes the Born rule as the correspondence between Hilbert space structure and admissibility measure, without deriving it from more primitive principles (cf. Gleason, 1957; Deutsch, 1999; Wallace, 2007 for alternative derivation approaches). The measure $\mu$ quantifies the "volume" of admissible configurations associated with each outcome.

**Measurement process:**

1. **Pre-measurement**: System in state $|\psi\rangle$, admissible region $\mathcal{A}_\psi$
2. **Apparatus interaction**: Measurement apparatus imposes constraint $C_{\text{meas}}$, inducing partition of $\mathcal{A}_\psi$ into $\{\mathcal{A}_{\psi,k}\}$
3. **Outcome determination**: Constraint satisfaction selects single configuration from appropriate $\mathcal{A}_{\psi,k}$, with probability $\mu(\mathcal{A}_{\psi,k})$
4. **Post-measurement**: Actualized configuration is determinate; no physical discontinuity occurs

The apparatus interaction induces effective orthogonality of outcome subregions $\mathcal{A}_{\rho,k}$ (decoherence) (Zurek, 2003; Schlosshauer, 2007), making outcome records stable within $A^*$.

**Corollary 8.1.**  
**Excluded Middle** requires determinate actuality: exactly one configuration in $A^*$ is actualized. The measurement process determines which configuration satisfies all constraints, including the apparatus interaction. There is no "measurement problem" because outcomes are determinate by $L_3$ and probabilities are given by the admissibility measure.

### 8.5 Bell Correlations from Global Admissibility

Bell's theorem (Bell, 1964, 1987) shows that no local hidden variable theory can reproduce quantum correlations. LRT is not a local hidden variable theory: admissibility constraints operate globally on $(A^*, d_A, \prec)$.

**Proposition 8.1 (Non-local Correlations from Global Constraint Structure).**  
For entangled systems, the admissible configuration space $\mathcal{A}_\rho$ imposes global constraints: configurations at location $A$ constrain admissible configurations at location $B$, even under spacelike separation.

*Explanation:* When particles are prepared in an entangled state like $|\psi\rangle = \frac{1}{\sqrt{2}}(|↑↓\rangle - |↓↑\rangle)$, the constraint structure encoded in $\Pi(|\psi\rangle)$ links configurations across spatial separation. This is not action-at-a-distance; it is global constraint satisfaction. The admissibility of the composite system was never localized to independent subsystems.

Bell correlations violate Jarrett's parameter independence (choice of measurement at $A$ affects statistics at $B$ when conditioned on classical communication), but preserve outcome independence (local outcomes are determinate given the global configuration). LRT naturally violates parameter independence because constraint structure is global.

**Caveat on Tsirelson bounds:** Recovering the specifically quantum (Tsirelson-bounded) correlation polytope (Tsirelson, 1980), rather than more general no-signaling correlations (PR-boxes) (Popescu & Rohrlich, 1994), requires the Hilbert space representability conditions from Section 5.3 together with Postulates 8.1-8.2. Global admissibility constraints alone do not exclude superquantum correlations; the specific inner-product structure of quantum theory (emergent from admissibility regularity in Section 5.3) restricts correlations to the quantum polytope.

**Comparison to Many-Worlds:** MWI explains correlations via ontological branching into multiple worlds, each with definite outcomes. LRT achieves the same correlation structure without branching: global admissibility constrains outcomes at both locations simultaneously when measurement constraints are added. Only one outcome is actualized in $A^*$, but the correlation structure reflects the global constraint geometry.

### 8.6 No-Signaling from Marginal Invariance

Despite non-local correlations, quantum mechanics forbids superluminal signaling (Nielsen & Chuang, 2000; Peres & Terno, 2004). Within LRT, this follows from the structure of constraint factorization for spacelike separated systems.

**Proposition 8.2 (No-Signaling as Marginal Invariance).**  
Let $A$ and $B$ be spacelike separated subsystems with joint state $\rho_{AB}$. For any local completely positive trace-preserving (CPTP) map $\Lambda_A$ at location $A$:

$$\rho'_B = \mathrm{Tr}_A[(\Lambda_A \otimes I_B)(\rho_{AB})] = \mathrm{Tr}_A[\rho_{AB}] = \rho_B.$$

Therefore, the statistics of measurement outcomes at $B$ are invariant under local operations at $A$ in the absence of classical communication.

*Interpretation in LRT:* Local constraint updates at $A$ (measurements, unitary operations) modify the joint admissible region $\mathcal{A}_{\rho_{AB}}$, but preserve the marginal admissibility structure at $B$. The measure $\mu$ over configurations at $B$ remains unchanged. Global correlations exist (joint constraints link $A$ and $B$), but local operations cannot control the marginal statistics at a spacelike separated location.

This is the standard no-signaling condition from quantum information theory (Nielsen & Chuang, 2000; Clifton et al., 2003), now interpreted as: local admissibility updates preserve marginal measures over remote subsystems when subsystems are spacelike separated.

The temporal ordering $\prec$ (Definition 3.5-3.6) respects light cone structure when properly embedded in relativistic spacetime (Section 6.5). Spacelike separated events are not ordered by $\prec$, preventing causal influence while permitting global constraint correlation.

### 8.7 Comparison to Existing Interpretations

| Interpretation | Definite Outcomes | Global Correlations | Ontological Cost |
|----------------|-------------------|---------------------|------------------|
| Copenhagen | Via collapse (ad hoc) | Via non-locality | Measurement primitive |
| Many-Worlds (Everett, 1957; Wallace, 2012) | All branches real | Via branching | All possible worlds |
| Bohmian Mechanics (Bohm, 1952) | Particle trajectories | Via pilot wave | Hidden variables + non-local dynamics |
| Consistent Histories (Griffiths, 2002; Omnès, 1994) | Via decoherence | Via history selection | Classical logic emergence |
| **LRT** | Via $L_3$ (EM) | Via global $A^*$ constraint | Single $A^* = L_3(I_{\infty})$ |

**Structural comparison to MWI:**

LRT achieves Many-Worlds' advantages (unitary evolution preserved, no collapse, global correlation explanation) (Wallace, 2012; Saunders et al., 2010) while avoiding ontological branching. Where MWI commits to all branches being real, LRT commits only to: (1) a space of possible configurations $I_{\infty}$, (2) admissibility constraints $L_3$, and (3) a measure $\mu$ over admissible regions. Single actualization in $A^*$ replaces branching multiplicity.

**Sharp distinction from MWI:**  
In Many-Worlds, other outcome branches are physically real, existing in parallel with equal ontological status. In LRT, other outcomes correspond to non-actualized admissible configurations in $I_{\infty}$. Only the actualized configuration in $A^*$ exists physically. The global constraint structure that determines probabilities is defined over $A^*$ and its relation to $I_{\infty}$, but this is modal/mathematical structure, not physical branching.

**Born rule stance:**  
LRT does not claim a novel derivation of the Born rule. Postulate 8.2 asserts that the admissibility measure $\mu$ corresponds to Born probabilities. This is compatible with existing derivation approaches (Gleason, 1957; Deutsch, 1999; Wallace, 2007) but reinterprets them: whatever the correct derivation, it must fit the picture of $\mu$ as a measure over admissible configuration regions. The contribution is not a new proof but a new ontological grounding showing *why* such a measure structure must exist.

### 8.8 Falsifiability and Empirical Predictions

LRT reproduces standard quantum mechanics in domains where QM is well-tested (via Postulates 8.1-8.2). However, it suggests potential deviations in regimes where admissibility structure might differ:

1. **Macroscopic superposition limits**: If $L_3$ constraints impose bounds on coherent superposition at macroscopic scales (configurations approaching inadmissibility), LRT predicts deviations from perfect linearity. Test: large-scale interference experiments (Arndt et al., 1999; Eibenberger et al., 2013).

2. **Quantum gravity regime**: Discreteness in $(A^*, d_A, \prec)$ at the Planck scale would modify propagators and correlation functions. Test: high-energy scattering, early universe cosmology.

3. **Cosmological boundary conditions**: Global admissibility over entire universe history might constrain the wavefunction of the universe beyond standard Wheeler-DeWitt approaches (Barbour, 1999). Test: cosmological observables sensitive to initial conditions.

These are not ad hoc modifications but natural consequences of taking admissibility constraints as fundamental at all scales.

### 8.9 Summary

Within LRT:

* Quantum states represent admissible configuration regions in $A^*$ (Postulate 8.1).
* The Born rule corresponds to an admissibility measure $\mu$ (Postulate 8.2).
* Measurement determines actualization by constraint addition; no collapse occurs.
* Bell correlations arise from global constraint structure, not local hidden variables.
* No-signaling follows from marginal invariance: local operations preserve remote marginal measures.
* LRT achieves structural parity with Many-Worlds without ontological branching.

This completes the application of Logic Realism Theory to quantum foundations.

## 9. Falsifiability, Predictions, and Research Program

### 9.1 What Would Falsify LRT?

Logic Realism Theory (LRT) is not falsified by reproducing established quantum and relativistic predictions; rather, it is falsified if the world exhibits physically instantiated violations of ontological admissibility as characterized by $L_3$, or if the theory's additional structural commitments (the existence of an admissibility-induced ordering and admissibility-induced measures) prove empirically incompatible with observation.

At minimum, LRT entails three falsifiable commitments:

1. **Admissibility Closure**: Physically realized processes cannot instantiate contradictions in the same respect (ontological non-contradiction) and must yield determinate actuality at the level of outcomes (ontological excluded middle).
2. **Constraint-First Dynamics**: What is dynamically realized is selected by admissibility constraints on histories (action/constraint selection), not by unconstrained state evolution plus ad hoc collapse.
3. **Representation Consistency**: The standard Hilbert-space formalism is a representation of admissibility regions $\Pi(\rho)\subseteq A^*$ with a measure $\mu$ compatible with the Born rule; if this bridge fails in any domain, the LRT-QM link is falsified.

The crucial point is that LRT is not "true by definition": it makes claims about what cannot be physically realized, and it locates possible deviations from standard theory precisely where admissibility regularity might fail.

### 9.2 Sharp Falsification Criteria (Executive Summary)

Logic Realism Theory is falsified if any of the following are observed:

**1. Ontic Contradictory Outcomes**  
A single physical process instantiates mutually exclusive outcomes in the same respect (not epistemic uncertainty, not contextuality). This would violate the **Non-Contradiction** constraint at the ontological level.

**2. Post-Quantum No-Signaling Correlations**  
Experimentally verified violations of Tsirelson bounds (Tsirelson, 1980), reproducible under controlled conditions. Observation of PR-box correlations (Popescu & Rohrlich, 1994) would falsify the Hilbert representability postulate (Postulate 8.1).

**3. Perfect Macroscopic Linearity Under Arbitrary Scale**  
Demonstration that isolated quantum interference remains exactly linear with no scale-, complexity-, or configuration-dependent deviation across all experimentally accessible mass/complexity regimes. This would constrain admissibility-boundary models to the point of eliminating all testable microstructure predictions.

**4. Fundamental Energy Nonconservation in a Closed System**  
Robust violation of energy conservation not attributable to cosmological effects, open-system interactions, or measurement error. This would falsify the claim that admissibility constraints are temporally homogeneous (Section 7.5).

**5. Failure of Hilbert Representability**  
Empirically required physical predictions incompatible with any admissibility-region representation $\Pi : \mathcal{H} \to \mathcal{P}(A^*)$ satisfying Postulates 8.1-8.2. This would require fundamental revision or abandonment of the LRT-QM bridge.

These criteria are operational and testable. LRT is not merely an interpretation but a framework making specific commitments about physical realizability.

### 9.3 Two Levels of Empirical Content

LRT yields testable content at two distinct levels:

**Level I (Interpretive Equivalence):**  
If Postulates 8.1–8.2 hold universally, LRT reproduces standard QM predictions (and standard relativistic structure once $(A^*,d_A,\prec)$ is identified with a Lorentzian causal structure). At this level, LRT is empirically equivalent to the represented theory but provides a different ontology.

**Level II (Admissibility Microstructure):**  
LRT becomes empirically distinctive if the admissibility structure has fine-grained properties not captured by standard axioms (e.g., discreteness, contextual admissibility boundaries, scale-dependent constraints). This is where concrete predictions arise.

Accordingly, falsifiable predictions in LRT are predictions about the microstructure of admissibility: the detailed form of $(A^*,d_A,\prec)$, the constraint functional $C[\gamma]$, and the admissibility measure $\mu$.

### 9.4 Distinctive Prediction Classes

#### 9.4.1 Macroscopic Superposition as an Admissibility-Boundary Effect

**Hypothesis (Admissibility-Induced Nonlinearity):**  
For sufficiently complex/macroscopic configurations, admissible regions $\mathcal{A}_\rho$ approach the boundary of $A^*$ in the sense that $\phi(i)=\inf_{j\notin A^*}d_A(i,j)$ becomes small. If $\mu$ or the constraint functional $C[\gamma]$ is sensitive to $\phi$, then interference visibility should deviate from standard linear quantum predictions beyond some scale.

**Quantitative benchmark model:**  
To demonstrate testability, consider a minimal admissibility model where interference visibility scales as:

$$V_{\text{LRT}}(m) = V_{\text{QM}} \exp\left(-\alpha\, \frac{m^2}{m_*^2}\right),$$

where $m$ is system mass, $m_*$ characterizes the admissibility-boundary proximity scale, and $\alpha$ is a dimensionless coupling. This benchmark differs from:
- Continuous Spontaneous Localization (CSL) models: $V_{\text{CSL}} \sim \exp(-\lambda m t)$ (linear in mass)
- Environmental decoherence: $V_{\text{env}} \sim \exp(-\Gamma m^2 T t)$ (temperature-dependent)
- LRT benchmark: geometric admissibility suppression (mass-squared, temperature-independent under isolation)

This is not asserted as the correct form, but demonstrates that LRT yields distinguishable functional predictions.

**Observable consequence:**  
A scale-dependent suppression of interference (or effective decoherence) not attributable to environmental coupling, with characteristic $m^2$ scaling rather than linear mass dependence.

**Null test:**  
Increasing-mass interferometry (matter-wave interference) with systematic control of environmental decoherence. If interference remains perfectly consistent with linear QM arbitrarily deep into the macroscopic regime under controlled isolation, admissibility-boundary models of this type are constrained or ruled out. Current experiments (Arndt et al., 1999; Eibenberger et al., 2013) constrain $m_*$ but do not yet rule out all plausible values.

This does not assert collapse; it predicts constraint-induced departure from perfect linear superposition only where admissibility geometry forces it.

#### 9.4.2 Bell Correlations: Excluding Superquantum No-Signaling Correlations

LRT explains Bell correlations (Bell, 1964) via global admissibility structure. However, global constraint satisfaction alone is consistent with broader no-signaling correlation polytopes (e.g., PR-box-type correlations) (Popescu & Rohrlich, 1994). Therefore, LRT must commit to a structural restriction explaining why nature realizes the quantum (Tsirelson-bounded) set (Tsirelson, 1980).

**Proposition 9.1 (Tsirelson Constraint from Hilbert Representability).**  
Any admissibility structure representable by $\Pi : \mathcal{H} \to \mathcal{P}(A^*)$ with inner-product regularity and satisfying Postulates 8.1-8.2 necessarily satisfies Tsirelson bounds on correlation functions.

*Justification:* The Hilbert space inner product structure constrains admissible joint probability distributions. Post-quantum correlations would require representational structures beyond standard Hilbert spaces, violating the bridge postulates.

**Falsification statement:**  
Observation of reproducible post-quantum no-signaling correlations (PR-box violations of Tsirelson bounds) would falsify LRT in its current form. Either (i) the admissibility representation must be generalized beyond Hilbert spaces, or (ii) the framework must be abandoned.

This is a clean logical fork: LRT must either (i) recover Tsirelson by admissibility regularity → Hilbert structure, or (ii) accept broader correlations and thereby predict physics beyond standard QM. Current experimental evidence (Hensen et al., 2015) supports Tsirelson bounds, consistent with LRT.

#### 9.4.3 Relativistic Ordering: Microcausality as a Derived Regularity

In LRT, causal structure arises from admissibility ordering $\prec$ together with regularity/quasi-locality assumptions on $C[\gamma]$. This implies that relativistic microcausality is not merely assumed but should emerge as a stability condition.

**Prediction class:**  
In regimes where admissibility becomes discrete or non-manifold-like (e.g., near Planckian structure), effective locality/microcausality may fail in controlled, bounded ways—e.g., modified dispersion relations, altered commutator structure, or small violations of Lorentz invariance (depending on the detailed form of $(A^*,d_A,\prec)$).

**Falsification criterion:**  
If LRT claims discrete/admissibility microstructure, then it must predict a specific pattern of high-energy or early-universe deviations. Absence of any such deviations with increasingly sensitive tests progressively constrains the admissibility-microstructure hypothesis space.

(As written, LRT need not commit yet to which deviation; it must commit once a specific microstructure is proposed.)

#### 9.4.4 Energy Conservation as Temporal Homogeneity of Admissibility

Section 7 derives conservation of $H$ from $\partial L/\partial o=0$, i.e., temporal homogeneity of admissibility.

**Commitment:**  
If LRT is correct and admissibility constraints are temporally homogeneous (as required for fundamental laws), then no fundamental energy nonconservation should be observed in closed systems.

**Known limitations:**
- Open systems exchange energy with environment (not violations)
- Cosmological settings with time-dependent backgrounds (context-dependent)
- Apparent violations due to measurement limitations

**Falsification criterion:**  
Robust, reproducible evidence of fundamental energy nonconservation in a demonstrably closed system, not attributable to experimental error, unknown interactions, or cosmological effects, would falsify the claim that admissibility is temporally homogeneous. This would require either:
1. Modifying LRT to allow time-dependent admissibility constraints, or
2. Abandoning the framework if no consistent modification exists.

**Alternative prediction:**  
Conversely, if LRT allows controlled admissibility inhomogeneity in specific contexts (e.g., global cosmological constraints), the theory must specify the form and magnitude of expected energy variations. Current formulation assumes homogeneity; deviations would require explicit extension.

### 9.5 A Minimal Sharp Prediction

Even before specifying microstructure, LRT makes one crisp, nontrivial claim that differentiates it from a broad class of interpretations:

**Prediction (Single-Actualization Constraint):**  
For any measurement context with outcome events $k$, exactly one outcome configuration is actualized in $A^*$, and the Born statistics arise from a measure $\mu$ over admissible regions. Therefore, any experimentally verified requirement of simultaneous contradictory outcome actuality (not merely epistemic indeterminacy or contextuality) would falsify LRT.

This sounds philosophical, but it is operational once tied to concrete proposals claiming "real" contradictory outcomes (ontic dialetheism, genuine contradiction-valued observables, etc.). LRT forbids those as physically instantiated.

### 9.6 Sharp Benchmark Prediction: Minimal Admissibility Model

To demonstrate that LRT is not merely interpretive, we specify a minimal admissibility model as a concrete falsification target.

**Model specification:**  
Consider $A^*$ as a smooth metric space with characteristic boundary curvature scale $\ell_A$. Configurations approaching the admissibility boundary experience suppression of coherent quantum amplitudes. The admissibility proximity function $\phi(i) = \inf_{j \notin A^*} d_A(i,j)$ couples to the admissibility measure $\mu$ such that:

$$\mu(\mathcal{A}_\rho) \propto \int_{\mathcal{A}_\rho} \exp\left(-\frac{1}{\ell_A^2} \mathcal{K}[\rho]\right) d\mu_0,$$

where $\mathcal{K}[\rho]$ is a complexity functional (e.g., configuration entropy, spatial extent, mass) and $\mu_0$ is the standard quantum measure.

**Predicted deviation:**  
Interference visibility scales as $V(m) \sim \exp(-m^2/m_*^2)$ for isolated systems, distinguishable from CSL ($\sim \exp(-\lambda m t)$) and environmental decoherence ($\sim \exp(-\Gamma m^2 T t)$).

**Current experimental constraints:**  
Existing matter-wave interference experiments constrain this model:
- Fullerene (C$_{60}$, $m \approx 720$ amu): Interference observed (Arndt et al., 1999)
- Large molecules ($m > 10^4$ amu): Interference observed (Eibenberger et al., 2013)
- These results require $m_* \gtrsim 10^5$ amu if $\alpha \sim 1$

This constraint is significant but not fatal: $m_*$ could plausibly be at molecular-protein scales ($10^6$-$10^8$ amu) where experiments are challenging but feasible. Next-generation experiments with virus particles or nanocrystals will further constrain or rule out this scaling.

**Falsifiability:**  
This benchmark model is not claimed to be realistic; its purpose is to show how LRT yields falsifiable deviations distinguishable from collapse models and decoherence. Systematic tests of matter-wave interference at increasing mass scales under controlled isolation directly constrain or falsify this class of admissibility structures.

**Key point:**  
Failure to observe any such deviations within the predicted scaling regime across all accessible mass/complexity scales would progressively constrain admissibility-microstructure models, eventually forcing either:
1. Abandonment of geometric boundary effects, or
2. Pushing $m_*$ to unphysically large scales (fine-tuning problem)

Unlike collapse models (CSL) which introduce new stochastic dynamics, LRT predicts deviations only where admissibility geometry imposes them. This makes the theory more conservative (no new fundamental dynamics) but equally testable (definite scaling predictions).

### 9.7 Research Program and Parameterization

To become a predictive physical theory rather than only a grounding framework, LRT requires explicit parameterizations of:

1. The metric $d_A$ (or a family $d_A^{(\theta)}$)
2. The ordering structure $\prec$ (e.g., causal cones or discrete orders)
3. The constraint functional $C[\gamma]$ (local/quasi-local densities $c$)
4. The admissibility measure $\mu$ (and conditions yielding $\mu(\mathcal{A}_{\rho,k})=\mathrm{Tr}(\rho E_k)$)

This parameterization defines a model class. Each model yields quantitative predictions and is directly falsifiable.

### 9.8 Summary

LRT is falsifiable in two ways:

1. **Directly**: If physically realized processes require ontic contradictions or indeterminate actuality in violation of $L_3$.
2. **Structurally**: If proposed admissibility microstructure (for $d_A$, $\prec$, $C$, $\mu$) yields measurable deviations that fail, or if nature exhibits post-quantum correlations (or other phenomena) inconsistent with Hilbert-representable admissibility.

In this way, LRT is not merely interpretive: it defines a constrained family of physically testable admissibility structures and invites experimental discrimination at the boundary regimes where admissibility regularity may fail.

## 10. Discussion

### 10.1 Relationship to Existing Foundational Programs

Logic Realism Theory occupies a distinctive position in the landscape of foundational approaches to physics. This section clarifies how LRT relates to major existing programs and where it offers potential advantages.

#### 10.1.1 Information-Theoretic Reconstructions

Programs seeking to reconstruct quantum mechanics from information-theoretic principles (Hardy, 2001; Chiribella et al., 2011; Höhn & Wharton, 2016) treat information as primitive. LRT inverts this priority: information presupposes distinguishability, which presupposes admissibility under $L_3$. Where information reconstructions must postulate principles like "no superluminal signaling" or "continuous reversibility," LRT derives these as consequences of admissibility structure.

**Advantage:** LRT explains why information principles hold rather than assuming them.

**Challenge:** Information reconstructions are often more directly operational. LRT must show that its ontological grounding provides explanatory power beyond operational convenience.

#### 10.1.2 Quantum Logic and Topos Approaches

Quantum logic programs (Birkhoff & von Neumann, 1936) and topos-theoretic approaches (Isham & Butterfield, 1998; Döring & Isham, 2008; Heunen et al., 2009) treat non-classical logic or higher categorical structures as fundamental to quantum theory. LRT maintains classical logic ($L_3$) at the ontological level while explaining quantum structure through admissibility constraints on configuration spaces.

**Key distinction:** LRT treats quantum "weirdness" as constraint geometry, not logical revision. Non-classical algebraic structures (non-commutative observables, complementarity) emerge from the geometry of admissible regions, not from modifications to logic itself.

#### 10.1.3 Constructive Empiricism and Structural Realism

Van Fraassen's constructive empiricism (van Fraassen, 1980) treats theories as instruments for predicting observables without ontological commitment. Structural realists (Ladyman & Ross, 2007; French, 2014) commit to structure but remain agnostic about intrinsic natures.

LRT commits to ontological admissibility as real but treats specific physical structures (spacetime, fields, particles) as representations of that admissibility. This is a form of constrained realism: reality is structured by $L_3$, and physics represents that structure.

**Position:** LRT is more ontologically committed than constructive empiricism (admissibility is real) but less committed than naive realism about specific physical ontology (spacetime and fields are representational).

#### 10.1.4 Category-Theoretic Foundations

Recent category-theoretic approaches (Abramsky & Coecke, 2004; Coecke & Kissinger, 2017; Baez & Stay, 2011) treat physical theories as categories with morphisms representing processes. LRT is compatible with categorical formulations: admissibility constraints naturally define categories where objects are configurations in $A^*$ and morphisms are admissible transitions.

**Potential synthesis:** Category theory provides the mathematical language for admissibility structure. LRT provides the ontological grounding explaining why categorical structures appear in physics.

### 10.2 LRT as Unified Grounding for Multiple Theories

One of LRT's most significant potential contributions is providing unified grounding for disparate physical theories. Rather than treating quantum mechanics, general relativity, thermodynamics, and field theory as independent frameworks, LRT suggests they represent different aspects of a single admissibility structure.

#### 10.2.1 Quantum Mechanics

**Grounding:** Hilbert space structure represents admissible configuration regions $\mathcal{A}_\rho \subseteq A^*$ (Section 8). Unitary evolution preserves admissibility. Measurement adds constraints, determining actualization.

**What LRT adds:** Ontological grounding for superposition (constraint-based specification), measurement (constraint addition), and non-locality (global admissibility structure).

#### 10.2.2 General Relativity

**Grounding:** Spacetime is ordered geometry $(A^*, d_A, \prec)$ (Section 6). Einstein's equations would emerge as constraints on admissible geometric configurations: $G_{\mu\nu} = 8\pi T_{\mu\nu}$ expresses which geometric-matter configurations are admissible.

**What LRT adds:** Spacetime is not a dynamical field requiring its own dynamics, but the representation of admissible relational-sequential structure. The metric $g_{\mu\nu}$ encodes $d_A$ and $\prec$ in local coordinates.

**Open challenge:** Derive Einstein's equations from admissibility constraints. This requires showing that the specific form of $G_{\mu\nu}$ follows from requiring geometric configurations to preserve admissibility under composition and variation.

#### 10.2.3 Quantum Field Theory

**Grounding:** Fields $\phi(x)$ represent degrees of freedom in admissible configurations at each spacetime point. The action $S[\phi]$ is the constraint functional $C[\gamma]$ in field-theoretic form. Renormalization could reflect admissibility regularization at different scales.

**What LRT adds:** Unified treatment of quantum and field structures. Both arise from admissibility: quantum structure from constraint-based specification, field structure from continuous degrees of freedom in $(A^*, d_A, \prec)$.

**Open challenge:** Explain gauge symmetry and internal symmetries as admissibility invariances. Show that gauge freedom represents redundancy in describing admissible configurations, not physical degrees of freedom.

#### 10.2.4 Thermodynamics and Statistical Mechanics

**Grounding:** Entropy measures admissible configuration volume at coarse-grained scales. The second law reflects that admissible evolution tends toward regions of larger $\mu$-measure (more admissible microstates per macrostate).

**What LRT adds:** Thermodynamic arrow of time emerges from asymmetric boundary conditions on global admissibility, compatible with time-reversal symmetry of fundamental laws (Lemma 3.8).

**Open challenge:** Derive Boltzmann entropy $S = k_B \ln \Omega$ from admissibility measure $\mu$. Show that $\Omega$ (microstate count) corresponds naturally to $\mu(\mathcal{A}_{\text{macro}})$ for coarse-grained regions.

### 10.3 Implications for Quantum Gravity

LRT's approach to spacetime (ordered geometry, not primitive substance) aligns naturally with quantum gravity requirements:

1. **Background independence:** $(A^*, d_A, \prec)$ is not a fixed background but emerges from admissibility structure. Different configurations can have different geometric properties.

2. **Discreteness:** If admissibility is discrete at fundamental scales (finite distinguishability), spacetime inherits natural discreteness without requiring separate quantization (Sorkin, 2005).

3. **Causal structure:** The ordering $\prec$ provides causal structure prior to metric structure, aligning with causal set approaches (Sorkin, 2005) and asymptotic safety programs.

**Potential connection to loop quantum gravity:** LRT's constraint-first approach parallels LQG's emphasis on constraints and canonical quantization (Ashtekar & Lewandowski, 2004; Rovelli, 2004). Spin networks might represent discrete admissibility structures.

**Potential connection to string theory:** If admissibility structure requires extended objects for consistency at high energy, string degrees of freedom (Polchinski, 1998; Witten, 1995) could emerge as representations of admissible configurations.

### 10.4 Open Questions and Future Directions

Several key questions remain for developing LRT into a complete physical theory:

#### 10.4.1 Deriving Specific Dynamics

**Question:** Can specific field equations (Einstein, Maxwell, Dirac) be derived from admissibility constraints, or must they be input as "laws of admissibility"?

**Approach:** Show that requiring consistency of admissibility under composition, symmetry, and variation forces specific functional forms. This is analogous to deriving Maxwell's equations from gauge invariance and locality.

#### 10.4.2 Explaining Dimensionality

**Question:** Why 3+1 spacetime dimensions rather than other configurations?

**Status:** Section 6.6 acknowledges this as empirical. A complete LRT would ideally derive dimensionality from admissibility requirements for rich physical structure.

**Possible approach:** Show that 3 spatial dimensions provide minimal structure for stable, complex configurations (Ehrenfest's argument) combined with single temporal dimension from single ordering $\prec$.

#### 10.4.3 Particle Physics and the Standard Model

**Question:** How do elementary particles, gauge groups, and coupling constants arise in LRT?

**Speculation:** Particles could represent stable, localized admissibility structures (soliton-like). Gauge groups might encode symmetries of admissibility-preserving transformations. Coupling constants might parametrize admissibility-proximity sensitivity.

**Challenge:** This requires substantial technical development to make concrete.

#### 10.4.4 Consciousness and Observation

**Question:** Does LRT require observers or consciousness for measurement?

**Answer:** No. Measurement is constraint addition through physical interaction (Section 8.4). Consciousness is irrelevant to admissibility determination. Any physical system that adds sufficient constraints to determine actualization functions as a "measurement" regardless of whether observers are present.

This resolves a persistent ambiguity in Copenhagen-style interpretations without invoking Many-Worlds branching.

### 10.5 Philosophical Implications

#### 10.5.1 Ontological Parsimony

LRT's ontology is remarkably sparse: only $I_{\infty}$ (possible configurations), $L_3$ (admissibility constraints), and the resulting $A^* = L_3(I_{\infty})$ (physical reality). All physical structures—mathematics, geometry, spacetime, dynamics, quantum mechanics—are representations of this admissibility structure.

This achieves significant ontological reduction without eliminativism: physical structures are real as representations of admissibility, not as independent substances.

#### 10.5.2 Modal Realism Without Possible Worlds

LRT requires modal structure ($I_{\infty}$ includes non-actualized possibilities) but avoids David Lewis-style modal realism. Possible configurations exist as abstract possibilities for constraint satisfaction, not as concrete alternate realities.

This provides modal structure needed for physical counterfactuals and laws without ontological profligacy.

#### 10.5.3 Laws as Constraints, Not Governing Entities

Physical laws in LRT are not external governing principles but characterizations of admissibility structure. The "laws" are the constraints $L_3$ applied to configuration spaces. Specific equations (Einstein, Schrödinger, etc.) are representations of these constraints in particular domains.

This dissolves the mystery of why nature "obeys" laws: there is no obedience, only constraint satisfaction.

### 10.6 Summary

LRT provides:

1. **Unified grounding** for quantum mechanics, relativity, and field theory through admissibility structure
2. **Ontological clarity** without ontological extravagance
3. **Natural connections** to quantum gravity, information theory, and category theory
4. **Research program** with concrete technical challenges and falsifiable predictions

The theory's success depends on whether admissibility structure can genuinely derive the specific forms of physical laws observed in nature, not merely provide post-hoc interpretations. This remains the central challenge for future development.

## 11. Applications and Future Research Directions

### 11.1 Near-Term Theoretical Applications

#### 11.1.1 Quantum Computing and Information Processing

**Application:** LRT's treatment of superposition as admissible configuration regions provides a framework for understanding quantum computational resources without invoking collapse or branching.

**Concrete direction:** Analyze quantum algorithms (Shor, Grover) in terms of admissibility-region evolution. The computational advantage might arise from parallel exploration of admissible configurations constrained to a single outcome, without requiring branching into multiple worlds.

**Potential advantage:** Could provide insights into decoherence-free subspaces and error correction as regions of high admissibility-measure preservation.

**Research question:** Can quantum error correction codes be understood as structures that maximize $\phi(i)$ (admissibility proximity) for computational states, making them robust to perturbations?

#### 11.1.2 Quantum Measurement and Control

**Application:** Optimal measurement strategies and quantum control protocols could be analyzed in terms of constraint addition that maximally determines actualization while minimizing disturbance.

**Concrete direction:** Develop a calculus of constraint addition for LRT. Given initial region $\mathcal{A}_\rho$, characterize measurements by how they partition this region and how different partitioning strategies affect information extraction.

**Practical impact:** Could inform design of measurement protocols in quantum sensing and metrology.

#### 11.1.3 Foundations of Quantum Field Theory

**Application:** Renormalization and effective field theory naturally fit LRT's multi-scale admissibility picture. UV divergences might reflect attempting to probe configurations at scales where admissibility structure changes character.

**Concrete direction:** Reformulate renormalization group flow as scale-dependent admissibility constraints. The running of coupling constants could represent how admissibility-proximity sensitivity varies with energy scale.

**Research question:** Can the specific form of beta functions be derived from admissibility regularity requirements?

### 11.2 Computational and Algorithmic Applications

#### 11.2.1 Constraint Satisfaction and Optimization

**Application:** LRT's constraint-first approach directly applies to computational constraint satisfaction problems (CSP). The framework of admissible configurations under logical constraints is identical in structure.

**Concrete direction:** Develop LRT-inspired algorithms for CSP. Treat solution spaces as admissible configuration regions with measure. Use admissibility-proximity concepts to guide search toward high-measure regions.

**Potential advantage:** Physical intuition from admissibility geometry might suggest novel heuristics for hard optimization problems.

#### 11.2.2 Causal Inference and Counterfactual Reasoning

**Application:** The ordering relation $\prec$ and admissibility constraints provide a formal framework for causal reasoning. Counterfactuals correspond to alternate admissible histories under modified constraints.

**Concrete direction:** Apply LRT structure to Pearl-style causal inference. The do-operator could correspond to constraint modification. Counterfactual queries become questions about alternate admissible regions.

**Practical impact:** Could improve causal discovery algorithms and counterfactual prediction in machine learning.

#### 11.2.3 Verification and Formal Methods

**Application:** Software and hardware verification requires proving that systems satisfy constraints. LRT's formal treatment of constraint satisfaction could inform verification methods.

**Concrete direction:** Develop verification tools based on admissibility checking. Treat program states as configurations, correctness conditions as admissibility constraints.

### 11.3 Experimental Physics Applications

#### 11.3.1 Macroscopic Quantum Systems

**Application:** Section 9.3.1 predicts potential deviations in macroscopic superpositions. This guides experimental design for testing fundamental limits.

**Concrete experiments:**
- Large molecule interferometry (fullerenes, proteins, nanocrystals) with precise decoherence control (Arndt et al., 1999; Eibenberger et al., 2013)
- Optomechanical systems in quantum superposition states
- Superconducting circuits at mesoscopic scales

**Measurement strategy:** Systematically increase system complexity (mass, number of particles, spatial extent) while controlling environmental decoherence. Look for departures from perfect quantum linearity not attributable to known decoherence channels.

**Expected signature:** If admissibility-boundary effects exist, interference visibility should decay with a characteristic dependence on configuration complexity not present in standard decoherence models (Zurek, 2003; Schlosshauer, 2007).

#### 11.3.2 Bell Tests and Quantum Correlations

**Application:** Section 9.3.2 identifies testing Tsirelson bounds (Tsirelson, 1980) as crucial for LRT validation.

**Concrete experiments:**
- High-efficiency loophole-free Bell tests with improved statistics (Hensen et al., 2015)
- Search for post-quantum correlations in exotic systems (high-dimensional entanglement, continuous variables)
- Quantum networks testing correlations beyond bipartite settings

**What to look for:** Any violation of Tsirelson bounds would falsify standard LRT-QM bridge. Confirming Tsirelson bounds under all conditions would support LRT's claim that Hilbert structure emerges from admissibility regularity.

#### 11.3.3 Planck-Scale Physics

**Application:** Section 9.3.3 suggests potential modifications to locality/causality at Planck scale if admissibility structure is discrete.

**Observable signatures:**
- Modified dispersion relations (energy-dependent speed of light)
- Threshold anomalies in cosmic ray spectra
- Quantum gravity phenomenology in astrophysical observations

**Current constraints:** Existing bounds on Lorentz violation and modified dispersion already constrain possible admissibility microstructure.

### 11.4 Interdisciplinary Applications

#### 11.4.1 Biology and Complex Systems

**Application:** Biological systems operate under multiple constraints (thermodynamic, chemical, informational). LRT's framework of constraint satisfaction under admissibility could model biological organization.

**Concrete direction:** Model evolutionary dynamics as exploration of admissible configuration space under fitness constraints. Adaptation corresponds to discovering high-measure regions under environmental constraints.

**Speculative extension:** Consciousness and cognition might involve constraint-based modeling of admissible world-states. Perception as constraint addition determining actualization has parallels to LRT measurement.

#### 11.4.2 Economics and Game Theory

**Application:** Economic agents operate under resource constraints, logical consistency requirements, and strategic considerations. LRT's mathematical structure could formalize these.

**Concrete direction:** Model equilibria as admissible configurations under strategic constraints. Nash equilibria correspond to mutually admissible strategy profiles. Market dynamics as admissibility-region evolution under changing constraints.

#### 11.4.3 Artificial Intelligence and Machine Learning

**Application:** Neural network training involves constraint satisfaction (loss minimization) under architectural constraints. LRT provides a formal framework.

**Concrete directions:**
- Interpret deep learning as admissible configuration search in parameter space
- Use admissibility-measure concepts to understand generalization (high-measure regions = good generalizers)
- Apply constraint geometry to understand inductive biases and representation learning

**Research question:** Can we derive training algorithms from admissibility principles that outperform current methods?

### 11.5 Formal Development Priorities

For LRT to mature into a complete physical theory, several formal developments are essential:

#### 11.5.1 Explicit Parameterizations

**Priority 1:** Develop explicit families of admissibility structures $(A^*_\theta, d_{A,\theta}, \prec_\theta, C_\theta, \mu_\theta)$ parametrized by $\theta$.

**Goal:** Each $\theta$ corresponds to a concrete model with computable predictions. Falsification becomes testing parameter constraints.

**Approach:** Start with simplified models (discrete configuration spaces, finite-dimensional systems) and develop computational methods for constraint checking and measure calculation.

#### 11.5.2 Derivation of Field Equations

**Priority 2:** Derive Einstein's equations and gauge field equations from admissibility constraints.

**Approach:** 
- Show that geometric configurations must satisfy consistency conditions (Bianchi identities)
- Prove that matter-geometry coupling is constrained by admissibility preservation
- Demonstrate that the Einstein-Hilbert action emerges as the minimal admissibility-preserving action

**Milestone:** If successful, this would demonstrate LRT genuinely derives physics rather than merely interpreting it.

#### 11.5.3 Standard Model Embedding

**Priority 3:** Show how particle physics emerges from admissibility structure.

**Challenges:**
- Explain gauge groups as admissibility symmetries
- Derive particle multiplets from configuration constraints  
- Explain mass generation and symmetry breaking

**Approach:** Particles as topological defects or stable structures in admissible configuration space. Gauge transformations as redundancies in describing admissible configurations.

#### 11.5.4 Computational Toolkit

**Priority 4:** Develop numerical methods for working with admissibility structures.

**Required tools:**
- Algorithms for constraint satisfaction checking
- Methods for computing admissibility measures $\mu$
- Visualization of admissible configuration regions
- Simulation of constraint evolution

**Impact:** Would enable concrete calculations and predictions, moving LRT from conceptual framework to working theory.

### 11.6 Educational Applications

**Pedagogical advantage:** LRT's constraint-first approach might provide clearer conceptual grounding for students learning quantum mechanics and relativity.

**Potential curriculum:**
1. Start with logical admissibility ($L_3$) as foundation
2. Develop mathematics and geometry as necessary representations
3. Introduce quantum mechanics as admissibility-region dynamics
4. Present measurement as constraint addition, not mysterious collapse
5. Derive spacetime structure from ordered geometry

This could demystify quantum mechanics while maintaining mathematical rigor.

### 11.7 Research Community and Collaboration

**Needed expertise:**
- Mathematical physics (geometry, topology, functional analysis)
- Quantum information theory
- Computational physics and numerical methods
- Philosophy of physics
- Experimental quantum physics

**Collaborative directions:**
- Workshops on constraint-first approaches to physics
- Shared computational infrastructure for admissibility calculations
- Experimental collaborations testing falsifiable predictions
- Interdisciplinary connections to computer science, complexity theory, and optimization

### 11.8 Summary

LRT offers applications across:
- **Theoretical physics:** QFT renormalization, quantum gravity, measurement theory
- **Experimental physics:** Macroscopic quantum tests, Bell experiments, Planck-scale phenomenology  
- **Computation:** Constraint satisfaction, verification, causal inference
- **Interdisciplinary:** Biology, economics, artificial intelligence
- **Education:** Clearer conceptual foundations for teaching physics

The breadth of potential applications reflects LRT's foundational character: as a grounding framework, it touches all domains where constraint satisfaction and logical admissibility are relevant.

Success requires developing explicit parameterizations, deriving specific dynamics, and engaging experimental programs. The framework is in place; substantive physics awaits detailed development.

## 12. Conclusion

This paper has developed Logic Realism Theory (LRT), a foundational framework grounding physical theory in ontological admissibility constraints rather than dynamics, information, or measurement. The central claim is compact:

$$A^* = L_3(I_{\infty})$$

Physical reality consists of those configurations from the space of possibilities that satisfy the logical constraints of identity, non-contradiction, and excluded middle.

From this grounding, we have derived:

**Mathematics** (Section 4) as the formal articulation of admissible distinction, resolving Wigner's "unreasonable effectiveness" puzzle. Mathematical consistency is necessary for physical realizability.

**Geometry** (Section 5) as structured admissible relation, showing why configuration spaces must be geometric and why specific structures (manifolds, metrics, symmetries) appear in physical theory.

**Spacetime** (Section 6) as ordered geometry $(A^*, d_A, \prec)$, where temporal structure arises from logical incompatibility of joint actualization and spatial structure from relational admissibility.

**Dynamics** (Section 7) from admissibility constraints over histories, deriving the action principle, Lagrangian formulation, Hamiltonian as generator of admissible sequencing, and energy as conserved admissibility cost.

**Quantum mechanics** (Section 8) without collapse or branching, explaining superposition as admissible configuration regions, measurement as constraint addition, Bell correlations from global admissibility structure, and no-signaling from marginal invariance.

LRT achieves the structural advantages of Many-Worlds interpretations (unitary evolution preserved, global correlations explained, no ad hoc collapse) while avoiding ontological branching. Only one configuration is actualized in $A^*$, but the admissibility structure is global.

The theory is falsifiable (Section 9) at two levels: directly through violations of $L_3$ in physical processes, and structurally through deviations predicted by admissibility microstructure in regimes where standard theory may fail. Concrete tests include macroscopic superposition limits, Tsirelson bound verification, and Planck-scale phenomenology.

LRT provides potential unified grounding (Section 10) for quantum mechanics, general relativity, quantum field theory, and thermodynamics through a single admissibility structure. Rather than treating these as independent frameworks requiring separate foundations, LRT suggests they represent different aspects of constraint satisfaction in $(A^*, d_A, \prec)$.

Applications (Section 11) extend beyond fundamental physics to quantum computing, constraint satisfaction algorithms, causal inference, experimental design, and interdisciplinary domains where constraint-based reasoning is relevant.

**What has been accomplished:**

1. A rigorously defined ontological foundation for physical theory
2. Derivation of core physical structures from admissibility constraints
3. Unified explanations for quantum puzzles without additional ontology
4. Falsifiable predictions distinguishing LRT from alternatives
5. Research program with concrete technical challenges

**What remains:**

1. Explicit parameterizations of admissibility structures for quantitative predictions
2. Derivation of specific field equations (Einstein, gauge theories) from admissibility
3. Embedding of Standard Model particle physics in the framework
4. Computational tools for working with admissible configuration spaces
5. Experimental programs testing predicted deviations

The theory is sufficiently developed to be evaluated on its explanatory power, internal consistency, and compatibility with established physics. It is sufficiently concrete to be falsified through experiment. It is sufficiently ambitious to provide genuine unification if its technical program succeeds.

Logic Realism Theory proposes that the structure of physical law reflects the structure of logical admissibility. If correct, the "unreasonable effectiveness of mathematics" is resolved: mathematics works because physics presupposes the distinctions mathematics formalizes. Quantum mechanics is strange because admissibility constraints are global. Spacetime is geometric because admissible relations must be structured. Dynamics follow action principles because admissibility over histories has extremal structure.

The framework invites both philosophical scrutiny and technical development. It stands or falls on whether admissibility structure genuinely constrains physics in the specific ways observed, or whether it merely redescribes established results in new language. The falsifiability criteria and research program provided in Sections 9-11 offer clear paths to adjudication.

Physical reality, in LRT, is constrained possibility. The constraints are logical. The task of physics is to determine which constraints apply and to represent their structure. This paper has shown that taking this perspective seriously yields a coherent, falsifiable, and potentially unifying foundation for fundamental physics.

## References

### Quantum Mechanics Foundations

Bell, J. S. (1964). On the Einstein Podolsky Rosen paradox. *Physics Physique Физика*, 1(3), 195-200.

Bell, J. S. (1987). *Speakable and Unspeakable in Quantum Mechanics*. Cambridge University Press.

Bohm, D. (1952). A suggested interpretation of the quantum theory in terms of "hidden" variables. I and II. *Physical Review*, 85(2), 166-193.

Everett, H. (1957). "Relative state" formulation of quantum mechanics. *Reviews of Modern Physics*, 29(3), 454-462.

von Neumann, J. (1932). *Mathematische Grundlagen der Quantenmechanik*. Springer. [English translation: *Mathematical Foundations of Quantum Mechanics*, Princeton University Press, 1955.]

Griffiths, R. B. (2002). *Consistent Quantum Theory*. Cambridge University Press.

Omnès, R. (1994). *The Interpretation of Quantum Mechanics*. Princeton University Press.

Zurek, W. H. (2003). Decoherence, einselection, and the quantum origins of the classical. *Reviews of Modern Physics*, 75(3), 715-775.

### Many-Worlds and Everettian Approaches

DeWitt, B. S., & Graham, N. (Eds.). (1973). *The Many-Worlds Interpretation of Quantum Mechanics*. Princeton University Press.

Wallace, D. (2012). *The Emergent Multiverse: Quantum Theory according to the Everett Interpretation*. Oxford University Press.

Saunders, S., Barrett, J., Kent, A., & Wallace, D. (Eds.). (2010). *Many Worlds? Everett, Quantum Theory, & Reality*. Oxford University Press.

Vaidman, L. (2002). Many-worlds interpretation of quantum mechanics. *Stanford Encyclopedia of Philosophy*.

### Quantum Information and No-Signaling

Tsirelson, B. S. (1980). Quantum generalizations of Bell's inequality. *Letters in Mathematical Physics*, 4(2), 93-100.

Popescu, S., & Rohrlich, D. (1994). Quantum nonlocality as an axiom. *Foundations of Physics*, 24(3), 379-385.

Nielsen, M. A., & Chuang, I. L. (2000). *Quantum Computation and Quantum Information*. Cambridge University Press.

Peres, A., & Terno, D. R. (2004). Quantum information and relativity theory. *Reviews of Modern Physics*, 76(1), 93-123.

Clifton, R., Bub, J., & Halvorson, H. (2003). Characterizing quantum theory in terms of information-theoretic constraints. *Foundations of Physics*, 33(11), 1561-1591.

### Information-Theoretic Reconstructions

Hardy, L. (2001). Quantum theory from five reasonable axioms. *arXiv preprint quant-ph/0101012*.

Chiribella, G., D'Ariano, G. M., & Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Höhn, P. A., & Wharton, K. B. (2016). Quantum theory from questions. *Physical Review A*, 94(4), 042108.

Fuchs, C. A., Mermin, N. D., & Schack, R. (2014). An introduction to QBism with an application to the locality of quantum mechanics. *American Journal of Physics*, 82(8), 749-754.

### Mathematics in Physics

Wigner, E. P. (1960). The unreasonable effectiveness of mathematics in the natural sciences. *Communications in Pure and Applied Mathematics*, 13(1), 1-14.

Weyl, H. (1949). *Philosophy of Mathematics and Natural Science*. Princeton University Press.

Tegmark, M. (2008). The mathematical universe. *Foundations of Physics*, 38(2), 101-150.

Penrose, R. (2004). *The Road to Reality: A Complete Guide to the Laws of the Universe*. Jonathan Cape.

Balaguer, M. (1998). *Platonism and Anti-Platonism in Mathematics*. Oxford University Press.

### Spacetime and Relativity Foundations

Einstein, A. (1916). Die Grundlage der allgemeinen Relativitätstheorie. *Annalen der Physik*, 354(7), 769-822. [English translation: The foundation of the general theory of relativity.]

Minkowski, H. (1909). Raum und Zeit. *Physikalische Zeitschrift*, 10, 75-88. [English translation: Space and time.]

Rovelli, C. (2004). *Quantum Gravity*. Cambridge University Press.

Sorkin, R. D. (2005). Causal sets: Discrete gravity. In A. Gomberoff & D. Marolf (Eds.), *Lectures on Quantum Gravity* (pp. 305-327). Springer.

Barbour, J. (1999). *The End of Time: The Next Revolution in Physics*. Oxford University Press.

Smolin, L. (2001). *Three Roads to Quantum Gravity*. Basic Books.

### Quantum Gravity and Unification

Ashtekar, A., & Lewandowski, J. (2004). Background independent quantum gravity: A status report. *Classical and Quantum Gravity*, 21(15), R53.

Polchinski, J. (1998). *String Theory* (Vols. 1-2). Cambridge University Press.

Witten, E. (1995). String theory dynamics in various dimensions. *Nuclear Physics B*, 443(1-2), 85-126.

Weinberg, S. (1995). *The Quantum Theory of Fields* (Vols. 1-3). Cambridge University Press.

### Quantum Logic and Algebraic Approaches

Birkhoff, G., & von Neumann, J. (1936). The logic of quantum mechanics. *Annals of Mathematics*, 37(4), 823-843.

Isham, C. J., & Butterfield, J. (1998). A topos perspective on the Kochen-Specker theorem: I. Quantum states as generalized valuations. *International Journal of Theoretical Physics*, 37(11), 2669-2733.

Döring, A., & Isham, C. J. (2008). A topos foundation for theories of physics: I-IV. *Journal of Mathematical Physics*, 49(5), 053515-053518.

Heunen, C., Landsman, N. P., & Spitters, B. (2009). A topos for algebraic quantum theory. *Communications in Mathematical Physics*, 291(1), 63-110.

### Category Theory in Physics

Abramsky, S., & Coecke, B. (2004). A categorical semantics of quantum protocols. In *Proceedings of the 19th Annual IEEE Symposium on Logic in Computer Science* (pp. 415-425).

Coecke, B., & Kissinger, A. (2017). *Picturing Quantum Processes: A First Course in Quantum Theory and Diagrammatic Reasoning*. Cambridge University Press.

Baez, J. C., & Stay, M. (2011). Physics, topology, logic and computation: A Rosetta Stone. In *New Structures for Physics* (pp. 95-172). Springer.

### Logic and Foundations

Frege, G. (1879). *Begriffsschrift, eine der arithmetischen nachgebildete Formelsprache des reinen Denkens*. Verlag von Louis Nebert. [English translation: *Conceptual Notation*.]

Russell, B., & Whitehead, A. N. (1910-1913). *Principia Mathematica* (Vols. 1-3). Cambridge University Press.

Tarski, A. (1944). The semantic conception of truth and the foundations of semantics. *Philosophy and Phenomenological Research*, 4(3), 341-376.

Quine, W. V. O. (1951). Two dogmas of empiricism. *The Philosophical Review*, 60(1), 20-43.

### Philosophy of Physics

van Fraassen, B. C. (1980). *The Scientific Image*. Oxford University Press.

Ladyman, J., & Ross, D. (2007). *Every Thing Must Go: Metaphysics Naturalized*. Oxford University Press.

French, S. (2014). *The Structure of the World: Metaphysics and Representation*. Oxford University Press.

Maudlin, T. (2007). *The Metaphysics within Physics*. Oxford University Press.

Albert, D. Z. (1992). *Quantum Mechanics and Experience*. Harvard University Press.

### Measurement and Decoherence

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885-893.

Deutsch, D. (1999). Quantum theory of probability and decisions. *Proceedings of the Royal Society of London A*, 455(1988), 3129-3137.

Wallace, D. (2007). Quantum probability from subjective likelihood: Improving on Deutsch's proof of the probability rule. *Studies in History and Philosophy of Modern Physics*, 38(2), 311-332.

Schlosshauer, M. (2007). *Decoherence and the Quantum-to-Classical Transition*. Springer.

### Constraint-Based Dynamics

Dirac, P. A. M. (1964). *Lectures on Quantum Mechanics*. Yeshiva University Press.

Henneaux, M., & Teitelboim, C. (1992). *Quantization of Gauge Systems*. Princeton University Press.

Rovelli, C. (1991). What is observable in classical and quantum gravity? *Classical and Quantum Gravity*, 8(2), 297-316.

Arnowitt, R., Deser, S., & Misner, C. W. (1962). The dynamics of general relativity. In L. Witten (Ed.), *Gravitation: An Introduction to Current Research* (pp. 227-265). Wiley.

### Action Principles and Variational Methods

Lanczos, C. (1970). *The Variational Principles of Mechanics* (4th ed.). Dover Publications.

Yourgrau, W., & Mandelstam, S. (1968). *Variational Principles in Dynamics and Quantum Theory* (3rd ed.). Dover Publications.

Goldstein, H., Poole, C., & Safko, J. (2002). *Classical Mechanics* (3rd ed.). Addison-Wesley.

### Experimental Quantum Foundations

Aspect, A., Dalibard, J., & Roger, G. (1982). Experimental test of Bell's inequalities using time-varying analyzers. *Physical Review Letters*, 49(25), 1804-1807.

Hensen, B., et al. (2015). Loophole-free Bell inequality violation using electron spins separated by 1.3 kilometres. *Nature*, 526(7575), 682-686.

Arndt, M., et al. (1999). Wave-particle duality of C60 molecules. *Nature*, 401(6754), 680-682.

Eibenberger, S., et al. (2013). Matter-wave interference of particles selected from a molecular library with masses exceeding 10,000 amu. *Physical Chemistry Chemical Physics*, 15(35), 14696-14700.

### Falsifiability and Scientific Method

Popper, K. R. (1959). *The Logic of Scientific Discovery*. Hutchinson. [Originally published in German as *Logik der Forschung*, 1934.]

Kuhn, T. S. (1962). *The Structure of Scientific Revolutions*. University of Chicago Press.

Lakatos, I. (1970). Falsification and the methodology of scientific research programmes. In I. Lakatos & A. Musgrave (Eds.), *Criticism and the Growth of Knowledge* (pp. 91-196). Cambridge University Press.
