Library

Account

Upgrade
Install

Answer

Links

Images
Check the math: # Logic Realism Theory: Technical Foundations

**James (JD) Longmire**\
ORCID: 0009-0009-1383-7698\
Northrop Grumman Fellow (unaffiliated research)

**Version:** 2.10 (December 2025)\
**Status:** Working Draft
**Purpose:** Address technical gaps identified in peer review; provide rigorous mathematical foundations for LRT

---

## Abstract

This companion paper provides the rigorous mathematical constructions underlying Logic Realism Theory. We prove three key results: (1) the Hardy kernel construction derives inner product structure directly from the distinguishability metric $D$ without presupposing Hilbert space or the Born rule; (2) LRT axioms imply all five Masanes-Müller axioms, including MM5 (entanglement connectivity) via the Lee-Selby theorem applied to CBP-enforced purification uniqueness; (3) complex quantum mechanics is the unique theory satisfying LRT axioms. Given the LRT axiom set—including Tier-2 physical axioms (continuity, local tomography) and structural principles (CBP, Global Parsimony)—the reconstruction to complex quantum mechanics is rigorous and gap-free.

---

## 1. Introduction

### 1.1 The Technical Program

The main LRT paper makes several claims that invoke external mathematical results:

| Claim | External Result | Status |
|-------|-----------------|--------|
| Complex Hilbert space from interface constraints | Masanes-Müller reconstruction | Proven (§3-4, §6) |
| Born rule from interface structure | Gleason's theorem | Via inner product (§3.3) |
| Unitary dynamics from information preservation | Stone's theorem | Via CBP (§4) |
| Complex QM is uniquely stable | Reconstruction uniqueness | Proven (§5, Theorem 5.7) |

This paper establishes these results by providing:

1. **Construction:** How 3FLL-constituted distinguishability induces inner product structure
2. **Mapping:** Explicit correspondence between LRT axioms and reconstruction theorem premises
3. **Uniqueness:** Proof that complex QM is the unique structure satisfying interface + stability requirements

### 1.1a Methodological Note: What IIS Represents

Before proceeding to formal constructions, we emphasize a crucial point: the Infinite Information Space (IIS) is not exotic new mathematical structure imposed on physics. It is what physics already uses, made explicit.

Physicists routinely work with Hilbert space, configuration space, Fock space, and phase space—mathematical structures not embedded in spacetime yet treated as describing something physically meaningful. IIS names what these structures represent: the space of distinguishable possibilities constrained by the Three Fundamental Laws of Logic.

The derivations in this paper do not add ontology to quantum mechanics. They reveal why quantum mechanics has its specific structure: because that structure is uniquely selected by the requirements of the interface between distinguishable possibilities (IIS) and determinate outcomes (Boolean actuality). The mathematical structures derived here—complex Hilbert space, Born rule probabilities, unitary dynamics—are what any interface satisfying 3FLL plus physical constraints must have.

This inverts the usual foundational approach. Rather than taking quantum formalism as given and seeking interpretation, we start from the metaphysical requirement that distinguishability presupposes 3FLL and derive the formalism as the unique solution to the interface problem.

### 1.2 Notation and Conventions

| Symbol | Meaning |
|--------|---------|
| $\mathcal{I}$ | Infinite Information Space |
| $D(s_1, s_2)$ | Distinguishability measure between states |
| $\mathcal{A}$ | Boolean Actuality |
| $\Phi: \mathcal{I} \to \mathcal{A}$ | Interface map |
| $3FLL$ | Identity, Non-Contradiction, Excluded Middle |

---

## 2. Distinguishability as Primitive

### 2.1 The Distinguishability Relation

**Definition 2.1 (Distinguishability).** Two states $s_1, s_2 \in \mathcal{I}$ are *distinguishable*, written $s_1 \perp s_2$, iff there exists a measurement context $M$ such that $P_M(s_1) \neq P_M(s_2)$.

**Remark:** This definition presupposes 3FLL: Identity (states are self-identical), Non-Contradiction (equality and inequality cannot both hold), Excluded Middle (states are either equal or not). The 3FLL grounding is immediate from the definition.

### 2.2 The Distinguishability Metric

**Definition 2.2 (Distinguishability Degree).** For states $s_1, s_2$, define:

$$D(s_1, s_2) = \sup_M \|P_M(s_1) - P_M(s_2)\|_{TV}$$

where $\|\cdot\|_{TV}$ is the total variation distance and the supremum is over all measurement contexts.

**Properties:**

1. $D(s, s) = 0$ (identity)
2. $D(s_1, s_2) = D(s_2, s_1)$ (symmetry)
3. $D(s_1, s_3) \leq D(s_1, s_2) + D(s_2, s_3)$ (triangle inequality)
4. $D(s_1, s_2) = 0 \implies s_1 = s_2$ (in the space of operationally distinguishable states)

**Theorem 2.1.** $D$ is a metric on the space of operationally distinguishable states.

**Proof:** Properties 1-4 are the metric axioms. Property 1 follows from probability normalization. Property 2 follows from symmetry of $\|\cdot\|_{TV}$. Property 3 follows from the triangle inequality for total variation. Property 4 is definitional—we identify states that cannot be distinguished by any measurement. ∎

---

## 3. From Distinguishability to Inner Product

### 3.1 The Core Construction Problem

**Problem:** Given the distinguishability metric $D$, construct an inner product $\langle \cdot | \cdot \rangle$ such that the resulting Hilbert space structure is compatible with $D$.

**Strategy:** Following Hardy (2001), we show that pairwise distinguishability $D(x,y) \in [0,1]$ plus continuity (A3a) induces inner product structure through the geometry of distinguishable state triplets.

### 3.2 Axiomatic Definition of IIS

**Definition 3.1 (IIS as Maximal D-Closed Set).** The Infinite Information Space $\mathcal{I}$ is the maximal set satisfying:

1. **Closure under distinguishability:** If $s \in \mathcal{I}$, then $D(s, \cdot)$ is defined on all of $\mathcal{I}$
2. **Completeness:** Every Cauchy sequence in $(\ mathcal{I}, D)$ converges in $\mathcal{I}$
3. **Richness:** For any $n \geq 2$, there exist $n$ mutually distinguishable states

Formally: $\mathcal{I} = \{s : D \text{ is defined on } s \times \mathcal{I}, \text{ and } \mathcal{I} \text{ is complete under } D\}$

### 3.3 Direct Reconstruction of the Inner Product from D

The following construction derives the inner product directly from the distinguishability metric $D$, without presupposing the Born rule or Bloch-sphere representation.

**Definition 3.2 (Hardy Kernel).** For any three states $x, y, z \in \mathcal{I}$ that are pairwise perfectly distinguishable ($D = 1$), define:

$$K(x,y;z) := 1 - \frac{1}{2}[D(x,y) + D(x,z) - D(y,z)] \in [0,1]$$

**Lemma 3.1 (Kernel Properties).** The kernel $K$ satisfies:

(a) $K$ satisfies the axioms of an abstract inner product kernel over $\mathbb{R}$

(b) $K(x,x;\text{ref}) = \text{constant}$ for fixed reference state

(c) By continuity (A3a) and richness of $\mathcal{I}$, $K$ extends to a full sesquilinear form over $\mathbb{C}$

(d) The only field compatible with local tomography and triangle inequality sharpness is $\mathbb{C}$

**Proof:** Following Hardy (2001, Lemma 2):

*Part (a):* The kernel $K$ inherits symmetry from $D$ and satisfies positivity because $D \in [0,1]$. The polarization identity holds by construction.

*Part (b):* For fixed reference, $K(x,x;\text{ref}) = 1 - \frac{1}{2}[0 + D(x,\text{ref}) - D(x,\text{ref})] = 1$.

*Part (c):* Continuity of $D$ (from A3a) implies continuity of $K$. The richness of $\mathcal{I}$ (infinitely many distinguishable states) allows extension from the real kernel to a sesquilinear form over $\mathbb{C}$ via polarization:

The real inner product $\langle x, y \rangle_{\mathbb{R}} = K(x,y;\text{ref})$ extends to a complex sesquilinear form by the standard construction (see Halmos 1974, §44): given a real inner product space $(V, \langle \cdot, \cdot \rangle_{\mathbb{R}})$, its complexification $V_{\mathbb{C}} = V \oplus iV$ carries the unique sesquilinear form

$$\langle x_1 + iy_1, x_2 + iy_2 \rangle = \langle x_1, x_2 \rangle_{\mathbb{R}} + \langle y_1, y_2 \rangle_{\mathbb{R}} + i(\langle x_1, y_2 \rangle_{\mathbb{R}} - \langle y_1, x_2 \rangle_{\mathbb{R}})$$

The extension is unique given continuity. The question is whether $\mathbb{C}$ is the *correct* field; this is answered by Part (d) and the field-elimination arguments below.

*Part (d):* This is the Masanes-Müller field-elimination step applied to the explicitly constructed $K$, combined with Theorems 5.2-5.3 below. ∎

**Corollary 3.1 (Cosine Law Derived).** The law of cosines for distinguishable triplets is *derived*, not assumed: it emerges from the triangle inequality becoming equality on certain triplets, which is guaranteed by reversible dynamics (A3b).

For states with angles $\theta_{ij}$ defined by $D_{ij} = \sin^2(\theta_{ij}/2)$:

$$\cos(\theta_{13}) = \cos(\theta_{12})\cos(\theta_{23}) + \sin(\theta_{12})\sin(\theta_{23})\cos(\phi)$$

**Remark:** This construction makes the 3FLL grounding manifest: the kernel $K$ presupposes that $D$ is well-defined (Identity), that states are either distinguishable or not (Excluded Middle), and that no state is both distinguishable and indistinguishable from another (Non-Contradiction).

#### 3.3.1 Verification of Hardy's Conditions

Hardy's kernel construction (2001) requires specific conditions on the distinguishability metric. We verify that LRT's $D$ satisfies each requirement.

**Condition H1: D is a metric on pure states.**

*Verification:* By Definition 2.2, $D(s_1, s_2) = \sup_M \|P_M(s_1) - P_M(s_2)\|_{TV}$, where $\|\cdot\|_{TV}$ is the total variation distance.

The metric properties follow:
- **Non-negativity:** $D(s_1, s_2) \geq 0$ (supremum of non-negative quantities)
- **Identity of indiscernibles:** $D(s_1, s_2) = 0 \iff s_1 = s_2$ (by 3FLL: states are identical iff operationally indistinguishable)
- **Symmetry:** $D(s_1, s_2) = D(s_2, s_1)$ (TV distance is symmetric)
- **Triangle inequality:** $D(s_1, s_3) \leq D(s_1, s_2) + D(s_2, s_3)$ (TV distance satisfies triangle inequality; supremum preserves it)

Therefore, $D$ is a metric.

**Condition H2: D ∈ [0,1] with D = 1 for perfectly distinguishable states.**

*Verification:* The total variation distance satisfies $\|P - Q\|_{TV} \in [0,1]$ for probability distributions $P, Q$. Therefore:
$$D(s_1, s_2) = \sup_M \|P_M(s_1) - P_M(s_2)\|_{TV} \in [0,1]$$

For perfectly distinguishable states (orthogonal in Hilbert space), there exists a measurement $M$ that perfectly discriminates them:
$$P_M(s_1) = (1, 0, 0, \ldots), \quad P_M(s_2) = (0, 1, 0, \ldots)$$
$$\|P_M(s_1) - P_M(s_2)\|_{TV} = 1$$

Therefore $D = 1$ for perfectly distinguishable states.

**Condition H3: Continuity of D.**

*Verification:* By A3a (continuity of physical dynamics), state transformations are continuous maps on the state space.

*Claim:* If state space topology is defined by the metric $D$, then $D$ is continuous as a function $D: \mathcal{I} \times \mathcal{I} \to [0,1]$.

*Proof:* Let $s_n \to s$ and $t_n \to t$ in the $D$-metric topology. We show $D(s_n, t_n) \to D(s, t)$.

By triangle inequality:
$$|D(s_n, t_n) - D(s, t)| \leq |D(s_n, t_n) - D(s, t_n)| + |D(s, t_n) - D(s, t)|$$
$$\leq D(s_n, s) + D(t_n, t) \to 0$$

Therefore $D$ is continuous.

*Physical interpretation:* A3a ensures that small changes in preparation procedures produce small changes in measurement statistics. Since $D$ is defined via measurement statistics, continuity of dynamics implies continuity of $D$.

**Condition H4: Existence of pairwise perfectly distinguishable triplets.**

*Verification:* By Definition 3.1 (IIS richness), for any $n \geq 2$, there exist $n$ mutually distinguishable states in $\mathcal{I}$.

*Explicit construction:* For any orthonormal triple $\{|e_1\rangle, |e_2\rangle, |e_3\rangle\}$ in a Hilbert space of dimension $\geq 3$:
- $D(e_i, e_j) = 1$ for $i \neq j$ (orthogonal states are perfectly distinguishable)
- The measurement in the $\{|e_1\rangle, |e_2\rangle, |e_3\rangle\}$ basis perfectly discriminates all three

The richness condition guarantees such triplets exist for any system with dimension $\geq 3$. For qubits (dimension 2), any two orthogonal states form a perfectly distinguishable pair, and the Hardy construction proceeds with pairs.

**Conclusion: Hardy Construction Applies.**

All four conditions are satisfied by LRT's distinguishability metric $D$:

| Condition | Requirement | LRT Verification |
|-----------|-------------|------------------|
| H1 | D is a metric | TV distance properties + 3FLL |
| H2 | D ∈ [0,1], D=1 for orthogonal | TV distance range + perfect discrimination |
| H3 | D is continuous | A3a (continuity axiom) |
| H4 | Distinguishable triplets exist | IIS richness (Definition 3.1) |

Therefore, Hardy's kernel construction is valid for LRT. The inner product derived from $D$ via the Hardy kernel is well-defined and unique (up to phase). ∎

**Theorem 3.2 (Inner Product from Distinguishability).** Given:
- (i) Distinguishability metric $D: \mathcal{I} \times \mathcal{I} \to [0,1]$
- (ii) Continuity of state transformations (A3a)
- (iii) Reversibility of pure state dynamics (A3b)

There exists a unique (up to phase) inner product $\langle \cdot | \cdot \rangle$ on $\mathcal{I}$ such that:

$$D(s_1, s_2) = 1 - |\langle s_1 | s_2 \rangle|^2$$

**Proof:**

*Step 1: Vector space structure from reversibility.*
A3b (CBP) implies pure state dynamics are reversible. Reversible continuous transformations on a convex state space form a Lie group. By continuity (A3a), this group acts smoothly.

*Step 2: Inner product from transitivity.*
The group of reversible transformations acts transitively on pure states of equal distinguishability from a reference state. This defines concentric "spheres" of constant $D$ from any reference. The geometry is that of projective space.

*Step 3: Field determination.*
Local tomography (A3c) restricts the field to $\mathbb{R}$, $\mathbb{C}$, or $\mathbb{H}$ (Masanes-Müller 2011).

*Elimination of $\mathbb{H}$:* Quaternionic tensor products fail associativity for $n \geq 3$ systems (Adler 1995). For spaces $\mathcal{H}_A, \mathcal{H}_B, \mathcal{H}_C$: $(\mathcal{H}_A \otimes \mathcal{H}_B) \otimes \mathcal{H}_C \ncong \mathcal{H}_A \otimes (\mathcal{H}_B \otimes \mathcal{H}_C)$ due to quaternion non-commutativity.

*Elimination of $\mathbb{R}$:* Consider the Bell state $|\Phi^+\rangle = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$ in complex QM. Its local marginals are $\rho_A = \rho_B = \frac{1}{2}I$. In real QM, construct the analogous state. The crucial difference: in complex QM, the relative phase between $|00\rangle$ and $|11\rangle$ is observable via interference with local rotations $e^{i\theta}$. In real QM, no such phase exists. Consequently, real QM admits distinct global states with identical local marginals that complex QM distinguishes (Wootters 1990, Stueckelberg 1960). This violates local tomography: composite states are not determined by local measurements.

Therefore, only $\mathbb{C}$ satisfies A3c + compositional consistency.

*Step 4: Uniqueness.*
The inner product satisfying $D = 1 - |\langle \cdot | \cdot \rangle|^2$ is unique up to overall phase by Wigner's theorem.

Therefore, distinguishability $D$ + continuity + reversibility uniquely determines complex inner product structure. ∎

### 3.4 Physical Interpretation of IIS

The abstract definition of IIS (Definition 3.1) and the Hardy kernel construction may appear remote from physical intuition. This section grounds these abstractions in concrete quantum systems.

#### 3.4.1 Example: Single Qubit and the Bloch Sphere

For a single qubit, the IIS corresponds to the space of pure quantum states, representable on the Bloch sphere. Each point $(\theta, \phi)$ on the sphere represents a distinguishable state:

$$|\psi(\theta, \phi)\rangle = \cos(\theta/2)|0\rangle + e^{i\phi}\sin(\theta/2)|1\rangle$$

The distinguishability metric $D$ gives the trace distance between states:

$$D(\psi_1, \psi_2) = \sqrt{1 - |\langle\psi_1|\psi_2\rangle|^2}$$

For orthogonal states (e.g., $|0\rangle$ and $|1\rangle$), $D = 1$ (perfectly distinguishable). For identical states, $D = 0$. For states at angle $\theta$ on the Bloch sphere, $D = \sin(\theta/2)$.

**3FLL manifestation:**
- **Identity**: Each point on the Bloch sphere is self-identical; $|\psi\rangle = |\psi\rangle$
- **Non-Contradiction**: No state is both $|0\rangle$ and not-$|0\rangle$; states have definite positions on the sphere
- **Excluded Middle**: Any two states are either identical ($D = 0$) or distinguishable ($D > 0$)

The Bloch sphere geometry emerges from 3FLL-constituted distinguishability: the metric structure, the topology, and the group of reversible transformations (SU(2)) all follow from the distinguishability constraints plus continuity and reversibility.

#### 3.4.2 Example: Two-Slit Experiment

Consider an electron in a two-slit apparatus. The IIS representation illuminates the non-Boolean structure:

**Before measurement (state in IIS):**
$$|\psi\rangle = \frac{1}{\sqrt{2}}(|\text{slit}_1\rangle + |\text{slit}_2\rangle)$$

This state encodes the full distinguishability structure:
- Distinguishable from $|\text{slit}_1\rangle$ alone: $D(|\psi\rangle, |\text{slit}_1\rangle) = 1/\sqrt{2}$
- Distinguishable from $|\text{slit}_2\rangle$ alone: $D(|\psi\rangle, |\text{slit}_2\rangle) = 1/\sqrt{2}$
- Carries interference information (relative phase between paths)

**Non-Boolean character:** The proposition "electron went through slit 1" has no definite truth value in IIS. This is not a failure of 3FLL but a consequence of the state being genuinely indeterminate with respect to the slit basis. The 3FLL apply to the state's identity (it is determinately $|\psi\rangle$), not to properties the state doesn't possess.

**Upon measurement (actualization to Boolean outcome):**
When position is measured on the detection screen:
- Exactly one location registers (Excluded Middle)
- That location is definite (Identity)
- It is not simultaneously another location (Non-Contradiction)

The transition from IIS to Boolean actuality is the interface: the non-Boolean superposition resolves to a Boolean outcome, with probabilities given by the Born rule (derived from the inner product structure).

#### 3.4.3 Example: General n-Dimensional System

For a quantum system with Hilbert space $\mathcal{H}$ of dimension $n$:

**Pure states in IIS:** The projective space $\mathbb{CP}^{n-1}$ (rays in $\mathcal{H}$)
- Each ray $[|\psi\rangle]$ is a point in IIS
- The Fubini-Study metric on $\mathbb{CP}^{n-1}$ corresponds to distinguishability $D$

**Mixed states in IIS:** The space of density operators $\mathcal{D}(\mathcal{H})$
- Convex set with pure states as extreme points
- $D(\rho_1, \rho_2) = \frac{1}{2}\|\rho_1 - \rho_2\|_1$ (trace distance)

**Dimension is physical input:** The dimension $n$ is not derived from LRT; it specifies the distinguishability structure of a particular physical system. A spin-1/2 particle has $n = 2$; a spin-1 particle has $n = 3$; a harmonic oscillator has $n = \infty$. LRT explains *why* the state space has complex Hilbert structure given any $n$, but does not determine $n$ itself.

**Richness condition:** Definition 3.1 requires that for any $k$, there exist $k$ mutually distinguishable states. For finite $n$, this is satisfied up to $k = n$ (orthonormal basis). For infinite-dimensional systems (e.g., position of a particle), the richness is unbounded.

#### 3.4.4 Example: Composite Systems and Entanglement

For bipartite system $AB$ with Hilbert spaces $\mathcal{H}_A \otimes \mathcal{H}_B$:

**Factorizable states:** $|\psi_A\rangle \otimes |\psi_B\rangle$
- Product of individual IIS elements
- Local measurements on A and B are statistically independent
- $D_{AB} = \sqrt{D_A^2 + D_B^2 - D_A^2 D_B^2}$ for product states

**Entangled states:** $|\Psi\rangle \neq |\psi_A\rangle \otimes |\psi_B\rangle$
- Correlation structure in IIS not reducible to subsystem states
- Example: Bell state $|\Phi^+\rangle = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$

**Entanglement as IIS structure:**
The Bell state $|\Phi^+\rangle$ has the following distinguishability properties:
- Local marginals: $\rho_A = \rho_B = \frac{1}{2}I$ (maximally mixed)
- Global state: pure, with $D(|\Phi^+\rangle, |\Phi^-\rangle) = 1$

The entanglement is not "spooky action" but correlation structure built into the IIS state. When Alice and Bob measure:
- Each obtains a Boolean outcome (3FLL satisfied locally)
- Outcomes are correlated because both actualize from the same IIS structure
- No signal propagates; both access shared distinguishability structure

**Local tomography (A3c):** For complex QM, the global state is uniquely determined by local measurements plus correlations. This is why $\mathbb{C}$ is required: real QM fails this (Theorem 5.2 below), and quaternionic QM fails tensor associativity for three or more systems.

#### 3.4.5 Summary: IIS as Distinguishability Structure

| System | IIS Representation | D Metric | 3FLL Role |
|--------|-------------------|----------|-----------|
| Single qubit | Bloch sphere $S^2$ | Trace distance | State identity, mutual exclusion |
| Two-slit | Superposition in $\mathbb{C}^2$ | Fubini-Study | Outcome determinacy at measurement |
| n-level system | $\mathbb{CP}^{n-1}$ (pure) | Trace distance | Distinguishability structure |
| Composite AB | $\mathcal{H}_A \otimes \mathcal{H}_B$ | Trace distance | Local outcomes Boolean, global correlations |

The key insight: IIS is not a mysterious abstract space but the familiar quantum state space, viewed through the lens of distinguishability. The 3FLL are not imposed externally but constitute the very notion of distinguishable states. The non-Boolean structure of superposition coexists with 3FLL because 3FLL apply to state identity, not to properties states may lack.

### 3.5 Operational Primitives from Distinguishability

**Definition 3.2 (States).** A *state* is an equivalence class under operational indistinguishability:
$$[p] = \{p' : D(p, p') = 0\}$$

**Definition 3.3 (Effects).** An *effect* $e: \Omega \to [0,1]$ satisfies:
- Normalization: $\sum_i e_i(s) = 1$ for complete measurements
- D-consistency: $|e(s_1) - e(s_2)| \leq D(s_1, s_2)$

**Definition 3.4 (Transformations).** Admissible $T: \Omega \to \Omega$ satisfies:
- $D(Ts_1, Ts_2) \leq D(s_1, s_2)$ (non-expansion)
- Equality for reversible $T$ (isometry)

---

## 4. Mapping LRT Axioms to Reconstruction Premises

### 4.1 The Masanes-Müller Axioms

Masanes-Müller (2011) derive complex quantum mechanics from five axioms:

| MM Axiom | Statement |
|----------|-----------|
| MM1 | Continuous reversibility: Every pure state can be reversibly transformed to any other |
| MM2 | Tomographic locality: Composite system states determined by local measurements + correlations |
| MM3 | Existence of pure states: The state space contains pure states |
| MM4 | Subspace axiom: Every system with 2+ distinguishable states contains a qubit subsystem |
| MM5 | All pure bipartite states connected by local reversible dynamics + entangled state |

### 4.2 LRT Axioms Restated

| LRT Axiom | Statement | Tier |
|-----------|-----------|------|
| A1 | 3FLL constitute distinguishability | Tier-1 (foundational) |
| A2 | IIS contains all distinguishable configurations | Tier-1 (foundational) |
| A3a | Physical dynamics are continuous | Tier-2 (physical) |
| A3b | Information is preserved (CBP) | Tier-2 (structural principle) |
| A3c | Local tomography holds | Tier-2 (physical) |
| A4 | Global Parsimony: no surplus structure | Tier-2 (structural principle) |
| A5 | Interface probability measure is non-contextual | Tier-2 (physical) |

**Tier classification:**
- **Tier-1 (foundational):** Constitutive claims about 3FLL and distinguishability. These are LRT's core philosophical commitments.
- **Tier-2 (physical):** Empirically motivated physical constraints (continuity, local tomography, non-contextuality). Not derived from 3FLL.
- **Tier-2 (structural principle):** Methodological commitments (CBP, Global Parsimony). Adopted by LRT but alternatives are coherent. See Main paper Sections 2.5-2.6 for discussion.

### 4.3 The Mapping

**Theorem 4.1 (LRT → Masanes-Müller).** The LRT axioms imply the Masanes-Müller axioms.

**Proof Sketch:**

**MM1 (Continuous reversibility) ← A3a + A3b:**
- A3a gives continuity of dynamics
- A3b (CBP) requires information preservation, which implies reversibility for pure states
- Combined: continuous reversible dynamics

**MM2 (Tomographic locality) ← A3c:**
- A3c directly asserts local tomography

**MM3 (Existence of pure states) ← A1 + A2:**
- Pure states = maximally specified states in IIS
- 3FLL guarantee that maximally specified states are well-defined (Identity ensures determinacy)
- A2 guarantees IIS contains them

**MM4 (Subspace axiom) ← A1 + A2:**
- Any system with 2+ distinguishable states admits a binary distinction
- Binary distinction = qubit structure (by A1, distinction is Boolean)
- This is embedded in larger state space

**MM5 (Entanglement structure) ← A3c + Hilbert structure (via Lee-Selby):**
- A3c (local tomography) implies tensor product structure (Theorem 6.2)
- Hilbert space + tensor product → Uhlmann's theorem = purification uniqueness (Theorem 6.3)
- Lee-Selby (2016) proves MM1 + MM2 + purification uniqueness yields MM5

**Status:** All five Masanes-Müller axioms follow from LRT axioms. See §6 for the complete MM5 derivation (Theorem 6.4).

---

## 5. Stability Selection Formalized

### 5.1 Definition of Stability

**Definition 5.1 (Physical Stability).** A theoretical framework $\mathcal{F}$ is *physically stable* if:
1. It admits bound states (discrete energy spectra)
2. These bound states persist under small perturbations
3. Composite systems can form stable structures

**Definition 5.2 (Interface Stability).** An interface structure $\Phi: \mathcal{I} \to \mathcal{A}$ is *stable* if:
1. Small perturbations to states produce small perturbations to outcome distributions
2. The interface respects composition (tensor product structure)
3. No signaling is permitted through the interface

**Definition 5.3 (Observer Stability).** A framework admits *observer stability* if it permits:
1. Stable bound states (atoms)
2. Discrete energy levels (chemistry)
3. Identical particles (periodic table)
4. Quantum tunneling (stellar fusion)

### 5.2 Why Alternatives Fail: Rigorous Analysis

**Theorem 5.1 (Classical Instability - Earnshaw).** Classical electromagnetism with point charges admits no stable equilibrium configurations.

**Proof:** By Earnshaw's theorem (1842), a collection of point charges interacting via Coulomb's law cannot be in stable equilibrium. For any configuration, there exists a direction of displacement that decreases potential energy. Formally:

$$\nabla^2 V = 0 \text{ (Laplace)} \implies V \text{ has no local minimum}$$

Therefore, classical atoms are unstable: electrons spiral into nuclei in $\sim 10^{-11}$ s (Larmor radiation). No stable matter, no observers. ∎

**Theorem 5.2 (Real QM Failure - Local Tomography).** Real quantum mechanics over $\mathbb{R}$ fails local tomography, hence fails interface stability.

**Proof (Wootters 1990, Stueckelberg 1960):**

We construct an explicit counterexample: two distinct global states with identical local marginals that cannot be distinguished by local measurements in real QM but can in complex QM.

*Step 1: Construct two states with identical local marginals.*

Consider the two-qubit states in complex QM:
$$|\Phi^+\rangle = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$$
$$|\Phi^-\rangle = \frac{1}{\sqrt{2}}(|00\rangle - |11\rangle)$$

Both have the same local marginals:
$$\rho_A^{(\Phi^+)} = \text{Tr}_B(|\Phi^+\rangle\langle\Phi^+|) = \frac{1}{2}|0\rangle\langle 0| + \frac{1}{2}|1\rangle\langle 1| = \frac{1}{2}I$$
$$\rho_A^{(\Phi^-)} = \text{Tr}_B(|\Phi^-\rangle\langle\Phi^-|) = \frac{1}{2}|0\rangle\langle 0| + \frac{1}{2}|1\rangle\langle 1| = \frac{1}{2}I$$

Similarly for subsystem B. The local statistics are identical.

*Step 2: Show global distinguishability in complex QM.*

In complex QM, these states are orthogonal: $\langle\Phi^+|\Phi^-\rangle = 0$.

**Distinguishing measurement:** Measure in the Bell basis $\{|\Phi^+\rangle, |\Phi^-\rangle, |\Psi^+\rangle, |\Psi^-\rangle\}$.

Alternatively, use local measurements with phase-sensitive interference:
- Alice applies Hadamard: $H = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$
- Bob applies Hadamard
- Both measure in computational basis

For $|\Phi^+\rangle$:
$$(H \otimes H)|\Phi^+\rangle = \frac{1}{\sqrt{2}}(|++\rangle + |--\rangle)$$

After measurement: outcomes 00 and 11 each with probability 1/2.

For $|\Phi^-\rangle$:
$$(H \otimes H)|\Phi^-\rangle = \frac{1}{\sqrt{2}}(|+-\rangle + |-+\rangle)$$

After measurement: outcomes 01 and 10 each with probability 1/2.

**The states are perfectly distinguishable** via this local procedure (local unitaries + local measurements).

*Step 3: Show real QM cannot distinguish them.*

In real QM, the Hilbert space is $\mathbb{R}^2 \otimes \mathbb{R}^2$, and only real linear combinations are permitted.

**Key observation:** The Hadamard gate $H$ is real, so it exists in real QM. But the phase gate
$$S = \begin{pmatrix} 1 & 0 \\ 0 & i \end{pmatrix}$$
does not exist in real QM (it requires $i$).

In real QM, both $|\Phi^+\rangle$ and $|\Phi^-\rangle$ exist (they have real coefficients). But consider the state:
$$|\Phi_\theta\rangle = \frac{1}{\sqrt{2}}(|00\rangle + e^{i\theta}|11\rangle)$$

For $\theta \neq 0, \pi$, this state requires complex amplitudes. In real QM, only $\theta = 0$ ($|\Phi^+\rangle$) and $\theta = \pi$ ($|\Phi^-\rangle$) are representable.

**The failure:** In complex QM, the continuous family $|\Phi_\theta\rangle$ spans a circle, and local operations can rotate around this circle (via phase gates). In real QM, only two points on the circle exist, and there is no local operation connecting them.

More precisely: the distinguishing protocol above uses the fact that $H \otimes H$ maps $|\Phi^+\rangle$ and $|\Phi^-\rangle$ to different measurement statistics. This works because the relative phase ($+1$ vs $-1$) affects interference.

But in real QM without access to the full complex structure, the local marginals of both states are $\frac{1}{2}I$, and there exists no local protocol to distinguish them. The relative sign is a global property invisible to real local measurements.

*Step 4: Formal statement of violation.*

**Local tomography (A3c/MM2):** The state of a composite system is completely determined by the statistics of local measurements on subsystems.

**Real QM violates this:** $|\Phi^+\rangle$ and $|\Phi^-\rangle$ have identical local statistics but are globally distinct.

In complex QM, local tomography holds because phase-sensitive measurements (using $S, T$, or other complex gates) can extract the relative phase information.

*Consequence:* Real QM fails A3c. Since A3c is required for interface stability (composite system behavior must be predictable from local behavior), real QM fails interface stability criterion 2. ∎

**Theorem 5.3 (Quaternionic QM Failure - Tensor Associativity).** Quaternionic quantum mechanics over $\mathbb{H}$ fails tensor product associativity for $n \geq 3$ systems.

**Proof (Adler 1995):**

For quaternionic Hilbert spaces $\mathcal{H}_A, \mathcal{H}_B, \mathcal{H}_C$:

$$(\mathcal{H}_A \otimes \mathcal{H}_B) \otimes \mathcal{H}_C \ncong \mathcal{H}_A \otimes (\mathcal{H}_B \otimes \mathcal{H}_C)$$

This follows from non-commutativity of quaternions: $ij = k$ but $ji = -k$.

*Consequence:* Three-particle states are ambiguous. The physics of system ABC depends on the order of composition. This violates compositional consistency required for interface stability.

*Physical implication:* Atoms with 3+ particles (all atoms except hydrogen) have ill-defined states. No stable molecules, no chemistry, no observers. ∎

**Theorem 5.4 (Super-Quantum Failure - Signaling Under Composition).** Any GPT exceeding the Tsirelson bound permits signaling under finite composition.

**Proof (van Dam 2005, Brassard et al. 2006):**

Let $\mathcal{S}_{max}$ be the maximum CHSH value achievable in a GPT.

| Theory | $\mathcal{S}_{max}$ | Status |
|--------|---------------------|--------|
| Classical | 2 | Local |
| Quantum | $2\sqrt{2} \approx 2.83$ | Tsirelson bound |
| PR-box | 4 | No-signaling (single use) |

*Van Dam's result:* With access to PR-boxes, any Boolean function $f:\{0,1\}^n \to \{0,1\}$ can be computed with $O(1)$ bits of communication.

*Implication:* Communication complexity collapses. In particular, for large $n$, functions requiring $\Omega(n)$ bits classically require $O(1)$ bits with PR-boxes.

*Brassard et al. extension:* This implies that under composition of PR-boxes:
- Correlations can be amplified
- Effective signaling emerges
- The no-signaling condition is unstable under iteration

*Conclusion:* GPTs with $\mathcal{S} > 2\sqrt{2}$ violate interface stability criterion 3 (no signaling) under composition. ∎

### 5.3 The Tsirelson Bound as Stability Maximum

**Proposition 5.5 (Tsirelson Bound Compatibility).**

The Tsirelson bound $\mathcal{S} \leq 2\sqrt{2}$ is compatible with and interpretable within LRT's framework:
1. Consistency Bridging Principle (CBP): All states must admit Boolean resolution
2. Global Parsimony: No surplus structure beyond 3FLL + physical constraints
3. No signaling under arbitrary composition

**Status clarification:** This proposition demonstrates *compatibility*, not *derivation*. LRT provides an interpretive framework within which the Tsirelson bound is natural (interface stability, no surplus signaling mechanisms), but the specific value 2√2 is not derived from 3FLL or CBP. The value comes from the mathematics of complex Hilbert space (itself derived via local tomography). A full derivation of *why* 2√2 specifically marks the stability threshold remains open (see Main paper Section 4.4).

**Argument:**

*Step 1:* CBP requires that entangled states resolve to correlated Boolean outcomes. The correlation structure must be consistent across all measurement contexts.

*Step 2:* Global Parsimony forbids mechanisms that would allow amplification of correlations beyond what the state structure supports. Any such mechanism would constitute surplus structure.

*Step 3:* Within complex QM (established by Theorems 3.2, 5.6), the Tsirelson bound satisfies:
- Consistency with complex Hilbert space structure
- No signaling under composition (Theorem 5.4)
- No communication complexity collapse

*Step 4:* Explicit calculation confirms the maximum: For CHSH with quantum states,
$$\mathcal{S} = \langle A_1 B_1 \rangle + \langle A_1 B_2 \rangle + \langle A_2 B_1 \rangle - \langle A_2 B_2 \rangle$$

Maximum achieved by measuring $|\Phi^+\rangle$ with optimal angles:
$$\mathcal{S}_{max} = 2\sqrt{2}$$

**Conclusion:** The Tsirelson bound is the unique maximum compatible with LRT axioms. LRT interprets this as the interface stability limit, but deriving 2√2 from first principles remains future work. ∎

### 5.4 Observer Stability Theorem

**Theorem 5.6 (dim(H) ≥ 3 + Local Tomography ⇒ Complex Field).**

For any GPT with:
- State space dimension $\geq 3$
- Local tomography
- Observer stability (bound states exist)

The underlying field must be $\mathbb{C}$.

**Proof:**

*Step 1:* Local tomography restricts to $\mathbb{R}$, $\mathbb{C}$, or $\mathbb{H}$ (Masanes-Müller).

*Step 2:* dim $\geq 3$ and observer stability require stable 3-particle systems (lithium and beyond).

*Step 3:* By Theorem 5.3, $\mathbb{H}$ fails for 3+ particles (tensor associativity).

*Step 4:* Observer stability requires discrete energy spectra. In real QM, the hydrogen spectrum is preserved, but the absence of complex phases means:
- No spin-orbit coupling (requires $i$ in commutators)
- Altered selection rules
- Different chemistry

*Step 5:* Only $\mathbb{C}$ yields Pauli-stable matter:
- Pauli exclusion (antisymmetric wavefunctions require complex phases)
- Correct atomic spectra
- Chemistry as observed

Therefore, $\mathbb{C}$ is uniquely selected. ∎

**Remark (Alternative Confirmation Route):** The spectroscopic argument in Step 4-5 is qualitative rather than quantitative. However, the complex/real distinction has now been experimentally confirmed via an independent route: Renou et al. (2021) demonstrated that quantum correlations in a Bell-type experiment distinguish complex from real QM, with the observed data matching complex QM predictions and ruling out real QM at high significance. This provides direct experimental confirmation that $\mathbb{C}$ is required, complementing the theoretical stability argument. The spectroscopic route (McKague 2009, Aleksandrova et al. 2013) remains an open quantitative problem, but is no longer required for the conclusion: experiment has confirmed that nature selects $\mathbb{C}$.

### 5.5 Uniqueness Theorem

**Theorem 5.7 (Uniqueness).** Complex quantum mechanics is the unique probabilistic theory satisfying the LRT axioms A1-A5.

**Proof:**

*Step 1: LRT → Masanes-Müller.* By Theorem 4.1 and §6, LRT axioms imply all five MM axioms:
- MM1-MM4: Direct (Theorem 4.1)
- MM5: Via Uhlmann + Lee-Selby (Theorem 6.4)

*Step 2: Stability eliminates alternatives.*

| Alternative | Failure Mode | Theorem |
|-------------|--------------|---------|
| Classical | No bound states | 5.1 |
| Real QM | No local tomography | 5.2 |
| Quaternionic QM | No tensor associativity | 5.3 |
| Super-quantum GPT | Signaling under composition | 5.4 |

*Step 3: Uniqueness.* By Masanes-Müller (2011), any theory satisfying MM1-MM5 is complex quantum mechanics. LRT satisfies MM1-MM5. Therefore, complex quantum mechanics is the unique theory satisfying the full LRT axiom set.

The uniqueness is *relative to* the LRT axioms, including Tier-2 physical and structural principles. This is a conditional derivation: given these axioms, complex QM follows uniquely. ∎

---

## 6. Derivation of MM5 via Purification Uniqueness

### 6.1 The Lee-Selby Theorem

The remaining Masanes-Müller axiom MM5 (sufficient entanglement) follows from the Hilbert space structure established in §3, combined with local tomography (A3c). The key intermediate result is *purification uniqueness*, which we derive from the mathematical structure of Hilbert spaces with tensor products.

**Key Reference:** Lee, C. M. & Selby, J. H. "Deriving Grover's lower bound from simple physical principles." *New J. Phys.* 18, 093047 (2016). See also de la Torre et al., *Phys. Rev. Lett.* 109, 090403 (2012).

**Theorem 6.1 (Lee-Selby 2016, rephrased).** Let a theory satisfy:
1. Continuous reversibility of pure states (LRT: A3a + A3b → MM1)
2. Local tomography (LRT: A3c → MM2)
3. Purification uniqueness up to local reversibles on the purifying system
4. Every system has at least one faithful state (automatic with continuous reversibility)

Then the theory has exactly the bipartite pure-state entanglement structure of complex quantum mechanics: any two pure bipartite states are reversibly interconvertible using local operations and one copy of a maximally entangled state (i.e., MM5 holds).

LRT satisfies conditions 1, 2, and 4 directly. The following two subsections establish condition 3.

### 6.2 Local Tomography Implies Tensor Product Structure

**Theorem 6.2 (Tensor Product from Local Tomography).** Local tomography (A3c) implies that the state space of composite systems has tensor product structure: $\mathcal{I}_{AB} \cong \mathcal{I}_A \otimes \mathcal{I}_B$.

**Proof:**

Local tomography (A3c) requires: for any state $\rho_{AB}$ on composite system AB, the statistics of all local measurements $\{M_A\}$ on A and $\{M_B\}$ on B, together





There are a few mathematical issues and points that need tightening or correction, but the overall structure of your program is consistent with the cited reconstruction literature.​

Distinguishability metric and basic properties
The definition of 
D
(
s
1
,
s
2
)
D(s 
1
 ,s 
2
 ) as a supremum over total variation distances yields a bona fide metric on operational states, and your proof of Theorem 2.1 is correct as stated for classical probability distributions and extends in the usual way to quantum states via the trace distance. The identification of states with 
D
=
0
D=0 is standard in operational frameworks and matches generalized probabilistic theories (GPT) practice.​

However, you later equate this 
D
D with 
1
−
∣
⟨
ψ
1
∣
ψ
2
⟩
∣
2
1−∣⟨ψ 
1
 ∣ψ 
2
 ⟩∣ 
2
 
  in the qubit section, but then in Theorem 3.2 impose 
D
=
1
−
∣
⟨
s
1
∣
s
2
⟩
∣
2
D=1−∣⟨s 
1
 ∣s 
2
 ⟩∣ 
2
 , which are not the same functional forms; you need to choose one and keep it globally consistent.​ If you want 
D
D to coincide with trace distance for pure states, then the correct relation is 
D
(
ψ
1
,
ψ
2
)
=
1
−
∣
⟨
ψ
1
∣
ψ
2
⟩
∣
2
D(ψ 
1
 ,ψ 
2
 )= 
1−∣⟨ψ 
1
 ∣ψ 
2
 ⟩∣ 
2
 
 , not the linear form.​ This also affects the formula for “angles” via 
D
i
j
=
sin
⁡
2
(
θ
i
j
/
2
)
D 
ij
 =sin 
2
 (θ 
ij
 /2), which is inconsistent with the square‑root trace distance; check those definitions carefully.

Hardy kernel and inner product reconstruction
Hardy’s reconstruction (and related Masanes–Müller style reconstructions) use a metric on pure states plus symmetry assumptions to obtain an invariant inner product, but they do not literally use the kernel 
K
(
x
,
y
;
z
)
=
1
−
1
2
[
D
(
x
,
y
)
+
D
(
x
,
z
)
−
D
(
y
,
z
)
]
K(x,y;z)=1− 
2
1
 [D(x,y)+D(x,z)−D(y,z)] built only from pairwise distances with 
D
(
x
,
y
)
=
1
D(x,y)=1 for “pairwise perfectly distinguishable” states, because those conditions would make this expression constant and trivial when all three are perfectly distinguishable. As you wrote it, if 
D
(
x
,
y
)
=
D
(
x
,
z
)
=
D
(
y
,
z
)
=
1
D(x,y)=D(x,z)=D(y,z)=1, then 
K
(
x
,
y
;
z
)
=
1
−
1
2
(
1
+
1
−
1
)
=
1
2
K(x,y;z)=1− 
2
1
 (1+1−1)= 
2
1
 , independent of the detailed geometry, so you cannot get a non‑degenerate inner product kernel from that formula alone.​

In Hardy‑type and MM‑type reconstructions, the usual route is:

Use continuous reversibility to make the pure states the homogeneous space of a compact Lie group with an invariant scalar product.

Use the metric structure to identify this scalar product (e.g., by putting the state space into Euclidean form), then invoke standard results that such homogeneous convex bodies must be unit balls in some inner product space.​

Your Lemma 3.1 currently asserts that “
K
K satisfies the axioms of an abstract inner product kernel” and that the polarization identity holds “by construction,” but no actual positive‑definiteness or polarization checks are written and, with the given definition, positive‑definiteness is not obvious. To make this rigorous you either need to (a) correct the kernel definition so that it is demonstrably of Schoenberg/positive‑definite type (as in standard distance‑kernel constructions), or (b) align explicitly with the convex‑state‑space plus group‑invariance route used in Masanes–Müller and similar works and drop the specific Hardy kernel formula.​

The real‑to‑complex “complexification” step via Halmos is mathematically correct as a construction once you already have a real inner product space, but in the reconstruction literature the allowed fields are constrained by locality/tomography and composition arguments, not simply by choosing to complexify. Your Part (d) sensibly appeals to the same field‑elimination logic as Masanes–Müller, but then you should clearly indicate that you are importing their structural result rather than deriving it just from your kernel.​

Mapping of LRT axioms to Masanes–Müller axioms
The mapping A3a+A3b→MM1 (continuous reversibility) and A3c→MM2 (tomographic locality) is structurally in line with Masanes–Müller’s use of “Continuous Reversibility” and “Tomographic Locality.” Likewise, the existence of pure states and qubit subspaces (MM3, MM4) from the richness of distinguishable configurations is conceptually reasonable, but the step “any binary distinction = qubit” is stronger than what is proven in the standard GPT reconstructions. Masanes–Müller require explicit assumptions about the existence and structure of a “gbit” and then show that its state space must be a Euclidean ball, not just a Boolean two‑valued variable. To be fully rigorous, you would need either:​

An explicit argument that every system with two distinguishable states has a 2‑dimensional, ball‑like convex state space with the right symmetry group, or

An explicit citation to an existing result that Boolean two‑outcome structure plus continuous reversibility and your other axioms force the Bloch‑ball form.​

Your use of Lee–Selby (2016) to derive MM5 (entanglement connectivity) from purification uniqueness and local tomography is consistent with current work that shows purification‑based constraints plus local structure fix the bipartite entanglement structure, but you should check the exact hypotheses in de la Torre et al. and Lee–Selby to ensure you match them (e.g., causality, convexity, and specific assumptions about effects and transformations are usually included).​

Field‑elimination and examples (real, quaternionic, super‑quantum)
The claims that real‑Hilbert‑space quantum theory fails local tomography and that quaternionic quantum theory fails associativity of tensor products for three or more subsystems are standard and correctly attributed. There is a subtler point, however:​

Real quantum theory as normally formulated can be made tomographically local if one allows suitable global operations, but there exist operational scenarios (e.g., certain network/Bell‑type configurations) where complex and real theories differ and only the complex one is compatible with observed correlations. Renou et al. (2021) explicitly show that complex quantum theory is experimentally singled out over real quantum theory by multipartite correlations, which you correctly allude to; this strengthens your overall conclusion but shifts the “local tomography failure” argument into “network tomography / correlation structure” rather than simple bipartite local tomography.​

The discussion of super‑Tsirelson GPTs and communication complexity collapse via PR‑box style correlations faithfully reflects the usual arguments that any theory that permits stronger‑than‑quantum nonsignaling correlations leads to implausible information‑processing consequences and instability under composition. That use of van Dam and follow‑up work is mathematically fine as a stability‑type criterion, with the caveat that the exact route from “super‑Tsirelson” to “signaling under composition” depends on specific closure assumptions.​

Internal consistency and minor corrections
A few internal mathematical consistency issues to fix:

Ensure one consistent definition of 
D
D in terms of 
∣
⟨
s
1
∣
s
2
⟩
∣
∣⟨s 
1
 ∣s 
2
 ⟩∣ is used everywhere; the “Bloch sphere” subsection uses the square‑root functional form, while Theorem 3.2 states a linear one, and the “angles” definitions mix a squared sine with those.​

If you intend the Bloch‑sphere metric to be the Fubini–Study metric, then 
D
D should be proportional to 
sin
⁡
(
θ
/
2
)
sin(θ/2), and you should clearly distinguish between trace distance, Fubini–Study distance, and your abstract 
D
D; they are related but not identical.​

The Hardy kernel expression and its claimed properties need either a corrected derivation (e.g., using a standard embedding from metric spaces into Hilbert spaces and showing 
K
K is positive definite) or a replacement by the more standard convex‑geometry/group‑invariance argument used in contemporary reconstructions.​

If you adjust those points—especially the global definition of 
D
D versus 
∣
⟨
⋅
∣
⋅
⟩
∣
∣⟨⋅∣⋅⟩∣ and the Hardy‑kernel claim—your technical foundations will line up much more closely with the established reconstruction theorems while preserving your LRT‑specific metaphysical framing.

Grade?
Overall: the program is strong conceptually but needs some technical tightening; roughly a B+ as a math foundations draft, with a path to A– once the key consistency issues are fixed.​

Major strengths
The operational definition of 
D
D as a supremum of total variation distances is standard and correctly yields a metric on the operational state space, matching GPT and reconstruction practice.​

The mapping from LRT axioms to Masanes–Müller–style premises (continuity, reversible dynamics, local tomography, etc.) is broadly aligned with the reconstruction literature and uses appropriate external results (Masanes–Müller, de la Torre et al., Lee–Selby).​

The field‑elimination and stability arguments for ruling out classical, real, quaternionic, and super‑Tsirelson alternatives track known results (Earnshaw, Wootters/Stueckelberg, Adler, van Dam/Brassard et al., Renou et al.).​

Key issues to fix for “A” level
Global consistency of 
D
D: You currently use both 
D
=
1
−
∣
⟨
s
1
∣
s
2
⟩
∣
2
D=1−∣⟨s 
1
 ∣s 
2
 ⟩∣ 
2
  and a Bloch‑sphere picture where 
D
D behaves like the trace distance 
1
−
∣
⟨
ψ
1
∣
ψ
2
⟩
∣
2
1−∣⟨ψ 
1
 ∣ψ 
2
 ⟩∣ 
2
 
 ; you need to choose one functional relationship and make all angle and cosine‑law formulas consistent with it.​

Hardy kernel rigor: The specific kernel 
K
(
x
,
y
;
z
)
K(x,y;z) as written is not obviously positive‑definite and becomes trivial when all three states are pairwise perfectly distinguishable, so the claim that it “satisfies the axioms of an abstract inner product kernel” needs a corrected derivation or a replacement by the standard convex‑geometry/group‑invariance route used in reconstruction papers.​

“Any binary distinction ⇒ qubit” step: The move from “two distinguishable states” to “qubit subsystem with Bloch‑ball geometry” is stronger than what is proven in Masanes–Müller; this step needs either a precise GPT‑style argument or an explicit citation to a result that enforces Bloch‑ball structure from your axioms.​

If you resolve those three points, especially the definition of 
D
D and the Hardy‑kernel section, the draft moves into A– territory as a technical foundations companion to the main LRT paper.

What would take it to A+?
To push this into A+ territory, three things would help: one technical clean‑up, one rigorous replacement, and one “flagship” theorem.

1. Make the metric–inner‑product link fully tight
Fix a single global relation between 
D
D and 
∣
⟨
s
1
∣
s
2
⟩
∣
∣⟨s 
1
 ∣s 
2
 ⟩∣ (e.g., trace distance for pure states) and propagate it consistently through all angle, cosine‑law, and Bloch‑sphere formulas.​

Prove a precise theorem of the form: “Given axioms A1–A3, the pure state space of any finite‑capacity system is a compact homogeneous Riemannian manifold whose unique invariant metric is induced by a Hilbert‑space inner product, and 
D
D coincides (up to a fixed monotone function) with the Fubini–Study/trace metric.” This mirrors the homogeneous‑ball derivation in Masanes–Müller and related work but in your 3FLL/IIS language.​

2. Replace the Hardy‑kernel sketch with a standard reconstruction‑grade argument
Drop or drastically revise the specific “Hardy kernel” formula and instead follow the modern GPT reconstruction pattern:

Define your convex state spaces and reversible group.

Use Continuous Reversibility to show each single‑system state space is the unit ball of an invariant inner product.​

Use the Subspace Axiom/“information unit” style assumptions to show the generalized bit has Bloch‑ball geometry with 
d
=
3
d=3.​

Present one clean theorem: “Under LRT axioms, every 2‑capacity system’s state space is affinely isomorphic to the Bloch ball,” with a proof that is recognizably parallel to Masanes–Müller or de la Torre–Masanes–Short–Müller, just with your metaphysical primitives.​

If you really want a kernel, prove it is positive‑definite using standard distance‑embedding results, not just by assertion.

3. Elevate the uniqueness/stability result to a sharp reconstruction theorem
Right now Theorem 5.7 is conditional and somewhat qualitative. For A+ level:

State a single “LRT Reconstruction Theorem” along the lines of:
“Any finite‑dimensional GPT satisfying A1–A5 is operationally equivalent to complex quantum theory (C
∗
∗
 ‑algebra of matrices with the usual Born rule), and no strictly stronger/no‑signaling GPT extension satisfies A1–A5 plus composition closure.”​

Prove it by explicitly chaining:

LRT axioms ⇒ Continuous Reversibility + Tomographic Locality + Existence of Information Unit (or equivalent) + No Simultaneous Encoding analogue, citing Masanes–Müller style theorems for each logical step.​

Those premises ⇒ QT or classical theory; then use your stability/elimination sections (Earnshaw, real vs complex, quaternionic associativity, PR‑box/communication‑complexity) as lemmas in a compact, formally structured uniqueness proof.​

If you can sharpen the “stability” criteria into explicit axioms and show that only complex QT satisfies them, that gives the paper a theorem at the same conceptual level as “Existence of an information unit as a postulate of quantum theory.”​

4. Structural polish
Two more modest but high‑impact improvements:

Isolate all imports from existing reconstructions in a single “External Theorems” section with exact hypotheses and then, in the main proofs, explicitly say “by Theorem X of Masanes–Müller / de la Torre et al.” rather than “following Hardy.” This makes the logical dependencies maximally transparent.​

Add one or two fully worked finite‑dimensional examples where you take a simple LRT axiom‑satisfying system and explicitly construct the full complex Hilbert model and Born rule, in parallel with an alternative (real/quaternionic) model that fails one of your stability conditions.​

With a rigorized single‑system reconstruction, a clean MM‑style chain to QT, and a formally stated, stability‑based uniqueness theorem, the draft would not just support LRT philosophically; it would stand as a first‑class reconstruction paper in its own right—that is A+ territory.

Do you feel I have the “bones” to get to A+?
Yes. The core structural pieces you already have are exactly the ones that successful reconstruction papers build on, so the “bones” are there.​

You are working in the same overall framework as Hardy, Masanes–Müller, de la Torre et al., and more recent reconstruction work: convex/operational state spaces, continuous reversible dynamics, local tomography, and an information‑theoretic or logical reading of the axioms.​

You already have a clear route from your LRT axioms to a Masanes–Müller–style axiom set and then to complex QT, plus a recognizably standard field‑elimination and “no stronger‑than‑QT” stability story.​

The remaining work is mostly sharpening: tightening the metric–inner‑product link, replacing one or two heuristic steps with reconstruction‑grade arguments, and packaging the uniqueness/stability result as a single clean theorem.​

Given those ingredients, turning this into A+ is a matter of polish and rigor, not of rethinking the foundational picture.

Related

Which sections most need improvement to reach A plus

Can you list exact grading criteria for A plus

What specific proofs require more rigor or detail next draft would add





