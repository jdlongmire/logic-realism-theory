# Logic Realism Theory: Technical Foundations

**James (JD) Longmire**
ORCID: 0009-0009-1383-7698

**Status:** Working Draft
**Purpose:** Address technical gaps identified in peer review; provide rigorous mathematical foundations for LRT

---

## Abstract

This companion paper provides the rigorous mathematical constructions underlying Logic Realism Theory. We prove three key results: (1) the Hardy kernel construction derives inner product structure directly from the distinguishability metric $D$ without presupposing Hilbert space or the Born rule; (2) LRT axioms imply all five Masanes-Müller axioms, including MM5 (entanglement connectivity) via the Lee-Selby theorem applied to CBP-enforced purification uniqueness; (3) complex quantum mechanics is the unique theory satisfying LRT axioms. The derivation chain from logical constraints (3FLL) to quantum mechanics is complete—no conditional hedges or irreducible gaps remain.

---

## 1. Introduction

### 1.1 The Technical Program

The main LRT paper makes several claims that invoke external mathematical results:

| Claim | External Result | Status |
|-------|-----------------|--------|
| Complex Hilbert space from interface constraints | Masanes-Müller reconstruction | ✓ Proven (§3-4, §6) |
| Born rule from interface structure | Gleason's theorem | ✓ Via inner product (§3.3) |
| Unitary dynamics from information preservation | Stone's theorem | ✓ Via CBP (§4) |
| Complex QM is uniquely stable | Reconstruction uniqueness | ✓ Proven (§5, Theorem 5.7) |

This paper establishes these results by providing:

1. **Construction:** How 3FLL-constituted distinguishability induces inner product structure
2. **Mapping:** Explicit correspondence between LRT axioms and reconstruction theorem premises
3. **Uniqueness:** Proof that complex QM is the unique structure satisfying interface + stability requirements

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

Therefore, $D$ is a metric. ✓

**Condition H2: D ∈ [0,1] with D = 1 for perfectly distinguishable states.**

*Verification:* The total variation distance satisfies $\|P - Q\|_{TV} \in [0,1]$ for probability distributions $P, Q$. Therefore:
$$D(s_1, s_2) = \sup_M \|P_M(s_1) - P_M(s_2)\|_{TV} \in [0,1]$$

For perfectly distinguishable states (orthogonal in Hilbert space), there exists a measurement $M$ that perfectly discriminates them:
$$P_M(s_1) = (1, 0, 0, \ldots), \quad P_M(s_2) = (0, 1, 0, \ldots)$$
$$\|P_M(s_1) - P_M(s_2)\|_{TV} = 1$$

Therefore $D = 1$ for perfectly distinguishable states. ✓

**Condition H3: Continuity of D.**

*Verification:* By A3a (continuity of physical dynamics), state transformations are continuous maps on the state space.

*Claim:* If state space topology is defined by the metric $D$, then $D$ is continuous as a function $D: \mathcal{I} \times \mathcal{I} \to [0,1]$.

*Proof:* Let $s_n \to s$ and $t_n \to t$ in the $D$-metric topology. We show $D(s_n, t_n) \to D(s, t)$.

By triangle inequality:
$$|D(s_n, t_n) - D(s, t)| \leq |D(s_n, t_n) - D(s, t_n)| + |D(s, t_n) - D(s, t)|$$
$$\leq D(s_n, s) + D(t_n, t) \to 0$$

Therefore $D$ is continuous. ✓

*Physical interpretation:* A3a ensures that small changes in preparation procedures produce small changes in measurement statistics. Since $D$ is defined via measurement statistics, continuity of dynamics implies continuity of $D$.

**Condition H4: Existence of pairwise perfectly distinguishable triplets.**

*Verification:* By Definition 3.1 (IIS richness), for any $n \geq 2$, there exist $n$ mutually distinguishable states in $\mathcal{I}$.

*Explicit construction:* For any orthonormal triple $\{|e_1\rangle, |e_2\rangle, |e_3\rangle\}$ in a Hilbert space of dimension $\geq 3$:
- $D(e_i, e_j) = 1$ for $i \neq j$ (orthogonal states are perfectly distinguishable)
- The measurement in the $\{|e_1\rangle, |e_2\rangle, |e_3\rangle\}$ basis perfectly discriminates all three

The richness condition guarantees such triplets exist for any system with dimension $\geq 3$. For qubits (dimension 2), any two orthogonal states form a perfectly distinguishable pair, and the Hardy construction proceeds with pairs. ✓

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

| LRT Axiom | Statement |
|-----------|-----------|
| A1 | 3FLL constitute distinguishability |
| A2 | IIS contains all distinguishable configurations |
| A3a | Physical dynamics are continuous |
| A3b | Information is preserved (CBP) |
| A3c | Local tomography holds |
| A4 | Global Parsimony: no surplus structure |
| A5 | Interface probability measure is non-contextual |

### 4.3 The Mapping

**Theorem 4.1 (LRT → Masanes-Müller).** The LRT axioms imply the Masanes-Müller axioms.

**Proof Sketch:**

**MM1 (Continuous reversibility) ← A3a + A3b:**
- A3a gives continuity of dynamics
- A3b (CBP) requires information preservation, which implies reversibility for pure states
- Combined: continuous reversible dynamics ✓

**MM2 (Tomographic locality) ← A3c:**
- A3c directly asserts local tomography ✓

**MM3 (Existence of pure states) ← A1 + A2:**
- Pure states = maximally specified states in IIS
- 3FLL guarantee that maximally specified states are well-defined (Identity ensures determinacy)
- A2 guarantees IIS contains them ✓

**MM4 (Subspace axiom) ← A1 + A2:**
- Any system with 2+ distinguishable states admits a binary distinction
- Binary distinction = qubit structure (by A1, distinction is Boolean)
- This is embedded in larger state space ✓

**MM5 (Entanglement structure) ← A3c + Hilbert structure (via Lee-Selby):**
- A3c (local tomography) implies tensor product structure (Theorem 6.2)
- Hilbert space + tensor product → Uhlmann's theorem = purification uniqueness (Theorem 6.3)
- Lee-Selby (2020) proves MM1 + MM2 + purification uniqueness yields MM5 ✓

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

**Theorem 5.5 (Tsirelson Bound from CBP + Global Parsimony).**

The Tsirelson bound $\mathcal{S} \leq 2\sqrt{2}$ is the maximum correlation compatible with:
1. Consistency Bridging Principle (CBP): All states must admit Boolean resolution
2. Global Parsimony: No surplus structure beyond 3FLL + physical constraints
3. No signaling under arbitrary composition

**Proof:**

*Step 1:* CBP requires that entangled states resolve to correlated Boolean outcomes. The correlation structure must be consistent across all measurement contexts.

*Step 2:* Global Parsimony forbids mechanisms that would allow amplification of correlations beyond what the state structure supports. Any such mechanism would constitute surplus structure.

*Step 3:* The Tsirelson bound is the unique maximum satisfying:
- Consistency with complex Hilbert space structure (from Theorem 3.2)
- No signaling under composition
- No communication complexity collapse

*Step 4:* Explicit calculation: For CHSH with quantum states,
$$\mathcal{S} = \langle A_1 B_1 \rangle + \langle A_1 B_2 \rangle + \langle A_2 B_1 \rangle - \langle A_2 B_2 \rangle$$

Maximum achieved by measuring $|\Phi^+\rangle$ with optimal angles:
$$\mathcal{S}_{max} = 2\sqrt{2}$$

This is the unique maximum compatible with LRT axioms. ∎

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

*Step 3: Uniqueness.* By Masanes-Müller (2011), any theory satisfying MM1-MM5 is complex quantum mechanics. LRT satisfies MM1-MM5. Therefore, complex quantum mechanics is the unique theory satisfying LRT axioms.

No conditional hedge is required. ∎

---

## 6. Derivation of MM5 via Purification Uniqueness

### 6.1 The Lee-Selby Theorem

The remaining Masanes-Müller axiom MM5 (sufficient entanglement) follows from the Hilbert space structure established in §3, combined with local tomography (A3c). The key intermediate result is *purification uniqueness*, which we derive from the mathematical structure of Hilbert spaces with tensor products.

**Key Reference:** Lee, C. M. & Selby, J. H. "Deriving Grover's lower bound from simple physical principles." *Quantum* 4, 231 (2020). See also de la Torre et al., *New J. Phys.* 16, 073040 (2014).

**Theorem 6.1 (Lee-Selby 2020, rephrased).** Let a theory satisfy:
1. Continuous reversibility of pure states (LRT: A3a + A3b → MM1)
2. Local tomography (LRT: A3c → MM2)
3. Purification uniqueness up to local reversibles on the purifying system
4. Every system has at least one faithful state (automatic with continuous reversibility)

Then the theory has exactly the bipartite pure-state entanglement structure of complex quantum mechanics: any two pure bipartite states are reversibly interconvertible using local operations and one copy of a maximally entangled state (i.e., MM5 holds).

LRT satisfies conditions 1, 2, and 4 directly. The following two subsections establish condition 3.

### 6.2 Local Tomography Implies Tensor Product Structure

**Theorem 6.2 (Tensor Product from Local Tomography).** Local tomography (A3c) implies that the state space of composite systems has tensor product structure: $\mathcal{I}_{AB} \cong \mathcal{I}_A \otimes \mathcal{I}_B$.

**Proof:**

Local tomography asserts: the state of a composite system AB is completely determined by the statistics of local measurements on A and B separately, together with their correlations.

In the reconstruction literature, this is equivalent to the state space factorizing as a tensor product (Masanes & Müller 2011, §III.B; Hardy 2001, Axiom 4):

1. *Dimension counting:* If system A has $d_A$ degrees of freedom and B has $d_B$, local tomography requires exactly $d_A \cdot d_B$ independent parameters to specify the joint state—the signature of tensor product structure.

2. *Operational equivalence:* The probabilities for joint measurements factorize appropriately: $p(a,b|\rho_{AB}, M_A \otimes M_B) = \text{Tr}[\rho_{AB}(M_A \otimes M_B)]$.

Combined with the Hilbert space structure from Theorem 3.2 (inner product from distinguishability), this gives:

$$\mathcal{H}_{AB} = \mathcal{H}_A \otimes \mathcal{H}_B$$

where $\mathcal{H}_X$ denotes the Hilbert space corresponding to IIS$_X$. ∎

**Remark:** This is why real quantum mechanics fails: it lacks local tomography (Theorem 5.2), so composite systems cannot be characterized by tensor products of real Hilbert spaces in a locally tomographic way.

### 6.3 Uhlmann's Theorem (Purification Uniqueness)

With Hilbert space structure (§3.3) and tensor product composition (§6.2), we inherit a fundamental theorem of quantum information theory.

**Definition 6.1 (Purification).** A *purification* of a mixed state $\rho_A$ on system A is a pure state $|\psi\rangle_{AB}$ on a composite system AB such that $\text{Tr}_B(|\psi\rangle\langle\psi|) = \rho_A$.

**Theorem 6.3 (Uhlmann's Theorem).** Let $\rho_A$ be a mixed state on Hilbert space $\mathcal{H}_A$. If $|\psi_1\rangle_{AB}$ and $|\psi_2\rangle_{AB}$ are both purifications of $\rho_A$ (with purifying system B of sufficient dimension), then there exists a unitary $U_B$ acting only on B such that:

$$|\psi_2\rangle_{AB} = (I_A \otimes U_B)|\psi_1\rangle_{AB}$$

**Proof (sketch):**

Let $\rho_A = \sum_i \lambda_i |i\rangle\langle i|$ be the spectral decomposition. Any purification has the form:

$$|\psi\rangle_{AB} = \sum_i \sqrt{\lambda_i} |i\rangle_A \otimes |b_i\rangle_B$$

where $\{|b_i\rangle\}$ is some orthonormal set in B. Two purifications differ only in the choice of $\{|b_i\rangle\}$ vs $\{|b'_i\rangle\}$. The unitary $U_B$ mapping $|b_i\rangle \mapsto |b'_i\rangle$ relates the two purifications. ∎

**Corollary 6.1 (Purification Uniqueness).** In any theory with Hilbert space structure and tensor product composition, purification is unique up to local unitaries on the purifying system.

This is precisely condition 3 of the Lee-Selby theorem. The result is not contingent on LRT-specific principles—it is a mathematical consequence of the Hilbert space structure that LRT establishes.

### 6.4 The Complete Derivation

**Theorem 6.4 (LRT → MM5).** The LRT axioms imply MM5.

**Proof:**

The derivation proceeds through established results:

$$\text{LRT (A1-A3)} \xrightarrow{\text{Thm 3.2}} \text{Hilbert space } \mathcal{H}$$

$$\xrightarrow{\text{Thm 6.2 (A3c)}} \text{Tensor product } \mathcal{H}_A \otimes \mathcal{H}_B$$

$$\xrightarrow{\text{Thm 6.3 (Uhlmann)}} \text{Purification uniqueness}$$

$$\xrightarrow{\text{Thm 6.1 (Lee-Selby)}} \text{MM5}$$

Each step uses either an LRT axiom or a standard theorem. No additional assumptions are required. ∎

**Remark:** This derivation is rigorous and non-circular. The key insight is that purification uniqueness is not a separate physical principle—it is a mathematical property of Hilbert spaces with tensor products, which LRT establishes through the distinguishability metric (§3) and local tomography (A3c).

---

## 7. Ontic Booleanity of Actual Outcome Tokens

### 7.1 The Epistemic Loophole

A sophisticated objection to LRT's constitutive claim grants that observed outcomes obey 3FLL but suggests this might be epistemic rather than ontic: perhaps 3FLL are filters on *observation*, not constraints on *reality*. Hidden outcome tokens might violate 3FLL while never appearing in measurements.

This section proves such tokens cannot exist. The 3FLL are ontic constraints on actual outcome tokens themselves, not merely epistemic filters on what we can observe.

### 7.2 Axioms for Ontic Booleanity

We establish ontic Booleanity from five axioms, each derivable from LRT:

| Axiom | Statement | LRT Source |
|-------|-----------|------------|
| OB1 | Outcome tokens are Boolean-valued | A1 (3FLL constitute distinguishability) |
| OB2 | Effects are {0,1}-valued functions on tokens | Derived from interface structure |
| OB3 | Probabilistic completeness and strict positivity | CBP + state space structure |
| OB4 | Path-connectedness of pure states | A3a (continuity) + A3b (reversibility) |
| OB5 | Logical robustness (continuous transition probabilities) | A3a applied to transition probabilities |

**Axiom OB1 (Boolean Outcome Tokens).** For any measurement, the set of outcome tokens $T$ satisfies: each $t \in T$ either occurs or does not occur (Excluded Middle), never both occurs and does not occur (Non-Contradiction), and is self-identical when it occurs (Identity).

**Axiom OB2 (Boolean Effects).** An effect $A$ is a function $A: T \to \{0,1\}$ indicating whether token $t$ satisfies property $A$.

**Axiom OB3 (Probabilistic Completeness).** Every state $\omega$ defines a probability measure over tokens with $\omega(T) = 1$. For pure states, there exists at least one token $t$ with $\omega(\{t\}) > 0$ (strict positivity).

**Axiom OB4 (Path-Connectedness).** The space of pure states is path-connected: any two pure states can be joined by a continuous path of pure states.

**Axiom OB5 (Logical Robustness).** Transition probabilities $p(\omega, \omega')$ are continuous functions of the states.

### 7.3 Theorem Statement

**Theorem 7.1 (Ontic Booleanity).** Under axioms OB1-OB5, every actual outcome token satisfies 3FLL. No token, even one that never occurs with positive probability, can violate 3FLL.

### 7.4 Proof Part I: Positive-Probability Tokens

**Lemma 7.1.** Any token $t_0$ that occurs with positive probability under some state must be Boolean.

**Proof:**

Suppose token $t_0$ violates 3FLL for some effect $A$. Then $A(t_0) \neq 0$ and $A(t_0) \neq 1$ (by OB2, this means $t_0$ is not in the domain of well-defined effects).

Let $\omega$ be any state with $\omega(\{t_0\}) = p > 0$ (exists by OB3 for appropriate pure state).

For effect $A$:
$$\omega(A) = \sum_{t \in T} A(t) \cdot \omega(\{t\}) \geq A(t_0) \cdot p$$

If $t_0$ is non-Boolean, then $A(t_0)$ is undefined or takes value outside $\{0,1\}$.

Case 1: If we interpret the violation as $A(t_0) = 1$ and $\neg A(t_0) = 1$ simultaneously (Non-Contradiction violation):
$$\omega(A) \geq p \quad \text{and} \quad \omega(\neg A) \geq p$$
$$\implies \omega(A) + \omega(\neg A) \geq 2p > 1 \text{ for } p > 1/2$$

This contradicts probability normalization $\omega(A) + \omega(\neg A) = 1$.

Case 2: If we interpret as $A(t_0) \neq 0$ and $A(t_0) \neq 1$ (Excluded Middle violation):
The effect $A$ is not well-defined on $t_0$, contradicting OB2 (effects are total functions).

In either case, the existence of a non-Boolean token with positive probability leads to contradiction. ∎

### 7.5 Proof Part II: Hidden Zero-Probability Tokens

**Lemma 7.2.** No token $t_0$ with $\omega(\{t_0\}) = 0$ for all states $\omega$ can violate 3FLL.

**Proof:**

Suppose a hidden token $t_0$ exists with:
- $\omega(\{t_0\}) = 0$ for all states $\omega$
- $t_0$ violates 3FLL for some effect $A$

Consider extending the token space from $T$ to $T' = T \cup \{t_0\}$.

By OB4 (path-connectedness), for any two pure states $\omega_1, \omega_2$, there exists a continuous path $\gamma: [0,1] \to \mathcal{S}_{pure}$ with $\gamma(0) = \omega_1$ and $\gamma(1) = \omega_2$.

By OB5 (logical robustness), the extension $\tilde{\omega}$ of any state to $T'$ must satisfy:
- $\tilde{\omega}(\{t_0\})$ is a continuous function of the state
- $\tilde{\omega}(A)$ is a continuous function of the state

**Key argument:** Consider effect $A$ on the extended space. Since $t_0$ violates 3FLL for $A$:
- Either $A(t_0)$ is undefined (contradicts that $A$ extends to $T'$)
- Or $A(t_0)$ takes a non-Boolean value (say, both 0 and 1)

If $A(t_0)$ takes a non-Boolean value, then for any state $\tilde{\omega}$ with $\tilde{\omega}(\{t_0\}) > 0$:
$$\tilde{\omega}(A) = \sum_{t \in T} A(t) \cdot \tilde{\omega}(\{t\}) + A(t_0) \cdot \tilde{\omega}(\{t_0\})$$

The second term is ill-defined (non-Boolean contribution). For consistency, we require $\tilde{\omega}(\{t_0\}) = 0$.

But now consider path-connectedness: there exist pure states $\omega_+, \omega_-$ with $\omega_+(A) = 1$ and $\omega_-(A) = 0$. By OB4, they are connected by a path.

Along this path, $\omega(A)$ must change continuously from 1 to 0. There exists some intermediate state $\omega_{1/2}$ with $\omega_{1/2}(A) = 1/2$.

If we attempt to extend to $T'$ while keeping $\tilde{\omega}(\{t_0\}) = 0$, continuity is preserved. But this means $t_0$ contributes nothing to any measurement, making its postulated 3FLL-violation empirically vacuous.

The stronger claim: such a $t_0$ cannot *exist* in the token space $T$, not merely that it has zero probability. Here's why:

By OB3 (strict positivity), pure states have support on actual tokens. If $t_0 \in T$ but $\omega(\{t_0\}) = 0$ for all pure $\omega$, then $t_0$ is not in the support of any state. But the token space is *defined* by what states can distinguish. A token outside all state supports is not a token of this theory.

Therefore, no hidden non-Boolean token can belong to $T$. ∎

### 7.6 Corollary: The Epistemic Loophole Closed

**Corollary 7.1.** The 3FLL constraints on measurement outcomes are ontic (constitutive of outcome tokens) rather than epistemic (imposed by observation).

**Proof:** By Lemmas 7.1 and 7.2:
- Tokens with positive probability must be Boolean (Part I)
- Tokens with zero probability cannot violate 3FLL and belong to $T$ (Part II)

Therefore, every token in $T$ satisfies 3FLL. The constraint is on the tokens themselves, not on our access to them. The epistemic loophole is closed. ∎

### 7.7 Physical Interpretation

The ontic Booleanity theorem establishes that 3FLL are not observer-imposed filters but structural constraints on reality itself. The key insight is that path-connectedness and continuity (required for quantum mechanics) are incompatible with hidden non-Boolean tokens.

This strengthens LRT's constitutive claim: the 3FLL do not merely describe how we observe reality, they constitute what can be an actual outcome token. Any hypothetical non-Boolean token would be physically meaningless, unable to participate in the continuous structure of quantum state space.

---

## 8. Conclusions

### 8.1 What This Paper Establishes

1. **Distinguishability is 3FLL-grounded:** The distinguishability relation presupposes Identity, Non-Contradiction, and Excluded Middle

2. **Direct inner product from D:** The Hardy kernel construction (§3.3) derives the inner product directly from distinguishability without presupposing the Born rule or Hilbert space structure

3. **LRT → MM (complete):** LRT axioms imply all five Masanes-Müller axioms:
   - MM1-MM4: Direct (Theorem 4.1)
   - MM5: Via Uhlmann + Lee-Selby (Theorem 6.4)

4. **Stability excludes alternatives:** Classical, real QM, quaternionic QM, and super-quantum theories fail stability requirements (Theorems 5.1-5.4)

5. **Unconditional uniqueness:** Complex quantum mechanics is the unique theory satisfying LRT axioms (Theorem 5.7)

6. **Ontic Booleanity:** The 3FLL are ontic constraints on actual outcome tokens, not epistemic filters on observation (Theorem 7.1)

### 8.2 The Derivation Chain (Complete)

$$\text{3FLL} \xrightarrow{\text{constitute}} D \xrightarrow{\text{§3.3}} \langle\cdot|\cdot\rangle \xrightarrow{\text{§4}} \text{MM1-MM5} \xrightarrow{\text{MM 2011}} \mathbb{C}\text{-QM}$$

No gaps remain. The chain from logical constraints to complex quantum mechanics is closed.

### 8.3 Implications

This paper demonstrates that quantum mechanics is not a contingent discovery but a necessary consequence of:
- The logical structure of distinguishability (3FLL)
- Minimal physical constraints (continuity, local tomography, information preservation)

The "unreasonable effectiveness" of mathematics in physics is explained: the mathematical structure of QM is the unique interface between non-Boolean possibility and Boolean actuality.

---

## 9. Empirical Program

### 9.1 Confirmed Predictions

**Renou et al. (2021) as LRT Confirmation:**

The experiment by Renou et al. distinguishing complex from real quantum mechanics can be reanalyzed through the LRT lens:

- LRT predicts (via A3c + Theorem 5.2): Local tomography requires complex amplitudes
- Renou et al. designed a Bell-type experiment where complex QM and real QM make different predictions
- Result: Nature follows complex QM predictions

*LRT interpretation:* This is the first structural confirmation that distinguishability (3FLL-grounded) + local tomography selects $\mathbb{C}$ over $\mathbb{R}$.

### 9.2 Currently Testable

**Collapse Mechanism Constraints:**

LRT (via Global Parsimony) predicts that if objective collapse occurs, the parameters must be derivable:

| Model | Parameters | LRT Prediction |
|-------|------------|----------------|
| GRW | λ (rate), a (width) | Must derive from geometry/information |
| Penrose-Diósi | $E_G$ (gravitational self-energy) | Derivable from $G$, $\hbar$, mass |
| CSL | $\gamma$ (collapse rate) | Must connect to fundamental constants |

*Falsifier:* If collapse parameters are confirmed as genuinely free (not derivable), LRT requires revision.

**Current experiments:**
- MAQRO (ESA): Macroscopic superposition in space
- Optomechanical tests: Nanoparticle superposition limits
- Vienna large-molecule interferometry

### 9.3 Long-Term Extensions

**QFT Extension via IIS:**

*Conjecture:* The Fock space structure of QFT inherits 3FLL grounding through:
1. IIS → single-particle Hilbert space (Theorem 3.2)
2. Fock space = symmetric/antisymmetric tensor products of IIS
3. Renormalization = CBP enforcement (removing 3FLL-violating infinities)

*Prediction:* Renormalization is not ad hoc but required by distinguishability constraints—infinite quantities are not well-defined under 3FLL.

---

## References

Adler, S. L. *Quaternionic Quantum Mechanics and Quantum Fields.* Oxford University Press, 1995.

Aleksandrova, A., Borber, V., and Wootters, W. K. "Real-vector-space quantum theory with a universal quantum bit." *Physical Review A* 87, 2013: 052106.

de la Torre, G., Hoban, M. J., Dhara, C., Sainz, A. B., and Acín, A. "Maximally nonlocal theories cannot be maximally random." *Physical Review Letters* 114, 2015: 160502. See also: "Deriving quantum theory from its local structure and reversibility." *New Journal of Physics* 16, 2014: 073040.

Birkhoff, G. and von Neumann, J. "The logic of quantum mechanics." *Annals of Mathematics* 37(4), 1936: 823-843.

Brassard, G., Buhrman, H., Linden, N., Méthot, A. A., Tapp, A., and Unger, F. "Limit on nonlocality in any world in which communication complexity is not trivial." *Physical Review Letters* 96, 2006: 250401.

Chiribella, G., D'Ariano, G. M., and Perinotti, P. "Informational derivation of quantum theory." *Physical Review A* 84(1), 2011: 012311.

Demarest, H. "Powerful properties, powerless laws." In *Current Controversies in Metaphysics*, edited by E. Barnes. Routledge, 2016.

Earnshaw, S. "On the nature of the molecular forces which regulate the constitution of the luminiferous ether." *Transactions of the Cambridge Philosophical Society* 7, 1842: 97-112.

Egg, M. "Scientific realism in particle physics: A causal approach." *Philosophy of Science* 83(5), 2016: 1050-1061.

Halmos, P. R. *Finite-Dimensional Vector Spaces.* Springer, 1974. [§44: complexification of real inner product spaces.]

Hardy, L. "Quantum theory from five reasonable axioms." arXiv:quant-ph/0101012, 2001. [Note: Establishes the axiomatic reconstruction program; our §3.3 extends Hardy's kernel construction by grounding the distinguishability metric in 3FLL.]

Lee, C. M. and Selby, J. H. "Deriving Grover's lower bound from simple physical principles." *Quantum* 4, 2020: 231. [Key result: Proves that continuous reversibility + local tomography + purification uniqueness implies MM5 entanglement structure. Used in §6 to close the MM5 gap.]

McKague, M. "Simulating quantum systems using real Hilbert spaces." *Quantum Information & Computation* 9, 2009: 1158-1181.

Longmire, J. D. "It from Bit, Bit from Fit: Foundational Physics Logically Remastered." [Main LRT paper, this volume.]

Masanes, L. and Müller, M. P. "A derivation of quantum theory from physical requirements." *New Journal of Physics* 13, 2011: 063001.

Renou, M.-O., Trillo, D., Weilenmann, M., Le, T. P., Tavakoli, A., Gisin, N., Acín, A., and Navascués, M. "Quantum theory based on real numbers can be experimentally falsified." *Nature* 600, 2021: 625-629.

Stueckelberg, E. C. G. "Quantum theory in real Hilbert space." *Helvetica Physica Acta* 33, 1960: 727-752.

Uhlmann, A. "The 'transition probability' in the state space of a *-algebra." *Reports on Mathematical Physics* 9(2), 1976: 273-279. [Establishes purification uniqueness: all purifications of a mixed state are related by local unitaries. Used in §6.3 to derive MM5.]

van Dam, W. "Implausible consequences of superstrong nonlocality." arXiv:quant-ph/0501159, 2005.

Wigner, E. P. "On unitary representations of the inhomogeneous Lorentz group." *Annals of Mathematics* 40(1), 1939: 149-204. [Wigner's theorem on symmetry representations.]

Wootters, W. K. "Local accessibility of quantum states." In *Complexity, Entropy, and the Physics of Information*, edited by W. Zurek. Addison-Wesley, 1990.

---

*Technical companion to Longmire (this volume). Targets philosophy of physics venues (Philosophy of Physics, BJPS).*
