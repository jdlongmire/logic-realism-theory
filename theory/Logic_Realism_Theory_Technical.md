# Logic Realism Theory: Technical Foundations

**James (JD) Longmire**
ORCID: 0009-0009-1383-7698

**Status:** Working Draft
**Purpose:** Address technical gaps identified in peer review; provide rigorous mathematical foundations for LRT

---

## Abstract

This companion paper provides the rigorous mathematical constructions underlying Logic Realism Theory. Where the main paper (*It from Bit, Bit from Fit*) presents the philosophical framework and its compatibility with quantum mechanics, this paper proves the formal results: that 3FLL-constituted distinguishability induces inner product structure, that LRT axioms satisfy reconstruction theorem premises, and that complex quantum mechanics is the unique stable interface structure.

---

## 1. Introduction

### 1.1 The Technical Program

The main LRT paper makes several claims that invoke external mathematical results:

| Claim | External Result | Gap |
|-------|-----------------|-----|
| Complex Hilbert space from interface constraints | Masanes-Müller reconstruction | No proof LRT axioms satisfy premises |
| Born rule from interface structure | Gleason's theorem | Assumed non-contextuality grounding |
| Unitary dynamics from information preservation | Stone's theorem | Assumed continuity grounding |
| Complex QM is uniquely stable | Reconstruction uniqueness | No independent proof |

This paper fills these gaps by providing:

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

### 3.3 The Distinguishability-Angle Correspondence

**Lemma 3.1 (Cosine Theorem on Distinguishable Triplets).** For any three states $s_1, s_2, s_3 \in \mathcal{I}$ with pairwise distinguishabilities $D_{12} = D(s_1, s_2)$, $D_{23} = D(s_2, s_3)$, $D_{13} = D(s_1, s_3)$, there exists a unique angle $\theta_{12} \in [0, \pi]$ such that:

$$D_{12} = \sin^2(\theta_{12}/2)$$

and the triplet satisfies the spherical law of cosines:

$$\cos(\theta_{13}) = \cos(\theta_{12})\cos(\theta_{23}) + \sin(\theta_{12})\sin(\theta_{23})\cos(\phi)$$

for some dihedral angle $\phi$.

**Proof:**
1. The distinguishability $D \in [0,1]$ with $D=0$ for identical states and $D=1$ for perfectly distinguishable states.
2. Define $\theta = 2\arcsin(\sqrt{D})$, giving the angle on the Bloch sphere for qubits.
3. For quantum states, $D(|\psi\rangle, |\phi\rangle) = 1 - |\langle\psi|\phi\rangle|^2$.
4. Thus $|\langle\psi|\phi\rangle|^2 = 1 - D = \cos^2(\theta/2)$, yielding $|\langle\psi|\phi\rangle| = \cos(\theta/2)$.
5. The spherical law follows from embedding in projective Hilbert space. ∎

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

### 3.4 Operational Primitives from Distinguishability

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

**MM5 (Entanglement structure) ← A3b + A3c:**
- A3b (information preservation) + A3c (local tomography) constrain bipartite structure
- **Gap:** This is the weakest link. Need to show these constraints imply the specific entanglement connectivity MM5 requires.

**Status:** MM1-MM4 follow from LRT axioms. MM5 requires additional work.

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

Consider a bipartite system in real QM. The state space is $\mathbb{R}^{n_A} \otimes \mathbb{R}^{n_B}$.

*Claim:* There exist distinct bipartite states $\rho_1 \neq \rho_2$ with identical local marginals.

*Construction:* Let $|+\rangle = \frac{1}{\sqrt{2}}(|0\rangle + |1\rangle)$ and $|-\rangle = \frac{1}{\sqrt{2}}(|0\rangle - |1\rangle)$.

In complex QM: $|\Phi^+\rangle = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$ and $|\Psi^+\rangle = \frac{1}{\sqrt{2}}(|01\rangle + |10\rangle)$ are locally distinguishable via phase-sensitive measurements.

In real QM: The relative phase information is absent. States that differ only by complex phases become identical. Local measurements cannot distinguish certain global states.

*Consequence:* Composite system states are not determined by local measurements + correlations. This violates MM2 (tomographic locality) and interface stability criterion 2. ∎

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

### 5.5 Uniqueness Theorem (Strengthened)

**Theorem 5.7 (Stability Uniqueness).** Complex quantum mechanics is the unique theory satisfying:
1. 3FLL-grounded distinguishability (A1)
2. Continuous reversible dynamics (A3a, A3b)
3. Local tomography (A3c)
4. Interface stability (Definition 5.2)
5. Observer stability (Definition 5.3)

**Proof:**

| Alternative | Failure Mode | Theorem |
|-------------|--------------|---------|
| Classical | No bound states | 5.1 |
| Real QM | No local tomography | 5.2 |
| Quaternionic QM | No tensor associativity | 5.3 |
| Super-quantum GPT | Signaling under composition | 5.4 |

Premises 1-3 satisfy MM1-MM4 (Theorem 4.1).
Premise 4-5 exclude all alternatives.
By exhaustion of the GPT landscape, complex QM is unique. ∎

---

## 6. The MM5 Gap

### 6.1 What MM5 Requires

MM5 states: For any two pure bipartite states of a composite system, there exists a reversible transformation (local operations on one subsystem plus access to a shared entangled state) connecting them.

### 6.2 Why This Is Hard

MM5 is specifically about entanglement structure. It's not obvious how this follows from:
- 3FLL (logical constraints)
- Local tomography (compositional constraint)
- Stability (physical constraint)

### 6.3 Possible Approaches

**Approach A: Derive from Interface Requirements**
- The interface must handle entangled states
- Entangled states must resolve to correlated Boolean outcomes
- This might constrain the entanglement structure enough to imply MM5

**Approach B: Add MM5 as Physical Axiom**
- Acknowledge MM5 as independent physical input
- Analogous to A3c (local tomography)
- Reduces the claim but maintains honesty

**Approach C: Weaken the Uniqueness Claim**
- Claim: Complex QM is the *only known* structure satisfying all requirements
- Do not claim to have proven exhaustiveness
- Let the reconstruction theorems carry the uniqueness claim

### 6.4 Adopted Resolution: Approach C

**This paper adopts Approach C.** The uniqueness claim is explicitly conditional:

> **Theorem 5.7 (Conditional Uniqueness).** Complex quantum mechanics is the unique theory satisfying LRT axioms A1-A5 *and* MM5 (entanglement connectivity).

**Interpretation:** LRT provides ontological grounding for MM1-MM4 via 3FLL-constituted distinguishability. MM5 remains irreducible physical input, analogous to local tomography (A3c). This is not a weakness but a feature: LRT identifies the *minimal* physical axioms beyond logic required for quantum mechanics.

**Future work:** Deriving MM5 from interface requirements (Approach A) would strengthen the framework but is not required for the conditional uniqueness result to hold.

---

## 7. Conclusions and Open Problems

### 7.1 What This Paper Establishes

1. **Distinguishability is 3FLL-grounded:** The distinguishability relation presupposes Identity, Non-Contradiction, and Excluded Middle
2. **Operational primitives from distinguishability:** States, effects, and transformations can be defined from distinguishability structure
3. **LRT → MM (partial):** LRT axioms imply Masanes-Müller axioms MM1-MM4
4. **Stability excludes alternatives:** Classical, real QM, quaternionic QM, and super-quantum theories fail stability requirements

### 7.2 What Remains Open

1. **MM5 gap:** Does 3FLL + stability imply MM5 (entanglement connectivity)?
2. **Direct inner product construction:** Can we construct ⟨·|·⟩ from D without invoking reconstruction theorems?
3. **Uniqueness without MM:** Is there a direct proof of complex QM uniqueness from LRT axioms?

### 7.3 Implications

If the MM5 gap cannot be closed:
- LRT provides *philosophical grounding* for reconstruction theorems
- The technical claim is: 3FLL + physical constraints → MM1-MM4 + stability → complex QM
- MM5 (or equivalent) remains irreducible physical input

This is still significant: we've reduced the axiom base and provided ontological grounding for the remaining axioms.

---

## 8. Empirical Program

### 8.1 Confirmed Predictions

**Renou et al. (2021) as LRT Confirmation:**

The experiment by Renou et al. distinguishing complex from real quantum mechanics can be reanalyzed through the LRT lens:

- LRT predicts (via A3c + Theorem 5.2): Local tomography requires complex amplitudes
- Renou et al. designed a Bell-type experiment where complex QM and real QM make different predictions
- Result: Nature follows complex QM predictions

*LRT interpretation:* This is the first structural confirmation that distinguishability (3FLL-grounded) + local tomography selects $\mathbb{C}$ over $\mathbb{R}$.

### 8.2 Currently Testable

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

### 8.3 Long-Term Extensions

**QFT Extension via IIS:**

*Conjecture:* The Fock space structure of QFT inherits 3FLL grounding through:
1. IIS → single-particle Hilbert space (Theorem 3.2)
2. Fock space = symmetric/antisymmetric tensor products of IIS
3. Renormalization = CBP enforcement (removing 3FLL-violating infinities)

*Prediction:* Renormalization is not ad hoc but required by distinguishability constraints—infinite quantities are not well-defined under 3FLL.

---

## References

Adler, S. L. *Quaternionic Quantum Mechanics and Quantum Fields.* Oxford University Press, 1995.

Birkhoff, G. and von Neumann, J. "The logic of quantum mechanics." *Annals of Mathematics* 37(4), 1936: 823-843.

Brassard, G., Buhrman, H., Linden, N., Méthot, A. A., Tapp, A., and Unger, F. "Limit on nonlocality in any world in which communication complexity is not trivial." *Physical Review Letters* 96, 2006: 250401.

Chiribella, G., D'Ariano, G. M., and Perinotti, P. "Informational derivation of quantum theory." *Physical Review A* 84(1), 2011: 012311.

Demarest, H. "Powerful properties, powerless laws." In *Current Controversies in Metaphysics*, edited by E. Barnes. Routledge, 2016.

Earnshaw, S. "On the nature of the molecular forces which regulate the constitution of the luminiferous ether." *Transactions of the Cambridge Philosophical Society* 7, 1842: 97-112.

Egg, M. "Scientific realism in particle physics: A causal approach." *Philosophy of Science* 83(5), 2016: 1050-1061.

Hardy, L. "Quantum theory from five reasonable axioms." arXiv:quant-ph/0101012, 2001. [Note: Establishes the axiomatic reconstruction program; our Theorem 3.2 extends Hardy's approach by grounding the distinguishability metric in 3FLL.]

Longmire, J. D. "It from Bit, Bit from Fit: Foundational Physics Logically Remastered." [Main LRT paper, this volume.]

Masanes, L. and Müller, M. P. "A derivation of quantum theory from physical requirements." *New Journal of Physics* 13, 2011: 063001.

Renou, M.-O., Trillo, D., Weilenmann, M., Le, T. P., Tavakoli, A., Gisin, N., Acín, A., and Navascués, M. "Quantum theory based on real numbers can be experimentally falsified." *Nature* 600, 2021: 625-629.

Stueckelberg, E. C. G. "Quantum theory in real Hilbert space." *Helvetica Physica Acta* 33, 1960: 727-752.

van Dam, W. "Implausible consequences of superstrong nonlocality." arXiv:quant-ph/0501159, 2005.

Wigner, E. P. "On unitary representations of the inhomogeneous Lorentz group." *Annals of Mathematics* 40(1), 1939: 149-204. [Wigner's theorem on symmetry representations.]

Wootters, W. K. "Local accessibility of quantum states." In *Complexity, Entropy, and the Physics of Information*, edited by W. Zurek. Addison-Wesley, 1990.

---

*Technical companion to Longmire (this volume). Targets philosophy of physics venues (Philosophy of Physics, BJPS).*
