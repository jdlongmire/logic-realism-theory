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

**Definition 2.1 (Distinguishability).** Two states $s_1, s_2 \in \mathcal{I}$ are *distinguishable*, written $s_1 \perp s_2$, if and only if there exists a measurement context $M$ such that the probability distributions over outcomes differ:

$$s_1 \perp s_2 \iff \exists M: P_M(s_1) \neq P_M(s_2)$$

**Claim:** This definition presupposes 3FLL.

**Proof:**
- *Identity:* For $P_M(s_1) \neq P_M(s_2)$ to be meaningful, $s_1$ must be self-identical ($s_1 = s_1$) and similarly for $s_2$. Without identity, there is no fact about what $s_1$ *is* that could differ from $s_2$.
- *Non-Contradiction:* The inequality requires that $P_M(s_1) = P_M(s_2)$ and $P_M(s_1) \neq P_M(s_2)$ cannot both hold. Without non-contradiction, distinguishability would be undefined.
- *Excluded Middle:* For any $s_1, s_2$, either $P_M(s_1) = P_M(s_2)$ or $P_M(s_1) \neq P_M(s_2)$. Without excluded middle, there could be state pairs for which distinguishability is undefined.

Thus 3FLL are preconditions for the distinguishability relation to be well-defined. ∎

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

**Approach:** We do not construct the inner product directly from $D$. Instead, we show that:
1. The operational primitives required by reconstruction theorems are definable from distinguishability
2. These primitives satisfy the reconstruction axioms
3. The reconstruction theorems then deliver the inner product structure

### 3.2 Operational Primitives from Distinguishability

**Definition 3.1 (States from Distinguishability).** A *state* is an equivalence class of preparation procedures under operational indistinguishability:

$$[p] = \{p' : D(p, p') = 0\}$$

The state space $\Omega$ is the set of all such equivalence classes.

**Definition 3.2 (Effects from Distinguishability).** An *effect* is a function $e: \Omega \to [0,1]$ representing the probability of a particular measurement outcome. Effects are constrained by:
- Normalization: For any state, effects sum to 1 over a complete measurement
- Consistency: Effects respect the distinguishability structure

**Definition 3.3 (Transformations from Distinguishability).** A *transformation* $T: \Omega \to \Omega$ is admissible if:
1. It maps states to states
2. It preserves the distinguishability structure: $D(Ts_1, Ts_2) \leq D(s_1, s_2)$
3. It is composable with other admissible transformations

**Claim:** These definitions provide the operational primitives required by GPT frameworks.

### 3.3 The Distinguishability Inner Product

**Theorem 3.1 (Polarization Identity).** If the state space admits a notion of "superposition" (coherent combination of states), then the distinguishability metric induces an inner product via:

$$\langle s_1 | s_2 \rangle = \frac{1}{4}\left[D(s_1 + s_2, 0)^2 - D(s_1 - s_2, 0)^2 + i(D(s_1 + is_2, 0)^2 - D(s_1 - is_2, 0)^2)\right]$$

**Note:** This construction requires:
1. A notion of state addition (superposition)
2. A notion of scalar multiplication (including $i$)
3. A reference state 0

These are not given by distinguishability alone—they emerge from the physical constraints (continuity, reversibility) that LRT adopts as axioms.

**Gap Acknowledged:** The construction above assumes structure (superposition, complex scalars) that must be justified. This is where the reconstruction theorems do the heavy lifting.

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

### 5.2 Why Alternatives Fail

**Theorem 5.1 (Classical Instability).** Classical probability theory is not physically stable.

**Proof:** In classical mechanics:
- Electrons in Coulomb potential spiral to nucleus (no stable atoms)
- No discrete energy levels (continuous spectra)
- No explanation for identical particles

These are not mere inconveniences but fundamental instabilities: classical physics cannot produce the stable structures required for observers. ∎

**Theorem 5.2 (Real QM Failure).** Real quantum mechanics (over ℝ) fails interface stability.

**Proof:** Real QM fails local tomography (Wootters, 1990). Composite system states cannot be determined from local measurements. This violates interface stability criterion 2 (compositional respect). ∎

**Theorem 5.3 (Quaternionic QM Failure).** Quaternionic quantum mechanics (over ℍ) fails interface stability.

**Proof:** Quaternionic QM fails associativity of tensor products for three or more systems. This violates compositional consistency required for interface stability. ∎

**Theorem 5.4 (Super-quantum Failure).** Generalized probabilistic theories exceeding the Tsirelson bound fail interface stability.

**Proof:** PR boxes and super-quantum correlations, while satisfying no-signaling for single uses, permit:
- Signaling under composition (van Dam, 2005)
- Communication complexity collapse (Brassard et al., 2006)

This violates interface stability criterion 3. ∎

### 5.3 Uniqueness Theorem

**Theorem 5.5 (Stability Uniqueness).** Complex quantum mechanics is the unique theory satisfying:
1. 3FLL-grounded distinguishability
2. Continuous reversible dynamics
3. Local tomography
4. Interface stability

**Proof:**
- Premises 1-3 satisfy MM1-MM4 (by Theorem 4.1)
- Masanes-Müller uniqueness: MM1-MM5 uniquely determine complex QM
- Premise 4 excludes the alternatives that Theorems 5.1-5.4 eliminate
- **Gap:** Need to show Premise 4 implies MM5

**Status:** Near-complete. The MM5 gap remains. ∎

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

### 6.4 Current Status

**Honest assessment:** We have not closed the MM5 gap. The technical paper can either:
1. Solve it (significant mathematical work)
2. Adopt Approach B (additional axiom)
3. Adopt Approach C (weakened claim)

Approach C is recommended for initial submission, with the MM5 gap flagged as open.

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

## References

Brassard, G., et al. "Limit on nonlocality in any world in which communication complexity is not trivial." *Physical Review Letters* 96, 2006: 250401.

Chiribella, G., D'Ariano, G. M., and Perinotti, P. "Informational derivation of quantum theory." *Physical Review A* 84(1), 2011: 012311.

Hardy, L. "Quantum theory from five reasonable axioms." arXiv:quant-ph/0101012, 2001.

Masanes, L. and Müller, M. P. "A derivation of quantum theory from physical requirements." *New Journal of Physics* 13, 2011: 063001.

van Dam, W. "Implausible consequences of superstrong nonlocality." arXiv:quant-ph/0501159, 2005.

Wootters, W. K. "Local accessibility of quantum states." In *Complexity, Entropy, and the Physics of Information*, edited by W. Zurek. Addison-Wesley, 1990.

---

*Working draft. Sections 4-6 require further development.*
