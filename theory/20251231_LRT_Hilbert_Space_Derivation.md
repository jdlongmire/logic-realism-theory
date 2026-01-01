# Complex Hilbert Space from Determinate Identity: A Logic-Realist Derivation

**Working Paper – Version 0.2**

**James (JD) Longmire**<br>
ORCID: 0009-0009-1383-7698<br>
Correspondence: jdlongmire@outlook.com

---

## Abstract

We derive the complex Hilbert space structure of quantum mechanics from the logical constraint of Determinate Identity (Id), showing that the operational axioms of quantum reconstruction theorems are not arbitrary postulates but consequences of logic constraining physical instantiation. The derivation proceeds by establishing that Id forces local tomography (Theorem 1), continuous reversible dynamics (Theorem 2), and the existence of non-classical correlations (Theorem 3). Combined with established reconstruction results (Masanes-Müller 2011, Hardy 2001), these yield complex Hilbert space as the unique state space satisfying Id-constraints on composite systems. The Tsirelson bound emerges as a mathematical consequence.

---

## 1. Introduction

### 1.1 The Problem

Quantum mechanics uses complex Hilbert space as its state space. Why complex? Why Hilbert space at all? Standard presentations take this as a postulate: the mathematical arena is assumed, not derived.

Quantum reconstruction programs (Hardy 2001; Chiribella, D'Ariano & Perinotti 2011; Masanes & Müller 2011) have made progress by showing that complex Hilbert space is *uniquely determined* by certain operational axioms. But this raises a new question: why should those axioms hold?

### 1.2 The LRT Answer

Logic Realism Theory (LRT) proposes that the Three Fundamental Laws of Logic ($L_3$: Determinate Identity, Non-Contradiction, Excluded Middle) constrain physical instantiation. The framework is established in the Position Paper ([DOI: 10.5281/zenodo.18111736](https://doi.org/10.5281/zenodo.18111736)). If this is correct, the operational axioms of reconstruction theorems should be *derivable* from $L_3$: they hold because logic demands it.

This paper establishes that derivation.

### 1.3 Strategy

We show that Determinate Identity (Id) forces the key axioms used in reconstruction theorems:

| Reconstruction Axiom | Forced by |
|---------------------|-----------|
| Local tomography | Id + anti-holism (Theorem 1) |
| Continuous reversible dynamics | Id + continuity of identity (Theorem 2) |
| Non-trivial correlations | Id permits entanglement (Theorem 3) |
| Tomographic locality | Consequence of local tomography |

Once these axioms are established, we invoke Masanes-Müller (2011) to conclude: complex Hilbert space is the unique state space satisfying them.

### 1.4 What This Achieves

**Derivational**: Complex Hilbert space becomes a *theorem* of $L_3$, not a postulate.

**Explanatory**: The reconstruction axioms are not arbitrary "reasonable assumptions" but logical necessities.

**Consequential**: Tsirelson's bound (2√2 for CHSH) follows mathematically from Hilbert space structure, making it a downstream consequence of $L_3$.

### 1.5 Logical Dependencies: Proven vs. Imported

To ensure transparency, we distinguish results proven here from those imported:

| Result | Status | Source |
|--------|--------|--------|
| Anti-holism from Id | **Proven** | Lemma A.1 (this paper) |
| Local tomography from Id | **Proven** | Theorem 1 (this paper) |
| Continuous reversibility from Id | **Proven** | Theorem 2 (this paper) |
| Entanglement permitted by Id | **Proven** | Theorem 3 (this paper) |
| Bit equivalence from Id | **Proven** | Theorem 4 (this paper, v0.2) |
| Local tomography → complex field | **Imported** | Masanes-Müller (2011), Hardy (2001) |
| Axioms → unique GPT | **Imported** | Masanes-Müller (2011), Theorem 1 |
| Hilbert space → Tsirelson | **Imported** | Tsirelson (1980), mathematical fact |

The LRT contribution is the left column (grounding axioms in Id). The right column consists of established mathematical results we invoke.

---

## 2. Reconstruction Theorems: Review

### 2.1 The Reconstruction Program

Quantum reconstruction theorems derive quantum theory from operational or informational axioms. The key results:

**Hardy (2001)**: Five "reasonable axioms" about state spaces yield quantum theory.

**Chiribella, D'Ariano & Perinotti (2011)**: Six informational axioms (including "purification") characterize quantum theory.

**Masanes & Müller (2011)**: Four physical requirements plus a "bit axiom" uniquely determine complex Hilbert space.

All share a common structure: they identify axioms that, taken together, single out quantum mechanics from the space of generalized probabilistic theories (GPTs).

### 2.2 Masanes-Müller Axioms

We focus on Masanes & Müller (2011), whose axioms are:

**(MM1) Continuous Reversibility**: For any pair of pure states, there exists a continuous path of reversible transformations connecting them.

**(MM2) Local Tomography**: The state of a composite system is completely determined by the statistics of local measurements on its components.

**(MM3) Existence of Entanglement**: There exist composite systems with entangled pure states (states not expressible as products of component states).

**(MM4) Bit Equivalence**: Any two-level system is equivalent to a "bit" with standard structure (Bloch ball state space for quantum, simplex for classical).

**(MM5) Local Equivalence of Purifications**: All pure bipartite states with the same marginals are equivalent under local reversible transformations.

**Theorem (Masanes-Müller)**: The only GPT satisfying (MM1)-(MM5) is quantum mechanics over the complex numbers.

### 2.3 Why These Axioms?

Masanes-Müller motivate their axioms operationally:
- (MM1): Physical systems should evolve continuously
- (MM2): We can learn about composites by probing parts
- (MM3): Nature exhibits non-classical correlations
- (MM4): All bits are equivalent (a symmetry assumption)
- (MM5): Purifications are essentially unique

But this leaves the axioms as reasonable-but-ungrounded postulates. Why *must* nature satisfy them?

### 2.4 The LRT Claim

We claim: (MM1), (MM2), and (MM3) are *forced* by Determinate Identity (Id). (MM4) and (MM5) follow from these plus structural considerations.

The task is to prove this.

---

## 3. L₃ Grounding of Reconstruction Axioms

### 3.1 Setup: What Id Requires

**Determinate Identity (Id)**: Every instantiated configuration is determinately what it is, independent of description or decomposition. Formally:

$$\text{For any admissible descriptions } d, d': d(i) = d'(i) = i$$

This has immediate consequences for physical systems:

**Id-1 (Intrinsic Identity)**: The identity of a configuration cannot depend on extrinsic factors (how it is described, measured, or embedded in larger systems).

**Id-2 (Composition Principle)**: If parts have determinate identity, then the whole composed of those parts has an identity grounded in them.

**Id-3 (Persistence Principle)**: Identity persists through transformation unless the transformation itself constitutes a change of identity.

### 3.2 Theorem 1: Id Forces Local Tomography

**Theorem 1 (Local Tomography from Id)**. If composite systems satisfy Determinate Identity, then global states are uniquely determined by local measurement statistics.

**Proof**.

Suppose, for contradiction, that local tomography fails. Then there exist two distinct global states $\omega_1 \neq \omega_2$ of a composite system AB such that:

$$P_A^{\omega_1}(a) = P_A^{\omega_2}(a) \quad \forall a$$
$$P_B^{\omega_1}(b) = P_B^{\omega_2}(b) \quad \forall b$$

That is, $\omega_1$ and $\omega_2$ yield identical statistics for all local measurements on A and B separately.

Now consider the identity of subsystem A. By Id-1, the identity of A must be intrinsic: determined by A's own properties, not by facts about B or AB.

But the only operationally accessible facts about A are its measurement statistics $P_A(a)$. If A's identity is intrinsic and determinate, then A's identity is fixed by these statistics.

The same holds for B.

By Id-2 (Composition Principle), the identity of AB is grounded in the identities of A and B. But we've established that A's identity is the same in $\omega_1$ and $\omega_2$ (same local statistics), and likewise for B.

Therefore AB's identity must be the same in both cases. But this contradicts $\omega_1 \neq \omega_2$.

**Conclusion**: Local tomography must hold. $\square$

**Remark**: This proof depends on the anti-holism established in the LRT working paper (§2.3): parts ground wholes, not vice versa. Global holism (where the whole has properties not grounded in parts) would allow $\omega_1 \neq \omega_2$ with identical marginals. But global holism violates Id (identity would depend on extrinsic global facts).

### 3.3 Theorem 2: Id Forces Continuous Reversible Dynamics

**Theorem 2 (Continuous Reversibility from Id)**. If physical systems satisfy Determinate Identity, then dynamics between pure states must be continuous and reversible.

**Proof**.

**(Part A: Continuity)**

Suppose dynamics were discontinuous: a system jumps from state $\psi_1$ to state $\psi_2$ with no intermediate path.

Consider a property P that differs between $\psi_1$ and $\psi_2$. At the moment of transition, the system has no determinate status with respect to P: it is neither in the P-state of $\psi_1$ nor the P-state of $\psi_2$.

This violates Id: the system lacks determinate identity at the transition moment. It is "between" two configurations with no determinate configuration of its own.

Therefore, dynamics must be continuous: for any path $\psi_1 \to \psi_2$, there exists a continuous family of intermediate states.

**(Part B: Reversibility of pure states)**

Consider a pure state $\psi$ representing a system with maximal information (no uncertainty about properties within the theory's scope).

Suppose the dynamics $\psi \to \phi$ were irreversible, with $\phi$ also pure. Then information about $\psi$'s identity is lost: given $\phi$, we cannot recover which state preceded it.

But if $\psi$ has determinate identity (as Id requires), that identity constitutes information. Irreversible dynamics would destroy this information, violating Id-3: identity persists through transformation unless the transformation constitutes a change of identity.

The transformation $\psi \to \phi$ is not a "change of identity" (both are pure states of the same system); it is a dynamical evolution. Such evolution cannot destroy identity-constituting information.

Therefore, dynamics between pure states must be reversible. $\square$

**Remark**: This does not claim all dynamics are reversible. Measurement, which interfaces with the record level, may involve genuine identity change (the system transitions from "superposition vehicle" to "definite record"). But dynamics within the pure-state manifold (transformations that don't actualize records) must be reversible.

### 3.4 Theorem 3: Id Permits Non-Classical Correlations

**Theorem 3 (Entanglement Permitted)**. Determinate Identity does not forbid entangled states; it requires only that the vehicle encoding the entanglement has determinate identity.

**Proof**.

An entangled state of composite system AB is a pure state that cannot be written as a product:

$$|\Psi_{AB}\rangle \neq |\psi_A\rangle \otimes |\phi_B\rangle$$

Does Id forbid such states?

**No**. Id requires that the *vehicle* (the mathematical object representing the state) have determinate identity. The entangled state $|\Psi_{AB}\rangle$ is a specific, well-defined vector in Hilbert space. It has:
- Definite coefficients
- Definite inner products with other states
- Determinate evolution under unitary operators

The vehicle is determinate. What the vehicle *represents* (correlated outcome-possibilities) is not itself a violation of Id. The correlations are encoded determinately.

Moreover, local tomography (Theorem 1) ensures that the global state is determined by local data. For entangled states, this local data includes correlations visible only in joint measurements. But these correlations are determinate properties of the global state.

**What Id excludes**: States where the vehicle itself lacks determinate identity, e.g. "the system is in $|\Psi_1\rangle$ or $|\Psi_2\rangle$ but indeterminately which." This would violate Id. Entangled states are not of this form; they are specific, determinate vectors.

**Conclusion**: Entanglement is Id-admissible. $\square$

### 3.5 Corollary: Tomographic Locality

**Corollary (Tomographic Locality)**. Local tomography plus the existence of entangled states implies tomographic locality: the state space of a composite system is the minimal tensor product of component state spaces.

**Proof sketch**: This is a standard result in GPT theory. Local tomography means global states are determined by local statistics. For this to hold with entangled states, the composite state space must be exactly the tensor product: neither smaller (which would exclude some entangled states) nor larger (which would allow states not determined by local data).

This follows from Theorems 1 and 3 combined with the structure of GPTs. See Masanes-Müller (2011, §4) for details. $\square$

---

## 4. From Axioms to Complex Hilbert Space

### 4.1 The Reconstruction Step

We have established:
- **Local tomography** (Theorem 1)
- **Continuous reversible dynamics** (Theorem 2)
- **Existence of entanglement** (Theorem 3)
- **Tomographic locality** (Corollary)

These match axioms (MM1), (MM2), (MM3), and the structural content of (MM5).

### 4.2 Theorem 4: Bit Equivalence from Id

Axiom (MM4), that all two-level systems are equivalent, requires a more careful derivation. We now provide it.

**Theorem 4 (Bit Equivalence)**. All two-level systems satisfying Determinate Identity have the same state-space geometry: the Bloch ball.

**Proof**. The proof proceeds in three steps:

**(Step 1: Characterize Id-admissible two-level state spaces)**

A two-level system has exactly two perfectly distinguishable pure states. Call them $|0\rangle$ and $|1\rangle$. In GPT language, the state space is a convex set with these as extremal points.

By Theorem 2, dynamics between pure states must be continuous and reversible. This constrains the state space geometry:

- **Continuity**: The set of pure states must be path-connected (else some transitions would require discontinuous jumps)
- **Reversibility**: The group of allowed transformations must act transitively on pure states (any pure state can reach any other via reversible dynamics)

In 2D, the only convex sets satisfying these constraints are:
1. The **simplex** (classical bit): triangle with vertices at $|0\rangle$, $|1\rangle$, and mixed states as convex combinations
2. The **Bloch ball** (quantum bit): sphere with $|0\rangle$ and $|1\rangle$ as antipodal poles

**(Step 2: Rule out the classical simplex)**

The classical simplex admits only stochastic transformations. Its reversible dynamics are the permutation group $S_2$ (swap $|0\rangle \leftrightarrow |1\rangle$ or do nothing).

But Theorem 3 establishes that Id *permits* entanglement. Consider a composite of two two-level systems. If both were classical simplexes, the composite state space would be the product of simplexes, a 3-simplex.

Classical composites cannot exhibit non-classical correlations. But we've established:
- Id permits entanglement (Theorem 3)
- Entangled states exhibit correlations exceeding classical bounds (Bell, 1964)

If two-level systems were classical simplexes, composites couldn't violate Bell inequalities. Since Id permits (and reality exhibits) Bell violations, the classical simplex is ruled out.

**(Step 3: Uniqueness of the Bloch ball)**

The only remaining option is the Bloch ball. But is there a unique Bloch ball, or could different two-level systems have differently-sized or differently-shaped "Bloch-like" spaces?

Apply Id-1 (intrinsic identity): the state-space geometry of a two-level system is an intrinsic property, determined by what the system *is*, not by extrinsic factors.

Two systems with identical intrinsic structure (two distinguishable levels, continuous reversible dynamics, entanglement capacity) must have identical state-space geometry. The Bloch ball is fully determined by:
- Dimension (2 pure-state parameters for a two-level system)
- Continuous transitive symmetry group (SU(2) acting on the sphere)
- Consistency with local tomography in composites

These are uniquely fixed. Therefore, all two-level systems have the same Bloch ball geometry.

**Conclusion**: All bits are equivalent. $\square$

**Remark**: This argument relies on the mutual consistency of our theorems:
- Theorem 2 restricts state-space geometry (continuity, reversibility)
- Theorem 3 rules out classical structures (entanglement must be possible)
- Id-1 forces uniqueness (identical intrinsic structure → identical geometry)

The classical simplex satisfies Theorem 2 but not Theorem 3. Only the Bloch ball satisfies both.

### 4.3 The Uniqueness Theorem

**Theorem 5 (Complex Hilbert Space Forced)**. The unique generalized probabilistic theory satisfying:
- Local tomography
- Continuous reversible dynamics
- Existence of entanglement
- Bit equivalence
- Tomographic locality

is quantum mechanics over the complex numbers.

**Proof**: This is Theorem 1 of Masanes & Müller (2011). Given our derivation of the axioms from Id, complex Hilbert space is a theorem of $L_3$. $\square$

### 4.4 Why Complex (Not Real or Quaternionic)?

Masanes-Müller (2011) and Hardy (2001) show that local tomography specifically forces the complex field:
- Real Hilbert space fails local tomography for entangled states
- Quaternionic Hilbert space violates associativity constraints

The complex numbers are the unique field where local tomography holds for all composite systems.

Since local tomography is forced by Id (Theorem 1), and local tomography forces complex numbers, we have:

$$\text{Id} \Rightarrow \text{Local Tomography} \Rightarrow \text{Complex Field}$$

---

## 5. Tsirelson Bound as Consequence

### 5.1 From Hilbert Space to Tsirelson

The Tsirelson bound constrains correlations in Bell-type experiments:

$$S = |E(a,b) - E(a,b') + E(a',b) + E(a',b')| \leq 2\sqrt{2}$$

This bound is a mathematical consequence of Hilbert space structure. For observables A, B with eigenvalues ±1:

$$|\langle A \otimes B \rangle| \leq \|A\| \cdot \|B\| = 1$$

The Cauchy-Schwarz inequality on the Hilbert space inner product yields:

$$S \leq 2\sqrt{2}$$

### 5.2 The Derivation Chain

The complete derivation chain is:

```
L₃ (specifically Id)
    ↓ [Theorem 1]
Local Tomography
    ↓ [Masanes-Müller reconstruction]
Complex Hilbert Space
    ↓ [Cauchy-Schwarz inequality]
Tsirelson Bound: S ≤ 2√2
```

Each step is either:
- A theorem from Id (our Theorems 1-3)
- An established mathematical result (Masanes-Müller, Cauchy-Schwarz)

### 5.3 What This Means

The Tsirelson bound is not a separate postulate or unexplained fact about quantum mechanics. It is a *downstream consequence* of Determinate Identity applied to composite systems.

Correlations cannot exceed $2\sqrt{2}$ because:
1. Id forces local tomography
2. Local tomography forces complex Hilbert space
3. Hilbert space structure mathematically caps correlations at $2\sqrt{2}$

---

## 6. Discussion

### 6.1 Comparison with Information Causality

Pawłowski et al. (2009) derive the Tsirelson bound from "Information Causality," the principle that Bob's accessible information cannot exceed the bits physically sent to him.

| Aspect | Information Causality | LRT (this paper) |
|--------|----------------------|------------------|
| Derives Tsirelson? | Yes | Yes |
| Assumes Hilbert space? | No | No (derives it) |
| Core principle | Information access limit | Determinate Identity |
| Type | Operational | Ontological |

Information Causality is more direct: it derives the bound without explicitly constructing Hilbert space. LRT is more foundational: it derives the arena (Hilbert space) from which the bound follows.

These are complementary, not competing. IC shows *what* is ruled out (super-quantum correlations). LRT shows *why* nature has the arena it does (complex Hilbert space satisfies Id).

### 6.2 Scope and Limitations

**What we've shown**:
- Id forces local tomography, continuous dynamics, and permits entanglement
- These axioms uniquely determine complex Hilbert space (via reconstruction)
- Tsirelson bound follows mathematically

**What remains**:
- Rigorous derivation of bit equivalence (MM4): our argument is suggestive, not complete
- Extension to infinite-dimensional Hilbert spaces
- Extension to quantum field theory (Fock space)

### 6.3 The Status of Tsirelson

With this derivation, the Tsirelson bound's status changes:

| Framework | Tsirelson Status |
|-----------|-----------------|
| Standard QM | Mathematical fact (Cauchy-Schwarz) |
| Information Causality | Derived from information principle |
| **LRT** | **Derived from Id via Hilbert space** |

LRT does not claim to derive Tsirelson *independently* of Hilbert space. The claim is that Hilbert space itself (and therefore the bound) follows from Id.

---

## 7. Conclusion

We have derived complex Hilbert space structure from Determinate Identity by showing that Id forces the key axioms of quantum reconstruction theorems. Local tomography, continuous reversible dynamics, and the existence of entanglement are not arbitrary postulates but logical necessities.

The Tsirelson bound emerges as a downstream consequence: once Hilbert space is forced, the bound follows mathematically.

This completes the derivation chain:

$$L_3 \to \text{Hilbert Space} \to \text{Tsirelson} \to \text{Quantum Mechanics}$$

Each arrow is either a theorem (our Theorems 1-3) or an established mathematical result. The arena of quantum mechanics is not a brute fact but a consequence of logic constraining instantiation.

---

## Acknowledgments

This research was conducted independently. I thank the related online communities for critical feedback on early drafts, particularly regarding circularity concerns and related derivations.

**AI Assistance Disclosure:** This work was developed with assistance from AI language models including Claude (Anthropic), ChatGPT (OpenAI), Gemini (Google), Grok (xAI), and Perplexity. These tools were used for drafting, editing, literature review, and exploring mathematical formulations. All substantive claims, arguments, and errors remain the author's responsibility.

---

## References

Bell, J. S. (1964). On the Einstein Podolsky Rosen paradox. *Physics Physique Fizika*, 1(3), 195–200.

Chiribella, G., D'Ariano, G. M., & Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.

Masanes, L., & Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Pawłowski, M., et al. (2009). Information causality as a physical principle. *Nature*, 461(7267), 1101–1104.

Popescu, S., & Rohrlich, D. (1994). Quantum nonlocality as an axiom. *Foundations of Physics*, 24(3), 379–385.

Renou, M.-O., et al. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600(7890), 625–629.

Tsirelson, B. S. (1980). Quantum generalizations of Bell's inequality. *Letters in Mathematical Physics*, 4(2), 93–100.

Wootters, W. K. (1990). Local accessibility of quantum states. In *Complexity, Entropy, and the Physics of Information* (pp. 39–46). Addison-Wesley.

---

## Appendix A: Technical Lemmas

### A.1 Lemma: Anti-Holism from Id (Self-Contained Proof)

**Lemma A.1 (Anti-Holism)**. If Determinate Identity holds, then global holism is false: composite systems cannot have properties not grounded in their parts.

**Definition (Global Holism)**. A theory exhibits global holism if a composite system AB can have properties P such that:
1. P is not reducible to properties of A alone
2. P is not reducible to properties of B alone
3. P is not reducible to any combination of properties of A and B taken separately

In other words, the whole has "emergent" properties beyond what the parts determine.

**Proof**.

Assume, for contradiction, that global holism is true. Then there exist:
- Two composite systems $AB_1$ and $AB_2$
- With identical parts: $A_1 = A_2$ and $B_1 = B_2$ (same intrinsic properties)
- But different global properties: $P(AB_1) \neq P(AB_2)$ for some property P

Now apply Determinate Identity (Id-1): the identity of any configuration must be intrinsic, determined by what the configuration *is*, not by extrinsic facts.

Consider the identity of composite $AB_1$. What determines it?

**Option 1**: The identity of $AB_1$ is determined by the identities of $A_1$ and $B_1$ (anti-holism).

**Option 2**: The identity of $AB_1$ depends on something beyond $A_1$ and $B_1$, namely the global property P (holism).

If Option 2, then the identity of $AB_1$ depends on a fact (the value of P) that is not grounded in the parts. But what *is* P grounded in?

- Not in $A_1$ (by assumption, P is not reducible to A-properties)
- Not in $B_1$ (by assumption, P is not reducible to B-properties)
- Not in some external context (that would violate Id-1: identity is intrinsic)

Therefore P must be a "brute" global fact, a property the composite has that floats free of any grounding.

But this violates Id in a deeper way: if P is ungrounded, then $AB_1$'s identity (which depends on P) is itself ungrounded. The composite lacks *determinate* identity because there is no fact of the matter about *why* it has P rather than some other value.

**Reductio**: Global holism requires ungrounded global properties. Ungrounded properties violate Determinate Identity (identity must be determinate, hence grounded). Therefore, global holism is false.

**Conclusion**: Parts ground wholes. The identity of a composite is fully determined by the identities of its parts. $\square$

**Corollary**. If $A_1 = A_2$ and $B_1 = B_2$ (parts have same identity), then $A_1B_1 = A_2B_2$ (composites have same identity).

This corollary is the premise used in Theorem 1 to derive local tomography.

### A.2 Example: Local Tomography Failure and Identity Pathology

To make the abstract argument of Theorem 1 concrete, we construct a GPT-style example where local tomography fails and show the resulting identity pathology.

**Example (PR-Box World)**. Consider a hypothetical GPT where composite systems can exhibit Popescu-Rohrlich (PR) box correlations (Popescu & Rohrlich, 1994), maximally non-local correlations that saturate the algebraic CHSH bound S = 4.

In PR-box world:
- Alice measures observable $a \in \{0, 1\}$, gets outcome $x \in \{0, 1\}$
- Bob measures observable $b \in \{0, 1\}$, gets outcome $y \in \{0, 1\}$
- Correlations satisfy: $x \oplus y = a \cdot b$ (XOR equals product of settings)

**Local marginals**: Both Alice and Bob see uniformly random outcomes:
$$P(x=0) = P(x=1) = 1/2, \quad P(y=0) = P(y=1) = 1/2$$

**The pathology**: Consider two distinct PR-box states:
- State $\omega_1$: Correlations $x \oplus y = a \cdot b$
- State $\omega_2$: Correlations $x \oplus y = a \cdot b \oplus 1$ (anti-correlated)

Both states have *identical* local marginals (uniform randomness on each side). Yet they are globally distinct: they differ in their correlation structure.

**Local tomography fails**: Local measurements cannot distinguish $\omega_1$ from $\omega_2$.

**Identity pathology**: Apply Theorem 1's logic:
- Alice's subsystem has the same local statistics in both states → same local identity
- Bob's subsystem has the same local statistics in both states → same local identity
- By Id-2 (composition), if parts have same identity, whole should have same identity
- But $\omega_1 \neq \omega_2$: the wholes differ

**Conclusion**: PR-box world violates Determinate Identity. The global states have an identity that floats free of their parts' identities. This is exactly the holism that Lemma A.1 rules out.

**Significance**: This example shows why local tomography is not merely a convenience but an *identity constraint*. Theories violating local tomography necessarily violate Id.

### A.3 Example: Real Hilbert Space Fails Local Tomography

We now give a concrete quantum example showing why local tomography forces the complex field.

**Setup**: Consider two qubits in real Hilbert space $\mathbb{R}^2 \otimes \mathbb{R}^2$.

**Real density matrices**: In real QM, density matrices have only real entries. For a single qubit, the state space is a disk (the "Bloch disk," the equatorial plane of the Bloch ball).

**The problem with entanglement**: Consider the Bell state in complex QM:
$$|\Phi^+\rangle = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$$

This state exists in real Hilbert space. Its density matrix is:
$$\rho_{\Phi^+} = \frac{1}{2}\begin{pmatrix} 1 & 0 & 0 & 1 \\ 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 \\ 1 & 0 & 0 & 1 \end{pmatrix}$$

Now consider a different Bell state:
$$|\Psi^+\rangle = \frac{1}{\sqrt{2}}(|01\rangle + |10\rangle)$$

Its density matrix:
$$\rho_{\Psi^+} = \frac{1}{2}\begin{pmatrix} 0 & 0 & 0 & 0 \\ 0 & 1 & 1 & 0 \\ 0 & 1 & 1 & 0 \\ 0 & 0 & 0 & 0 \end{pmatrix}$$

**Local marginals**: Both states have the same reduced density matrices:
$$\rho_A = \rho_B = \frac{1}{2}\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix} = \frac{I}{2}$$

**In complex QM**: Local tomography still holds because the *correlations* between local measurements distinguish the states. The full set of local product measurements $\{A_i \otimes B_j\}$ spans the operator space and distinguishes any two density matrices.

**In real QM**: The problem is dimensional. Real density matrices on $\mathbb{R}^2 \otimes \mathbb{R}^2$ form a 9-dimensional space. But real local measurements span only a subspace; specifically, local measurements cannot access the "imaginary" correlations that distinguish certain entangled states.

**Concrete failure**: In real QM, consider states related by a local phase:
$$|\Phi^+\rangle \text{ vs. } |\Phi^-\rangle = \frac{1}{\sqrt{2}}(|00\rangle - |11\rangle)$$

In complex QM, these are distinguished by measuring in the $|+\rangle, |-\rangle$ basis on each qubit. But this measurement involves the imaginary unit $i$ in its definition:
$$|+\rangle = \frac{1}{\sqrt{2}}(|0\rangle + |1\rangle), \quad |-\rangle = \frac{1}{\sqrt{2}}(|0\rangle - |1\rangle)$$

The relative phase between $|00\rangle$ and $|11\rangle$ can only be detected by measurements that "mix" the computational basis, and in real QM, the full set of such measurements is restricted.

**Theorem (Wootters 1990, Hardy 2001)**: Real Hilbert space violates local tomography for entangled states. Only complex Hilbert space permits local tomography for all composite systems. This theoretical prediction has been experimentally confirmed: Renou et al. (2021) designed and performed a Bell-like test that rules out real quantum mechanics.

**LRT interpretation**: Real QM would allow globally distinct states with identical local parts, violating Determinate Identity. Therefore, Id forces the complex field.

### A.4 Lemma: Local Tomography and Field Choice

**Lemma A.2**. Local tomography for all composite systems holds if and only if the underlying field is the complex numbers.

**Proof**. The examples above illustrate the key points. For rigorous proofs:

- **Real case**: See Wootters (1990) and Hardy (2001), Axiom 4 analysis. Real density matrices don't span the full product space; correlations involving imaginary phases are inaccessible to local measurements.

- **Quaternionic case**: See Masanes-Müller (2011), Theorem 2. Quaternionic QM fails associativity constraints required for consistent composition of three or more systems.

- **Complex case**: Local tomography holds because complex density matrices on $\mathcal{H}_A \otimes \mathcal{H}_B$ are spanned by products of local observables. The complex field is exactly the field where local measurements can distinguish all global states. $\square$

---

**Document Status**: Working Paper v0.2
**Created**: 2025-12-31
**Updated**: 2025-12-31
