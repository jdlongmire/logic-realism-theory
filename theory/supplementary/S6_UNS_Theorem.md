# S6: Formalization of the Unique Next State (UNS) Theorem

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Addresses:** Core Derivation Step 8 (UNS theorem)

---

## Abstract

The Unique Next State (UNS) theorem asserts that for every actual configuration $c \in A_\Omega$, there exists a unique successor configuration $c' \in A_\Omega$ selected by the action primitive A. This supplement formalizes the argument presented in the master document, making explicit the logical structure that connects Determinate Identity (DI), L<sub>3</sub>'s laws, and A's Boolean character to the existence and uniqueness of successor states. The proof proceeds through three stages: (1) existence via DI-preservation, (2) uniqueness via Boolean exclusion, and (3) the well-definedness of the successor function. We address the quantum superposition objection and clarify the scope of UNS relative to dynamical laws.

---

## 1. The Problem

### 1.1 What the Master Document Claims

Section 5.2 of LRT-MASTER states:

> "For every actual configuration c ∈ A<sub>Ω</sub>, there exists a unique next configuration c' ∈ A<sub>Ω</sub> such that A selects c' as the successor of c."

The epistemic status is marked ARGUED. The argument appeals to:
- Determinate Identity (DI) from Step 2
- A's Boolean character: $A : D \to \{0,1\}$
- L<sub>3</sub>'s laws (Identity, Non-Contradiction, Excluded Middle)

This supplement makes the logical structure explicit, transforming the prose argument into a numbered derivation with clearly stated premises and inferences.

### 1.2 The Scope Question

UNS does not claim that a configuration $c$ alone determines its successor independent of physical laws. The claim is conditional:

**UNS (Conditional Form):** Given the actual Hamiltonian $H$ and interaction structure of the physical system, for any $c \in A_\Omega$, there exists a unique $c' \in A_\Omega$ such that A selects $c'$ as the successor of $c$.

The Hamiltonian is an empirical input (Step 13). UNS establishes that *given* such a law, succession is determinate. It does not derive the specific form of any Hamiltonian.

### 1.3 What Must Be Proven

Three claims:

1. **Existence:** Every $c \in A_\Omega$ has at least one successor in $A_\Omega$.
2. **Uniqueness:** Every $c \in A_\Omega$ has at most one successor in $A_\Omega$.
3. **Well-definedness:** The successor function $S : A_\Omega \to A_\Omega$ is total and single-valued.

---

## 2. Preliminaries

### 2.1 Determinate Identity (DI)

From Step 2, every $c \in A_\Omega$ satisfies:

$$c = c \quad \text{(Identity)}$$
$$\neg(P(c) \land \neg P(c)) \quad \text{for all properties } P \quad \text{(Non-Contradiction)}$$
$$P(c) \lor \neg P(c) \quad \text{for all well-defined properties } P \quad \text{(Excluded Middle)}$$

**DI at the sequence level:** Section 2.3 of LRT-MASTER extends DI to sequential instantiation. A transition from $c$ to $c'$ must preserve structural determinacy: $c'$ must itself satisfy DI, and the transition relation must be determinate.

### 2.2 The Action Primitive A

A is defined as:

$$A : D \to \{0,1\}$$

where $D = L_3(I_\infty)$ is the domain of L<sub>3</sub>-admissible configurations. For any configuration $c$ and successor candidate $c'$:

$$A(c' \mid c) = \begin{cases} 1 & \text{if } c' \text{ is the actual next configuration} \\ 0 & \text{if } c' \text{ is not the actual next configuration} \end{cases}$$

### 2.3 The Admissibility Constraint

For $c'$ to be a valid successor of $c$:

1. $c' \in A_\Omega$ (the successor must be L<sub>3</sub>-admissible)
2. The pair $(c, c')$ must satisfy sequential DI (the transition must be determinate)
3. $A(c' \mid c) = 1$ (A must select $c'$)

---

## 3. Existence of Successor States

### 3.1 The Argument

**Premise E1:** Every $c \in A_\Omega$ has determinate identity (Step 2).

**Premise E2:** Actuality is not static; the dynamic aspect A operates continuously (from X ≡ [L<sub>3</sub> : I<sub>∞</sub> : A]).

**Premise E3:** A is total on its domain—for every configuration $c$ and every instant, A assigns a definite value.

**Inference E4:** At the instant after $c$'s instantiation, some configuration must be instantiated. If no configuration were instantiated, this would violate:
- Excluded Middle: for any candidate $c'$, either $c'$ is actual or it is not
- The dynamic character of X: actuality does not halt

**Premise E5:** Any configuration instantiated after $c$ must be in $A_\Omega$ (only L<sub>3</sub>-admissible configurations can be instantiated).

**Conclusion (Existence):** For every $c \in A_\Omega$, there exists at least one $c' \in A_\Omega$ such that $A(c' \mid c) = 1$.

### 3.2 Addressing the Termination Objection

**Objection:** Could $c$ be a "final" configuration with no successor?

**Response:** This is a cosmological question, not a foundational one. If the actualization trajectory has an endpoint (e.g., cosmological heat death, Big Crunch), UNS applies to the interior of the trajectory. The claim is:

$$\forall c \in A_\Omega^{\text{interior}} : \exists c' \in A_\Omega : A(c' \mid c) = 1$$

Boundary behavior is a separate issue addressed via physical cosmology, not by the logical structure of X.

---

## 4. Uniqueness of Successor States

This is the core content of UNS. The argument proceeds by showing that multiple simultaneous successors violate L<sub>3</sub>.

### 4.1 Stage 1: Non-Contradiction Excludes Multiple Actual Successors

**Premise U1:** Suppose, for contradiction, that $c$ has two distinct successors $c'_1$ and $c'_2$ with:
$$A(c'_1 \mid c) = 1 \quad \text{and} \quad A(c'_2 \mid c) = 1$$

**Premise U2:** $c'_1 \neq c'_2$ (they are distinct configurations).

**Inference U3:** Let $P$ be the property "is the actual next configuration after $c$". Then:
- $P(c'_1) = \text{true}$
- $P(c'_2) = \text{true}$

**Inference U4:** But $c'_1 \neq c'_2$. If both are "the" next configuration, then "the next configuration" fails to denote a unique entity. This violates Identity applied to the successor relation: there is no determinate answer to "what is the next configuration after $c$?"

**Inference U5:** More precisely, consider the proposition $Q$: "The unique actual next configuration after $c$ is $c'_1$."
- If $A(c'_1 \mid c) = 1$ and $A(c'_2 \mid c) = 1$ with $c'_1 \neq c'_2$, then $Q$ and $\neg Q$ both hold (since the next configuration both is and is not $c'_1$).
- This violates Non-Contradiction.

**Conclusion (U6):** Multiple simultaneous successors are ruled out by Non-Contradiction.

### 4.2 Stage 2: Excluded Middle Excludes Indeterminate Succession

**Premise U7:** For any candidate successor $c'$, consider the proposition $R_{c'}$: "A selects $c'$ as the successor of $c$."

**Premise U8:** By Excluded Middle: $R_{c'} \lor \neg R_{c'}$. There is no third option.

**Inference U9:** Combined with A's Boolean definition ($A(c' \mid c) \in \{0,1\}$), exactly one of the following holds:
- $A(c' \mid c) = 1$ (c' is the successor)
- $A(c' \mid c) = 0$ (c' is not the successor)

**Inference U10:** There is no indeterminate state where succession is undefined or partial.

### 4.3 Stage 3: Identity Requires Determinate Successor Relation

**Premise U11:** DI at the sequence level (Section 2.3 of LRT-MASTER) requires that the transition relation be determinate.

**Premise U12:** A determinate transition relation means: given $c$, the identity of the successor is fixed.

**Inference U13:** If the successor were not uniquely determined, the transition relation would lack determinate content. This violates Identity applied to the relation itself.

**Formal statement:** Let $T \subseteq A_\Omega \times A_\Omega$ be the transition relation. DI requires that $T$ be a function: for each $c$, there is exactly one $c'$ such that $(c, c') \in T$.

### 4.4 Synthesis

Combining the three stages:

1. Non-Contradiction excludes multiple simultaneous successors (Stage 1)
2. Excluded Middle excludes indeterminate succession (Stage 2)
3. Identity requires a determinate transition relation (Stage 3)

**Conclusion (Uniqueness):** For every $c \in A_\Omega$, there exists at most one $c' \in A_\Omega$ such that $A(c' \mid c) = 1$.

---

## 5. The Successor Function

### 5.1 Definition

Combining Existence (Section 3) and Uniqueness (Section 4):

**Definition:** The successor function $S : A_\Omega \to A_\Omega$ is defined by:

$$S(c) = c' \quad \Leftrightarrow \quad A(c' \mid c) = 1$$

### 5.2 Properties of S

**Theorem (UNS):** $S$ is a well-defined total function on $A_\Omega$.

*Proof:*
- **Total:** By Existence, every $c \in A_\Omega$ has at least one successor.
- **Single-valued:** By Uniqueness, every $c \in A_\Omega$ has at most one successor.
- Therefore $S$ assigns exactly one successor to each configuration. $\square$

**Corollary (Injectivity):** $S$ is injective: if $S(c_1) = S(c_2)$, then $c_1 = c_2$.

*Proof:* Suppose $S(c_1) = S(c_2) = c'$ with $c_1 \neq c_2$. Then $c'$ has two distinct predecessors. Consider the property "is the predecessor of $c'$." Both $c_1$ and $c_2$ satisfy this property. But if $c_1 \neq c_2$, then "the predecessor of $c'$" fails to denote uniquely, violating Identity at the sequence level. Therefore $c_1 = c_2$. $\square$

---

## 6. The Quantum Superposition Objection

### 6.1 The Objection

**Objection:** In standard quantum mechanics, a system in superposition does not have a definite state until measurement. Consider $\lvert\psi\rangle = \alpha\lvert 0\rangle + \beta\lvert 1\rangle$. What is the "unique next state"? Does UNS conflict with quantum indeterminacy?

### 6.2 The Resolution

**Key Distinction:** UNS concerns states in $A_\Omega$, not measurement outcomes.

1. **The superposition is the unique next state.** The configuration $\lvert\psi\rangle = \alpha\lvert 0\rangle + \beta\lvert 1\rangle$ is itself a determinate element of $\mathbb{C}\mathcal{H}$. It is the unique next state in the sense that the system's configuration is determinately $\lvert\psi\rangle$, not some other state.

2. **UNS does not require classical definiteness.** The "unique next state" need not be an eigenstate of any particular observable. Superpositions are L<sub>3</sub>-admissible configurations. They have determinate identity (the superposition $\lvert\psi\rangle$ is self-identical), they are non-contradictory (no property is both true and false of $\lvert\psi\rangle$), and they satisfy Excluded Middle (for any well-defined property $P$, either $P(\lvert\psi\rangle)$ or $\neg P(\lvert\psi\rangle)$).

3. **Measurement is a separate question.** What is indeterminate prior to measurement is not the state in $A_\Omega$ but which outcome A will select from the PVM decomposition. UNS says the state evolves deterministically under the Hamiltonian; it does not claim that measurement outcomes are predetermined.

### 6.3 Formal Clarification

Let $\lvert\psi(t)\rangle$ be the state at time $t$. UNS claims:

$$\lvert\psi(t + dt)\rangle = U(dt)\lvert\psi(t)\rangle$$

where $U(dt) = e^{-iH\,dt/\hbar}$ is the unitary time evolution operator. The successor state is determined by the Hamiltonian $H$.

What UNS does **not** claim: that the measurement outcome (eigenvalue of some observable $\hat{O}$) is predetermined. The Born rule gives probabilities for outcomes; A selects one outcome per measurement event. That selection is Boolean, not the state evolution.

---

## 7. Relation to PVM Structure

### 7.1 UNS and Step 5

Step 5 establishes that event operators are projections (PVMs). UNS (Step 8) establishes that state evolution is deterministic between measurement events.

The two claims are complementary:
- **Step 5:** When A selects, it selects a Boolean outcome from a PVM.
- **Step 8:** Between selections, the state evolves deterministically via unitary dynamics.

### 7.2 No Tension with Probabilistic Outcomes

UNS is consistent with the Born rule. The probabilities $p(E\lvert\psi) = \langle\psi\lvert P_E\lvert\psi\rangle$ describe dispositions toward A's Boolean selection. The selection itself is not determined by UNS; it is determined by A operating on the PVM structure. UNS governs what happens between selections.

---

## 8. Dependency Structure

### 8.1 What UNS Depends On

| Premise | Source | Status |
|---------|--------|--------|
| Determinate Identity | Step 2 | ESTABLISHED |
| A is Boolean | Definition of X | ESTABLISHED |
| L<sub>3</sub> constitutive | Section 1.3 of LRT-MASTER | Framework commitment |
| DI at sequence level | Section 2.3 of LRT-MASTER | Framework commitment |

### 8.2 What Depends on UNS

| Downstream Step | Content |
|-----------------|---------|
| Step 9 | Ordinal time (S induces well-ordered structure) |
| Step 10 | Continuous time via Debreu-Nachbin |
| Steps 11-13 | Dynamics, Stone's theorem, Schrödinger equation |

UNS is the foundation of the temporal derivation chain.

---

## 9. Formal Summary

**Theorem (Unique Next State):** Let $A_\Omega = L_3(I_\infty)$ be the actualized domain with action primitive $A : D \to \{0,1\}$. For every configuration $c \in A_\Omega$, there exists a unique configuration $c' \in A_\Omega$ such that:

$$A(c' \mid c) = 1$$

This defines a total injective function $S : A_\Omega \to A_\Omega$.

**Proof outline:**

1. **Existence:** The dynamic character of X and totality of A ensure some successor exists (Section 3).
2. **Uniqueness via NC:** Multiple simultaneous successors violate Non-Contradiction (Section 4.1).
3. **Uniqueness via EM:** Indeterminate succession violates Excluded Middle (Section 4.2).
4. **Uniqueness via I:** A non-functional transition relation violates Identity at the sequence level (Section 4.3).
5. **Well-definedness:** $S$ is total and single-valued by (1) and (2)-(4). $\square$

---

## 10. Epistemic Status

**Previous Status:** ARGUED (prose argument in LRT-MASTER Section 5.2)

**Current Status:** ARGUED (formalized with explicit premises and inferences)

**Remaining for ESTABLISHED:**
- Lean 4 formalization of the logical structure
- Explicit treatment of the boundary case (cosmological endpoints)
- Verification that DI at the sequence level is a consequence of DI, not an independent assumption

**Note:** The argument's validity depends on the constitutive status of L<sub>3</sub>. A critic who rejects L<sub>3</sub>'s constitutive role rejects the framework, not this inference within it.

---

## 11. Open Questions

### 11.1 The Reversibility Question

Is $S$ surjective? Does every configuration have a predecessor?

**Initial answer:** Yes, by time-reversal symmetry of unitary dynamics. But this requires the Hamiltonian to be time-reversal symmetric, which is an empirical constraint. UNS itself does not entail reversibility.

### 11.2 The Identity of S with Unitary Evolution

Is the successor function $S$ identical to infinitesimal unitary evolution $U(dt)$?

**Expected:** Yes, via the chain UNS → ordinal time → continuous time → Stone → Schrödinger. The supplement S4 bridges ordinal to continuous time.

### 11.3 Quantum Gravity Implications

Does UNS hold when spacetime itself is dynamical?

**Status:** OPEN. The derivation assumes a fixed background Hilbert space. Extension to quantum gravity requires additional work.

---

## 12. Relation to Other Supplements

### 12.1 Dependency on S1

S6 uses "physical proposition" language (e.g., "is the actual next configuration after $c$"). S1 (PPC Derivation) establishes that such propositions require operational distinguishability. This supports the claim that successor relations must be determinate—a successor relation without operational signature would fail the PPC.

### 12.2 Relation to S3

S3 establishes PVM structure (Step 5). S6 establishes UNS (Step 8). Both are inputs to the dynamics derivation (Steps 9-13). They are independent in their core arguments but complementary in the overall derivation.

### 12.3 Relation to S4

S4 derives the Debreu-Nachbin conditions for Step 10. S6 provides the UNS foundation that S4 presupposes. The successor function $S$ from S6 generates the ordinal structure that S4 lifts to continuous time.

---

## References

Anandan, J., and Aharonov, Y. (1990). Geometry of quantum evolution. *Physical Review Letters*, 65(14), 1697-1700.

Fine, K. (2012). Guide to ground. In F. Correia and B. Schnieder (Eds.), *Metaphysical Grounding: Understanding the Structure of Reality* (pp. 37-80). Cambridge University Press.

Stone, M. H. (1930). Linear transformations in Hilbert space. III. *Proceedings of the National Academy of Sciences*, 16, 172-175.

---

*Supplement S6 | Logic Realism Theory Project | 2026-03-13*
