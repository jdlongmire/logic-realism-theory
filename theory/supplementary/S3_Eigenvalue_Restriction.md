# S3: Eigenvalue Restriction Lemma: From Boolean Action to PVM Structure

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Addresses:** Core Derivation Step 5 (PVM structure from Boolean actualization)

---

## Abstract

This supplement develops the formal argument that the Boolean character of LRT's action primitive **A** entails projection-valued measures (PVMs) as the only admissible event operators. The argument proceeds through three stages: (1) characterizing A's Boolean output structure, (2) connecting Boolean outputs to operator eigenvalue constraints, and (3) demonstrating that these constraints select projections uniquely. The result closes Step 5 of the Core Derivation chain.

---

## 1. The Problem Stated Precisely

LRT defines the action primitive as:

$$A : D \to \{0,1\}$$

where $D = L_3(I_\infty)$ is the domain of L<sub>3</sub>-admissible configurations.

The claim to establish: operators representing actualization events in $\mathcal{H}$ must be projection operators (eigenvalues in $\{0,1\}$), not general POVM elements (eigenvalues in $[0,1]$).

This is **Critical Conjecture 2** in the Core Derivation. Its failure would leave POVM-based quantum logic as a viable alternative to LRT's PVM-only ontology.

---

## 2. Preliminary Distinctions

### 2.1 Two Maps, Two Domains

**Truth-value map (ontological):**
$$A_{\text{event}} : \text{Events} \to \{0,1\}$$

Given an event E (a proposition about a physical configuration), $A_{\text{event}}(E) = 1$ iff E is actual.

**Probability map (epistemic):**
$$p(E\lvert\psi) : \text{Events} \times \text{States} \to [0,1]$$

Given state $\lvert\psi\rangle$, $p(E\lvert\psi)$ is the probability that E obtains upon measurement.

The distinction is critical: the probability map takes values in $[0,1]$, but this does not license event operators with eigenvalues in $(0,1)$. The eigenvalues of event operators concern *which outcomes are possible*, not *how probable* they are.

### 2.2 Events vs. Effects

**Events** are Boolean propositions: "spin is up", "particle detected in region A". Under L<sub>3</sub>, every event is determinately true or false of an actual configuration.

**Effects** in generalized probabilistic theories are positive operators $E$ with $0 \leq E \leq I$. They encode measurement statistics but need not correspond to determinate events.

LRT's claim: at the ontological level (what is actual), only events matter. Effects arise as convenient mathematical descriptions of incomplete knowledge, not as fundamental structure.

---

## 3. The Core Argument

### 3.1 Stage 1: A's Boolean Character Is Ontological

**Premise 1 (From L<sub>3</sub>):** For any well-formed proposition P about an actual configuration $c \in A_\Omega$:
- P = P (Identity)
- Not (P and not-P) (Non-Contradiction)
- Exactly one of P, not-P holds (Excluded Middle)

**Premise 2 (From A's definition):** A assigns actuality status to configurations. For configuration c and event predicate E:
$$A_{\text{event}}(E, c) \in \{0,1\}$$

There is no third status. A configuration either satisfies E or it doesn't.

**Conclusion 1:** The actualization of events is Boolean. Intermediate actualization values are excluded by Excluded Middle.

### 3.2 Stage 2: Event Operators Must Have Boolean Eigenvalues

**Definition:** An event operator is a self-adjoint operator $\hat{E}$ on $\mathcal{H}$ such that the proposition "system has property E" corresponds to measuring $\hat{E}$.

**The Eigenvalue Question:** What are the possible outcomes when $\hat{E}$ is measured?

**Premise 3 (Spectral Theorem):** Measuring $\hat{E}$ yields an eigenvalue of $\hat{E}$ as the outcome.

**Premise 4 (Actualization Interpretation):** The measurement outcome corresponds to the actualization status of the event E. If the outcome is $\lambda$:
- $\lambda = 1$ means "E is actual"
- $\lambda = 0$ means "E is not actual"

**Premise 5 (No Intermediate Actualization):** By Conclusion 1, there is no actualization status between 0 and 1. Therefore measurement outcomes must be in $\{0,1\}$.

**Conclusion 2:** Event operators $\hat{E}$ must have eigenvalues only in $\{0,1\}$.

### 3.3 Stage 3: Operators with {0,1} Eigenvalues Are Projections

**Lemma (Characterization of Projections):** A bounded self-adjoint operator $P$ on a Hilbert space has spectrum contained in $\{0,1\}$ if and only if $P = P^2$.

*Proof:*

$(\Rightarrow)$ Suppose spec$(P) \subseteq \{0,1\}$. By the spectral theorem for self-adjoint operators:
$$P = \int_{\text{spec}(P)} \lambda \, dE_\lambda = 0 \cdot E_0 + 1 \cdot E_1 = E_1$$
where $E_0, E_1$ are the spectral projections onto the $\lambda = 0$ and $\lambda = 1$ eigenspaces.
Since $E_1$ is a spectral projection, $E_1^2 = E_1$, hence $P^2 = P$.

$(\Leftarrow)$ Suppose $P^2 = P$. Then for any eigenvalue $\lambda$ with eigenvector $\lvert\phi\rangle$:
$$P^2\lvert\phi\rangle = \lambda^2\lvert\phi\rangle = P\lvert\phi\rangle = \lambda\lvert\phi\rangle$$
Therefore $\lambda^2 = \lambda$, giving $\lambda \in \{0,1\}$. $\square$

**Conclusion 3:** Event operators with eigenvalues in $\{0,1\}$ are projections.

### 3.4 Synthesis: Boolean A to PVM-Only Events

Combining Conclusions 1-3:

1. A's Boolean character (from L<sub>3</sub>) entails Boolean actualization values
2. Boolean actualization values entail eigenvalues in $\{0,1\}$
3. Eigenvalues in $\{0,1\}$ characterize projections
4. Therefore: event operators in LRT are projections (PVMs)

**The Eigenvalue Restriction Lemma:** If the action primitive A is Boolean (A : D -> {0,1}), then every event operator representing an actualization predicate is a projection operator.

---

## 4. Why POVM Elements Are Excluded

### 4.1 The Structure of POVMs

A POVM (Positive Operator-Valued Measure) is a collection $\{E_k\}$ of positive operators satisfying $\sum_k E_k = I$.

Unlike PVM elements:
- POVM elements $E_k$ need not satisfy $E_k^2 = E_k$
- Eigenvalues of $E_k$ can be any value in $[0,1]$
- $E_k$ need not be orthogonal to each other

### 4.2 The L<sub>3</sub> Argument Against Primitive POVMs

Consider a POVM element $E$ with eigenvalue $\lambda \in (0,1)$ and corresponding eigenstate $\lvert\phi\rangle$.

**The problematic question:** Is event E actual for system in state $\lvert\phi\rangle$?

The formalism gives:
$$\langle\phi\lvert E\lvert\phi\rangle = \lambda \in (0,1)$$

This $\lambda$ cannot be interpreted as A's output:
- If $\lambda$ were the actualization value, then $A_{\text{event}}(E, \phi) = \lambda \in (0,1)$
- But A is Boolean: outputs only in $\{0,1\}$
- Contradiction

**Resolution options:**

**(a) lambda is a probability, not an actualization value:**
This works: $\lambda$ represents $p(E\lvert\phi)$, the probability of E given state $\lvert\phi\rangle$. But then E is not a predicate about the actual configuration: it is a statistical summary of possible outcomes.

**(b) The eigenstate condition is unphysical:**
Perhaps $\lvert\phi\rangle$ (eigenstate of non-projection $E$) cannot be an L<sub>3</sub>-admissible configuration. Then $\lvert\phi\rangle \notin A_\Omega$, and the problematic case doesn't arise.

Both resolutions confirm: POVM elements with $\lambda \in (0,1)$ cannot serve as primitive event operators in LRT. They encode probability information, not actualization predicates.

### 4.3 Naimark Dilation: POVMs as Derived Structure

The Naimark dilation theorem states: every POVM on $\mathcal{H}$ arises as the reduction of a PVM on a larger Hilbert space $\mathcal{H} \otimes \mathcal{K}$.

Explicitly: for POVM $\{E_k\}$ on $\mathcal{H}$, there exist:
- An ancillary space $\mathcal{K}$
- A PVM $\{P_k\}$ on $\mathcal{H} \otimes \mathcal{K}$

such that:
$$E_k = \text{Tr}_{\mathcal{K}}[P_k]$$

**LRT's interpretation:** POVMs describe measurements where the full system (including apparatus) has PVM structure, but the subsystem of interest shows effective POVM statistics after tracing out the environment. The fundamental events are still PVM (projection-valued); POVMs are epistemic reductions.

This is fully compatible with LRT's ontology:
- Ontologically: all events are PVM (Boolean actualization)
- Epistemically: partial access to composite systems yields POVM statistics
- No fundamental POVM elements required

---

## 5. Addressing Potential Objections

### 5.1 "Measurement outcomes can be non-Boolean"

**Objection:** Real measurements have finite precision. Outcomes are not perfectly 0 or 1 but 0.0001 or 0.9998.

**Response:** This is epistemic imprecision, not ontological indeterminacy. The detector either clicked or didn't (Boolean). Our *knowledge* of whether it clicked may be imperfect, but the *fact* of the click is Boolean. LRT's A operates at the ontological level. Measurement noise is a separate, epistemological concern.

### 5.2 "Quantum logic doesn't require classical logic"

**Objection:** Quantum logic (Birkhoff-von Neumann) replaces distributivity with a weaker lattice structure. LRT's L<sub>3</sub> imposes classical logic where quantum logic would be more appropriate.

**Response:** LRT applies L<sub>3</sub> at the **vehicle level**: completed measurement records, not at the content level (quantum state superpositions). At the vehicle level, every record is Boolean: the pointer is at position x or it isn't. Quantum logic describes relationships among propositions in $I_\infty$; L<sub>3</sub> constrains the structure of $A_\Omega$. No conflict.

### 5.3 "Weak measurements violate the Boolean assumption"

**Objection:** Weak measurements yield continuous outcomes, not discrete eigenvalues. This seems incompatible with Boolean A.

**Response:** Weak measurement outcomes are statistical averages over many runs, each of which involves a Boolean actualization (the detector clicked or didn't, the spin flipped or didn't). The continuous outcome is an ensemble property. Individual actualization events remain Boolean.

---

## 6. Formal Summary

**Theorem (Eigenvalue Restriction):** In Logic Realism Theory, every event operator on $\mathcal{H}$ representing an actualization predicate is a projection operator.

**Proof outline:**

1. $A : D \to \{0,1\}$ (definition of action primitive)
2. Actualization events have Boolean truth values (from L<sub>3</sub>'s Excluded Middle)
3. Measurement outcomes correspond to actualization values (actualization interpretation)
4. Measurement outcomes are eigenvalues of event operators (spectral theorem)
5. Therefore eigenvalues of event operators $\in \{0,1\}$
6. Self-adjoint operators with spectrum $\subseteq \{0,1\}$ are projections (characterization lemma)
7. Therefore event operators are projections $\square$

**Corollary:** POVMs arise in LRT only as derived structure (via Naimark dilation), not as fundamental event operators.

---

## 7. Epistemic Status and Remaining Work

**Status:** ARGUED

The argument is complete as a philosophical derivation. The chain from L<sub>3</sub> to Boolean actualization to eigenvalue restriction to projection operators is logically valid.

**Remaining for ESTABLISHED:**
- Lean 4 formalization of the characterization lemma
- Explicit treatment of unbounded observables (the argument uses bounded operators; extension to unbounded self-adjoint operators is straightforward via spectral theory but should be verified)

**Dependency check:** This argument does not presuppose Step 3 (local tomography) or Step 4 (Hilbert space). It applies to *any* event-based quantum theory with Boolean actualization. The Hilbert space context is imported for definiteness, but the core argument (Boolean to projection) is algebraic.

---

## 8. Connection to Core Derivation

This supplement addresses **Critical Conjecture 2** from the Core Derivation (Step 5).

With this argument:
- Step 5 (PVM structure) is elevated from CONJECTURED to ARGUED
- Step 6 (Gleason's theorem) applies unconditionally to the PVM structure
- Step 7 (Born rule) inherits ARGUED status from Step 3 only, not from Step 5

The Core Derivation's epistemic summary should be updated:
- ESTABLISHED: 8
- ARGUED: 4 (was 3; Step 5 now ARGUED)
- CONJECTURED: 1 (was 2; Step 5 resolved)
- PARTIALLY ARGUED: 1

---

## 9. Relation to Other Supplements

### 9.1 Dependency on S1

S3 requires that "A selects outcome O" is a physical proposition. S1 (PPC Derivation) ensures this: A's selection has an operational signature (the measurement outcome itself).

### 9.2 Relation to S2

S2 establishes local tomography (Step 3), which provides Hilbert space structure (Step 4). S3 operates within this Hilbert space to establish PVM structure. The two supplements are independent in their core arguments but sequential in the derivation chain.

### 9.3 Connection to S4

S3 establishes event structure; S4 (Debreu-Nachbin) establishes time structure. Both feed into the dynamics derivation (Steps 11-13).

---

## References

Anandan, J. (1991). A geometric approach to quantum mechanics. *Foundations of Physics*, 21, 1265-1284.

Birkhoff, G., and von Neumann, J. (1936). The logic of quantum mechanics. *Annals of Mathematics*, 37(4), 823-843.

Busch, P. (2003). Quantum states and generalized observables: A simple proof of Gleason's theorem. *Physical Review Letters*, 91(12), 120403.

Naimark, M. A. (1943). Positive definite operator functions on a commutative group. *Izvestiya Rossiiskoi Akademii Nauk. Seriya Matematicheskaya*, 7(5), 237-244.

---

*Supplement S3 | Logic Realism Theory Project | 2026-03-13*
