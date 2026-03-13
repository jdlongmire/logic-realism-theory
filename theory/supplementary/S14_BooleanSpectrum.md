# S14: Boolean Spectrum — Deriving Eigenvalue Restriction from Actualization Semantics

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Supports:** Step 5 (Eigenvalue Restriction / PVM Structure)
**Addresses:** The boolean_spectrum placeholder in Lean formalization; grounds P² = P from actualization semantics

---

## Abstract

This supplement derives the Boolean spectrum constraint — that actualization operators have eigenvalues in $\{0,1\}$ only — directly from the semantics of actualization within Logic Realism Theory. While S3 established this result via the formal structure of the action primitive $\mathbf{A}$, this supplement provides the deeper semantic grounding: why actualization must be Boolean in the first place. The derivation proceeds through four stages: (1) analyzing what "actualization" means as selection from $I_\infty$ into $A_\Omega$, (2) showing that partial actualization is semantically incoherent under L<sub>3</sub>, (3) connecting this to the mathematical characterization of projection operators, and (4) establishing the idempotent condition $P^2 = P$ as the algebraic expression of actualization semantics. This grounds the `boolean_spectrum` axiom and provides the prose derivation connecting actualization to projection-valued measures.

---

## 1. The Problem

### 1.1 What Needs Grounding

The Lean formalization in Step 5 includes the structure:

```lean
theorem boolean_spectrum (P : EventOperator) :
  ∀ λ ∈ spectrum P, λ = 0 ∨ λ = 1
```

S3 established this formally via the chain:

$$\mathbf{A} : D \to \{0,1\} \implies \text{eigenvalues} \in \{0,1\} \implies P^2 = P$$

This supplement addresses a deeper question: **why must actualization be Boolean?** The answer lies in the semantics of what it means for a configuration to be "actual" versus "not actual."

### 1.2 The Semantic Question

The action primitive $\mathbf{A}$ is defined as:

$$\mathbf{A} : D \to \{0,1\}$$

where $D = L_3(I_\infty)$ is the domain of L<sub>3</sub>-admissible configurations.

But this definition invites the question: why $\{0,1\}$ rather than $[0,1]$? Could there be "degrees of actualization"? Could a configuration be "70% actual"?

This supplement shows that such intermediate actualization is semantically incoherent — not merely excluded by definition, but excluded by the meaning of "actual" under L<sub>3</sub>.

### 1.3 Relation to S3

S3 (Eigenvalue Restriction) provides the formal argument connecting Boolean $\mathbf{A}$ to projection operators. This supplement (S14) provides the semantic grounding for why $\mathbf{A}$ must be Boolean, making the S3 argument non-circular.

The dependency is:

$$\text{S14 (actualization semantics)} \to \text{S3 (eigenvalue restriction)} \to \text{Step 5 (PVM structure)}$$

---

## 2. The Semantics of Actualization

### 2.1 Actualization as Selection

In LRT, actualization is the primitive operation that selects which configurations from $I_\infty$ are instantiated in $A_\Omega$. This is not a physical process occurring within $A_\Omega$; it is the primitive dynamic aspect of $\mathbf{X} \equiv [L_3 : I_\infty : \mathbf{A}]$.

The core equation:

$$A_\Omega = L_3(I_\infty)$$

states that $A_\Omega$ is the L<sub>3</sub>-admissible subset of $I_\infty$. For any configuration $c \in I_\infty$:

- If $c$ satisfies L<sub>3</sub>, then $c \in A_\Omega$ (c is actualized)
- If $c$ violates L<sub>3</sub>, then $c \notin A_\Omega$ (c is not actualized)

There is no third option within L<sub>3</sub>: by Excluded Middle, either $c \in A_\Omega$ or $c \notin A_\Omega$.

### 2.2 What "Actual" Means

**Definition (Actualization):** A configuration $c$ is *actual* if and only if $c \in A_\Omega$.

This is a binary predicate. Being actual is not a matter of degree. The question "Is c actual?" admits only two answers: yes or no.

**Why no degrees?** Consider what "70% actual" would mean:

1. The configuration $c$ has partial membership in $A_\Omega$
2. There is a "degree" to which $c$ is instantiated
3. $c$ is neither fully in $A_\Omega$ nor fully outside it

Each of these interpretations violates L<sub>3</sub>:

**(1) Partial membership:** Sets do not admit partial membership. Either $c \in A_\Omega$ or $c \notin A_\Omega$. Fuzzy set theory allows degrees of membership, but L<sub>3</sub> is not fuzzy: Identity, Non-Contradiction, and Excluded Middle require classical set membership.

**(2) Degrees of instantiation:** Instantiation is the relation between a configuration and actuality. If this relation admitted degrees, then for some degree $d$, we would have:
- $c$ is instantiated to degree $d$
- $c$ is not (fully) instantiated

But then: is the state of affairs "c is instantiated to degree d" itself actual or not? This meta-question must have a determinate answer (Excluded Middle). If we say "partially actual," we have an infinite regress. The regress terminates only when we reach a level at which actualization is binary.

**(3) Neither in nor out:** This directly violates Excluded Middle. For any well-formed proposition P about $c$'s membership in $A_\Omega$, either P or $\neg P$.

*[Epistemic Status: ARGUED — depends on L<sub>3</sub> as constitutive]*

### 2.3 The Determinate/Indeterminate Dichotomy

A configuration $c$ is either:

- **Determinate:** $c$ has a fixed position in $I_\infty$, satisfies L<sub>3</sub>, and is (or is not) in $A_\Omega$
- **Indeterminate:** $c$ lacks determinate identity and thus is not a configuration at all

There is no middle ground of "partially determinate." A configuration with partial determinacy would violate Identity: it would not be fully self-identical.

This dichotomy maps directly onto the $\{0,1\}$ codomain of $\mathbf{A}$:

| State | Meaning | $\mathbf{A}$ value |
|-------|---------|-------------------|
| Actualized | $c \in A_\Omega$ | 1 |
| Not actualized | $c \notin A_\Omega$ | 0 |
| Partially actualized | (Incoherent) | — |

---

## 3. From Boolean Actualization to Boolean Spectrum

### 3.1 Event Predicates and Actualization

An **event predicate** is a proposition of the form "system S has property P" or "measurement M yields outcome O."

In quantum mechanics, event predicates are represented by operators on Hilbert space. The question: what operators can represent actualization predicates?

**Claim:** If $\hat{E}$ represents an actualization predicate, then $\hat{E}$ must have Boolean spectrum.

### 3.2 The Argument

**Step 1: Actualization predicates have Boolean truth values.**

An actualization predicate concerns whether some event is actual. By §2, actualization is binary: either the event is actual (truth value 1) or it is not (truth value 0).

**Step 2: Measurement outcomes correspond to truth values.**

When we measure $\hat{E}$, we ask: "Is the event E actual?" The measurement outcome is the answer to this question.

By the spectral theorem, measuring a self-adjoint operator yields one of its eigenvalues. The eigenvalue obtained is the answer to the actualization question.

**Step 3: Eigenvalues must be in $\{0,1\}$.**

If $\hat{E}$ represents an actualization predicate:
- Outcome $\lambda = 1$ means "E is actual"
- Outcome $\lambda = 0$ means "E is not actual"

No other eigenvalue makes semantic sense:
- $\lambda = 0.7$ would mean "E is 70% actual" — incoherent (§2.2)
- $\lambda = -1$ would mean... what? Negative actualization?
- $\lambda = 2$ would mean... super-actualization?

Only $\{0,1\}$ corresponds to the binary truth values that actualization predicates can have.

**Step 4: Therefore the spectrum of $\hat{E}$ is contained in $\{0,1\}$.**

*[Epistemic Status: ARGUED — depends on the semantic analysis of §2]*

### 3.3 The Semantic Grounding

This argument does not merely assert that $\mathbf{A}$ has Boolean codomain. It explains **why** the codomain must be Boolean:

1. Actualization is the selection of configurations into $A_\Omega$
2. Selection into a set is a binary operation (in or out)
3. L<sub>3</sub> (specifically Excluded Middle) requires binary set membership
4. Therefore actualization values are in $\{0,1\}$

The Boolean spectrum is not an arbitrary choice but a necessary consequence of what actualization means under L<sub>3</sub>.

---

## 4. The Idempotent Condition: P² = P

### 4.1 Characterization of Boolean-Spectrum Operators

**Lemma (from S3):** A bounded self-adjoint operator $P$ on a Hilbert space has spectrum contained in $\{0,1\}$ if and only if $P = P^2$.

*Proof sketch:*

$(\Rightarrow)$ If spec$(P) \subseteq \{0,1\}$, then by the spectral theorem:
$$P = 0 \cdot E_0 + 1 \cdot E_1 = E_1$$
where $E_0$, $E_1$ are the spectral projections. Since $E_1^2 = E_1$ (spectral projections are idempotent), we have $P^2 = P$.

$(\Leftarrow)$ If $P^2 = P$, then for any eigenvalue $\lambda$ with eigenvector $|\phi\rangle$:
$$P^2|\phi\rangle = \lambda^2|\phi\rangle = P|\phi\rangle = \lambda|\phi\rangle$$
Therefore $\lambda^2 = \lambda$, giving $\lambda(\lambda - 1) = 0$, hence $\lambda \in \{0,1\}$. $\square$

### 4.2 Semantic Interpretation of Idempotence

The condition $P^2 = P$ has a direct semantic interpretation in terms of actualization:

**Idempotence as "actualization is stable":**

Consider applying the actualization check twice:
- First application: Is E actual? Answer: $P|\psi\rangle$
- Second application: Is "E being actual" actual? Answer: $P(P|\psi\rangle) = P^2|\psi\rangle$

If actualization is a genuine binary property, then asking "is it actual that E is actual?" should give the same answer as "is E actual?" There is no meta-level of actualization beyond the first level.

Formally: $P^2 = P$ says that the actualization operator is a fixed point under self-composition. Once you've determined that E is actual, re-determining adds nothing. This is exactly what we expect from a binary property.

**Contrast with non-idempotent operators:**

A general positive operator $E$ with $E^2 \neq E$ would have:
- First check: $E|\psi\rangle$ gives some state
- Second check: $E^2|\psi\rangle \neq E|\psi\rangle$

This would mean that repeated actualization checks give different results — incompatible with actualization being a determinate property.

### 4.3 Connection to Projection Operators

Operators satisfying $P^2 = P$ (idempotent) and $P = P^{\dagger}$ (self-adjoint) are precisely the **orthogonal projection operators**.

Projection operators:
- Project onto a closed subspace of $\mathcal{H}$
- Divide $\mathcal{H}$ into "yes" eigenspace (eigenvalue 1) and "no" eigenspace (eigenvalue 0)
- Represent sharp yes/no questions about the system

This is the algebraic characterization of Boolean actualization predicates: they are projection operators.

---

## 5. From Projections to PVMs

### 5.1 Complete Measurements

A **complete measurement** determines the outcome for a collection of mutually exclusive, exhaustive events. If $\{E_1, E_2, \ldots, E_n\}$ are the possible outcomes:

- Mutual exclusivity: At most one $E_i$ is actual
- Exhaustiveness: At least one $E_i$ is actual

By L<sub>3</sub> (specifically Non-Contradiction and Excluded Middle), exactly one $E_i$ is actual.

### 5.2 PVM Structure

Let $\{P_1, P_2, \ldots, P_n\}$ be the projection operators representing $\{E_1, \ldots, E_n\}$.

**Mutual exclusivity (Non-Contradiction):** If $E_i$ and $E_j$ are mutually exclusive, then:
$$P_i P_j = 0 \quad \text{for } i \neq j$$

*Why:* If both $E_i$ and $E_j$ could be actual simultaneously, we would have $\mathbf{A}(E_i) = 1$ and $\mathbf{A}(E_j) = 1$ for the same configuration. But the events are mutually exclusive — this is a contradiction. Therefore no state can yield outcome 1 for both projections, which means $P_i P_j = 0$.

**Exhaustiveness (Excluded Middle):** If the $\{E_i\}$ exhaust all possibilities:
$$\sum_{i=1}^n P_i = I$$

*Why:* For any state $|\psi\rangle$, exactly one outcome must be actual. The probabilities must sum to 1 for any state. By the Born rule (Step 7), $\langle\psi|P_i|\psi\rangle$ gives the probability of outcome $E_i$. Summing:
$$\sum_i \langle\psi|P_i|\psi\rangle = 1 \quad \text{for all } |\psi\rangle$$

This holds for all $|\psi\rangle$ iff $\sum_i P_i = I$.

### 5.3 Definition of PVM

A **Projection-Valued Measure (PVM)** is a collection of projection operators $\{P_i\}$ satisfying:
1. $P_i^2 = P_i$ for all $i$ (idempotence)
2. $P_i P_j = 0$ for $i \neq j$ (orthogonality)
3. $\sum_i P_i = I$ (completeness)

This structure follows directly from:
1. Boolean actualization (§2-3) $\Rightarrow$ idempotence
2. Non-Contradiction $\Rightarrow$ orthogonality
3. Excluded Middle $\Rightarrow$ completeness

*[Epistemic Status: ARGUED — depends on L<sub>3</sub> semantics of actualization]*

---

## 6. Why Not POVMs at the Fundamental Level?

### 6.1 The POVM Alternative

A **Positive Operator-Valued Measure (POVM)** is a collection of positive operators $\{E_i\}$ satisfying:
1. $E_i \geq 0$ (positivity)
2. $\sum_i E_i = I$ (completeness)

POVMs do not require:
- Idempotence ($E_i^2 = E_i$ may fail)
- Orthogonality ($E_i E_j = 0$ may fail for $i \neq j$)

POVMs describe general quantum measurements including noisy, coarse-grained, and approximate measurements.

### 6.2 Why POVMs Cannot Be Fundamental Under L<sub>3</sub>

**Claim:** POVM elements with eigenvalues in $(0,1)$ cannot represent fundamental actualization predicates.

**Argument:**

Consider a POVM element $E$ with eigenvalue $\lambda \in (0,1)$ and eigenstate $|\phi\rangle$.

Measuring $E$ on $|\phi\rangle$ gives:
$$\langle\phi|E|\phi\rangle = \lambda$$

What does this mean for the actualization question "Is E actual?"

Option 1: $\lambda$ is an actualization value
- Then $\mathbf{A}(E, \phi) = \lambda \in (0,1)$
- But $\mathbf{A}$ has codomain $\{0,1\}$ (§2)
- Contradiction

Option 2: $\lambda$ is a probability
- Then $\lambda = p(E|\phi)$ is the probability of E being actual
- But $|\phi\rangle$ is an eigenstate of $E$ — what does "probability" mean for an eigenstate?
- For projections, $P|\phi\rangle = \lambda|\phi\rangle$ with $\lambda \in \{0,1\}$ gives certainty
- For POVM elements, $E|\phi\rangle = \lambda|\phi\rangle$ with $\lambda \in (0,1)$ gives... partial certainty?

The issue: eigenstates of projections have determinate outcomes. Eigenstates of non-projection POVM elements do not have determinate outcomes in the same sense.

**Resolution:** POVMs describe effective statistics when:
- The system is entangled with an environment
- The full system-plus-environment has PVM structure
- The POVM arises by tracing out the environment

This is the Naimark dilation: every POVM on $\mathcal{H}$ arises from a PVM on an extended space $\mathcal{H} \otimes \mathcal{K}$.

Under LRT, the fundamental events are always PVM (Boolean actualization). POVMs are epistemic descriptions of our partial access to a larger PVM structure.

*[Epistemic Status: ARGUED — depends on actualization semantics]*

---

## 7. Formal Statement for Lean

### 7.1 The Grounding Result

The Lean theorem:

```lean
theorem boolean_spectrum (P : EventOperator) :
  ∀ λ ∈ spectrum P, λ = 0 ∨ λ = 1
```

is grounded by the following derivation chain:

| Step | Content | Epistemic Status |
|------|---------|------------------|
| 1 | Actualization is selection into $A_\Omega$ | ESTABLISHED (definition) |
| 2 | Selection into a set is binary (L<sub>3</sub>) | ESTABLISHED |
| 3 | Binary actualization ⇒ Boolean truth values | ARGUED |
| 4 | Truth values = eigenvalues (spectral theorem) | ESTABLISHED |
| 5 | Therefore eigenvalues in $\{0,1\}$ | ARGUED |
| 6 | Spectrum $\subseteq \{0,1\}$ ⇔ $P^2 = P$ | ESTABLISHED |

### 7.2 Tier Classification

The `boolean_spectrum` property is:

- **Not Tier 1:** It is not a primitive assumption about L<sub>3</sub> or $I_\infty$
- **Tier 2:** It is derived from the L<sub>3</sub> framework via actualization semantics
- **Confidence:** HIGH — depends on L<sub>3</sub>'s constitutive status (a core LRT commitment)

### 7.3 Relation to S3

S3 provides the **formal** argument: $\mathbf{A} : D \to \{0,1\}$ ⇒ eigenvalue restriction.

S14 provides the **semantic** argument: why $\mathbf{A}$ must have Boolean codomain in the first place.

The two supplements are complementary:
- S3 answers: Given Boolean $\mathbf{A}$, why are eigenvalues in $\{0,1\}$?
- S14 answers: Why is $\mathbf{A}$ Boolean?

Together they close the gap from L<sub>3</sub> to PVM structure.

---

## 8. Connection to Other Steps

### 8.1 Upstream Dependencies

| Dependency | Source | Status |
|------------|--------|--------|
| L<sub>3</sub> (Excluded Middle) | Step 0 / X | ESTABLISHED |
| $A_\Omega = L_3(I_\infty)$ | Step 1 | ESTABLISHED |
| Determinate Identity | Step 2 | ESTABLISHED |
| Physical Proposition Criterion | S1 | ARGUED |

### 8.2 Downstream Consumers

| Consumer | How Used |
|----------|----------|
| Step 5 (PVM structure) | Boolean spectrum ⇒ projections ⇒ PVMs |
| Step 6 (Frame function) | PVMs define frame functions on $\mathcal{H}$ |
| Step 7 (Gleason/Born) | Unique probability measure on PVM structure |

### 8.3 Related Supplements

- **S1 (PPC Derivation):** Establishes that actualization events are physical propositions
- **S3 (Eigenvalue Restriction):** Formal version of the boolean_spectrum argument
- **S12 (Product Effects):** Uses PVM structure for composite systems

---

## 9. Open Questions

### 9.1 Unbounded Observables

The argument uses bounded self-adjoint operators. For unbounded observables (position, momentum):

- The spectral theorem still applies (via spectral measures)
- Projection-valued spectral measures decompose $\mathcal{H}$
- Each spectral projection has Boolean spectrum

The extension is straightforward but should be made explicit in the Lean formalization.

**Status:** OPEN — extension to unbounded case needed for full treatment.

### 9.2 Superselection Rules

Are there physical constraints that restrict which projections represent actual events?

Superselection rules (charge, mass, spin statistics) impose constraints on admissible observables. Under LRT, superselection would arise from L<sub>3</sub> constraints on which propositions are well-formed.

**Status:** OPEN — superselection within LRT not developed.

### 9.3 Continuous Spectra

For observables with continuous spectra (position, momentum), the projection-valued measure is a measure on the real line rather than a discrete sum.

The actualization interpretation: "Is the particle in region $\Delta$?" is a Boolean question. The projection $P_\Delta$ (onto states supported in $\Delta$) has Boolean spectrum. The continuous spectrum of the position operator $\hat{x}$ is not a violation of boolean_spectrum; it is a collection of infinitely many Boolean questions indexed by regions.

**Status:** ADDRESSED — continuous spectra compatible with Boolean actualization.

---

## 10. Summary

| Section | Content | Status |
|---------|---------|--------|
| §2 | Actualization is binary (L<sub>3</sub> semantics) | ARGUED |
| §3 | Boolean actualization ⇒ eigenvalues in $\{0,1\}$ | ARGUED |
| §4 | Eigenvalues in $\{0,1\}$ ⇔ $P^2 = P$ | ESTABLISHED |
| §5 | Projections + L<sub>3</sub> ⇒ PVM structure | ARGUED |
| §6 | POVMs derived, not fundamental | ARGUED |

The Boolean spectrum constraint is not an arbitrary choice but a necessary consequence of actualization semantics under L<sub>3</sub>:

$$L_3 \to \text{Binary set membership} \to \text{Binary actualization} \to \text{Boolean truth values}$$

$$\text{Boolean truth values} \to \text{Eigenvalues in } \{0,1\} \to P^2 = P \to \text{Projections}$$

$$\text{Projections} + \text{Non-Contradiction} + \text{Excluded Middle} \to \text{PVM structure}$$

The `boolean_spectrum` axiom in the Lean formalization is thereby grounded in the semantics of what it means for a configuration to be actual under L<sub>3</sub>.

---

## References

Birkhoff, G., and von Neumann, J. (1936). The logic of quantum mechanics. *Annals of Mathematics*, 37(4), 823-843.

Busch, P. (2003). Quantum states and generalized observables: A simple proof of Gleason's theorem. *Physical Review Letters*, 91(12), 120403.

Naimark, M. A. (1943). Positive definite operator functions on a commutative group. *Izvestiya Rossiiskoi Akademii Nauk. Seriya Matematicheskaya*, 7(5), 237-244.

Reed, M. and Simon, B. (1980). *Methods of Modern Mathematical Physics I: Functional Analysis*. Academic Press.

---

*Supplement S14 | Logic Realism Theory Project | 2026-03-13*
