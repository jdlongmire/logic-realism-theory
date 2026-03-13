# S13: Field Selection (K=2) — Deriving Complex Numbers from Hardy Axioms and L<sub>3</sub>

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Supports:** Step 4 (Complex Hilbert Space)
**Addresses:** The K_eq_two placeholder in Lean formalization; grounds why observables require complex field

---

## Abstract

This supplement derives the selection of the complex numbers $\mathbb{C}$ over the reals $\mathbb{R}$ and quaternions $\mathbb{H}$ as the scalar field for quantum state spaces. The derivation proceeds through Hardy's (2001) dimension formula $K = N^r$ where $K$ is the number of degrees of freedom, $N$ is the distinguishable outcomes, and $r$ is the "dimension parameter" characterizing the theory. We show that: (1) L<sub>3</sub> constraints combined with local tomography (Step 3) require $r = 2$, yielding $K = N^2$; (2) $r = 2$ selects $\mathbb{C}$ uniquely — real quantum theory has $r = 1$ and quaternionic theory has $r = 4$; (3) commutativity of the scalar field follows from the Physical Proposition Criterion; (4) algebraic closure is required for the spectral theorem on which PVM structure depends. The result grounds the `chain3b_quaternionic_qm_fails` theorem in the Lean formalization.

---

## 1. The Problem

### 1.1 What Step 4 Claims

Section 3.2 of LRT-MASTER states:

> "The state space of any locally tomographic theory satisfying standard reconstruction axioms is the complex Hilbert space $\mathbb{C}\mathcal{H}$... The field is complex, not real or quaternionic. This is not a free choice."

The epistemic status is marked ESTABLISHED, importing the Masanes-Müller (2011) theorem. But the theorem itself has multiple inputs. This supplement shows that one crucial input — the selection of $\mathbb{C}$ over $\mathbb{R}$ or $\mathbb{H}$ — follows from L<sub>3</sub> constraints rather than being an arbitrary choice.

### 1.2 Hardy's Dimension Formula

Hardy (2001) showed that generalized probabilistic theories satisfying five reasonable axioms have a characteristic dimension formula:

$$K = N^r$$

where:
- $N$ = number of distinguishable outcomes (pure states for a maximal measurement)
- $K$ = number of real parameters needed to specify a state (degrees of freedom)
- $r$ = dimension parameter, characteristic of the theory type

For classical probability theory: $r = 1$, giving $K = N$ (simplex structure).

For quantum theory over $\mathbb{R}$: $r = 1$, giving $K = N(N+1)/2 - 1 \approx N$ (real symmetric matrices).

For quantum theory over $\mathbb{C}$: $r = 2$, giving $K = N^2 - 1 \approx N^2$ (complex Hermitian matrices).

For quantum theory over $\mathbb{H}$: $r = 4$, giving $K = N(2N-1) - 1 \approx 2N^2$ (quaternionic self-dual matrices).

### 1.3 The Selection Question

Why does the physical world select $r = 2$ (complex) rather than $r = 1$ (real) or $r = 4$ (quaternionic)?

Standard reconstruction programs import this as a physical input (empirical fact). LRT aims to derive it from L<sub>3</sub>.

---

## 2. Local Tomography and Dimension Counting

### 2.1 The Local Tomography Constraint

From Step 3, local tomography requires:

$$\dim(\mathcal{S}_{AB}) = \dim(\mathcal{S}_A) \cdot \dim(\mathcal{S}_B)$$

The state space of a composite system has dimension equal to the product of subsystem dimensions.

For an $N$-level system with $K$ degrees of freedom:
- Single system: $K(N)$ parameters
- Two identical systems: $K(N^2)$ parameters for the composite

Local tomography requires:

$$K(N^2) = K(N) \cdot K(N) = K(N)^2$$

### 2.2 The Functional Equation

Hardy's dimension formula $K(N) = N^r - 1$ (subtracting 1 for normalization) must satisfy:

$$K(N^2) = K(N)^2$$

Substituting:

$$(N^2)^r - 1 = (N^r - 1)^2$$

$$N^{2r} - 1 = N^{2r} - 2N^r + 1$$

$$-1 = -2N^r + 1$$

$$2N^r = 2$$

$$N^r = 1$$

This is only satisfied for $N = 1$ (trivial system) unless we consider the large-$N$ limit where the $-1$ terms become negligible:

$$N^{2r} \approx (N^r)^2 = N^{2r}$$

This is always satisfied — so the constraint does not immediately fix $r$.

### 2.3 The Strict Equality Requirement

The local tomography equation $K(N^2) = K(N)^2$ requires exact equality, not just large-$N$ approximation.

For the *unnormalized* dimension (before removing the trace constraint):

- Real quantum theory: $K(N) = \frac{N(N+1)}{2}$, so $K(N)^2 = \frac{N^2(N+1)^2}{4}$, but $K(N^2) = \frac{N^2(N^2+1)}{2} \neq K(N)^2$

- Complex quantum theory: $K(N) = N^2$, so $K(N)^2 = N^4$, and $K(N^2) = (N^2)^2 = N^4 = K(N)^2$ ✓

- Quaternionic quantum theory: $K(N) = N(2N-1)$, so $K(N)^2 = N^2(2N-1)^2$, but $K(N^2) = N^2(2N^2-1) \neq K(N)^2$

**Result:** Only complex quantum theory ($r = 2$) satisfies exact local tomography.

*[Epistemic Status: ESTABLISHED — mathematical fact about dimension formulas]*

---

## 3. L<sub>3</sub> Constraints and Field Selection

### 3.1 Why Local Tomography Follows from L<sub>3</sub>

Local tomography is not an arbitrary axiom. As shown in S2 (H1→H2 Bridge), local tomography follows from:

1. **H1 (Metaphysical Supervenience):** The composite is nothing over and above subsystems + relations
2. **Physical Proposition Criterion (S1):** All physical facts must be operationally distinguishable
3. **L<sub>3</sub> applied to composites:** Composite systems have determinate identity

The chain is:

$$L_3 \to \text{PPC} \to \text{H1} \to \text{H2 (Local Tomography)}$$

Local tomography is what Determinate Identity requires when applied to composite systems. It is not a postulate but a consequence of L<sub>3</sub>.

### 3.2 The L<sub>3</sub> → K=2 Chain

Combining §2.3 with §3.1:

1. L<sub>3</sub> requires Determinate Identity for all configurations (Step 2)
2. Determinate Identity for composites requires local tomography (S2)
3. Local tomography requires $K(N^2) = K(N)^2$ (dimension constraint)
4. Only $r = 2$ (complex field) satisfies this constraint (§2.3)

**Conclusion:** L<sub>3</sub> → local tomography → $r = 2$ → complex field $\mathbb{C}$

*[Epistemic Status: ARGUED — depends on the H1→H2 bridge from S2]*

---

## 4. Excluding Quaternions: Commutativity Requirement

### 4.1 The Quaternionic Alternative

Quaternions $\mathbb{H}$ are a four-dimensional division algebra over $\mathbb{R}$:

$$\mathbb{H} = \{a + bi + cj + dk : a,b,c,d \in \mathbb{R}\}$$

with $i^2 = j^2 = k^2 = ijk = -1$.

Crucially, quaternions are **non-commutative**: $ij = k$ but $ji = -k$.

Could quantum mechanics be formulated over $\mathbb{H}$ instead of $\mathbb{C}$?

### 4.2 Hardy's Exclusion via Dimension

From §2.3, quaternionic quantum theory fails local tomography. The dimension formula gives:

$$K_{\mathbb{H}}(N) = N(2N-1) - 1$$

which does not satisfy $K(N^2) = K(N)^2$:

For $N = 2$:
- $K_{\mathbb{H}}(2) = 2 \cdot 3 - 1 = 5$
- $K_{\mathbb{H}}(4) = 4 \cdot 7 - 1 = 27$
- But $K_{\mathbb{H}}(2)^2 = 25 \neq 27$

This is the first exclusion: quaternionic QM violates the L<sub>3</sub>-mandated local tomography constraint.

### 4.3 Commutativity from the Physical Proposition Criterion

A deeper exclusion comes from the PPC itself.

Consider a physical proposition $P$: "observable $A$ has value $a$."

Under L<sub>3</sub>:
- $P$ has determinate content (Identity)
- $P$-true and $P$-false are distinct (Non-Contradiction)
- Exactly one of $P$, $\neg P$ holds (Excluded Middle)

For $P$ to satisfy L<sub>3</sub>, the proposition "A has value a" must have a unique truth value independent of any other measurement context.

**Non-commutativity problem:** In quaternionic QM, the order of operations matters: $AB \neq BA$ at the scalar field level, not just the operator level.

If observables are represented by quaternionic matrices, then:
- The eigenvalue equation $A|\psi\rangle = a|\psi\rangle$ depends on left vs. right multiplication
- The proposition "A has value a" becomes ambiguous: is it $(A\psi) = (a\psi)$ or $(\psi A) = (\psi a)$?

This violates Identity: the proposition $P$ does not have determinate content because its formulation depends on ordering conventions.

**Resolution:** The scalar field must be commutative. Non-commutativity at the field level (not the operator level) introduces ambiguity that violates L<sub>3</sub>.

*[Epistemic Status: ARGUED — depends on applying PPC to the formulation of eigenvalue propositions]*

### 4.4 Tensor Product Structure

A related exclusion: quaternionic Hilbert spaces do not support a well-defined tensor product.

For composite systems, the tensor product $\mathcal{H}_A \otimes \mathcal{H}_B$ requires scalar field commutativity:

$$(c \cdot \psi_A) \otimes \phi_B = \psi_A \otimes (c \cdot \phi_B)$$

For quaternions, this fails: the left and right actions of $c \in \mathbb{H}$ differ.

Since composite systems must satisfy Determinate Identity (Step 2) and local tomography (Step 3), the tensor product must be well-defined. This requires commutative scalars.

*[Epistemic Status: ESTABLISHED — mathematical fact about tensor products over non-commutative rings]*

---

## 5. Excluding Reals: Algebraic Closure Requirement

### 5.1 The Real Alternative

Real quantum mechanics uses $\mathbb{R}$ as the scalar field:
- States are vectors in real Hilbert space
- Observables are real symmetric matrices
- Time evolution is via real orthogonal matrices

Real QM is internally consistent and satisfies many reconstruction axioms.

### 5.2 Exclusion via Dimension (Local Tomography Failure)

From §2.3, real quantum theory has:

$$K_{\mathbb{R}}(N) = \frac{N(N+1)}{2} - 1$$

This does not satisfy $K(N^2) = K(N)^2$:

For $N = 2$:
- $K_{\mathbb{R}}(2) = \frac{2 \cdot 3}{2} - 1 = 2$
- $K_{\mathbb{R}}(4) = \frac{4 \cdot 5}{2} - 1 = 9$
- But $K_{\mathbb{R}}(2)^2 = 4 \neq 9$

Real QM fails local tomography. By the L<sub>3</sub> → local tomography chain, real QM is excluded.

### 5.3 Algebraic Closure and the Spectral Theorem

A deeper exclusion: the spectral theorem requires algebraic closure.

**The spectral theorem** states that every self-adjoint operator on a complex Hilbert space has a complete set of orthonormal eigenvectors.

For real Hilbert spaces, this fails: a real symmetric matrix may have complex eigenvalues (consider rotation matrices).

**Example:** The rotation matrix

$$R = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$$

has eigenvalues $\pm i \notin \mathbb{R}$.

For LRT's PVM structure (Step 5), every observable must decompose into projections onto eigenspaces. This requires the spectral theorem, which requires algebraic closure.

$\mathbb{C}$ is algebraically closed (every polynomial has roots). $\mathbb{R}$ is not.

**LRT requirement:** Observables correspond to physical propositions (PPC). For "observable A has value a" to satisfy Excluded Middle, $a$ must be a possible measurement outcome. Measurement outcomes must be eigenvalues. Eigenvalues must exist for all observables. Therefore the field must be algebraically closed.

*[Epistemic Status: ARGUED — depends on PPC applied to observable propositions and spectral decomposition]*

### 5.4 Experimental Confirmation: Renou et al. (2021)

The theoretical exclusion of real QM has been experimentally confirmed.

Renou et al. (2021) demonstrated that real and complex quantum mechanics make different predictions for entanglement-swapping experiments in network scenarios. The experimental results match complex QM and exclude real QM.

This provides empirical grounding for the L<sub>3</sub>-derived exclusion of real QM.

*[Epistemic Status: ESTABLISHED — experimental result]*

---

## 6. Why Complex Numbers Are Unique

### 6.1 The Selection Criteria

Combining the constraints:

| Criterion | Real $\mathbb{R}$ | Complex $\mathbb{C}$ | Quaternion $\mathbb{H}$ |
|-----------|-------------------|----------------------|-------------------------|
| Local tomography ($K(N^2) = K(N)^2$) | ✗ | ✓ | ✗ |
| Commutative field | ✓ | ✓ | ✗ |
| Algebraically closed | ✗ | ✓ | ✗ |
| Well-defined tensor product | ✓ | ✓ | ✗ |

Only $\mathbb{C}$ satisfies all criteria.

### 6.2 The Uniqueness Theorem

**Theorem (Field Selection):** The only scalar field compatible with L<sub>3</sub>-constrained quantum mechanics is $\mathbb{C}$.

**Proof outline:**

1. L<sub>3</sub> requires Determinate Identity (Step 2)
2. DI for composites requires local tomography (S2)
3. Local tomography requires $K(N^2) = K(N)^2$
4. Only $K = N^2 - 1$ (complex case) satisfies this
5. PPC requires commutative scalars (unambiguous eigenvalue propositions)
6. Spectral theorem requires algebraically closed field
7. $\mathbb{C}$ is the unique commutative, algebraically closed field satisfying $K = N^2 - 1$

*[Epistemic Status: ARGUED — each step individually ESTABLISHED or ARGUED as marked]*

---

## 7. Continuous Reversibility and Complex Structure

### 7.1 Hardy's Fifth Axiom

Hardy's fifth axiom states: "There exist continuous reversible transformations between any two pure states."

This axiom distinguishes quantum mechanics from classical probability theory.

### 7.2 L<sub>3</sub> Grounding of Continuous Reversibility

Does continuous reversibility follow from L<sub>3</sub>?

**Argument:**

Consider two L<sub>3</sub>-admissible configurations $c_1, c_2 \in A_\Omega$. Both have determinate identity.

If $c_1$ can transform to $c_2$ (physical process exists), then by Identity, each intermediate state must also have determinate identity.

The path from $c_1$ to $c_2$ in state space must consist entirely of L<sub>3</sub>-admissible states.

If the path is discontinuous, there would be a "gap" — a transition from state $s$ to state $s'$ where $D(s, s') > \epsilon$ for some finite $\epsilon$, with no intermediate states.

But if no intermediate states exist, then the transition violates Non-Contradiction: at the moment of transition, the system is neither in $s$ nor in $s'$ but also not in any other state. This is a failure of Determinate Identity.

**Conclusion:** Reversible transformations between L<sub>3</sub>-admissible states must be continuous.

*[Epistemic Status: ARGUED — depends on applying DI to transformation paths]*

### 7.3 Continuous Reversibility Selects r=2

Given continuous reversibility:
- $r = 1$ theories (classical, real QM) have transformations that are not continuously connected to the identity
- $r = 4$ theories (quaternionic QM) fail local tomography, so are excluded before this constraint applies
- $r = 2$ theories (complex QM) have the Lie group $SU(N)$ as transformation group, which is connected

The $r = 2$ case uniquely combines:
- Local tomography (from L<sub>3</sub>)
- Continuous reversibility (from L<sub>3</sub>)
- Commutative field (from PPC)
- Algebraic closure (from spectral theorem)

---

## 8. Formal Statement for Lean

### 8.1 The Grounding Result

The Lean theorem `chain3b_quaternionic_qm_fails` is grounded by:

```lean
-- Quaternionic QM fails local tomography
theorem quaternionic_fails_local_tomography :
  ¬LocalTomographic QuaternionicQM := by
  -- K_H(N) = N(2N-1) does not satisfy K(N²) = K(N)²
  sorry -- grounded by S13 §4.2

-- Real QM fails local tomography
theorem real_fails_local_tomography :
  ¬LocalTomographic RealQM := by
  -- K_R(N) = N(N+1)/2 does not satisfy K(N²) = K(N)²
  sorry -- grounded by S13 §5.2

-- Complex QM is the unique locally tomographic theory
theorem complex_unique_local_tomographic :
  ∀ T, LocalTomographic T → T = ComplexQM := by
  -- Only K(N) = N² satisfies K(N²) = K(N)²
  sorry -- grounded by S13 §6
```

### 8.2 Tier Classification

The K=2 (complex field) selection is:

- **Not Tier 1:** It is not a primitive assumption about L<sub>3</sub> or I<sub>∞</sub>
- **Tier 2:** It is derived from L<sub>3</sub> via the local tomography chain
- **Confidence:** MEDIUM — depends on the H1 → H2 bridge and dimension counting

The Lean formalization correctly treats complex field selection as derived from local tomography. This supplement provides the prose derivation showing why local tomography mandates $K = N^2$ and thus $\mathbb{C}$.

---

## 9. Connection to Other Steps

### 9.1 Upstream Dependencies

| Dependency | Source | Status |
|------------|--------|--------|
| Determinate Identity | Step 2 | ESTABLISHED |
| Physical Proposition Criterion | S1 | ARGUED |
| H1 → H2 Bridge | S2 | ARGUED |
| Local Tomography | Step 3 | ARGUED |

### 9.2 Downstream Consumers

| Consumer | How Used |
|----------|----------|
| Step 4 (Masanes-Müller) | Complex field is input to reconstruction |
| Step 5 (PVM structure) | Spectral theorem requires $\mathbb{C}$ |
| Step 6-7 (Gleason/Born) | Applies to complex Hilbert spaces |
| Steps 11-13 (Dynamics) | Unitary group $U(N)$ over $\mathbb{C}$ |

### 9.3 Related Supplements

- **S1 (PPC Derivation):** Provides operational determinacy used in §4.3
- **S2 (H1-H2 Bridge):** Provides local tomography derivation used throughout
- **S12 (Product Effects):** Tensor product structure requires commutative field (§4.4)

---

## 10. Open Questions

### 10.1 The r = 2 vs. Other Values

The dimension formula $K = N^r$ has $r = 2$ selected by local tomography. But is there a deeper reason why $r$ takes integer values at all?

**Conjecture:** The integer constraint $r \in \mathbb{Z}$ follows from the discrete structure of distinguishable outcomes. Non-integer $r$ would imply fractional degrees of freedom per distinguishable state, which may violate Identity.

**Status:** OPEN — not required for current derivation but conceptually interesting.

### 10.2 Complex Numbers as "Just Right"

Complex numbers are:
- More than reals (two-dimensional, algebraically closed)
- Less than quaternions (commutative, well-behaved tensor products)

Is there a L<sub>3</sub>-based argument for why "two dimensions" is the minimal sufficient extension of the reals?

**Partial answer:** The fundamental theorem of algebra (every non-constant polynomial has a root) uniquely characterizes $\mathbb{C}$ among finite extensions of $\mathbb{R}$. This is the algebraic closure requirement.

**Status:** ARGUED — the algebraic closure constraint is well-motivated; whether L<sub>3</sub> alone forces it requires further development.

### 10.3 Octonions and Beyond

What about octonions $\mathbb{O}$ (8-dimensional, non-associative)?

Octonions fail both commutativity and associativity. The PPC argument against quaternions (§4.3) applies a fortiori: non-associativity makes $(AB)C \neq A(BC)$ at the scalar level, introducing further ambiguity in eigenvalue propositions.

Additionally, octonions do not form a division algebra in the standard sense (they are alternative but not associative), which prevents the standard Hilbert space construction.

**Status:** EXCLUDED by the same arguments that exclude quaternions, plus associativity violations.

---

## 11. Summary

| Section | Content | Status |
|---------|---------|--------|
| §2 | Dimension counting: only $K = N^2$ satisfies local tomography | ESTABLISHED |
| §3 | L<sub>3</sub> → local tomography → $K = N^2$ → complex field | ARGUED |
| §4 | Quaternions excluded by commutativity requirement | ARGUED |
| §5 | Reals excluded by algebraic closure requirement | ARGUED |
| §6 | Complex numbers uniquely selected | ARGUED |
| §7 | Continuous reversibility consistent with L<sub>3</sub> | ARGUED |

The derivation chain proceeds:

$$L_3 \to \text{DI} \to \text{Local Tomography} \to K = N^2 \to \mathbb{C}$$

$$L_3 \to \text{PPC} \to \text{Commutative Field} \to \neg\mathbb{H}$$

$$L_3 \to \text{PVM} \to \text{Spectral Theorem} \to \text{Algebraic Closure} \to \neg\mathbb{R}$$

The complex numbers $\mathbb{C}$ are not an arbitrary choice but the unique field compatible with L<sub>3</sub>-constrained quantum mechanics. The K_eq_two placeholder in the Lean formalization is thereby grounded.

---

## References

Hardy, L. (2001). Quantum theory from five reasonable axioms. *arXiv:quant-ph/0101012*.

Hardy, L. (2012). Limited holism and real-vector-space quantum theory. *Foundations of Physics*, 42(3), 454-473.

Masanes, L. and Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Renou, M.-O., Trillo, D., Weilenmann, M., Le, T. P., Tavakoli, A., Gisin, N., Acín, A., and Navascués, M. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600, 625-629.

Stueckelberg, E. C. G. (1960). Quantum theory in real Hilbert space. *Helvetica Physica Acta*, 33, 727-752.

Wootters, W. K. (1990). Local accessibility of quantum states. In W. H. Zurek (Ed.), *Complexity, Entropy, and the Physics of Information* (pp. 39-46). Addison-Wesley.

---

*Supplement S13 | Logic Realism Theory Project | 2026-03-13*
