# S13: Field Selection (K=2) — Deriving Complex Numbers from Hardy Axioms and L<sub>3</sub>

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Supports:** Step 4 (Hardy Axiom / Masanes-Müller Reconstruction)
**Addresses:** The K=2 (complex field) selection; grounds the K_eq_two placeholder

---

## Abstract

This supplement derives why quantum mechanics operates over the complex numbers $\mathbb{C}$ rather than the reals $\mathbb{R}$ or quaternions $\mathbb{H}$. The derivation proceeds through Hardy's K-parameter analysis combined with L<sub>3</sub> constraints within Logic Realism Theory. We show that: (1) local tomography requires a specific relationship between state space dimension and the number of continuous parameters, (2) this relationship uniquely selects K=2 (complex numbers) from among the division algebras, (3) quaternions are excluded by non-commutativity and tensor product non-associativity, and (4) reals are excluded by failure of local tomography for bipartite systems. The result grounds the field selection at Step 4 and provides the prose derivation for the `complex_field_selection` axiom in the Lean formalization.

---

## 1. The Problem

### 1.1 What Needs Grounding

The Lean formalization includes axioms asserting that the state space is a module over $\mathbb{C}$:

```lean
axiom complex_field_selection :
  ∃ (_ : AddCommGroup (QuotientSpace dist)) (_ : Module ℂ (QuotientSpace dist)), True
```

The master document (Section 3.2) states:

> "The field is complex, not real or quaternionic. This is not a free choice. Renou et al. (2021) demonstrated experimentally that real quantum theory makes different predictions from complex quantum theory in network scenarios."

But the derivation from L<sub>3</sub> to complex numbers requires explicit development. Why does quantum mechanics use $\mathbb{C}$ rather than $\mathbb{R}$ or $\mathbb{H}$?

### 1.2 The Three Candidates

By Frobenius's theorem (1878), the only finite-dimensional associative division algebras over $\mathbb{R}$ are:

1. **$\mathbb{R}$ (reals):** Dimension 1 over itself; commutative
2. **$\mathbb{C}$ (complex numbers):** Dimension 2 over $\mathbb{R}$; commutative; algebraically closed
3. **$\mathbb{H}$ (quaternions):** Dimension 4 over $\mathbb{R}$; non-commutative

Each can support a quantum-like theory. The question is which is selected by physical constraints.

### 1.3 Hardy's K-Parameter

Hardy (2001) introduced a parameter K representing the number of continuous real parameters needed to specify a state of an N-level system. The relationship between K and N distinguishes quantum theories:

| Theory | K(N) | Field |
|--------|------|-------|
| Classical probability | N - 1 | — |
| Real QM | $\frac{N(N+1)}{2} - 1$ | $\mathbb{R}$ |
| Complex QM | $N^2 - 1$ | $\mathbb{C}$ |
| Quaternionic QM | $N(2N-1) - 1$ | $\mathbb{H}$ |

*[Epistemic Status: ESTABLISHED — Hardy 2001, de la Torre et al. 2012]*

---

## 2. Local Tomography and Field Selection

### 2.1 The Local Tomography Constraint

Local tomography (H2 from Step 3) requires:

> The state of a composite system AB is completely determined by the statistics of local measurements on A and B.

For a composite system AB where A has $N_A$ levels and B has $N_B$ levels, this means:

$$K(N_A \cdot N_B) = K(N_A) \cdot K(N_B) + K(N_A) + K(N_B)$$

This is the dimensionality condition: the joint state space dimensionality equals the product of marginal dimensions plus correlation dimensions accessible via local measurements.

### 2.2 The Independent Composition Rule

A stronger formulation: **independent composition** requires that the dimension of the composite state space satisfies:

$$\dim(\mathcal{S}_{AB}) = \dim(\mathcal{S}_A) \cdot \dim(\mathcal{S}_B)$$

For density matrices over field $\mathbb{F}$:
- $\dim(\mathcal{S}_A) = N_A^2$ (complex) or $N_A(N_A+1)/2$ (real) or $N_A(2N_A-1)$ (quaternionic)

Local tomography forces the product rule.

### 2.3 Testing the Candidates

**Complex QM ($\mathbb{C}$):**

For an N-level system, the density matrix has $N^2 - 1$ real parameters (accounting for normalization and Hermiticity).

Composite: $(N_A \cdot N_B)^2 - 1 = N_A^2 \cdot N_B^2 - 1$

Product of marginals: $(N_A^2 - 1) + (N_B^2 - 1) + (N_A^2 - 1)(N_B^2 - 1) = N_A^2 \cdot N_B^2 - 1$ ✓

The product rule is satisfied.

**Real QM ($\mathbb{R}$):**

For an N-level system, the real symmetric density matrix has $\frac{N(N+1)}{2} - 1$ parameters.

Composite (if local tomography held):

$$\frac{N_A N_B (N_A N_B + 1)}{2} - 1$$

Product structure would require:

$$\left(\frac{N_A(N_A+1)}{2} - 1\right) \cdot \left(\frac{N_B(N_B+1)}{2} - 1\right) + ...$$

These do not match. Real QM violates local tomography.

*[Epistemic Status: ESTABLISHED — Wootters 1990, Stueckelberg 1960]*

**Quaternionic QM ($\mathbb{H}$):**

The quaternionic case has dimension $N(2N-1) - 1$ per system. More seriously, tensor products of quaternionic Hilbert spaces are not associative:

$$(H_A \otimes H_B) \otimes H_C \ncong H_A \otimes (H_B \otimes H_C)$$

This violates the independent composition rule at the structural level.

*[Epistemic Status: ESTABLISHED — Adler 1995]*

---

## 3. Why Quaternions Are Excluded

### 3.1 Non-Commutativity and Observables

Quaternions satisfy $ij = k$ but $ji = -k$. This non-commutativity has consequences:

**Claim:** Non-commutativity of the field violates the Physical Proposition Criterion (PPC) for composite observables.

**Argument:**

Consider observables $A$ on system 1 and $B$ on system 2. In standard QM, the joint observable $A \otimes B$ represents "measure A on system 1 and B on system 2."

For commutativity of joint measurement outcomes:
$$\langle A \otimes B \rangle = \langle B \otimes A \rangle$$

This is required by the Physical Proposition Criterion: the proposition "A yields value $a$ and B yields value $b$" must have the same truth conditions as "B yields value $b$ and A yields value $a$" — the order of spatially separated measurements cannot affect their outcomes (no signaling).

In quaternionic QM, the tensor product inherits non-commutativity from the field:
$$A \otimes_{\mathbb{H}} B \neq B \otimes_{\mathbb{H}} A$$

This breaks the symmetry required by L<sub>3</sub> for composite propositions.

*[Epistemic Status: ARGUED — depends on PPC application to observables]*

### 3.2 Tensor Product Non-Associativity

**Theorem (Adler 1995):** Quaternionic tensor products fail associativity for three or more systems:

$$(H_A \otimes H_B) \otimes H_C \ncong H_A \otimes (H_B \otimes H_C)$$

**Physical consequence:** States of 3+ particle systems are ill-defined.

Consider three systems A, B, C. The joint state $|\Psi_{ABC}\rangle$ must be an element of some state space. If $(H_A \otimes H_B) \otimes H_C \neq H_A \otimes (H_B \otimes H_C)$, then there is no well-defined composite state space.

By Determinate Identity (Step 2), the composite system ABC must have determinate identity. If there is no well-defined state space, there is no state to have identity. This violates L<sub>3</sub>.

**Conclusion:** Quaternionic QM is excluded by L<sub>3</sub> applied to composite systems with three or more subsystems.

*[Epistemic Status: ESTABLISHED — structural mathematical fact]*

---

## 4. Why Reals Are Excluded

### 4.1 Local Tomography Failure

**Theorem (Wootters 1990, Stueckelberg 1960):** Real quantum mechanics violates local tomography.

**Proof sketch:**

Consider the Bell states in real QM:
$$|\Phi^+\rangle = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$$
$$|\Phi^-\rangle = \frac{1}{\sqrt{2}}(|00\rangle - |11\rangle)$$

In complex QM, these states are distinguishable by local measurements: measure in the $\{|+\rangle, |-\rangle\}$ basis on each qubit and observe correlations.

In real QM, the relative phase between $|00\rangle$ and $|11\rangle$ is $\pm 1$ (real). But local measurements in a real Hilbert space cannot access this sign difference: the marginal states are identical.

$$\rho_A^{\Phi^+} = \rho_A^{\Phi^-} = \frac{1}{2}I$$
$$\rho_B^{\Phi^+} = \rho_B^{\Phi^-} = \frac{1}{2}I$$

Yet $|\Phi^+\rangle \neq |\Phi^-\rangle$ as states. Local measurements cannot distinguish them.

This violates local tomography: distinct joint states with identical local statistics.

*[Epistemic Status: ESTABLISHED — Wootters 1990]*

### 4.2 L<sub>3</sub> and Distinguishability

By the Physical Proposition Criterion (S1), if two states are distinct physical configurations, they must be operationally distinguishable. The distinguishability metric D requires:

$$D(|\Phi^+\rangle, |\Phi^-\rangle) > 0 \iff \exists \text{ measurement } M : P_M(|\Phi^+\rangle) \neq P_M(|\Phi^-\rangle)$$

In real QM, no local measurement M satisfies this for $|\Phi^+\rangle$ and $|\Phi^-\rangle$.

**Dilemma for real QM:**

1. Either $|\Phi^+\rangle = |\Phi^-\rangle$ (they are the same state), contradicting mathematical distinctness
2. Or they are distinct but indistinguishable, violating PPC

Under L<sub>3</sub>, option (2) is impossible: distinct configurations must be distinguishable. Therefore real QM cannot satisfy L<sub>3</sub> for bipartite systems.

*[Epistemic Status: ARGUED — depends on PPC]*

### 4.3 Empirical Confirmation

Renou et al. (2021) experimentally tested predictions distinguishing real from complex QM in network scenarios. Their results are consistent with complex QM and inconsistent with real QM.

This provides empirical confirmation that the L<sub>3</sub>-derived exclusion of real QM is physically correct.

*[Epistemic Status: ESTABLISHED — empirical result]*

---

## 5. The Selection Argument

### 5.1 Why K=2 (Complex Numbers)

The K-parameter measures the "richness" of the state space relative to the dimension:

| Field | K for N=2 | Constraint Status |
|-------|-----------|-------------------|
| $\mathbb{R}$ | K = 2 | Violates local tomography |
| $\mathbb{C}$ | K = 3 | Satisfies all constraints |
| $\mathbb{H}$ | K = 6 | Violates tensor associativity |

The Hardy parameter K is related to the field dimension:
- $\mathbb{R}$: real dimension 1
- $\mathbb{C}$: real dimension 2
- $\mathbb{H}$: real dimension 4

The "K=2" designation refers to $\mathbb{C}$ having dimension 2 over $\mathbb{R}$, making it the field where:

$$K(N) = N^2 - 1 = (N-1)(N+1)$$

This is the unique relationship compatible with local tomography and tensor product associativity.

### 5.2 Formal Selection Theorem

**Theorem (Field Selection):** Among the real division algebras $\{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$, only $\mathbb{C}$ satisfies:

1. Local tomography (H2 from Step 3)
2. Tensor product associativity for composite systems
3. Physical Proposition Criterion for composite observables

**Proof:**

$\mathbb{R}$ fails (1): Wootters-Stueckelberg theorem (§4.1)
$\mathbb{H}$ fails (2): Adler theorem (§3.2)
$\mathbb{C}$ satisfies (1), (2), (3): Masanes-Müller reconstruction

Therefore $\mathbb{C}$ is uniquely selected. $\square$

*[Epistemic Status: ARGUED — combines ESTABLISHED mathematical theorems with LRT framework]*

---

## 6. Connection to L<sub>3</sub>

### 6.1 Identity and Algebraic Closure

The Law of Identity requires that each configuration has determinate, self-identical character. For observables to have determinate spectra, the field must support spectral decomposition.

$\mathbb{C}$ is algebraically closed: every polynomial has roots in $\mathbb{C}$. This guarantees that every observable (self-adjoint operator) has a complete spectral decomposition.

$\mathbb{R}$ is not algebraically closed: $x^2 + 1 = 0$ has no real solutions. Some observables would lack real eigenvalues, making measurement outcomes indeterminate — violating Identity.

$\mathbb{H}$ has algebraic closure issues compounded by non-commutativity: the spectral theorem does not apply in the standard form.

### 6.2 Non-Contradiction and Commutativity

The Law of Non-Contradiction requires $\neg(P \land \neg P)$. For composite propositions "A on system 1 has value $a$ AND B on system 2 has value $b$":

The joint proposition must be well-defined. This requires:

$$[A \otimes I, I \otimes B] = 0$$

In $\mathbb{C}$-QM, this holds automatically by tensor product construction.

In $\mathbb{H}$-QM, non-commutativity of the field can induce non-commutativity of supposedly compatible observables, creating contradictory joint propositions.

### 6.3 Excluded Middle and Complete Tomography

The Law of Excluded Middle requires $P \lor \neg P$. For any physical proposition about a composite system, there must be a fact of the matter.

Local tomography ensures that all facts about the composite are accessible via local measurements. If local tomography fails (as in $\mathbb{R}$-QM), there exist propositions about the composite with no operational determination — violating Excluded Middle as a physical constraint.

---

## 7. Formal Statement for Lean

### 7.1 The Grounding Result

The Lean axiom `complex_field_selection` is grounded by:

| Step | Content | Epistemic Status |
|------|---------|------------------|
| 1 | Frobenius: only $\mathbb{R}, \mathbb{C}, \mathbb{H}$ are candidates | ESTABLISHED |
| 2 | Local tomography (H2) excludes $\mathbb{R}$ | ESTABLISHED |
| 3 | Tensor associativity excludes $\mathbb{H}$ | ESTABLISHED |
| 4 | L<sub>3</sub> + PPC reinforce exclusions | ARGUED |
| 5 | Therefore $\mathbb{C}$ uniquely selected | ARGUED |

### 7.2 Tier Classification

The `complex_field_selection` property is:

- **Not Tier 1:** It is not a primitive assumption about L<sub>3</sub> or I<sub>∞</sub>
- **Tier 2:** It is derived from established mathematical theorems (Frobenius, Wootters, Adler) combined with LRT framework constraints
- **Confidence:** HIGH — depends on well-established external theorems

---

## 8. Connection to Other Steps

### 8.1 Upstream Dependencies

| Dependency | Source | Status |
|------------|--------|--------|
| Local tomography (H2) | Step 3, S2 | ARGUED |
| Determinate Identity | Step 2 | ESTABLISHED |
| Physical Proposition Criterion | S1 | ARGUED |
| Tensor product structure | S12 | ARGUED |

### 8.2 Downstream Consumers

| Consumer | How Used |
|----------|----------|
| Step 4 (Masanes-Müller) | Complex field input to reconstruction |
| Step 5 (PVM structure) | Spectral theorem on complex Hilbert space |
| Step 6-7 (Gleason/Born) | Trace formula on complex density matrices |
| Step 12-13 (Stone/Schrödinger) | Unitary group on complex Hilbert space |

### 8.3 Related Supplements

- **S1 (PPC Derivation):** Provides operational determinacy used in §4.2
- **S2 (H1-H2 Bridge):** Establishes local tomography used throughout
- **S12 (Product Effects):** Establishes tensor product structure used in §3

---

## 9. Open Questions

### 9.1 Octonions and Beyond

The octonions $\mathbb{O}$ (dimension 8 over $\mathbb{R}$) are a non-associative division algebra. They are excluded by Frobenius (which requires associativity), but one might ask: could a non-associative algebra support physics?

**Answer:** No. The composition of operations (measurements, transformations) requires associativity. If $(A \circ B) \circ C \neq A \circ (B \circ C)$, the order of grouping affects outcomes, making physics path-dependent in an unphysical way.

*[Status: ADDRESSED]*

### 9.2 Infinite-Dimensional Algebras

Are there infinite-dimensional alternatives to $\mathbb{C}$?

For finite-dimensional quantum systems, $\mathbb{C}$ is unique. For QFT, one works with algebras of operators on complex Hilbert spaces. The complex field remains essential.

*[Status: OPEN — QFT extension not developed here]*

### 9.3 The "Why $\sqrt{-1}$" Question

Why does nature require a number whose square is negative?

The operational answer: interference requires amplitudes that can cancel. Real numbers can only add constructively or destructively (same sign or opposite sign). Complex numbers allow partial cancellation at arbitrary phases, enabling the full interference structure of quantum mechanics.

The L<sub>3</sub> answer: complex amplitudes are what local tomography requires for composite systems. The imaginary unit $i$ is not a mysterious ontological entity; it is the mathematical structure that ensures distinguishability of all physical configurations.

*[Status: ARGUED]*

---

## 10. Summary

| Section | Content | Status |
|---------|---------|--------|
| §2 | Local tomography constrains K | ESTABLISHED |
| §3 | Quaternions excluded by non-commutativity and non-associativity | ESTABLISHED |
| §4 | Reals excluded by local tomography failure | ESTABLISHED |
| §5 | Complex numbers uniquely selected | ARGUED |
| §6 | L<sub>3</sub> grounds field selection | ARGUED |

The complex field $\mathbb{C}$ is not an arbitrary choice but the unique field compatible with L<sub>3</sub>:

$$L_3 \to \text{Local Tomography (H2)} \to \text{Exclude } \mathbb{R}$$

$$L_3 \to \text{Tensor Associativity} \to \text{Exclude } \mathbb{H}$$

$$\text{Frobenius} \to \{\mathbb{R}, \mathbb{C}, \mathbb{H}\} \to \text{Only } \mathbb{C} \text{ survives}$$

The K=2 designation (complex field dimension 2 over reals) is thereby grounded in the logical-informational structure of X.

---

## References

Adler, S. L. (1995). *Quaternionic Quantum Mechanics and Quantum Fields*. Oxford University Press.

de la Torre, G., Masanes, Ll., Short, A. J., and Müller, M. P. (2012). Deriving quantum theory from its local structure and reversibility. *Physical Review Letters*, 109, 090403.

Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.

Hardy, L. (2012). Limited holism and real-vector-space quantum theory. *Foundations of Physics*, 42(3), 454-473.

Masanes, L. and Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Renou, M. O., et al. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600(7890), 625-629.

Stueckelberg, E. C. G. (1960). Quantum theory in real Hilbert space. *Helvetica Physica Acta*, 33, 727-752.

Wootters, W. K. (1990). Local accessibility of quantum states. In W. H. Zurek (Ed.), *Complexity, Entropy, and the Physics of Information*. Addison-Wesley.

---

*Supplement S13 | Logic Realism Theory Project | 2026-03-13*
