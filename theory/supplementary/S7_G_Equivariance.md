# S7: G-Equivariance Derivation from L<sub>3</sub> Symmetry Constraints

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Addresses:** Core Derivation Step 11 (G-equivariance and unitary dynamics)

---

## Abstract

This supplement derives the G-equivariance requirement for time evolution from L<sub>3</sub> symmetry constraints. The central argument: transformations that preserve the distinguishability structure of $A_\Omega$ form a symmetry group $G$, and time evolution must commute with $G$ to preserve Determinate Identity (DI). The derivation proceeds through four stages: (1) identifying $G$ as the group of DI-preserving transformations, (2) showing that time evolution must preserve DI, (3) establishing the equivariance requirement $U(t) \circ g = g \circ U(t)$ for all $g \in G$, and (4) connecting G-equivariance to unitary structure. We distinguish clearly between what LRT derives (the equivariance requirement) and what remains a physical input (the specific form of $G$).

---

## 1. The Problem

### 1.1 What the Master Document Claims

Section 5.5 of LRT-MASTER states:

> "The configuration space $A_\Omega$ carries a symmetry group G: the group of transformations of $\mathbb{C}\mathcal{H}$ that preserve the distinguishability metric D and the PVM structure of Step 5. Any physically admissible time evolution must commute with these symmetries – evolution that broke G-symmetry would change the distinguishability structure of states, which would alter their identity under DI."

The epistemic status is marked ARGUED. The concern: the inference from "G preserves distinguishability" to "time evolution must commute with G" requires explicit derivation. This supplement provides that derivation.

### 1.2 What Must Be Established

Three claims require justification:

1. **Symmetry group existence:** $A_\Omega$ admits a natural symmetry group $G$ defined by DI-preservation.
2. **Equivariance requirement:** Time evolution $U(t)$ must satisfy $U(t) \circ g = g \circ U(t)$ for all $g \in G$.
3. **Unitary structure:** G-equivariance combined with inner product preservation forces $U(t)$ to be unitary.

### 1.3 The Scope Distinction

**What LRT derives:** The *requirement* that time evolution be G-equivariant follows from L<sub>3</sub> constraints on identity preservation.

**What is physically specified:** The *particular form* of $G$ (e.g., $U(\mathcal{H})$ for non-relativistic systems, the Poincaré group for relativistic systems) is an empirical input determined by the symmetries of the physical system under study.

This distinction is critical. LRT does not derive that $G = U(\mathcal{H})$ from pure logic; it derives that whatever symmetry group $G$ the physical system has, time evolution must be equivariant with respect to $G$.

---

## 2. Stage 1: The Symmetry Group of $A_\Omega$

### 2.1 DI-Preserving Transformations

Recall from Step 2 that Determinate Identity (DI) requires every configuration $c \in A_\Omega$ to satisfy:

$$c = c \quad \text{(Identity)}$$
$$\neg(P(c) \land \neg P(c)) \quad \text{for all properties } P \quad \text{(Non-Contradiction)}$$
$$P(c) \lor \neg P(c) \quad \text{for all well-defined properties } P \quad \text{(Excluded Middle)}$$

**Definition (DI-Preservation):** A transformation $g : A_\Omega \to A_\Omega$ is DI-preserving if:

1. $g(c) \in A_\Omega$ for all $c \in A_\Omega$ (closure)
2. $D(g(c_1), g(c_2)) = D(c_1, c_2)$ for all $c_1, c_2 \in A_\Omega$ (metric preservation)
3. $g$ preserves the PVM structure: if $\{P_k\}$ is a PVM, then $\{g \cdot P_k \cdot g^{-1}\}$ is also a PVM (structure preservation)

### 2.2 The Symmetry Group $G$

**Proposition 1:** The set of all DI-preserving transformations forms a group under composition.

*Proof:*

- **Closure:** If $g_1$ and $g_2$ are DI-preserving, then $g_1 \circ g_2$ preserves $D$ (since both do) and preserves PVM structure (by composition of conjugation actions).
- **Identity:** The identity transformation is trivially DI-preserving.
- **Inverses:** If $g$ is DI-preserving, then $g^{-1}$ exists (since $g$ is a bijection on $A_\Omega$) and is DI-preserving (metric preservation and PVM preservation are symmetric under inversion).
- **Associativity:** Follows from associativity of function composition. $\square$

**Definition:** Let $G$ denote the group of DI-preserving transformations of $A_\Omega$.

### 2.3 The Physical Content of $G$

The abstract definition of $G$ as "DI-preserving transformations" does not specify which transformations concretely belong to $G$. This is where physical input enters:

- **Non-relativistic quantum mechanics:** $G$ includes spatial rotations, translations, and (in the covering group sense) $U(\mathcal{H})$ as the group of all unitaries on Hilbert space.
- **Relativistic systems:** $G$ includes Lorentz transformations and extends to the Poincaré group.
- **Gauge theories:** $G$ includes gauge transformations that leave physical observables invariant.

The specific content of $G$ is determined by the physical system's symmetries. LRT's contribution is to show that whatever $G$ is, time evolution must be equivariant with respect to it.

---

## 3. Stage 2: Time Evolution Must Preserve DI

### 3.1 The Preservation Requirement

**Premise (from UNS, Step 8):** The successor function $S : A_\Omega \to A_\Omega$ is total and well-defined. For continuous time, $U(t)$ generalizes $S$ to arbitrary time intervals.

**Claim:** $U(t) : A_\Omega \to A_\Omega$ must preserve DI for all $t$.

**Argument:**

**Step 1:** By UNS, every $c \in A_\Omega$ has a unique successor $S(c) \in A_\Omega$.

**Step 2:** The successor $S(c)$ must satisfy DI (by definition of $A_\Omega$). A configuration outside $A_\Omega$ cannot be an actual successor because it would violate L<sub>3</sub>.

**Step 3:** Generalizing to continuous time: $U(t)(c)$ is the configuration reached after time $t$ from initial configuration $c$. By iteration of UNS over infinitesimal intervals, $U(t)(c) \in A_\Omega$.

**Conclusion:** $U(t)$ maps $A_\Omega$ to $A_\Omega$, preserving membership in the L<sub>3</sub>-admissible domain.

### 3.2 Metric Preservation

**Claim:** $U(t)$ preserves the distinguishability metric $D$.

**Argument:**

**Premise 1:** The distinguishability metric $D$ encodes identity relations:
$$D(c_1, c_2) = \sup_M \lvert P_M(c_1) - P_M(c_2) \rvert_{TV}$$

**Premise 2:** If $U(t)$ changed $D$, configurations that were distinct at time $0$ could become identical at time $t$, or vice versa.

**Premise 3:** Identity is absolute under L<sub>3</sub>. If $c_1 \neq c_2$ (i.e., $D(c_1, c_2) > 0$), this distinctness is a fact about $c_1$ and $c_2$, not a time-dependent property.

**Premise 4:** Suppose $D(U(t)(c_1), U(t)(c_2)) \neq D(c_1, c_2)$. Then the identity relation between $c_1$ and $c_2$ has changed over time. But under Identity, $c_1 = c_1$ at all times; it cannot become a different configuration.

**Premise 5:** Time evolution transforms states, but it cannot alter the *relation* of distinctness between evolved states. If $c_1$ and $c_2$ are distinct and evolve to $c'_1$ and $c'_2$, the pairs must preserve their distinguishability structure.

**Formal statement:** For all $c_1, c_2 \in A_\Omega$ and all $t$:
$$D(U(t)(c_1), U(t)(c_2)) = D(c_1, c_2)$$

**Conclusion:** $U(t)$ is a DI-preserving transformation for each $t$.

---

## 4. Stage 3: The Equivariance Requirement

### 4.1 Why Time Evolution Must Commute with $G$

**Theorem (G-Equivariance):** For every $g \in G$ and every $t \in \mathbb{R}$:
$$U(t) \circ g = g \circ U(t)$$

**Proof:**

**Step 1:** Let $g \in G$ be a symmetry transformation. By definition, $g$ preserves $D$ and the PVM structure.

**Step 2:** Consider two ways of evolving a symmetric configuration:
- Path A: Apply $g$ first, then evolve by $U(t)$: $c \mapsto g(c) \mapsto U(t)(g(c))$
- Path B: Evolve first, then apply $g$: $c \mapsto U(t)(c) \mapsto g(U(t)(c))$

**Step 3:** Since $g$ is a symmetry of $A_\Omega$, the physical content of $c$ and $g(c)$ is identical with respect to all DI-relevant structure. They are related by a transformation that L<sub>3</sub> cannot distinguish (by definition of symmetry).

**Step 4:** If $U(t) \circ g \neq g \circ U(t)$, then:
$$U(t)(g(c)) \neq g(U(t)(c))$$

for some $c$. But this means the dynamical evolution distinguishes between $c$ and $g(c)$ in a way that the symmetry structure of $A_\Omega$ does not.

**Step 5:** This creates a contradiction: $g$ is supposed to be a symmetry (indistinguishable under all DI-relevant measurements), yet dynamics treats $c$ and $g(c)$ differently. This violates the premise that $g$ preserves the full structure of $A_\Omega$.

**Step 6:** More precisely: let $c' = U(t)(g(c))$ and $c'' = g(U(t)(c))$. If $c' \neq c''$, then $D(c', c'') > 0$. But:
- $c'$ is the result of applying symmetry $g$ to $c$, then evolving
- $c''$ is the result of evolving $c$, then applying $g$

If these differ, the dynamics breaks the symmetry $g$. But $g$ was defined as a symmetry of $A_\Omega$'s structure, including its dynamical structure (since dynamics preserves DI by Stage 2).

**Conclusion:** $U(t) \circ g = g \circ U(t)$ for all $g \in G$. $\square$

### 4.2 Alternative Formulation

**Corollary:** The time evolution operators $\{U(t)\}_{t \in \mathbb{R}}$ lie in the commutant of $G$:
$$U(t) \in G' = \{A : Ag = gA \text{ for all } g \in G\}$$

This is the standard mathematical characterization of G-equivariance.

---

## 5. Stage 4: From Equivariance to Unitarity

### 5.1 Inner Product Preservation

**Premise:** The distinguishability metric $D$ is related to the inner product structure on $\mathcal{H}$. Specifically, for pure states represented by unit vectors $\lvert\psi_1\rangle$ and $\lvert\psi_2\rangle$:
$$D(\psi_1, \psi_2) = f(\lvert\langle\psi_1\lvert\psi_2\rangle\rvert)$$

where $f$ is a monotonic function (with $f(1) = 0$ for identical states and $f(0) = 1$ for orthogonal states).

**Consequence:** Preserving $D$ requires preserving inner products (up to phases). A transformation $U$ preserves $D$ if and only if:
$$\lvert\langle U\psi_1\lvert U\psi_2\rangle\rvert = \lvert\langle\psi_1\lvert\psi_2\rangle\rvert$$

### 5.2 Wigner's Theorem

**Theorem (Wigner, 1931):** Every transformation on a Hilbert space that preserves transition probabilities (equivalently, $D$-preserving) is either unitary or anti-unitary.

**Application:** Since $U(t)$ preserves $D$ (by Stage 2), Wigner's theorem entails that $U(t)$ is either unitary or anti-unitary.

### 5.3 Excluding Anti-Unitary Time Evolution

**Argument:**

**Premise 1:** Anti-unitary operators satisfy $\langle U\psi\lvert U\phi\rangle = \overline{\langle\psi\lvert\phi\rangle}$ (complex conjugation of inner products).

**Premise 2:** Time evolution forms a continuous one-parameter group: $U(t_1 + t_2) = U(t_1) \circ U(t_2)$ and $U(0) = I$.

**Premise 3:** The composition of two anti-unitary operators is unitary. If $U(t)$ were anti-unitary for all $t > 0$, then $U(2t) = U(t) \circ U(t)$ would be unitary, contradicting the premise that all $U(t)$ are anti-unitary.

**Premise 4:** The only consistent possibility is that $U(t)$ is unitary for all $t$ (with $U(0) = I$ being trivially unitary).

**Conclusion:** $U(t)$ is a unitary operator for all $t$.

### 5.4 The One-Parameter Unitary Group

**Theorem:** $\{U(t)\}_{t \in \mathbb{R}}$ is a strongly continuous one-parameter group of unitary operators.

*Proof:*

1. **Unitarity:** Established in Section 5.3.
2. **Group property:** $U(t_1 + t_2) = U(t_1) \circ U(t_2)$ follows from the composition of successive time evolutions.
3. **Strong continuity:** The Fubini-Study topology on states (from Step 10, continuous time) ensures that $U(t)\lvert\psi\rangle$ varies continuously with $t$.

This completes the derivation. Stone's theorem (Step 12) then provides the self-adjoint generator $H$. $\square$

---

## 6. Dependency Structure

### 6.1 What This Derivation Requires

| Premise | Source | Status |
|---------|--------|--------|
| Determinate Identity (DI) | Step 2 | ESTABLISHED |
| Distinguishability metric $D$ | Framework (I<sub>∞</sub> structure) | ESTABLISHED |
| PVM structure | Step 5 | ARGUED |
| Unique Next State (UNS) | Step 8 | ARGUED |
| Continuous time | Step 10 | ARGUED |
| Hilbert space structure | Step 4 | ESTABLISHED |

### 6.2 What Depends on G-Equivariance

| Downstream Step | Content |
|-----------------|---------|
| Step 12 | Stone's theorem: existence of self-adjoint $H$ |
| Step 13 | Schrödinger equation |

G-equivariance is the bridge between continuous time (Step 10) and the Hamiltonian structure (Step 12).

---

## 7. The Physical Input Question

### 7.1 What LRT Derives vs. What Is Specified

**Derived from L<sub>3</sub>:**
- The *existence* of a symmetry group $G$ (DI-preserving transformations)
- The *requirement* that $U(t)$ commute with $G$
- The *unitarity* of $U(t)$ (from $D$-preservation and Wigner's theorem)

**Physical input (not derived):**
- The *specific content* of $G$ for a given physical system
- Whether $G = U(\mathcal{H})$, or a subgroup, or includes additional structure

### 7.2 The Identification $G = U(\mathcal{H})$

For non-relativistic quantum mechanics, the standard choice is $G = U(\mathcal{H})$, the full unitary group. This choice is *consistent* with LRT but not *derived* from it.

**Argument for $G = U(\mathcal{H})$:**

1. In the absence of additional constraints (no external fields, no fixed reference frame), all unitary transformations preserve $D$ and PVM structure.
2. Therefore, the maximal symmetry group consistent with the Hilbert space structure is $U(\mathcal{H})$.
3. $U(\mathcal{H})$ is the natural default when no symmetry-breaking is specified.

**Caveat:** This is a physical argument (based on the absence of external structure), not a logical derivation from L<sub>3</sub>.

### 7.3 Relativistic Extension

For relativistic systems, $G$ must include Lorentz transformations. Whether the Lorentz group can be derived from L<sub>3</sub> constraints on spacetime structure is an open question (Section 9.2 of LRT-MASTER). The current derivation establishes only that *whatever* symmetry group applies, time evolution must be equivariant with respect to it.

---

## 8. Addressing Potential Objections

### 8.1 "The Derivation Is Circular"

**Objection:** You define $G$ as the group of DI-preserving transformations, then show that time evolution must preserve DI and hence commute with $G$. Isn't this circular?

**Response:** The argument is not circular but has two distinct steps:

1. **Definition of $G$:** $G$ is defined independently of time evolution, as the group of transformations preserving $A_\Omega$'s intrinsic structure ($D$ and PVMs).

2. **Derivation of equivariance:** Time evolution is shown (by separate argument) to preserve DI, hence to be an element of the broader class of DI-preserving maps. The equivariance requirement then follows from consistency: if both $U(t)$ and $g$ preserve DI, and $g$ is a symmetry, then $U(t)$ must commute with $g$.

The circularity would arise only if we defined $G$ *using* time evolution. We don't; $G$ is defined statically.

### 8.2 "Symmetry Breaking Exists"

**Objection:** Real physical systems exhibit symmetry breaking. The ground state of a ferromagnet breaks rotational symmetry. How can time evolution commute with broken symmetries?

**Response:** Symmetry breaking concerns the *state*, not the *dynamics*. The Hamiltonian of a ferromagnet is rotationally symmetric; the ground state is not. Time evolution (generated by $H$) commutes with rotations even though specific states do not respect rotational symmetry.

G-equivariance is a statement about the dynamical law, not about particular solutions. Symmetry-broken states are consistent with equivariant dynamics.

### 8.3 "What About Time-Dependent Hamiltonians?"

**Objection:** For time-dependent Hamiltonians $H(t)$, the symmetry group may vary with time. Does G-equivariance still hold?

**Response:** The argument applies at each instant. If $H(t)$ varies, the instantaneous symmetry group $G(t)$ may also vary. The equivariance requirement becomes:

$$U(t_2, t_1) \circ g = g \circ U(t_2, t_1)$$

for $g \in G(t_1) \cap G(t_2)$ (transformations that are symmetries at both initial and final times).

For symmetries that persist through the evolution, equivariance holds. For symmetries that are broken by the time-dependent perturbation, equivariance fails—as expected physically.

---

## 9. Formal Summary

**Theorem (G-Equivariance from L<sub>3</sub>):** Let $A_\Omega = L_3(I_\infty)$ be the actualized domain with distinguishability metric $D$. Let $G$ be the group of transformations of $A_\Omega$ that preserve $D$ and the PVM structure. Then:

1. Time evolution $U(t)$ preserves $D$ (from DI-preservation under dynamics).
2. By Wigner's theorem, $U(t)$ is unitary.
3. $U(t)$ commutes with all $g \in G$: $U(t) \circ g = g \circ U(t)$.
4. $\{U(t)\}_{t \in \mathbb{R}}$ is a strongly continuous one-parameter group of unitary operators.

**Proof outline:**

1. DI requires $U(t)(c) \in A_\Omega$ for all $c \in A_\Omega$ (Section 3.1).
2. Identity preservation requires $D(U(t)(c_1), U(t)(c_2)) = D(c_1, c_2)$ (Section 3.2).
3. $D$-preservation plus Wigner's theorem gives unitarity (Section 5.2-5.3).
4. Symmetries $g \in G$ must commute with $U(t)$ to avoid breaking the symmetry structure that $g$ represents (Section 4.1). $\square$

---

## 10. Epistemic Status

**Previous Status:** ARGUED (prose argument in LRT-MASTER Section 5.5)

**Current Status:** ARGUED (formalized with explicit premises and inferences)

**Remaining for ESTABLISHED:**

1. **Lean 4 formalization:** The logical structure of the equivariance argument should be machine-verified.
2. **Precise characterization of $G$:** The relationship between DI-preservation and the standard unitary group $U(\mathcal{H})$ requires formal treatment.
3. **Extension to relativistic systems:** The argument for including Lorentz transformations in $G$ is physical, not derived from L<sub>3</sub>.

**Note:** The distinction between "derived" (equivariance requirement) and "specified" (particular $G$) is essential. Critics who object that LRT does not derive the unitary group from logic are correct—but this is a feature, not a bug. LRT provides the *form* of the constraint; physics provides the *content*.

---

## 11. Open Questions

### 11.1 Can $G$ Be Derived?

**Question:** Is there an argument from L<sub>3</sub> alone (without physical input) that determines $G = U(\mathcal{H})$?

**Current answer:** No such argument is known. The maximal symmetry group consistent with Hilbert space structure is $U(\mathcal{H})$, but "maximal consistent" is not the same as "logically required."

**Possible direction:** If $A_\Omega$'s structure uniquely determines its automorphism group, and if that group can be shown to be $U(\mathcal{H})$ from the I<sub>∞</sub> axioms, then $G$ would be derived. This is speculative.

### 11.2 Superselection Rules

**Question:** Superselection rules restrict the symmetry group to a subgroup of $U(\mathcal{H})$. How does LRT accommodate this?

**Preliminary answer:** Superselection rules are additional constraints on $A_\Omega$ beyond L<sub>3</sub>. They restrict which states are physically realizable, effectively reducing $G$ to the group of unitaries that respect superselection sectors. This is consistent with LRT's framework: physical input specifies $G$, and equivariance holds for the specified $G$.

### 11.3 Discrete Symmetries

**Question:** Time reversal ($T$) is an anti-unitary symmetry. Does the derivation accommodate anti-unitary symmetries?

**Preliminary answer:** The derivation shows $U(t)$ is unitary, not anti-unitary. Discrete symmetries like $T$ are transformations of $A_\Omega$ that may be anti-unitary. The equivariance requirement $U(t) \circ T = T \circ U(t)$ does not require $T$ to be unitary—only that $U(t)$ commute with $T$ if $T$ is a symmetry.

For CPT-symmetric theories, the combined transformation $CPT$ is a symmetry, and time evolution commutes with it. This is consistent with the derivation.

---

## 12. Relation to Other Supplements

### 12.1 Dependency on S6

S7 presupposes the Unique Next State theorem (S6). UNS establishes that time evolution is well-defined; S7 establishes that it is equivariant.

### 12.2 Relation to S4

S4 (Debreu-Nachbin) establishes continuous time. S7 uses this continuity to argue for strong continuity of $U(t)$.

### 12.3 Relation to S3

S3 establishes PVM structure. The symmetry group $G$ is defined in part by PVM-preservation, so S7 depends on S3.

### 12.4 Connection to Step 12-13

S7 completes the setup for Stone's theorem (Step 12). With strongly continuous one-parameter unitary groups established, Stone's theorem applies directly to give the self-adjoint generator $H$.

---

## References

Stone, M. H. (1930). Linear transformations in Hilbert space. III. *Proceedings of the National Academy of Sciences*, 16, 172-175.

Wigner, E. P. (1931). *Gruppentheorie und ihre Anwendung auf die Quantenmechanik der Atomspektren*. Vieweg.

Bargmann, V. (1964). Note on Wigner's theorem on symmetry operations. *Journal of Mathematical Physics*, 5(7), 862-868.

Weinberg, S. (1995). *The Quantum Theory of Fields, Vol. 1: Foundations*. Cambridge University Press.

---

*Supplement S7 | Logic Realism Theory Project | 2026-03-13*
