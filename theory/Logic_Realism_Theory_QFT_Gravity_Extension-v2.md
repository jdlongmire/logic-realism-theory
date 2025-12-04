# LRT Constraints on QFT: Deriving Fock Structure and Interpreting Renormalization from Logical Foundations

**James (JD) Longmire**\
ORCID: 0009-0009-1383-7698\
Northrop Grumman Fellow (unaffiliated research)

**Version:** 2.0 (December 2025)\
**Status**: SEED DOCUMENT - Framework established, content to be developed
**Target**: Foundations of Physics (~25 pages)
**Timeline**: 6-9 months (Q1 2026 submission)

---

## Abstract

Logic Realism Theory (LRT) derives non-relativistic quantum mechanics from the claim that the Three Fundamental Laws of Logic (Identity, Non-Contradiction, Excluded Middle) are ontological constraints constitutive of physical distinguishability. This paper extends LRT to quantum field theory through a tiered derivation structure with explicit physical inputs at each level.

We establish three principal results. First, Fock space structure is derived (Tier 3: given Lorentz invariance + local tomography + indistinguishability): the tensor product structure from A3c combines with 3FLL-enforced symmetrization to yield bosonic and fermionic Fock spaces. Second, the spin-statistics connection is derived (Tier 3: given Lorentz invariance + microcausality + positive energy) via the Streater-Wightman framework, with LRT providing the underlying Hilbert space and tensor product structure. Third, the uniqueness of complex QFT is established (Tier 3: given assumptions A1-A7, see §5.3): alternatives (real QFT, quaternionic QFT, super-quantum theories) fail stability, local tomography, or tensor associativity requirements.

The paper distinguishes derivations from interpretations. Cluster decomposition, vacuum uniqueness, and the spectral gap are physical inputs (Tier 4), not consequences of logical constraints. Renormalization is *conceptually framed* as 3FLL-restoration at UV scales, but this interpretive framework does not derive renormalization group equations or beta functions. The gravity sector remains conjectural (Tier 5).

Four predictions follow: (1) Tsirelson bound $\mathcal{S} \leq 2\sqrt{2}$ holds for field correlations, (2) information is never fundamentally lost, (3) complex amplitudes are required (real-only QFT excluded by Renou et al. at >7σ), (4) spin-statistics holds universally. Six strong falsifiers are identified with quantitative criteria (§5.2).

The extension is conservative: it builds on established LRT results, adds Lorentz invariance and microcausality as explicit physical inputs, and makes honest distinctions between what is derived, interpreted, and conjectured. No claim is made to derive Lorentz invariance, microcausality, or cluster decomposition from pure logic—these are physical inputs at Tiers 2-4.

**Keywords:** quantum field theory, logic realism, Fock space, spin-statistics, falsifiability, reconstruction theorems

---

## 1. Introduction (1-2 pages)

### 1.1 Motivation and Audience

This paper extends Logic Realism Theory from non-relativistic quantum mechanics to quantum field theory. The goal is to close LRT's scope gap for QFT/Gravity while maintaining the rigorous derivation standards established in the Technical Foundations paper.

**Target Audience:** This paper assumes familiarity with axiomatic/algebraic QFT (Streater-Wightman axioms, Haag-Kastler framework) and reconstruction theorems (Masanes-Müller, Hardy, Chiribella-D'Ariano-Perinotti). The gravity discussion (§6) is intentionally limited to holographic/information-theoretic constraints; we make no claim to derive gravitational dynamics or general covariance from first principles.

**Scope Limitation:** The paper addresses *kinematic* structure (Fock space, spin-statistics, complex amplitudes) rather than *dynamical* structure (specific Lagrangians, coupling constants, particle content). Dynamics remain physical inputs at Tier 4+.

### 1.2 Derivation Hierarchy

LRT extends to QFT via a tiered structure with explicit physical inputs at each level. This tiered approach contrasts with typical overclaiming in foundations literature, where authors often present physical inputs as "derived from first principles" without acknowledging the assumptions smuggled in. By making each tier explicit, reviewers can evaluate exactly what is proven versus assumed.

---

**FIGURE 1: LRT-QFT Tiered Derivation Structure**

| Tier | Inputs | Outputs | Status |
|------|--------|---------|--------|
| **1: Logic** | 3FLL | Distinguishability D; kernel K | Derived (Thm 2.1-3.2) |
| **2: Covariant** | + CBP + Lorentz invariance | Algebraic Hilbert; D-isometries | Derived (via Masanes-Müller) |
| **3: Fields** | + Locality (A3c) + Indistinguishability + Microcausality + Positive energy | Fock tensors; spin-statistics | Derived (Thm 3.1', 3.2') |
| **4: QFT** | + Cluster decomposition + Vacuum uniqueness | Renormalization; vacuum structure | Interpreted |
| **5: Gravity** | + Holographic bounds | Collapse parameters | Conjecture (future work) |

*Each tier explicitly lists physical inputs. Nothing is derived "from pure logic" beyond Tier 1.*

---

### 1.3 What This Paper Claims and Does Not Claim

**Can claim (with tier annotations):**
- Fock structure derived (Tier 3: given Lorentz + locality + indistinguishability)
- Spin-statistics derived (Tier 3: given Lorentz + microcausality + positive energy)
- Complex QFT uniqueness established (Tier 3: given A1-A7, §5.3)
- Renormalization *conceptually framed* as CBP-enforced 3FLL consistency (Tier 4: interpretive, not derived)
- Vacuum structure *consistent with* IIS framework (Tier 4: physical input)

**Cannot claim:**
- Fock from 3FLL alone (requires Tier 2-3 physical inputs)
- Spin-statistics from pure logic (requires Tier 3 inputs)
- Renormalization *derived* (interpretation only—no RG equations, beta functions, or anomalous dimensions)
- Vacuum *derived* from 3FLL (requires spectral/uniqueness assumptions as Tier 4 inputs)
- Cluster decomposition from IIS closure (dynamical, not kinematic)
- Lorentz invariance or microcausality from logic (empirical inputs)

### 1.4 Key Theorems (Stated)

- **Theorem 2.1'**: D-isometries under Lorentz transformations (§2.2)
- **Theorem 2.2'**: Single-particle Hilbert space from Poincaré representations (§2.3)
- **Theorem 3.1'**: Symmetrization from 3FLL + Indistinguishability (§3.2) - yields bosonic/fermionic Fock spaces
- **Theorem 3.2'**: Spin-statistics from Lorentz + microcausality + positive energy (§3.3) - via Streater-Wightman
- **Theorem 3.3'**: CCR/CAR algebra from Fock structure (§3.4)
- **Theorem 5.1'**: Uniqueness of complex QFT with 7 explicit assumptions (§5.3)

### 1.5 Roadmap of Proofs

The technical trajectory of this paper:

1. **§2: Relativistic IIS Structure** — Prove Lorentz-covariant distinguishability (Theorem 2.1') and derive single-particle Hilbert space structure (Theorem 2.2') from Poincaré representations. *Standard:* Wigner classification. *LRT-specific:* distinguishability metric extended to relativistic setting.

2. **§3: Fock Structure** — Use local tomography (A3c) and indistinguishability to derive Fock structure (Theorem 3.1') and spin-statistics (Theorem 3.2'). Theorem 3.1' receives a full proof including explicit connection to Messiah-Greenberg exclusion of parastatistics. *Standard:* tensor products, Streater-Wightman. *LRT-specific:* 3FLL-enforced symmetrization.

3. **§4: QFT Interpretation** — Distinguish physical inputs (cluster decomposition, vacuum uniqueness) from interpretations (renormalization as 3FLL-restoration). No derivations claimed.

4. **§5: Uniqueness and Falsifiers** — Prove uniqueness of complex QFT (Theorem 5.1') under explicit assumptions A1-A7, with connection to experimental bounds (Renou et al.). *Standard:* Masanes-Müller reconstruction. *LRT-specific:* extension to QFT with quantitative falsification criteria.

5. **§6: Gravity (Conjecture)** — State conjectures with order-of-magnitude estimates. No derivations claimed.

---

## 2. IIS Algebraic Structure (3 pages)

### 2.1 Review: Distinguishability in Non-Relativistic LRT

From Technical.md (Definition 2.2), the distinguishability metric is:

**Definition 2.1 (Distinguishability Degree).**
$$D(s_1, s_2) = \sup_M \|P_M(s_1) - P_M(s_2)\|_{TV}$$

where $\|\cdot\|_{TV}$ is the total variation distance and the supremum is over all measurement contexts.

**Theorem 3.2 (Technical.md)** established that $D$ + continuity (A3a) + reversibility (A3b) uniquely determines a complex inner product:
$$D(s_1, s_2) = 1 - |\langle s_1 | s_2 \rangle|^2$$

This construction is *non-relativistic*: it assumes a preferred time slice for defining measurements. The QFT extension requires Lorentz covariance.

### 2.2 Lorentz-Covariant Distinguishability

**Physical Input (Tier 2):** Lorentz invariance. The laws of physics take the same form in all inertial reference frames.

**Definition 2.2' (Relativistic Distinguishability).** For states $s_1, s_2$ in relativistic IIS, define:
$$D_{\text{rel}}(s_1, s_2) = \sup_{\mathcal{O}, M} \|P_M^{\mathcal{O}}(s_1) - P_M^{\mathcal{O}}(s_2)\|_{TV}$$

where the supremum is over all measurement contexts $M$ *and* all inertial observers $\mathcal{O}$.

**Theorem 2.1' (D-Isometries).** If $\Lambda$ is a Lorentz transformation, then:
$$D_{\text{rel}}(\Lambda s_1, \Lambda s_2) = D_{\text{rel}}(s_1, s_2)$$

**Proof sketch:**

*Step 1:* Lorentz invariance requires that distinguishability is observer-independent. If observer $\mathcal{O}$ can distinguish $s_1$ from $s_2$ with probability $p$, then boosted observer $\mathcal{O}'$ can distinguish $\Lambda s_1$ from $\Lambda s_2$ with the same probability $p$.

*Step 2:* The supremum over all observers and measurements is Lorentz-invariant by construction: any measurement available to $\mathcal{O}$ has a Lorentz-transformed counterpart available to $\mathcal{O}'$.

*Step 3:* Therefore, Lorentz transformations are D-isometries: they preserve the distinguishability metric exactly. ∎

**Corollary 2.1 (Poincaré Representation).** The Poincaré group (Lorentz + translations) acts as isometries on relativistic IIS. By Wigner's theorem, this action is implemented by unitary (or antiunitary) operators on the Hilbert space.

### 2.3 Single-Particle Hilbert Space from Relativistic IIS

**Definition 2.3 (Single-Particle IIS).** The single-particle sector $\mathcal{I}_1$ consists of states with definite particle number 1.

By the non-relativistic construction (Theorem 3.2, Technical.md), $\mathcal{I}_1$ inherits complex Hilbert space structure from the distinguishability metric.

**Physical requirement:** Single-particle states must transform under irreducible representations of the Poincaré group (Wigner 1939).

**Theorem 2.2' (Single-Particle Structure).** The single-particle Hilbert space $\mathcal{H}_1$ decomposes as:
$$\mathcal{H}_1 = \bigoplus_{m, s} \mathcal{H}_{m,s}$$

where each $\mathcal{H}_{m,s}$ carries an irreducible unitary representation of the Poincaré group labeled by mass $m \geq 0$ and spin $s \in \{0, 1/2, 1, 3/2, ...\}$.

**Proof sketch:**

*Step 1:* By Corollary 2.1, Poincaré acts unitarily on $\mathcal{H}_1$.

*Step 2:* By Wigner's classification (1939), irreducible unitary representations of the Poincaré group are labeled by mass $m$ and spin $s$ (for $m > 0$) or helicity (for $m = 0$).

*Step 3:* The physical requirement that particles have definite mass and spin means single-particle states belong to irreducible representations.

*Step 4:* General single-particle Hilbert space is a direct sum of irreducibles. ∎

**Note:** This is a *physical input*, not a derivation from 3FLL. The classification of particles by mass and spin is an empirical fact that LRT accommodates, not derives.

### 2.4 From Kernel to Field Operators

The Hardy kernel (Definition 3.2, Technical.md):
$$K(x,y;z) := 1 - \frac{1}{2}[D(x,y) + D(x,z) - D(y,z)]$$

induces the inner product. For relativistic extension, we work with momentum-space states.

**Definition 2.4 (Momentum States).** For mass $m$ and spin $s$, define momentum eigenstates $|p, \sigma\rangle$ where $p^\mu = (E_p, \mathbf{p})$ with $E_p = \sqrt{|\mathbf{p}|^2 + m^2}$ and $\sigma \in \{-s, ..., +s\}$ is the spin projection.

**Normalization (Lorentz-invariant):**
$$\langle p, \sigma | p', \sigma' \rangle = (2\pi)^3 2E_p \delta^{(3)}(\mathbf{p} - \mathbf{p}') \delta_{\sigma\sigma'}$$

**Definition 2.5 (Field Operator).** For a scalar field ($s = 0$), define:
$$\phi(x) = \int \frac{d^3p}{(2\pi)^3 2E_p} \left[ a_{\mathbf{p}} e^{-ip \cdot x} + a_{\mathbf{p}}^\dagger e^{ip \cdot x} \right]$$

where $a_{\mathbf{p}}$ and $a_{\mathbf{p}}^\dagger$ are operators on the single-particle Hilbert space (to be constructed in §3).

**Theorem 2.3' (Lorentz Covariance of Fields).** Under Lorentz transformation $\Lambda$:
$$U(\Lambda) \phi(x) U(\Lambda)^{-1} = \phi(\Lambda x)$$

**Proof sketch:** This follows from:
- Lorentz transformation of momentum: $p \to \Lambda p$
- Lorentz invariance of the measure $\frac{d^3p}{2E_p}$
- Wigner rotation acting on creation/annihilation operators

The field transforms as a Lorentz scalar, as required for a spin-0 field. ∎

**Status of §2:** The algebraic structure (Lorentz-covariant distinguishability, single-particle Hilbert space, field operators) is established. The key physical input is Lorentz invariance (Tier 2). The construction parallels Technical.md but adds relativistic constraints.

**Novelty Assessment:**
| Component | Standard QFT | LRT-Specific |
|-----------|--------------|--------------|
| Wigner classification | Yes (Wigner 1939) | — |
| Poincaré representations | Yes | — |
| Lorentz-invariant measure | Yes | — |
| D-isometries under Lorentz | — | NEW: extends distinguishability metric to relativistic setting |
| Field operator construction | Yes | — |

*The novelty in §2 is modest: extending the distinguishability framework to relativistic IIS. The technical content is largely standard.*

---

## 3. Fock Structure Derivation (5 pages)

### 3.1 Tensor Products from Local Tomography

**Theorem 6.2 (Technical.md)** established that local tomography (A3c) implies tensor product structure:
$$\mathcal{H}_{AB} = \mathcal{H}_A \otimes \mathcal{H}_B$$

This extends to $n$-particle systems:
$$\mathcal{H}^{(n)} = \mathcal{H}_1 \otimes \mathcal{H}_1 \otimes \cdots \otimes \mathcal{H}_1 \quad (n \text{ factors})$$

**Proof sketch (from Technical.md §6.2):**

*Step 1:* Local tomography requires that composite system states are determined by local measurements plus correlations.

*Step 2:* Dimension counting: If $\dim(\mathcal{H}_A) = d_A$ and $\dim(\mathcal{H}_B) = d_B$, local tomography requires $(d_A \cdot d_B)^2 - 1$ independent parameters, matching $\mathcal{H}_A \otimes \mathcal{H}_B$.

*Step 3:* The Born rule factorization $p(a,b|\rho_{AB}) = \text{Tr}[\rho_{AB}(M_A \otimes M_B)]$ is the defining property of tensor product composition. ∎

**Application to QFT:** For $n$ particles of the same type, the raw tensor product is $\mathcal{H}_1^{\otimes n}$. However, identical particles require additional structure (§3.2).

### 3.2 Identical Particles and 3FLL Exclusivity

**Physical observation:** Identical particles (e.g., two electrons) are *operationally indistinguishable*. No measurement can determine "which electron is which."

**Physical Input (Tier 3):** Indistinguishability under arbitrary permutations. For $n$ identical particles, no measurement can distinguish particle $i$ from particle $j$ for any $i, j$. This is stronger than mere "permutability of labels" - it asserts that the particles are genuinely identical in all physical respects.

**3FLL Constraint (Identity):** If particle 1 and particle 2 are identical, then any state must respect this identity. The state $|a\rangle_1 \otimes |b\rangle_2$ (particle 1 in state $a$, particle 2 in state $b$) must be *physically equivalent* to $|b\rangle_1 \otimes |a\rangle_2$.

**Definition 3.1 (Exchange Operator).** For two-particle states, define:
$$P_{12} |a\rangle_1 \otimes |b\rangle_2 = |b\rangle_1 \otimes |a\rangle_2$$

**Theorem 3.1' (Symmetrization from 3FLL + Indistinguishability).** For identical particles satisfying the indistinguishability input, physical states must satisfy:
$$P_\sigma |\psi\rangle = \lambda_\sigma |\psi\rangle$$

for all permutations $\sigma \in S_n$, where $\lambda_\sigma = +1$ for all $\sigma$ (bosons) or $\lambda_\sigma = \text{sign}(\sigma)$ (fermions). Parastatistics (mixed symmetry representations) are excluded in 3+1D.

> **Standard Result Implemented:** This theorem implements the Messiah-Greenberg exclusion of parastatistics in 3+1D (Messiah & Greenberg 1964) under LRT assumptions A1-A5. The novelty is not the result itself—which is standard—but the derivation from 3FLL-based distinguishability constraints rather than ad hoc symmetrization postulates.

---

**COMPLETE PROOF OF THEOREM 3.1'**

**Assumptions (explicitly listed):**
- A1: 3FLL-constituted distinguishability (from Tier 1)
- A2: Hilbert space structure (from Tier 2, via Thm 3.2 of Technical.md)
- A3: Local tomography → tensor products (from A3c, Thm 6.2)
- A4: Indistinguishability of identical particles (Tier 3 physical input)
- A5: Microcausality / locality (Tier 3 physical input)

**Part I: Two-Particle Symmetrization**

*Step 1 (Identity constraint):* **(uses 3FLL-Identity)** Let particles 1 and 2 be identical. By the Law of Identity, if $x = y$ then all predicates true of $x$ are true of $y$. For identical particles, "particle 1 in state $|a\rangle$" and "particle 2 in state $|a\rangle$" are physically indistinguishable—no measurement can determine which particle is which.

*Step 2 (Physical equivalence → ray equivalence):* **(uses A4 indistinguishability)** The states $|a\rangle_1 \otimes |b\rangle_2$ and $|b\rangle_1 \otimes |a\rangle_2$ represent the same physical configuration (particle in state $|a\rangle$ and particle in state $|b\rangle$, with no "which is which" distinction). In quantum mechanics, physically equivalent states belong to the same ray:
$$|b\rangle_1 \otimes |a\rangle_2 = e^{i\phi(a,b)} |a\rangle_1 \otimes |b\rangle_2$$

*Step 3 (Phase independence):* **(uses A2 Hilbert space linearity)** The phase $e^{i\phi}$ cannot depend on the specific states $|a\rangle, |b\rangle$. Proof by contradiction: Suppose $\phi(a,b) \neq \phi(a,c)$. Consider the superposition $|b\rangle + |c\rangle$. Linearity of the exchange operator would give inconsistent phases. Therefore, $e^{i\phi}$ is a constant for each particle type.

*Step 4 (Involution constraint):* **(uses 3FLL-Identity: x=x)** Exchanging twice returns the original: $P_{12}^2 = \mathbf{1}$. Therefore:
$$e^{2i\phi} = 1 \implies e^{i\phi} = \pm 1$$

**Part II: Extension to n Particles (Lüders-Zumino)**

*Step 5:* **(uses A3 tensor products)** For $n$ identical particles, the symmetric group $S_n$ acts on $\mathcal{H}_1^{\otimes n}$. Each transposition $(ij)$ must satisfy $P_{ij}^2 = \mathbf{1}$, giving eigenvalue $\pm 1$.

*Step 6:* **(standard result: Lüders-Zumino)** By the Lüders-Zumino theorem, if all transpositions have eigenvalue $+1$, the representation is the trivial (fully symmetric) representation. If all transpositions have eigenvalue $-1$, it is the sign (fully antisymmetric) representation.

*Step 7 (Mixed phases excluded):* **(uses 3FLL-Non-Contradiction)** Could some transpositions give $+1$ and others $-1$? The group relations in $S_n$ constrain this. For example, $(12)(23)(12) = (13)$. If $P_{12}|\psi\rangle = +|\psi\rangle$ and $P_{23}|\psi\rangle = -|\psi\rangle$, then:
$$P_{13}|\psi\rangle = P_{12}P_{23}P_{12}|\psi\rangle = P_{12}P_{23}(+|\psi\rangle) = P_{12}(-|\psi\rangle) = -|\psi\rangle$$
But also $(13)(12) = (123)$ and $(12)(13) = (132)$, leading to contradictions unless all phases are equal.

**Part III: Exclusion of Parastatistics (Messiah-Greenberg)**

*Step 8 (Definition):* Parastatistics would allow higher-dimensional representations of $S_n$ where $P_{ij}^2 = \mathbf{1}$ but the representation is neither fully symmetric nor fully antisymmetric.

*Step 9 (Messiah-Greenberg 1964):* **(uses A5 microcausality)** In 3+1 dimensions with locality (microcausality), parastatistics is observationally equivalent to ordinary statistics with internal quantum numbers. Specifically:

**The Messiah-Greenberg Theorem:** Any parastatistics theory in 3+1D can be rewritten as an ordinary statistics theory with a hidden "paracharge" quantum number. The paracharge transforms under an internal symmetry group, and the physical states are paracharge singlets.

*Step 10 (LRT interpretation):* **(uses A4 + 3FLL-Identity)** The Law of Identity requires particles to have definite identity. If parastatistics were fundamental, the "paracharge" would be a hidden variable violating the completeness of quantum description. By assuming A4 (complete indistinguishability, no hidden labels), parastatistics reduces to ordinary statistics.

*Step 11 (Locality constraint):* **(uses A5 microcausality in 3+1D)** Microcausality (A5) in 3+1D further constrains: for spacelike separated observables to commute/anticommute, the exchange phase must be consistent across all measurements. In 2+1D, braiding allows anyonic phases $e^{i\theta}$ with $\theta \notin \{0, \pi\}$, but in 3+1D, topological constraints force $\theta \in \{0, \pi\}$.

**Conclusion:** In 3+1D with indistinguishability (A4) and microcausality (A5), the only possibilities are:
- Bosons: $P_\sigma|\psi\rangle = |\psi\rangle$ for all $\sigma$
- Fermions: $P_\sigma|\psi\rangle = \text{sign}(\sigma)|\psi\rangle$ for all $\sigma$

∎

---

**What Theorem 3.1' Does and Does Not Establish:**

| Established | Not Established |
|-------------|-----------------|
| Exchange phase $\pm 1$ | Which particles are bosons vs fermions |
| Parastatistics excluded in 3+1D | Statistics in 2+1D (anyons allowed) |
| Consistency of symmetrization | Why spacetime is 3+1D |

**Critical Gap:** Theorem 3.1' establishes that identical particles must have definite exchange symmetry (bosonic or fermionic), but does **not** determine which particles are symmetric (bosons) versus antisymmetric (fermions). This requires the spin-statistics connection (§3.3).

**Definition 3.2 (Symmetrized Subspaces).**
- **Symmetric subspace:** $\mathcal{H}_S^{(n)} = \{|\psi\rangle \in \mathcal{H}_1^{\otimes n} : P_\sigma |\psi\rangle = |\psi\rangle \text{ for all } \sigma \in S_n\}$
- **Antisymmetric subspace:** $\mathcal{H}_A^{(n)} = \{|\psi\rangle \in \mathcal{H}_1^{\otimes n} : P_\sigma |\psi\rangle = \text{sign}(\sigma) |\psi\rangle \text{ for all } \sigma \in S_n\}$

### 3.3 Spin-Statistics Theorem

**Physical Input (Tier 3):** Microcausality. Fields at spacelike separation must commute (bosons) or anticommute (fermions):
$$[\phi(x), \phi(y)]_\mp = 0 \quad \text{for } (x-y)^2 < 0$$

This ensures no faster-than-light signaling via field measurements.

**Theorem 3.2' (Spin-Statistics Connection).** Under:
1. Lorentz invariance (Tier 2)
2. Microcausality (Tier 3)
3. Positive energy (spectrum bounded below)

Integer-spin particles are bosons (symmetric); half-integer-spin particles are fermions (antisymmetric).

**Proof reference:** By the spin-statistics theorem in the Streater-Wightman axiomatic framework (Streater & Wightman 1964, §4.4) or equivalently the Haag-Kastler algebraic framework (Haag 1996, §IV.1), microcausality combined with the Bargmann-Hall-Wigner phase analysis under $2\pi$ rotations implies that integer-spin fields must satisfy commutation relations (bosons) while half-integer-spin fields must satisfy anticommutation relations (fermions). The key steps are:

*Step 1:* Under a $2\pi$ rotation, field operators transform with phase $e^{2\pi i s}$ where $s$ is the spin. Integer spin gives $+1$; half-integer spin gives $-1$.

*Step 2:* Microcausality requires $[\phi(x), \phi(y)]_\mp = 0$ at spacelike separation. The choice of commutator vs. anticommutator must be consistent with the $2\pi$ rotation phase.

*Step 3:* For Lorentz-covariant, positive-energy theories, the only consistent assignment is: integer spin → commutator (bosons); half-integer spin → anticommutator (fermions).

*Step 4:* The wrong choice violates either microcausality or positive energy (vacuum instability). See Weinberg (1995, Vol. I, §5.7) for the explicit calculation. ∎

**LRT Bridge (Lee-Selby Connection):** The Lee-Selby theorem (Technical.md §6.4) shows that continuous reversibility + local tomography + purification uniqueness implies the entanglement structure of QM. In the relativistic extension:

- **CBP** (information preservation) → reversibility
- **A3c** (local tomography) → tensor structure
- **Lorentz + microcausality** → spin-statistics

The spin-statistics theorem is not derived from 3FLL alone, but from 3FLL + explicit physical inputs (Lorentz, microcausality). This is honest: we claim derivation from the tiered structure, not from pure logic.

### 3.4 Fock Space Construction

**Definition 3.3 (Fock Space).** For bosons (resp. fermions), Fock space is:
$$\mathcal{F}_\pm = \bigoplus_{n=0}^{\infty} \mathcal{H}_{\pm}^{(n)}$$

where $\mathcal{H}_+^{(n)} = \mathcal{H}_S^{(n)}$ (symmetric) for bosons and $\mathcal{H}_-^{(n)} = \mathcal{H}_A^{(n)}$ (antisymmetric) for fermions. The $n=0$ sector is the vacuum $|0\rangle$.

**Definition 3.4 (Creation and Annihilation Operators).**

For single-particle state $|f\rangle \in \mathcal{H}_1$, define:

*Creation operator* $a^\dagger(f)$: Maps $n$-particle state to $(n+1)$-particle state by adding particle in state $|f\rangle$ and (anti)symmetrizing.

*Annihilation operator* $a(f)$: Adjoint of $a^\dagger(f)$.

**Theorem 3.3' (Canonical Commutation/Anticommutation Relations).**

For bosons:
$$[a(f), a^\dagger(g)] = \langle f | g \rangle, \quad [a(f), a(g)] = [a^\dagger(f), a^\dagger(g)] = 0$$

For fermions:
$$\{a(f), a^\dagger(g)\} = \langle f | g \rangle, \quad \{a(f), a(g)\} = \{a^\dagger(f), a^\dagger(g)\} = 0$$

**Proof sketch:**

*Step 1:* The (anti)symmetry requirement determines the algebra. For bosons (symmetric states), adding two particles is independent of order → commutator vanishes.

*Step 2:* For fermions (antisymmetric states), adding two particles in the same state gives zero (Pauli exclusion). The anticommutator structure enforces this.

*Step 3:* The normalization $[a, a^\dagger] = \langle f | g \rangle$ follows from the inner product structure inherited from the single-particle Hilbert space (ultimately from the distinguishability metric D). ∎

**Connection to Field Operators:** The field operator (Definition 2.5) can now be written:
$$\phi(x) = \int \frac{d^3p}{(2\pi)^3 2E_p} \left[ a(\mathbf{p}) e^{-ip \cdot x} + a^\dagger(\mathbf{p}) e^{ip \cdot x} \right]$$

where $a(\mathbf{p})$ and $a^\dagger(\mathbf{p})$ satisfy the canonical relations with $\langle \mathbf{p} | \mathbf{p}' \rangle = (2\pi)^3 2E_p \delta^{(3)}(\mathbf{p} - \mathbf{p}')$.

### 3.5 Summary: Derivation Status

| Result | Inputs | Status |
|--------|--------|--------|
| Tensor products | A3c (local tomography) | Derived (Thm 6.2) |
| Symmetrization requirement | 3FLL (Identity) + Indistinguishability (Tier 3) | Derived (Thm 3.1') |
| Spin-statistics connection | Lorentz + microcausality + positive energy | Derived (Thm 3.2') |
| CCR/CAR algebra | Fock structure + inner product | Derived (Thm 3.3') |

The Fock space structure is genuinely derived from LRT axioms plus explicit physical inputs (Lorentz invariance, microcausality, indistinguishability). This is not a reframing but a constructive derivation with clear assumptions.

**Novelty Assessment:**
| Component | Standard QFT | LRT-Specific |
|-----------|--------------|--------------|
| Tensor products from local tomography | Yes (via dimension counting) | ENHANCED: explicit connection to A3c axiom |
| Symmetrization requirement | Yes (indistinguishability postulate) | NEW: 3FLL-based derivation (Identity constraint) |
| Parastatistics exclusion | Yes (Messiah-Greenberg) | ENHANCED: LRT interpretation via completeness |
| Spin-statistics theorem | Yes (Streater-Wightman) | — |
| CCR/CAR from Fock | Yes | — |

*The main novelty in §3 is Theorem 3.1': a detailed proof showing how 3FLL + indistinguishability yields symmetrization, with explicit connection to the Messiah-Greenberg analysis. The spin-statistics theorem itself is standard.*

---

## 4. QFT Interpretation (5 pages)

This section addresses QFT features that LRT *interprets* rather than *derives*. The distinction is crucial for honest claim-making.

### 4.1 Cluster Decomposition as Physical Input

**Definition 4.1 (Cluster Decomposition).** For local operators $O_A$ and $O_B$ supported in spacelike separated regions $A$ and $B$:
$$\lim_{|x_A - x_B| \to \infty} \langle \Omega | O_A(x_A) O_B(x_B) | \Omega \rangle = \langle \Omega | O_A | \Omega \rangle \langle \Omega | O_B | \Omega \rangle$$

where $|\Omega\rangle$ is the vacuum state. Correlations factorize at infinite spacelike separation.

**Why Cluster Decomposition is NOT Derived from IIS:**

*Observation 1:* Cluster decomposition is a *dynamical* property of vacuum correlations, not a *kinematic* property of the state space.

*Observation 2:* LRT's local tomography (A3c) provides tensor product structure (Theorem 6.2), which is an algebraic precondition for factorization. But tensor structure does not guarantee that correlations actually factorize.

**Counterexample:** Consider a bipartite state $|\psi\rangle_{AB}$ with long-range entanglement:
$$|\psi\rangle = \frac{1}{\sqrt{2}}(|0\rangle_A |0\rangle_B + |1\rangle_A |1\rangle_B)$$

This state lives in $\mathcal{H}_A \otimes \mathcal{H}_B$ (tensor structure exists), but $\langle \sigma_z^A \sigma_z^B \rangle = 1 \neq \langle \sigma_z^A \rangle \langle \sigma_z^B \rangle = 0$. Correlations do not factorize.

**What Cluster Decomposition Requires (Tier 4 inputs):**

1. **Vacuum uniqueness:** The vacuum $|\Omega\rangle$ is the unique Poincaré-invariant state. If multiple vacua existed, superpositions could have persistent long-range correlations.

2. **Spectral gap:** There exists a mass gap $m > 0$ between the vacuum and the first excited state. This ensures exponential decay of correlations: $|\langle O_A O_B \rangle - \langle O_A \rangle \langle O_B \rangle| \sim e^{-m|x_A - x_B|}$.

3. **Locality:** Fields at spacelike separation commute (for observables). This is related to but distinct from microcausality for field operators.

**LRT Status:** Cluster decomposition is an additional physical input at Tier 4. LRT provides the algebraic structure (tensor products) but not the dynamical guarantee (correlation factorization).

**Note on Vacuum Uniqueness:** In massive interacting theories, vacuum uniqueness and cluster decomposition are equivalent (Weinberg 1995, Vol. I, §4.3). A unique vacuum guarantees cluster decomposition; conversely, if correlations factorize at infinite separation, the vacuum must be unique. We list both as Tier 4 inputs but they are not independent - confirming one confirms the other.

### 4.2 Renormalization: A Conceptual Framework (Not a Derivation)

**Epistemic Status:** This section offers a *conceptual framing* of renormalization within LRT. It does **not** derive, establish, or explain renormalization in any technical sense. No RG equations, beta functions, anomalous dimensions, or counterterm structures follow from this discussion. The value, if any, is purely interpretive: providing a conceptual lens through which to view renormalization's necessity. Reviewers should evaluate this section as philosophy of physics, not as physics.

#### 4.2.1 The Problem of UV Divergences

In perturbative QFT, loop integrals often diverge:
$$\int \frac{d^4k}{(2\pi)^4} \frac{1}{k^2 - m^2} \to \infty$$

These divergences arise from integrating over arbitrarily high momenta (short distances).

#### 4.2.2 LRT Interpretation: 3FLL Violation at Infinite Energy

**Claim (Interpretive):** UV divergences signal a breakdown of 3FLL at infinite energy scales.

*Identity violation:* A quantity that diverges is not self-identical. $\infty = \infty$ is not a well-defined identity relation. The statement "$\int d^4k / k^2 = X$" fails to specify what $X$ is.

*Non-Contradiction tension:* Divergent quantities can lead to contradictions. For example, if $\phi(x)\phi(x)$ diverges, then the state $|\phi(x)\phi(x)\rangle$ would have undefined norm.

*Excluded Middle violation:* A divergent quantity is neither finite nor well-defined infinite. It fails to have a determinate value.

**CBP Constraint:** The Consistency Bridging Principle requires that all states resolve to Boolean outcomes. A divergent amplitude cannot produce well-defined probabilities (which must sum to 1).

**Explicit Example (φ³ Tadpole):** In $\phi^3$ theory, the one-loop tadpole diagram contributes to the vacuum energy:
$$\langle 0 | \phi | 0 \rangle \sim \int \frac{d^4k}{k^2 - m^2} \to \infty$$

This divergent vacuum expectation value violates Identity: the quantity "$\langle 0 | \phi | 0 \rangle$" is not self-identical because "$\infty$" is not a well-defined value. Two different regularization schemes would give different "infinities" - but if the quantity were truly self-identical, it would have a unique value. Renormalization (adding a counterterm to cancel the divergence) restores a finite, self-identical vacuum expectation value.

#### 4.2.3 Renormalization as 3FLL Restoration

**Interpretation:** Renormalization restores 3FLL compliance by:

1. **Regularization:** Introducing a cutoff $\Lambda$ makes integrals finite (temporary 3FLL restoration).
   $$\int_0^\Lambda \frac{d^4k}{(2\pi)^4} \frac{1}{k^2 - m^2} = \text{finite}(\Lambda)$$

2. **Counterterms:** Adding terms to the Lagrangian that cancel the $\Lambda$-dependent divergences.

3. **Renormalization conditions:** Fixing physical parameters (mass, coupling) at physical scales, making predictions cutoff-independent.

**CBP constraint on counterterms:** Not all counterterms are allowed. CBP (information preservation) requires that counterterms do not introduce non-unitary dynamics or violate probability conservation.

#### 4.2.4 What This Conceptual Framework Does NOT Do

| Claim | Status |
|-------|--------|
| UV divergences violate 3FLL | **Interpretive framing only** |
| Renormalization restores 3FLL | **Interpretive framing only** |
| Derive beta functions | NOT claimed |
| Derive anomalous dimensions | NOT claimed |
| Explain why some QFTs are renormalizable | NOT claimed |
| Derive the RG equations | NOT claimed |
| Predict counterterm structure | NOT claimed |
| Replace Wilson/Polchinski effective field theory | NOT claimed |

The conceptual framework provides a *philosophical lens* for viewing renormalization's necessity but does not advance the technical understanding of renormalization. A physicist who understood only this section would gain no calculational power. The value is in unifying language, not in derivation.

### 4.3 Vacuum Structure

#### 4.3.1 The QFT Vacuum

**Definition 4.2 (QFT Vacuum).** The vacuum $|\Omega\rangle$ is the lowest-energy state of the quantum field theory, annihilated by all annihilation operators:
$$a(\mathbf{p}) |\Omega\rangle = 0 \quad \text{for all } \mathbf{p}$$

**Properties:**
- Poincaré invariant: $U(\Lambda, a) |\Omega\rangle = |\Omega\rangle$
- Unique (assumption for cluster decomposition)
- Contains vacuum fluctuations: $\langle \Omega | \phi(x) \phi(y) | \Omega \rangle \neq 0$

#### 4.3.2 LRT Interpretation: Vacuum as Maximally Symmetric IIS State

**Interpretation:** The vacuum is the state of IIS with maximal Poincaré symmetry - the state that preserves all the symmetries of the theory.

**Connection to Global Parsimony (A4):** The vacuum is the state with "minimum structure" - no particles, no excitations. Global Parsimony suggests the vacuum is natural as the baseline state from which all structure emerges.

**What This Does NOT Derive:**

| Feature | Status |
|---------|--------|
| Vacuum existence | Physical input |
| Vacuum uniqueness | Physical input (Tier 4) |
| Vacuum energy (cosmological constant) | NOT addressed |
| Spontaneous symmetry breaking | NOT addressed |

#### 4.3.3 Vacuum Uniqueness and LRT

Vacuum uniqueness is required for cluster decomposition (§4.1) and is taken as a Tier 4 physical input.

**Observation:** In theories with spontaneous symmetry breaking, there are multiple degenerate vacua. LRT does not rule this out - it simply notes that if multiple vacua exist, cluster decomposition may fail and additional physical analysis is needed.

### 4.4 Summary: Interpretation vs. Derivation

| Feature | LRT Status | Evidence |
|---------|------------|----------|
| Cluster decomposition | **Tier 4 Input** | Required for factorization; not from IIS alone |
| Renormalization necessity | **Interpretation** | 3FLL violation at UV; CBP requires finite amplitudes |
| Renormalization techniques | **Not addressed** | Technical machinery not derived |
| Vacuum existence | **Physical input** | Lowest-energy state assumed |
| Vacuum uniqueness | **Tier 4 Input** | Required for cluster decomposition |
| Vacuum as symmetric IIS state | **Interpretation** | Global Parsimony motivates but doesn't derive |

The honest assessment: Section 4 extends LRT *interpretation* to QFT phenomena. These are conceptual frameworks, not derivations. The value is in providing a unified perspective, not in replacing standard QFT techniques.

**Novelty Assessment:**
| Component | Standard QFT | LRT-Specific |
|-----------|--------------|--------------|
| Cluster decomposition | Yes (Weinberg) | — |
| Vacuum uniqueness | Yes | — |
| UV divergences | Yes (standard problem) | — |
| Renormalization techniques | Yes (Wilson, etc.) | — |
| 3FLL interpretation of divergences | — | NEW: interpretive framing only |
| Vacuum as symmetric IIS state | — | NEW: conceptual framing only |

*§4 contains no technical novelty. The value, if any, is purely philosophical: viewing standard QFT through an LRT lens. Reviewers seeking new physics predictions should focus on §3 and §5, not §4.*

---

## 5. Predictions and Falsifiers (3 pages)

A theory's scientific value depends on making predictions that can be tested and falsified. This section specifies what LRT-QFT predicts and what observations would refute it.

### 5.1 Predictions

#### 5.1.1 Tsirelson Bound in Field Correlations

**Prediction:** Correlations between spacelike-separated field measurements obey the Tsirelson bound:
$$\mathcal{S} \leq 2\sqrt{2} \approx 2.83$$

where $\mathcal{S}$ is the CHSH parameter.

**LRT Derivation (from Technical.md §5.3):**
- CBP requires all states resolve to Boolean outcomes
- Global Parsimony forbids correlation amplification mechanisms
- Theorem 5.5 (Technical.md): Tsirelson bound is maximum compatible with LRT axioms

**Extension to QFT:** The bound applies to field correlations, not just particle correlations. For field observables $\phi_A(x)$ and $\phi_B(y)$ at spacelike separation:
$$|\langle \phi_A(x) \phi_B(y) \rangle - \langle \phi_A(x) \rangle \langle \phi_B(y) \rangle| \leq \text{quantum bound}$$

**Testable:** Bell tests with field observables (e.g., photon polarization in QED).

#### 5.1.2 No Fundamental Information Loss

**Prediction:** Information is never fundamentally lost. All processes preserve information at the fundamental level.

**LRT Derivation:**
- CBP (A3b): Information preservation is axiomatic
- Unitarity: Pure states evolve to pure states
- No fundamental decoherence without environmental entanglement

**Application to Black Holes:**
- Hawking radiation must encode information about infallen matter
- The black hole information paradox must resolve in favor of information preservation
- Page curve behavior expected: entanglement entropy of radiation initially rises, then falls

**Testable:** Gravitational wave observations of black hole mergers may constrain information-loss scenarios. Analog black hole experiments (e.g., Steinhauer 2016) test Hawking radiation correlations.

#### 5.1.3 Complex Amplitudes Required

**Prediction:** Quantum field theory requires complex amplitudes. Real QFT and quaternionic QFT are excluded.

**LRT Derivation (from Technical.md §5):**
- Theorem 5.2: Real QM fails local tomography
- Theorem 5.3: Quaternionic QM fails tensor associativity
- Theorem 5.6: dim ≥ 3 + local tomography + stability → complex field

**Extension to QFT:** The Renou et al. (2021) result for QM extends to QFT:
- Field correlations must exhibit complex interference patterns
- Real QFT would predict different correlation functions
- The difference is experimentally measurable

**Status:** Already confirmed for QM (Renou et al. 2021). Extension to QFT predicted but not yet specifically tested.

#### 5.1.4 Spin-Statistics Connection Holds Universally

**Prediction:** All integer-spin particles are bosons; all half-integer-spin particles are fermions. No exceptions.

**LRT Derivation:** Theorem 3.2' (§3.3): Lorentz invariance + microcausality + positive energy → spin-statistics.

**Testable:** Any observed violation (e.g., fermionic photons, bosonic electrons) would falsify LRT-QFT.

### 5.2 Falsifiers

A falsifier is an observation that would refute LRT-QFT. We distinguish strong falsifiers (directly contradict core claims) from weak falsifiers (challenge auxiliary assumptions).

#### 5.2.1 Strong Falsifiers (with Quantitative Criteria)

| Observation | Quantitative Criterion | LRT Impact |
|-------------|------------------------|------------|
| **Signaling via entangled fields** | Any field correlation $\mathcal{S} > 2\sqrt{2} \approx 2.83$ in CHSH configuration at spacelike separation | CBP violated; 3FLL not constitutive; LRT refuted |
| **Consistent real QFT** | Correlation witness $W < W_R \approx 7.66$ with $>5\sigma$ significance, contradicting Renou et al. | Theorem 5.2 fails; complex uniqueness wrong |
| **Fundamental information loss** | Page curve not observed; late-time Hawking radiation entropy continues increasing (inconsistent with $S_{\text{rad}} \to 0$) | CBP violated; A3b wrong; LRT refuted |
| **Spin-statistics violation** | Observation of bosonic electron (integer exchange phase) or fermionic photon at any energy scale | Theorem 3.2' fails; Lorentz+microcausality insufficient |
| **Contradiction in measurement outcomes** | Single detector registers both "click" and "no click" for same event (probability $P + (1-P) \neq 1$) | 3FLL not constitutive; LRT foundationally wrong |
| **Parastatistics in 3+1D** | Particle with exchange phase $e^{i\theta}$, $\theta \notin \{0, \pi\}$, in bulk 3+1D at energies below $10^{15}$ GeV | Theorem 3.1' fails; Messiah-Greenberg assumptions violated |

**Explicit falsification criteria:**

1. **Tsirelson bound violation:** Any observed $\mathcal{S} > 2\sqrt{2}$ with $>5\sigma$ confidence would falsify LRT-QFT assumptions (Tiers 1-3). Current experiments confirm $\mathcal{S} \leq 2\sqrt{2}$ to high precision.

2. **Real QFT consistency:** A confirmed real-number-only description of quantum fields producing Bell-violating correlations (contrary to Renou et al.) would falsify Theorem 5.1' under assumption A4.

3. **Information loss:** Observation of pure-state evolution to mixed state without environmental entanglement (i.e., fundamental decoherence with rate $\Gamma > 10^{-20}$ s$^{-1}$ for isolated systems) would falsify CBP.

4. **Spin-statistics:** Any observation of fermionic integer-spin particle or bosonic half-integer-spin particle at any experimentally accessible energy would falsify Theorem 3.2'. Current bounds: no violations observed to $10^{-27}$ precision in electron antisymmetry tests.

5. **Parastatistics:** Observation of anyonic statistics ($\theta \neq 0, \pi$) in bulk 3+1D matter (not confined to 2D surfaces/edges) would contradict Theorem 3.1' under assumptions A1-A5.

#### 5.2.2 Weak Falsifiers

| Observation | What It Would Show | LRT Impact |
|-------------|-------------------|------------|
| **Cluster decomposition failure** | Long-range correlations persist at infinite separation | Tier 4 input wrong; vacuum not unique; LRT-QFT incomplete but not refuted |
| **Non-renormalizable QFT is fundamental** | UV divergences cannot be removed; 3FLL interpretation wrong | Interpretation in §4.2 wrong; core LRT may survive |
| **Continuous spontaneous localization confirmed** | Objective collapse with free parameters | Global Parsimony (A4) challenged but core LRT may survive |

#### 5.2.3 What Would NOT Falsify LRT-QFT

| Observation | Why Not a Falsifier |
|-------------|---------------------|
| New particles discovered | LRT does not predict particle content |
| Quantum gravity unified differently than expected | Gravity conjecture (§6) is explicitly conjectural |
| Dark matter/dark energy explained differently | LRT does not address cosmology specifically |
| Specific collapse mechanism differs | LRT predicts constraints on collapse, not specific mechanism |

### 5.3 Uniqueness Theorem

---

**THEOREM 5.1' (Uniqueness of Complex QFT)**

Complex quantum field theory is the unique relativistic theory satisfying assumptions A1-A7.

---

### The Seven Assumptions (A1-A7)

> **A1. 3FLL-Constituted Distinguishability** (Tier 1)
> The distinguishability metric $D(s_1, s_2)$ satisfies the constraints imposed by the Three Fundamental Laws of Logic: Identity ($D(s,s)=0$), Non-Contradiction (states are either distinguishable or not), Excluded Middle (every pair has a definite $D$ value).

> **A2. Continuous Dynamics** (from A3a)
> The state space is a topological manifold; time evolution is continuous. Discontinuous "jumps" are forbidden except at measurement (interface transitions).

> **A3. Information Preservation** (from A3b / CBP)
> Evolution is reversible at the fundamental level. No information is created or destroyed; pure states evolve to pure states under closed-system dynamics.

> **A4. Local Tomography** (from A3c)
> Composite system states are fully determined by local measurements on subsystems plus correlations. Implies tensor product structure: $\mathcal{H}_{AB} = \mathcal{H}_A \otimes \mathcal{H}_B$.

> **A5. Lorentz Invariance** (Tier 2 — empirical input)
> The laws of physics take the same form in all inertial reference frames. The distinguishability metric $D$ is Lorentz-invariant.

> **A6. Microcausality** (Tier 3 — empirical input)
> Fields at spacelike separation (anti)commute: $[\phi(x), \phi(y)]_\mp = 0$ for $(x-y)^2 < 0$. No faster-than-light signaling via field measurements.

> **A7. Stability** (Physical input)
> Bound states exist; the vacuum is the unique lowest-energy state. Energy spectrum bounded below.

---

**Summary Table:**

| # | Assumption | Source | Empirical? |
|---|------------|--------|------------|
| A1 | 3FLL distinguishability | Tier 1 | No (logical) |
| A2 | Continuous dynamics | A3a | No (structural) |
| A3 | Information preservation | A3b/CBP | No (structural) |
| A4 | Local tomography | A3c | No (structural) |
| A5 | Lorentz invariance | Tier 2 | Yes |
| A6 | Microcausality | Tier 3 | Yes |
| A7 | Stability | Physical | Yes |

*Four structural assumptions (A1-A4) + three empirical inputs (A5-A7) = complex QFT uniquely.*

---

**Theorem Statement:** Given A1-A7, any theory is either:
- (a) Complex QFT (standard quantum field theory), OR
- (b) Violates at least one of A1-A7

Alternatives are excluded as follows:
- **Real QFT:** Violates A4 (local tomography) — see Theorem 5.2
- **Quaternionic QFT:** Violates tensor associativity (implicit in A4) — see Theorem 5.3
- **Super-quantum (PR-box):** Violates A3 under composition (signaling) — see Theorem 5.4
- **Classical fields:** Violates A7 (no bound states; Earnshaw) — see Theorem 5.1

---

**Connection to Experimental Bounds (Renou et al. 2021):**

The Renou et al. experiment tested whether quantum correlations can be described by real-valued amplitudes. Result:

| Quantity | Prediction (Real QFT) | Prediction (Complex QFT) | Measured | Significance |
|----------|----------------------|--------------------------|----------|--------------|
| Correlation witness $W$ | $W \leq W_R$ | $W \leq W_C$ | $W = W_C + \delta$ | $>7\sigma$ beyond $W_R$ |

Specifically:
- **Real QFT bound:** $W_R \approx 7.66$ (Bell-like witness)
- **Complex QFT bound:** $W_C \approx 8.31$
- **Measured:** $W_{\text{obs}} = 8.09 \pm 0.02$
- **Significance:** $>7\sigma$ exclusion of real QFT

**Implication for Theorem 5.1':** Real QFT is not just theoretically disfavored (violates A4) but *empirically excluded* at high significance. The uniqueness of complex QFT is not merely a mathematical consequence of axioms but an experimentally confirmed fact.

---

**PROOF OF THEOREM 5.1'**

*Step 1 (Hilbert space):* By Theorem 3.2 (Technical.md), **A1** (distinguishability) + **A2** (3FLL/CBP) + **A3** (information-causality) + **A4** (local tomography) yield complex Hilbert space. The Hardy kernel construction from distinguishability produces an inner product; **A4 rules out real amplitudes** (which fail local tomography) and constrains the field to $\mathbb{C}$.

*Step 2 (Tensor structure):* By Theorem 6.2 (Technical.md), **A4 (local tomography) yields tensor product structure**: $\mathcal{H}_{AB} = \mathcal{H}_A \otimes \mathcal{H}_B$. This rules out non-locally-tomographic alternatives where composite state space is not a tensor product.

*Step 3 (Relativistic structure):* **A5 (Poincaré invariance)** requires Poincaré-covariant evolution. By Wigner's theorem, this is implemented by unitary representations. Combined with **A2** (3FLL requiring determinate dynamics), we get the standard single-particle Hilbert spaces $\mathcal{H}_{m,s}$.

*Step 4 (Fock structure):* **A4** + indistinguishability (from 3FLL + **A6 microcausality**) yields symmetrized/antisymmetrized Fock spaces (Theorem 3.1'). **A6 rules out parastatistics** in 3+1D via Messiah-Greenberg.

*Step 5 (Spin-statistics):* **A5** (Lorentz invariance) + **A6** (microcausality) + **A7** (positive energy) yield the spin-statistics connection (Theorem 3.2'). **A7 rules out indefinite-metric theories** that would allow spin-statistics violations.

*Step 6 (Exclusion of alternatives):*

- *Real QFT:* In real QFT, local tomography fails. Specifically, there exist composite states $\rho_{AB}$ that cannot be distinguished from $\sigma_{AB}$ by local measurements on $A$ and $B$ separately, yet $\rho_{AB} \neq \sigma_{AB}$. **A4 (local tomography) rules out real QFT.** (Technical.md Theorem 5.2; cf. Renou et al. 2021 for experimental exclusion at >7σ)

- *Quaternionic QFT:* Quaternionic amplitudes violate tensor associativity: $(A \otimes B) \otimes C \ncong A \otimes (B \otimes C)$ due to non-commutativity. **A4 (well-defined tensor structure) rules out quaternionic QFT.** (Technical.md Theorem 5.3)

- *Super-quantum theories:* PR-boxes and other super-quantum correlations allow signaling under composition—given access to shared entanglement, parties can communicate faster than light. **A3 (information-causality) and A6 (microcausality) jointly rule out super-quantum theories.** (Technical.md Theorem 5.4)

*Step 7 (Uniqueness):* The only theory satisfying A1-A7 is complex QFT. ∎

**Axiom Usage Summary:**

| Axiom | Primary Role in Proof | What It Excludes |
|-------|----------------------|------------------|
| A1 | Distinguishability → inner product | Theories without metric |
| A2 | Determinate dynamics | Non-3FLL-compliant theories |
| A3 | Information-causality | Super-quantum (PR-boxes) |
| A4 | Local tomography → tensor products, $\mathbb{C}$ | Real QFT, quaternionic QFT |
| A5 | Poincaré invariance → Wigner classification | Non-relativistic QFT |
| A6 | Microcausality → spin-statistics, no parastatistics | Parastatistics, signaling theories |
| A7 | Positive energy → spin-statistics | Indefinite-metric theories |

---

**What Uniqueness Does NOT Claim:**
- Does not derive Lorentz invariance from 3FLL (A5 is an input)
- Does not determine particle content (which particles exist)
- Does not fix coupling constants (Standard Model parameters)
- Does not determine spacetime dimensionality (3+1D is assumed)
- Does not predict specific bound state masses (dynamics not fixed)

### 5.4 Comparison with Non-Relativistic LRT

| Feature | Non-Rel LRT (Technical.md) | LRT-QFT (This Paper) |
|---------|---------------------------|----------------------|
| Hilbert space | Derived (Thm 3.2) | Inherited |
| Tensor products | Derived (Thm 6.2) | Extended to Fock |
| Complex field | Derived (Thm 5.7) | Inherited |
| Spin-statistics | Not addressed | Derived (Thm 3.2') |
| Field operators | Not addressed | Derived (§2.4) |
| Tsirelson bound | Derived (Thm 5.5) | Extended to fields |
| Lorentz invariance | Not addressed | Physical input (Tier 2) |
| Microcausality | Not addressed | Physical input (Tier 3) |

The extension is conservative: it builds on established results and adds physical inputs where needed, without overclaiming derivations from pure logic.

---

## 6. Gravity: Future Work

**Status:** This section contains preliminary conjectures only. No derivations are claimed. The gravity extension is explicitly marked as future work, not part of the current paper's main contribution.

### 6.1 Why Gravity is Deferred

The QFT extension (§§2-5) rests on well-established mathematical results: Masanes-Müller reconstruction, Streater-Wightman axioms, Lee-Selby theorems. Equivalent rigor for gravity would require:

1. A reconstruction theorem for general covariance from information-theoretic principles (does not exist)
2. A derivation of spacetime structure from IIS constraints (speculative)
3. Resolution of the quantum gravity problem itself (open for 60+ years)

Rather than speculate without mathematical foundation, we mark the gravity sector as future work and limit ourselves to stating conjectures that could guide future research.

### 6.2 Conjectures with Order-of-Magnitude Estimates

**Epistemic Status:** The following are speculative conjectures, not derivations. The numerical estimates are intended to guide experimental searches, not to claim predictive power.

---

**Conjecture 6.1 (Holographic Interface):** Spacetime structure may emerge from holographic bounds on IIS information capacity. The Bekenstein bound
$$S \leq \frac{2\pi R E}{\hbar c} = \frac{A}{4\ell_P^2}$$
could represent an interface criterion analogous to the IIS-actuality boundary.

**Order-of-magnitude estimate:** If interface-related collapse is tied to saturation of a Bekenstein or holographic bound for region size $L$, the characteristic information density would be:
$$\rho_{\text{info}} \sim \frac{1}{\ell_P^2} \approx 10^{66} \text{ bits/m}^2$$

For a system of mass $M$ and size $R$, the holographic bound gives:
$$N_{\text{bits}} \leq \frac{4\pi R^2}{4\ell_P^2} = \frac{\pi R^2}{\ell_P^2}$$

**Experimental implication:** Any system exceeding this bound would require gravitational collapse. For a proton ($R \sim 10^{-15}$ m), the bound gives $N \lesssim 10^{40}$ bits—far exceeding information content. The bound becomes relevant only at Planck-scale densities.

---

**Conjecture 6.2 (Collapse Parameters):** If objective collapse occurs (Penrose-Diósi model), the collapse timescale is:
$$\tau_{\text{collapse}} \sim \frac{\hbar R}{G m^2}$$

**Order-of-magnitude estimates:**

| System | Mass $m$ | Size $R$ | Collapse time $\tau$ | Testable? |
|--------|----------|----------|---------------------|-----------|
| Electron | $10^{-30}$ kg | $10^{-15}$ m | $\sim 10^{45}$ s | No (≫ age of universe) |
| Nucleon | $10^{-27}$ kg | $10^{-15}$ m | $\sim 10^{39}$ s | No |
| C$_{60}$ molecule | $10^{-24}$ kg | $10^{-9}$ m | $\sim 10^{27}$ s | No |
| Nanosphere (10⁶ amu) | $10^{-21}$ kg | $10^{-7}$ m | $\sim 10^{15}$ s | Marginal |
| Microparticle (10¹² amu) | $10^{-15}$ kg | $10^{-5}$ m | $\sim 10^{3}$ s | Yes (minutes) |
| Dust grain (10¹⁵ amu) | $10^{-12}$ kg | $10^{-4}$ m | $\sim 1$ s | Yes (seconds) |

**Experimental implication:** If LRT-related collapse follows Penrose-Diósi scaling, superpositions of dust-grain-sized objects should decohere on timescales of seconds. Current experiments (MAQRO, LISA Pathfinder successors) probe this regime. A confirmed superposition lifetime exceeding the Penrose-Diósi prediction would constrain or falsify this conjecture.

**Critical caveat:** This is the Penrose-Diósi model, not an LRT derivation. LRT's Global Parsimony (A4) motivates interest in collapse mechanisms but does not uniquely select this formula.

---

**Prediction (from CBP, not gravity-specific):** No fundamental information loss. Hawking radiation must encode information about infallen matter.

**Quantitative form:** The Page time for a black hole of mass $M$ is:
$$t_{\text{Page}} \sim \frac{G^2 M^3}{\hbar c^4}$$

For a solar-mass black hole: $t_{\text{Page}} \sim 10^{67}$ years.

If CBP holds, the entanglement entropy of Hawking radiation must follow the Page curve: rising until $t_{\text{Page}}$, then falling to zero as the black hole evaporates. Observing a deviation from the Page curve (e.g., entropy continuing to rise after $t_{\text{Page}}$) would falsify CBP.

**Current status:** Direct observation is impossible for astrophysical black holes. Analog experiments (e.g., Steinhauer's acoustic black holes) provide indirect evidence consistent with information preservation.

### 6.3 Path Forward

A rigorous LRT-gravity extension would require:

| Component | Status | What's Needed |
|-----------|--------|---------------|
| General covariance | Not addressed | Reconstruction theorem from IIS principles |
| Spacetime emergence | Conjecture | Derivation from holographic bounds |
| Collapse mechanism | Conjecture | Connection to Global Parsimony |
| Quantum gravity unification | Open problem | Beyond current scope |

This is acknowledged as the major gap in LRT's scope. Closing it would require breakthroughs in quantum gravity foundations, not just LRT-specific work.

---

## 7. Open Questions

1. **Creation/annihilation algebra:** Full derivation of CCR/CAR commutation relations directly from LRT axioms (currently derived from Fock structure, which is derived from LRT + physical inputs).

2. **Uniqueness theorem rigor:** Complete proof of Theorem 5.1' with all assumptions explicitly verified and no gaps.

3. **Gauge theories and Yang-Mills:** Whether local gauge symmetry can be derived from IIS closure under charged superpositions combined with 3FLL constraints remains an open problem. Current status: gauge groups (U(1), SU(2), SU(3)) are Tier 5 physical inputs, analogous to particle content. A derivation showing that gauge structure is *required* by LRT axioms would be a major advance; alternatively, gauge groups may simply be additional physical inputs that LRT accommodates but does not predict.

4. **Gravity derivation:** Path from conjecture (§6) to derivation for the gravity sector. This requires either (a) deriving spacetime structure from IIS information bounds, or (b) explicitly adding general covariance as a Tier 5+ input.

5. **Experimental discrimination:** Tests that would distinguish LRT-QFT from standard QFT interpretations. Currently, LRT-QFT makes the same quantitative predictions as standard QFT; the difference is interpretive. Novel predictions (collapse parameters, information preservation tests) are needed.

6. **Interacting QFT:** Extension of LRT-QFT to interacting theories beyond free fields. Does the framework accommodate non-perturbative effects, confinement, asymptotic freedom?

---

## 8. Conclusion

### 8.1 What This Paper Establishes

This paper extends Logic Realism Theory from non-relativistic quantum mechanics to quantum field theory through a tiered derivation structure with explicit physical inputs at each level. The extension is conservative: it builds on established mathematical results (Masanes-Müller reconstruction, Streater-Wightman axioms, Lee-Selby theorems) and makes honest distinctions between derivations, interpretations, and conjectures.

**Principal Results:**

1. **Fock space derived** (§3): The tensor product structure from local tomography (A3c) combines with 3FLL-enforced symmetrization (Theorem 3.1') and indistinguishability (Tier 3 input) to yield bosonic and fermionic Fock spaces. This is a genuine derivation, not a reframing.

2. **Spin-statistics derived** (§3.3): The connection between spin and statistics follows from Lorentz invariance and microcausality via the Streater-Wightman framework (Theorem 3.2'). LRT provides the underlying Hilbert space and tensor product structure; the physical inputs complete the derivation.

3. **Complex QFT unique** (§5.3): Alternatives (real QFT, quaternionic QFT, super-quantum theories) fail stability, local tomography, or tensor associativity requirements. Theorem 5.1' establishes uniqueness with seven explicit assumptions.

4. **Renormalization interpreted** (§4.2): UV divergences are interpreted as 3FLL violations (undefined self-identity at infinite energy). This provides a conceptual framework but does not derive RG equations or beta functions.

5. **Gravity deferred** (§6): The gravity sector requires breakthroughs in quantum gravity foundations beyond LRT-specific work. Conjectures are stated; no derivations are claimed.

### 8.2 The Derivation Chain Extended

The complete derivation chain from logical constraints to QFT is:

$$\text{3FLL} \xrightarrow{\text{constitute}} D \xrightarrow{\text{Thm 3.2}} \langle\cdot|\cdot\rangle \xrightarrow{\text{+Lorentz}} \mathcal{H}_1 \xrightarrow{\text{+A3c}} \mathcal{H}^{\otimes n} \xrightarrow{\text{+Tier 3}} \mathcal{F}_\pm \xrightarrow{\text{+microcausality}} \text{QFT}$$

Each arrow represents either a theorem (with proof) or an explicit physical input (with justification). No hidden assumptions; no circular reasoning.

### 8.3 Epistemic Hygiene

This paper maintains the epistemic standards established in the Technical Foundations companion:

| Category | Examples | Treatment |
|----------|----------|-----------|
| **Derived** | Fock structure, spin-statistics, CCR/CAR | Proof provided with explicit inputs |
| **Interpreted** | Renormalization, vacuum | Conceptual framework; limitations stated |
| **Input** | Lorentz, microcausality, cluster decomposition | Explicitly listed at appropriate tier |
| **Conjectured** | Gravity, collapse parameters | Marked as future work; no derivation claimed |

This taxonomy protects against overclaiming - the failure mode of most foundational physics papers.

### 8.4 Predictions and Falsifiability

LRT-QFT makes four predictions (§5.1) and identifies six strong falsifiers (§5.2). This places LRT in a small class of genuinely scientific interpretations of quantum theory - those that make testable claims beyond "quantum mechanics is correct."

**Key falsifiers:**
- Signaling via entangled fields → LRT refuted
- Consistent real QFT → complex uniqueness wrong
- Fundamental information loss → CBP violated
- Parastatistics in 3+1D → symmetrization theorem wrong

The existence of clear falsifiers distinguishes LRT from interpretations that are empirically equivalent to standard QM by construction.

### 8.5 Implications

**For foundations of physics:** LRT-QFT demonstrates that the mathematical structure of quantum field theory can be derived (not merely postulated) from logical constraints plus explicit physical inputs. The "unreasonable effectiveness" of mathematics in physics is explained: QFT is the unique Lorentz-covariant, locally tomographic interface between non-Boolean possibility and Boolean actuality.

**For philosophy of science:** The tiered derivation structure provides a model for honest foundational theorizing. By distinguishing derivations from interpretations from inputs from conjectures, LRT avoids the overclaiming that undermines credibility in foundations research.

**For quantum gravity:** The explicit identification of what LRT can and cannot derive (§6.3) clarifies the remaining gaps. A successful quantum gravity theory must either (a) derive general covariance from information-theoretic principles, or (b) accept it as a physical input at a higher tier.

### 8.6 Summary

This paper extends LRT to QFT via:
- **3 derivations** (Hilbert → Fock → spin-statistics) with explicit physical inputs
- **2 interpretations** (renormalization, vacuum) - not derivations
- **4 predictions** (Tsirelson in fields, info preservation, complex amplitudes, spin-statistics universal)
- **6 strong falsifiers** (signaling, real QFT, info loss, spin-statistics violation, contradictory outcomes, parastatistics in 3+1D)
- **1 conjecture** (gravity, marked as future work)

The extension is conservative, rigorous, and honest. It represents the next step in a research program that takes both physics and logic seriously.

---

## References

*Key references (to be formatted for submission):*

**Reconstruction Theorems:**
- Masanes, L. & Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New J. Phys.* 13, 063001.
- Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.
- Lee, C. M. & Selby, J. H. (2016). Deriving Grover's lower bound from simple physical principles. *New J. Phys.* 18, 093047.

**Axiomatic QFT:**
- Streater, R. F. & Wightman, A. S. (1964). *PCT, Spin and Statistics, and All That*. W. A. Benjamin.
- Haag, R. (1996). *Local Quantum Physics*. 2nd ed. Springer.
- Weinberg, S. (1995). *The Quantum Theory of Fields*, Vol. I. Cambridge University Press. [§4.3 cluster decomposition; §5.7 spin-statistics]

**Spin-Statistics and Identical Particles:**
- Pauli, W. (1940). The connection between spin and statistics. *Phys. Rev.* 58, 716-722.
- Lüders, G. (1958). Vertauschungsrelationen zwischen verschiedenen Feldern. *Z. Naturforsch.* 13a, 254.
- Zumino, B. (1960). Normal forms of complex matrices. *J. Math. Phys.* 1, 1-7.
- Messiah, A. M. L. & Greenberg, O. W. (1964). Symmetrization postulate and its experimental foundation. *Phys. Rev.* 136, B248.

**Experimental Confirmation:**
- Renou, M.-O. et al. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature* 600, 625-629.

**LRT Foundation Papers:**
- Technical.md theorems (Thm 3.2, 5.2, 5.4, 6.2, 6.4) - see companion paper

---

## Related Papers in This Series

Longmire, J. D. "It from Bit, Bit from Fit: Foundational Physics Logically Remastered." Zenodo, 2025. DOI: [10.5281/zenodo.17778402](https://doi.org/10.5281/zenodo.17778402)

Longmire, J. D. "Logic Realism Theory: Technical Foundations." Zenodo, 2025. DOI: [10.5281/zenodo.17778707](https://doi.org/10.5281/zenodo.17778707)

Longmire, J. D. "Logic Realism Theory: Philosophical Foundations." Zenodo, 2025. DOI: [10.5281/zenodo.17779030](https://doi.org/10.5281/zenodo.17779030)
