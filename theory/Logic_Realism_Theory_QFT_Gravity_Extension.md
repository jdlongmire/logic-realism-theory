# LRT Constraints on QFT: Deriving Fock Structure and Interpreting Renormalization from Logical Foundations

**James (JD) Longmire**
ORCID: 0009-0009-1383-7698
Northrop Grumman Fellow (unaffiliated research)

**Status**: SEED DOCUMENT - Framework established, content to be developed
**Target**: Foundations of Physics (~25 pages)
**Timeline**: 6-9 months (Q1 2026 submission)

---

## Abstract

Logic Realism Theory (LRT) derives non-relativistic quantum mechanics from the claim that the Three Fundamental Laws of Logic (Identity, Non-Contradiction, Excluded Middle) are ontological constraints constitutive of physical distinguishability. This paper extends LRT to quantum field theory through a tiered derivation structure with explicit physical inputs at each level.

We establish three principal results. First, Fock space structure is derived from LRT axioms plus Lorentz invariance and locality: the tensor product structure from local tomography (A3c) combines with 3FLL-enforced symmetrization to yield bosonic and fermionic Fock spaces. Second, the spin-statistics connection follows from Lorentz invariance and microcausality via the standard Pauli argument, with LRT providing the underlying Hilbert space and tensor product framework. Third, the uniqueness of complex QFT is established: alternatives (real QFT, quaternionic QFT, super-quantum theories) fail stability, local tomography, or tensor associativity requirements inherited from the non-relativistic theory.

The paper distinguishes derivations from interpretations. Cluster decomposition, vacuum uniqueness, and the spectral gap are physical inputs (Tier 4), not consequences of logical constraints. Renormalization is interpreted as 3FLL-restoration at UV scales, but this conceptual framework does not derive renormalization group equations. The gravity sector remains conjectural.

Four predictions follow: (1) Tsirelson bound holds for field correlations, (2) information is never fundamentally lost, (3) complex amplitudes are required, (4) spin-statistics holds universally. Five strong falsifiers are identified, including signaling via entangled fields and fundamental information loss.

The extension is conservative: it builds on established LRT results, adds Lorentz invariance and microcausality as explicit physical inputs, and makes honest distinctions between what is derived, interpreted, and conjectured.

**Keywords:** quantum field theory, logic realism, Fock space, spin-statistics, falsifiability, reconstruction theorems

---

## 1. Introduction (1-2 pages)

### 1.1 Motivation

This paper extends Logic Realism Theory from non-relativistic quantum mechanics to quantum field theory. The goal is to close LRT's scope gap for QFT/Gravity while maintaining the rigorous derivation standards established in the Technical Foundations paper.

### 1.2 Derivation Hierarchy

LRT extends to QFT via a tiered structure with explicit physical inputs at each level:

| Tier | Inputs | Outputs | Status |
|------|--------|---------|--------|
| **1: Logic** | 3FLL | Distinguishability D; kernel K | Derived (Thm 2.1-3.2) |
| **2: Covariant** | + CBP + Lorentz invariance | Algebraic Hilbert; D-isometries | Derived (via Masanes-Muller) |
| **3: Fields** | + Locality (A3c) | Fock tensors; spin-statistics | Derived (via Lee-Selby) |
| **4: QFT** | + Cluster decomposition + Vacuum uniqueness | Renormalization; vacuum structure | Interpreted |
| **5: Gravity** | + Holographic bounds | Collapse parameters | Conjecture |

### 1.3 What This Paper Claims and Does Not Claim

**Can claim:**
- Fock structure derived from LRT axioms + explicit physical inputs (Lorentz, locality)
- Spin-statistics via Lee-Selby theorem bridge
- Renormalization interpreted as CBP-enforced 3FLL consistency
- Vacuum structure consistent with IIS framework
- Cluster decomposition as physical input (not derived)

**Cannot claim:**
- Fock from 3FLL alone (requires physical inputs)
- Spin-statistics from pure logic (requires Lorentz + microcausality)
- Renormalization derived (interpretation only)
- Vacuum derived from 3FLL (requires spectral/uniqueness assumptions)
- Cluster decomposition from IIS closure (it's dynamical, not kinematic)

### 1.4 Key Theorems (Stated)

- **Theorem 2.1'**: Lorentz-covariant distinguishability metric; kernel induces field operators
- **Theorem 3.1'**: Fock space as symmetric/antisymmetric IIS tensor products under locality
- **Theorem 3.2'**: Spin-statistics from 3FLL exclusivity + Lorentz + microcausality (via Lee-Selby)
- **Theorem 5.x'**: Complex QFT is unique Lorentz-covariant, locally tomographic IIS interface satisfying stability

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

**3FLL Constraint (Identity):** If particle 1 and particle 2 are identical, then any state must respect this identity. The state $|a\rangle_1 \otimes |b\rangle_2$ (particle 1 in state $a$, particle 2 in state $b$) must be *physically equivalent* to $|b\rangle_1 \otimes |a\rangle_2$.

**Definition 3.1 (Exchange Operator).** For two-particle states, define:
$$P_{12} |a\rangle_1 \otimes |b\rangle_2 = |b\rangle_1 \otimes |a\rangle_2$$

**Theorem 3.1' (Symmetrization from 3FLL).** For identical particles, physical states must satisfy:
$$P_{12} |\psi\rangle = \lambda |\psi\rangle$$

where $\lambda = \pm 1$ (since $P_{12}^2 = 1$).

**Proof:**

*Step 1 (Identity):* If particles are identical, then $|a\rangle_1 \otimes |b\rangle_2$ and $|b\rangle_1 \otimes |a\rangle_2$ represent the same physical configuration. Therefore, they must belong to the same ray in Hilbert space:
$$|b\rangle_1 \otimes |a\rangle_2 = e^{i\phi} |a\rangle_1 \otimes |b\rangle_2$$

*Step 2 (Consistency):* Applying the exchange twice returns to the original:
$$P_{12}^2 = 1 \implies e^{2i\phi} = 1 \implies e^{i\phi} = \pm 1$$

*Step 3 (Non-Contradiction):* A state cannot be both symmetric ($\lambda = +1$) and antisymmetric ($\lambda = -1$). Each particle type has a definite symmetry.

*Step 4 (Excluded Middle):* Every identical-particle state is either symmetric or antisymmetric. No other options exist. ∎

**Critical Gap:** Theorem 3.1' establishes that identical particles must have definite exchange symmetry, but does **not** determine which particles are symmetric (bosons) versus antisymmetric (fermions). This requires additional physical input (§3.3).

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

**Proof sketch (via Pauli 1940, Streater-Wightman axioms):**

*Step 1:* For a spin-$s$ field, the field operator transforms under the $(s, 0) \oplus (0, s)$ representation of the Lorentz group.

*Step 2:* Under a $2\pi$ rotation, the field picks up a phase $e^{2\pi i s}$:
- Integer $s$: $e^{2\pi i s} = +1$
- Half-integer $s$: $e^{2\pi i s} = -1$

*Step 3:* Microcausality requires $[\phi(x), \phi(y)]_\mp = 0$ at spacelike separation. For this to hold with Lorentz covariance:
- Integer spin: commutator $[\phi, \phi] = 0$ → bosons
- Half-integer spin: anticommutator $\{\phi, \phi\} = 0$ → fermions

*Step 4:* The wrong choice (integer spin with anticommutator, or half-integer with commutator) violates either microcausality or positive energy. ∎

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
| Symmetrization requirement | 3FLL (Identity) | Derived (Thm 3.1') |
| Spin-statistics connection | Lorentz + microcausality | Derived (Thm 3.2') |
| CCR/CAR algebra | Fock structure + inner product | Derived (Thm 3.3') |

The Fock space structure is genuinely derived from LRT axioms plus explicit physical inputs (Lorentz invariance, microcausality). This is not a reframing but a constructive derivation with clear assumptions.

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

### 4.2 Renormalization as CBP-Enforced Consistency

**Important:** This section offers an *interpretation* of renormalization within the LRT framework. It does **not** derive renormalization group equations, beta functions, or anomalous dimensions.

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

#### 4.2.3 Renormalization as 3FLL Restoration

**Interpretation:** Renormalization restores 3FLL compliance by:

1. **Regularization:** Introducing a cutoff $\Lambda$ makes integrals finite (temporary 3FLL restoration).
   $$\int_0^\Lambda \frac{d^4k}{(2\pi)^4} \frac{1}{k^2 - m^2} = \text{finite}(\Lambda)$$

2. **Counterterms:** Adding terms to the Lagrangian that cancel the $\Lambda$-dependent divergences.

3. **Renormalization conditions:** Fixing physical parameters (mass, coupling) at physical scales, making predictions cutoff-independent.

**CBP constraint on counterterms:** Not all counterterms are allowed. CBP (information preservation) requires that counterterms do not introduce non-unitary dynamics or violate probability conservation.

#### 4.2.4 What This Interpretation Does NOT Do

| Claim | Status |
|-------|--------|
| UV divergences violate 3FLL | Interpretive |
| Renormalization restores 3FLL | Interpretive |
| Derive beta functions | NOT claimed |
| Derive anomalous dimensions | NOT claimed |
| Explain why QFT is renormalizable | NOT claimed |
| Derive the RG equations | NOT claimed |

The interpretation provides a *conceptual framework* for why renormalization is necessary (3FLL compliance) but does not replace the technical machinery of renormalization theory.

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

#### 5.2.1 Strong Falsifiers

| Observation | What It Would Show | LRT Impact |
|-------------|-------------------|------------|
| **Signaling via entangled fields** | Correlations exceed Tsirelson bound; faster-than-light communication possible | CBP violated; 3FLL not constitutive; LRT refuted |
| **Consistent real QFT** | Complex amplitudes not required; local tomography not universal | Theorem 5.2 fails; complex uniqueness wrong |
| **Fundamental information loss** | Black hole destroys information irreversibly; unitarity fails fundamentally | CBP violated; A3b wrong; LRT refuted |
| **Spin-statistics violation** | Integer-spin fermion or half-integer boson observed | Theorem 3.2' fails; Lorentz+microcausality insufficient |
| **Contradiction in measurement outcomes** | Single measurement yields contradictory results (P and ¬P) | 3FLL not constitutive; LRT foundationally wrong |

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

**Theorem 5.1' (Uniqueness of Complex QFT).** Complex quantum field theory is the unique relativistic theory satisfying:
1. 3FLL-constituted distinguishability (A1)
2. Continuous dynamics (A3a)
3. Information preservation / CBP (A3b)
4. Local tomography (A3c)
5. Lorentz invariance (Tier 2)
6. Microcausality (Tier 3)
7. Stability (bound states exist)

**Proof sketch:**

*Step 1:* By Theorem 3.2 (Technical.md), conditions 1-4 yield complex Hilbert space structure.

*Step 2:* By Theorem 6.2 (Technical.md), condition 4 yields tensor product structure for composite systems.

*Step 3:* By §3, conditions 5-6 yield Fock space with spin-statistics (Theorem 3.2').

*Step 4:* Stability (condition 7) eliminates alternatives:
- Classical fields: No bound states (Earnshaw, Theorem 5.1)
- Real QFT: Fails local tomography (Theorem 5.2)
- Quaternionic QFT: Fails tensor associativity (Theorem 5.3)
- Super-quantum GPT: Signaling under composition (Theorem 5.4)

*Step 5:* By Masanes-Müller uniqueness, complex QM is unique under MM1-MM5. By extension, complex QFT is unique under the relativistic version of these axioms.

**Explicit Assumptions:**
| Assumption | Source | Status |
|------------|--------|--------|
| 3FLL constitute distinguishability | A1 | Foundational |
| Continuity | A3a | Physical |
| Information preservation | A3b (CBP) | Physical |
| Local tomography | A3c | Physical |
| Lorentz invariance | Tier 2 input | Empirical |
| Microcausality | Tier 3 input | Empirical |
| Stability | Definition 5.1-5.3 (Technical.md) | Physical |

**What Uniqueness Does NOT Claim:**
- Does not derive Lorentz invariance from 3FLL
- Does not determine particle content (which particles exist)
- Does not fix coupling constants
- Does not determine spacetime dimensionality

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

## 6. Gravity Conjecture (2 pages)

### 6.1 Holographic Interface

**Conjecture**: Spacetime structure emerges from holographic bounds on IIS information capacity.

### 6.2 Collapse Parameters

**Conjecture**: Penrose-Diósi collapse parameters derivable from Global Parsimony:

```
τ ~ ℏ / (G m²)
```

**Status**: Conjecture only. No derivation claimed.

### 6.3 Black Holes and Information

**Prediction**: No fundamental information loss (CBP). Hawking radiation must encode infalling information.

**Testable**: Gravitational wave signatures from quantum corrections near horizon.

---

## 7. Open Questions

1. Full derivation of creation/annihilation commutation relations from LRT
2. Rigorous proof of uniqueness theorem with explicit assumptions
3. Connection to gauge theories (Yang-Mills from IIS?)
4. Path from conjecture to derivation for gravity sector
5. Experimental tests distinguishing LRT-QFT from standard QFT interpretations

---

## 8. Conclusion (1 page)

*To be written*

**Summary**: This paper extends LRT to QFT via:
- 3 derivations (Hilbert → Fock → spin-statistics) with explicit physical inputs
- 2 interpretations (renormalization, vacuum) - not derivations
- 2 predictions (Tsirelson in fields, no info paradox)
- 3 falsifiers (signaling, real QFT, info loss)
- 1 conjecture (gravity collapse parameters)

---

## References

*To be added - Key references:*
- Masanes & Muller (2011) - Reconstruction theorems
- Lee & Selby (2016) - Spin-statistics
- Hardy (2001) - Quantum theory from axioms
- Renou et al. (2021) - Complex amplitudes experimental confirmation
- Weinberg - Cluster decomposition
- Technical.md theorems (Thm 3.2, 5.2, 5.4, 6.2, 6.4)

---

## Related Papers

- [Main Paper](Logic_Realism_Theory_Main.md) - Core thesis and 17 phenomena
- [Technical Foundations](Logic_Realism_Theory_Technical.md) - Mathematical proofs, derivation chain
- [Philosophical Foundations](Logic_Realism_Theory_Philosophy.md) - Ontological status of 3FLL
