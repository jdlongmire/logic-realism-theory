# Quantum Statistics from Determinate Identity: A Logic-Realist Derivation of the Symmetrization Postulate

**James D. (JD) Longmire**
ORCID: [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)

**Date**: December 2025
**Status**: Working Paper

---

## Abstract

The symmetrization postulate (that multi-particle quantum states must be either symmetric (bosons) or antisymmetric (fermions) under particle exchange) is standardly treated as an independent axiom of quantum mechanics. This paper derives the symmetrization postulate from Determinate Identity (L₁), the first of the three classical logical laws understood as ontological constraints on physical instantiation.

The core argument: if particles are intrinsically indistinguishable, then any quantum state that transforms non-trivially under permutation attributes distinguishable identity to indistinguishable entities. Such states violate L₁ and are therefore not physically instantiable. The only L₃-admissible states are those invariant (up to phase) under all permutations. Group-theoretic analysis shows that the symmetric group S_N has exactly two one-dimensional representations: the trivial representation (yielding bosons) and the sign representation (yielding fermions). The Fock space structure of quantum field theory follows as a corollary.

This result extends the Logic Realism programme, which previously derived the Born rule and complex Hilbert space structure from the same logical constraints (Longmire 2025). The paper also conjectures a connection between L₃ and the spin-statistics theorem, though a complete derivation remains future work.

**Keywords:** quantum statistics, symmetrization postulate, identical particles, logic realism, Determinate Identity, Fock space, bosons, fermions

---

## 1. Introduction

### 1.1 The Symmetrization Postulate

Standard quantum mechanics includes among its axioms the *symmetrization postulate*: the state vector of a system of identical particles must be either symmetric or antisymmetric under exchange of any two particles. Particles with symmetric wave functions are called bosons; those with antisymmetric wave functions are called fermions. This postulate has profound physical consequences (the Pauli exclusion principle, the stability of matter, Bose-Einstein condensation, the periodic table), yet within standard quantum mechanics it is simply posited, not derived.

The postulate raises an explanatory question: *why* must identical particles obey these specific symmetry constraints? Why are there exactly two types of quantum statistics, and not one, three, or infinitely many? The mathematical fact that the symmetric group has exactly two one-dimensional irreducible representations is well known, but this fact alone does not explain why physical states must transform according to one-dimensional representations rather than higher-dimensional ones.

### 1.2 The Logic Realism Programme

This paper addresses the symmetrization question from within the Logic Realism Theory (LRT) framework developed in Longmire (2025). LRT holds that the three classical logical laws (Determinate Identity (L₁), Non-Contradiction (NC), and Excluded Middle (EM), collectively denoted L₃) function as ontological constraints on physical instantiation, not merely as rules of coherent thought.

The core thesis: physical reality is constituted such that only configurations satisfying L₃ can be instantiated. A configuration without determinate identity is not a borderline entity but nothing at all. This constraint, applied to quantum systems, yields substantive physical consequences. Longmire (2025) derives the Born rule for quantum probabilities and the complex Hilbert space structure from L₃ alone, without empirical supplementation.

The present paper extends this programme to quantum statistics. We show that the symmetrization postulate is not an independent axiom but a consequence of Determinate Identity applied to systems of identical particles.

### 1.3 Paper Overview

Section 2 recapitulates the LRT framework, providing sufficient background for readers unfamiliar with the parent paper. Section 3 analyzes the identity problem for identical particles (the conceptual puzzle that the symmetrization postulate addresses). Section 4 presents the core argument: L₁ excludes non-symmetric states, leaving only bosonic and fermionic sectors as physically admissible. Section 5 discusses the connection to the spin-statistics theorem. Section 6 explores implications and predictions. Section 7 addresses objections. Section 8 concludes.

---

## 2. Logic Realism: Framework

This section summarizes the LRT framework. For complete development and proofs, see Longmire (2025).

### 2.1 L₃ as Ontological Constraint

Let L₃ denote the conjunction of three classical logical principles, understood as constraints on physical instantiation:

**Determinate Identity (L₁):** Every physical configuration is determinately the configuration it is, independent of description, distinct from every other configuration.

**Non-Contradiction (NC):** No physical configuration instantiates both property P and property ¬P in the same respect at the same time.

**Excluded Middle (EM):** For any well-defined property P applicable to a physical configuration, either the configuration instantiates P or it instantiates ¬P.

A configuration is *admissible* if it satisfies L₃. Physical reality, denoted A_Ω, is identified with the admissible subset of all conceivable configurations I_∞:

$$A_\Omega = \{ i \in I_\infty : L_3(i) \}$$

The claim is not that L₃ acts as a mechanism filtering configurations, but that "instantiated contradiction" is incoherent. Round squares are not excluded by a process; they are excluded by meaning.

### 2.2 Two Readings of Determinate Identity

The paper employs the weaker of two possible readings:

**Id-Strong:** To lack determinate identity is to be nothing. Indeterminate identity is not a borderline case of existence but a failure to exist at all.

**Id-Weak:** Any physical reality that admits determinate description, measurement, or record must satisfy Determinate Identity at least at the level of those descriptions, measurements, and records.

The derivations in this paper require only Id-Weak. A reader may accept Id-Weak as a working hypothesis while remaining agnostic about Id-Strong.

### 2.3 Key Results from the Parent Paper

Longmire (2025) establishes the following results from L₃:

1. **Born Rule**: The unique probability measure over quantum outcomes satisfying L₁-motivated constraints (basis-independence, non-contextuality) is the Born rule μ(P) = Tr(ρP).

2. **Complex Hilbert Space**: The unique arena for physical theories satisfying L₃ under composition and continuous transformation is complex Hilbert space (via the Masanes-Müller reconstruction theorem).

3. **Local Self-Sufficiency**: Genuine subsystems have intrinsic identity, not identity derivative from some global state. Parts ground wholes, not wholes parts.

These results provide the quantum-mechanical context within which the present argument operates.

---

## 3. The Identity Problem for Identical Particles

### 3.1 What "Identical" Means

Two particles are *identical* if they share all intrinsic properties: mass, charge, spin, and any other quantum numbers that characterize the particle type. All electrons are identical to all other electrons; all photons are identical to all other photons.

Crucially, "identical" here means *intrinsically indistinguishable*: there is no property intrinsic to particle 1 that distinguishes it from particle 2. The particles may differ in extrinsic properties (position, momentum, entanglement relations), but these are not properties of the particle itself; they are properties of the particle's state or relations.

### 3.2 The Standard Puzzle

Consider two electrons. In classical mechanics, we can label them "electron 1" and "electron 2" and track their trajectories continuously. Even if they have the same intrinsic properties, their distinct trajectories provide individuation.

In quantum mechanics, trajectories are not well-defined. If two electrons interact and then separate, we cannot say which outgoing electron is "the same" as which incoming electron. The labels "1" and "2" appear to be mere bookkeeping devices with no physical significance.

This raises a puzzle: if the labels are physically meaningless, why do we use a tensor product Hilbert space H ⊗ H that seems to presuppose two distinguishable systems? And why must physical states respect specific symmetry constraints under label exchange?

### 3.3 Why This Is an L₁ Problem

The puzzle is fundamentally about identity. Consider an arbitrary two-particle state:

$$|\psi\rangle = \sum_{i,j} c_{ij} |i\rangle_1 \otimes |j\rangle_2$$

where |i⟩₁ denotes particle 1 in state i and |j⟩₂ denotes particle 2 in state j. This notation presupposes that "particle 1" and "particle 2" refer to something, that there is a fact about which particle is which.

But if the particles are intrinsically indistinguishable, what grounds this distinction? If nothing intrinsic distinguishes particle 1 from particle 2, then any state that treats them differently (any state not invariant under the exchange 1 ↔ 2) attributes distinguishable identity to indistinguishable entities.

This is an L₁ violation. The state purports to describe a physical configuration, but it does so by attributing distinct identities where none exist.

### 3.4 Three Traditional Responses

The philosophical literature offers three responses to the identity problem:

**Haecceities**: Each particle has a primitive "thisness" that distinguishes it from others, independent of any qualitative properties. This view is metaphysically loaded and conflicts with the empirical success of treating identical particles as genuinely indistinguishable.

**Spatial individuation**: Particles are individuated by their spatial locations. This works in some contexts but fails when particles have overlapping wave functions or when we consider momentum-space representations.

**No individuation**: Identical particles are not individuals at all. The "two-electron system" is a single entity that does not decompose into two distinguishable parts. This view is closest to the LRT approach, but LRT provides a principled reason (L₁) rather than merely accepting it as primitive.

---

## 4. L₁ and the Symmetrization Postulate

This section presents the core argument. We show that L₁ excludes non-symmetric multi-particle states, leaving only the symmetric (bosonic) and antisymmetric (fermionic) sectors as physically admissible.

### 4.1 Setup: The N-Particle Hilbert Space

Let H be the Hilbert space of a single particle (e.g., L²(R³) ⊗ C² for a spin-½ particle in three dimensions). The N-particle Hilbert space is the tensor product:

$$\mathcal{H}^{(N)} = \underbrace{H \otimes H \otimes \cdots \otimes H}_{N \text{ factors}}$$

Elements of H^(N) are written as |ψ₁⟩ ⊗ |ψ₂⟩ ⊗ ⋯ ⊗ |ψ_N⟩ or more compactly as |ψ₁, ψ₂, …, ψ_N⟩.

### 4.2 Permutation Operators

The symmetric group S_N acts on H^(N) by permuting the tensor factors. For each permutation π ∈ S_N, define the unitary operator P_π by:

$$P_\pi |ψ_1, ψ_2, \ldots, ψ_N\rangle = |ψ_{\pi^{-1}(1)}, ψ_{\pi^{-1}(2)}, \ldots, ψ_{\pi^{-1}(N)}\rangle$$

For example, if π = (12) is the transposition exchanging 1 and 2:

$$P_{(12)} |ψ_1, ψ_2, ψ_3\rangle = |ψ_2, ψ_1, ψ_3\rangle$$

The operators {P_π : π ∈ S_N} form a unitary representation of S_N on H^(N).

### 4.3 Theorem 1: L₁ Excludes Non-Symmetric Sectors

**Theorem 1 (Symmetrization Required).** Let the N particles be identical (intrinsically indistinguishable). If L₁ holds for the N-particle system, then only states |ψ⟩ ∈ H^(N) satisfying

$$P_\pi |\psi\rangle = c(\pi) |\psi\rangle \quad \text{for all } \pi \in S_N$$

are L₃-admissible, where c: S_N → U(1) is a one-dimensional unitary representation.

**Proof.**

*Step 1: The physical content of a state.* A quantum state |ψ⟩ ∈ H^(N) represents a physical configuration of N particles. The physical content of this state is everything that can be measured or observed: all expectation values, probabilities, and correlations.

*Step 2: Label independence.* Since the particles are intrinsically indistinguishable, the labels "1", "2", …, "N" are not physical. They are notational devices for bookkeeping within the tensor product formalism. Consequently, the physical content of |ψ⟩ must be independent of how we assign labels to particles.

*Step 3: Applying L₁.* By Determinate Identity, a physical configuration is determinately what it is, independent of description. If two descriptions (two labelings) yield the same physical content, they describe the same configuration. If they yield different physical content, they describe different configurations.

Consider the states |ψ⟩ and P_π|ψ⟩ for some permutation π. These states arise from the same physical situation with different label assignments. By step 2, if the particles are truly identical, |ψ⟩ and P_π|ψ⟩ must represent the same physical configuration.

*Step 4: Same physical configuration implies same state (up to phase).* In quantum mechanics, two state vectors represent the same physical state if and only if they differ by a global phase: |ψ'⟩ = e^(iθ)|ψ⟩. Observable quantities depend only on the ray [|ψ⟩], not on the specific representative.

If |ψ⟩ and P_π|ψ⟩ represent the same physical configuration, then:

$$P_\pi |\psi\rangle = c(\pi) |\psi\rangle$$

for some c(π) ∈ U(1).

*Step 5: Consistency condition.* This must hold for all permutations π simultaneously. For the assignment π ↦ c(π) to be consistent with the group structure of S_N, we require:

$$c(\pi_1 \pi_2) = c(\pi_1) c(\pi_2)$$

(since P_{π₁π₂} = P_{π₁}P_{π₂} and the state must be an eigenstate of all P_π).

Therefore c: S_N → U(1) is a group homomorphism, i.e., a one-dimensional unitary representation of S_N. □

### 4.4 Theorem 2: Only Symmetric and Antisymmetric Survive

**Theorem 2 (Bosons and Fermions Only).** The symmetric group S_N (for N ≥ 2) has exactly two one-dimensional unitary representations:

1. The *trivial representation*: c(π) = 1 for all π.
2. The *sign representation*: c(π) = sgn(π), where sgn(π) = +1 for even permutations and −1 for odd permutations.

Therefore, L₁-admissible N-particle states are either:
- **Symmetric** (c = trivial): P_π|ψ⟩ = |ψ⟩ for all π. These are *bosonic* states.
- **Antisymmetric** (c = sign): P_π|ψ⟩ = sgn(π)|ψ⟩ for all π. These are *fermionic* states.

**Proof.**

A one-dimensional unitary representation c: S_N → U(1) is a group homomorphism to the abelian group U(1). The image c(S_N) is a subgroup of U(1).

S_N is generated by transpositions (two-element swaps). Each transposition τ satisfies τ² = e (the identity). Therefore c(τ)² = c(τ²) = c(e) = 1, which implies c(τ) = ±1.

*Case 1:* c(τ) = +1 for all transpositions. Then c(π) = 1 for all π, since every permutation is a product of transpositions. This is the trivial representation.

*Case 2:* c(τ) = −1 for all transpositions. Then c(π) = (−1)^k where π is a product of k transpositions. This equals sgn(π), the sign representation.

*Case 3:* c(τ₁) = +1 and c(τ₂) = −1 for some transpositions τ₁, τ₂. But all transpositions are conjugate in S_N (for N ≥ 2), meaning τ₂ = σ τ₁ σ⁻¹ for some σ. Then:

$$c(\tau_2) = c(\sigma \tau_1 \sigma^{-1}) = c(\sigma) c(\tau_1) c(\sigma)^{-1} = c(\tau_1)$$

(since U(1) is abelian). This contradicts c(τ₁) ≠ c(τ₂).

Therefore Cases 1 and 2 are the only possibilities. □

### 4.5 Corollary: Fock Space Structure

**Corollary (Fock Space).** The L₃-admissible sector of the multi-particle Hilbert space is the direct sum of symmetric and antisymmetric Fock spaces:

$$\mathcal{F}_{L_3} = \mathcal{F}_S \oplus \mathcal{F}_A$$

where:

$$\mathcal{F}_S = \bigoplus_{N=0}^{\infty} S^N(H) \quad \text{(symmetric/bosonic Fock space)}$$

$$\mathcal{F}_A = \bigoplus_{N=0}^{\infty} \Lambda^N(H) \quad \text{(antisymmetric/fermionic Fock space)}$$

Here S^N(H) is the N-fold symmetric tensor product and Λ^N(H) is the N-fold antisymmetric tensor product (exterior power).

**Proof.** By Theorems 1 and 2, only symmetric and antisymmetric states are L₃-admissible. A particle type is either a boson (all N-particle states symmetric) or a fermion (all N-particle states antisymmetric); mixing would violate consistency under particle creation/annihilation. The Fock space structure follows from taking the direct sum over particle numbers. □

---

## 5. The Spin-Statistics Connection

### 5.1 The Spin-Statistics Theorem

The spin-statistics theorem states:

- Particles with integer spin (0, 1, 2, …) are bosons.
- Particles with half-integer spin (½, 3/2, …) are fermions.

This connection between an intrinsic property (spin) and a statistical property (symmetry under exchange) is one of the deep results of relativistic quantum field theory.

### 5.2 Standard Proofs

The standard proof of the spin-statistics theorem relies on relativistic quantum field theory and the requirement of microcausality (local commutativity of spacelike-separated observables). The argument, due to Pauli (1940) and refined by subsequent authors, shows that violating the spin-statistics connection leads to either negative-norm states or violation of causality.

Duck and Sudarshan (1997) provide a comprehensive review of the various proofs and their assumptions.

### 5.3 The L₃ Perspective

From the LRT perspective, Section 4 establishes that identical particles must be either bosons or fermions; there is no third option. But it does not yet explain *which* particles are which.

Spin is a property related to behavior under spatial rotations (the rotation group SO(3) or its double cover SU(2)). Statistics is a property related to behavior under particle permutations (the symmetric group S_N). The spin-statistics theorem connects these two different symmetries.

### 5.4 Conjecture: L₃ + Lorentz Invariance → Spin-Statistics

We conjecture that the spin-statistics connection can be derived from L₃ combined with Lorentz invariance, without the full machinery of quantum field theory.

**Conjecture.** If a quantum theory satisfies L₃ and is Lorentz-invariant, then particles of integer spin are bosons and particles of half-integer spin are fermions.

*Sketch of approach:* The connection likely emerges from the interplay between L₁ (Determinate Identity) and the structure of the Lorentz group. The Lorentz group has two types of spinor representations (left-handed and right-handed), and 2π rotations act differently on integer-spin and half-integer-spin representations. If L₁ requires consistency between rotation and exchange, the spin-statistics connection may follow.

A complete proof remains future work. The present paper establishes only that *some* spin-statistics assignment must hold, not which one.

---

## 6. Implications and Predictions

### 6.1 Pauli Exclusion as L₁ Consequence

The Pauli exclusion principle (that no two fermions can occupy the same quantum state) follows immediately from antisymmetry:

$$|ψ, ψ\rangle_A = \frac{1}{\sqrt{2}}(|ψ\rangle ⊗ |ψ\rangle - |ψ\rangle ⊗ |ψ\rangle) = 0$$

An antisymmetrized state with two particles in the same single-particle state vanishes identically. This is not an empirical discovery but a mathematical consequence of the antisymmetry required by L₁.

### 6.2 Bose-Einstein Condensation as L₁-Admissible

For bosons, symmetric states not only allow but favor multiple particles in the same state:

$$|ψ, ψ\rangle_S = |ψ\rangle ⊗ |ψ\rangle$$

(no antisymmetry to cause cancellation). Bose-Einstein condensation (the macroscopic occupation of a single quantum state) is L₁-admissible for bosons.

### 6.3 Parastatistics Ruled Out

Parastatistics refers to hypothetical statistics corresponding to higher-dimensional representations of S_N. For example, parafermions of order p would have wave functions transforming according to p-dimensional representations.

Theorem 1 rules out parastatistics: L₁ requires one-dimensional representations. States transforming in higher-dimensional representations would attribute distinguishable identities (the different components of the representation) to indistinguishable particles.

This is a genuine prediction: if parastatistics were ever observed, L₁ (as applied here) would be falsified.

### 6.4 What Remains Empirical

L₃ determines *that* particles must be bosons or fermions but not *which* particles are which. The spin of a given particle type (and hence its statistics) is an empirical fact, not derivable from L₃ alone.

Similarly, the existence of specific particle types (electrons, photons, quarks, etc.) is empirical. L₃ constrains what can exist but does not determine what does exist.

---

## 7. Objections and Replies

### Objection 1: "This just redescribes the postulate."

*Objection:* The argument doesn't derive the symmetrization postulate; it just restates it in different language. Saying "L₁ requires symmetrization" is no more explanatory than saying "quantum mechanics requires symmetrization."

*Reply:* The objection conflates levels of explanation. The standard symmetrization postulate is *sui generis*: it appears in the axioms without connection to anything more fundamental. The L₁ argument grounds symmetrization in a general principle (Determinate Identity) that applies across physics and has independent motivation.

Moreover, the L₁ argument explains *why* there are exactly two options (bosons and fermions): because S_N has exactly two one-dimensional representations. This structural fact becomes intelligible when we see that L₁ requires one-dimensional representations.

### Objection 2: "Anyons violate this."

*Objection:* In two spatial dimensions, particles called anyons exhibit statistics intermediate between bosons and fermions. Exchange of two anyons produces a phase e^(iθ) where θ can be any value, not just 0 or π. This seems to contradict Theorem 2.

*Reply:* Anyons arise in two-dimensional systems where the configuration space of identical particles has non-trivial topology. In 2D, the fundamental group of the configuration space is the braid group B_N, not the permutation group S_N. Adiabatic exchange of particles traces a path in configuration space, and different paths can be topologically inequivalent.

The argument of Section 4 assumes that particle exchange corresponds to permutation (elements of S_N). This is correct in three or more spatial dimensions, where all paths implementing an exchange are topologically equivalent. In 2D, the richer topology allows for the continuous statistics parameter.

This is not a violation of L₁ but a refinement: in 2D, "identical particles" can have a richer identity structure due to topological constraints. The requirement that physical states transform consistently under exchange still holds; the group implementing exchange is simply larger.

### Objection 3: "You need more than L₁."

*Objection:* The argument assumes the Hilbert space framework. Without that assumption, the notions of permutation operators, representations, and tensor products don't make sense. So the derivation isn't really from L₁ alone.

*Reply:* This is correct: the argument requires quantum mechanics as input. But it does not require *more* quantum mechanics than L₃ itself provides. Longmire (2025) shows that complex Hilbert space is forced by L₃ via the Masanes-Müller reconstruction. The present paper then shows that L₃ further constrains which states in that Hilbert space are admissible.

The full derivation chain is:

$$L_3 \rightarrow \text{Hilbert space} \rightarrow \text{[this paper]} \rightarrow \text{Symmetrization}$$

Each step adds constraints without adding new empirical inputs.

---

## 8. Conclusion

### 8.1 Summary

We have shown that the symmetrization postulate of quantum mechanics (the requirement that multi-particle states be either symmetric (bosons) or antisymmetric (fermions)) is a consequence of Determinate Identity (L₁) applied to identical particles.

The argument proceeds as follows:

1. Identical particles have no intrinsic distinguishing properties.
2. L₁ requires that physical configurations be determinately what they are, independent of arbitrary labeling conventions.
3. States that transform non-trivially under particle permutation attribute distinguishable identities to indistinguishable particles, violating L₁.
4. The only L₁-admissible states are eigenstates of all permutation operators with eigenvalues forming a one-dimensional representation.
5. S_N has exactly two such representations: trivial (bosons) and sign (fermions).

### 8.2 Relation to LRT Programme

This result extends the Logic Realism programme in a significant direction. Where Longmire (2025) derived the Born rule and Hilbert space structure from L₃, the present paper derives quantum statistics. Together, these results suggest that much of the mathematical structure of quantum mechanics follows from logical constraints on instantiation.

### 8.3 Future Directions

Several questions remain for future work:

1. **Spin-statistics theorem**: Can the connection between spin and statistics be derived from L₃ + Lorentz invariance, without the full machinery of relativistic QFT?

2. **Vacuum uniqueness**: Is the uniqueness of the vacuum state in QFT an L₃ constraint?

3. **Renormalization**: Can renormalization be understood as L₃-admissibility filtering at different scales?

4. **Gauge symmetry**: Is local gauge invariance an L₃ constraint, or an empirical feature of our particular physics?

These questions define the frontier of the LRT programme's extension to quantum field theory.

---

## Appendix A: Formal Proofs

### A.1 Complete Proof of Theorem 1

**Theorem 1.** Let the N particles be identical. If L₁ holds, then only states |ψ⟩ satisfying P_π|ψ⟩ = c(π)|ψ⟩ for all π ∈ S_N are L₃-admissible, where c: S_N → U(1) is a one-dimensional unitary representation.

**Proof.**

*Premise 1 (Identical particles):* The N particles are intrinsically indistinguishable: they share all intrinsic properties (mass, charge, spin, etc.), and there is no physical property intrinsic to particle i that distinguishes it from particle j.

*Premise 2 (Determinate Identity):* L₁ holds: every physical configuration is determinately what it is, independent of how it is described.

*Definition (Physical equivalence):* Two quantum states |ψ⟩ and |ψ'⟩ are *physically equivalent* if they represent the same physical configuration, i.e., if they yield identical predictions for all observables.

*Lemma A.1:* Physical equivalence in quantum mechanics coincides with ray equivalence: |ψ⟩ and |ψ'⟩ are physically equivalent if and only if |ψ'⟩ = e^(iθ)|ψ⟩ for some θ ∈ R.

*Proof of Lemma A.1:* Observable quantities are given by expectation values ⟨ψ|A|ψ⟩/⟨ψ|ψ⟩ and transition probabilities |⟨φ|ψ⟩|²/(⟨φ|φ⟩⟨ψ|ψ⟩). Both are invariant under |ψ⟩ ↦ e^(iθ)|ψ⟩. Conversely, if all expectation values agree, the states lie on the same ray. □

*Derivation:*

(1) Consider an N-particle state |ψ⟩ ∈ H⊗N and any permutation π ∈ S_N.

(2) The state P_π|ψ⟩ is obtained from |ψ⟩ by relabeling the particles according to π.

(3) Since the particles are identical (Premise 1), this relabeling has no physical significance. The states |ψ⟩ and P_π|ψ⟩ describe the same physical situation.

(4) By L₁ (Premise 2), the physical configuration is determinate independent of description. Since |ψ⟩ and P_π|ψ⟩ are merely different descriptions of the same configuration, they must be physically equivalent.

(5) By Lemma A.1, physical equivalence implies ray equivalence:
   $$P_\pi|\psi\rangle = c(\pi)|\psi\rangle$$
   for some c(π) ∈ U(1).

(6) This must hold for all π ∈ S_N. For the phases to be consistent under composition:
   $$P_{\pi_1 \pi_2}|\psi\rangle = P_{\pi_1}(P_{\pi_2}|\psi\rangle) = P_{\pi_1}(c(\pi_2)|\psi\rangle) = c(\pi_2) c(\pi_1)|\psi\rangle$$
   But also:
   $$P_{\pi_1 \pi_2}|\psi\rangle = c(\pi_1 \pi_2)|\psi\rangle$$
   Therefore c(π₁π₂) = c(π₁)c(π₂) (since U(1) is abelian).

(7) Thus c: S_N → U(1) is a group homomorphism, i.e., a one-dimensional unitary representation. □

### A.2 Complete Proof of Theorem 2

**Theorem 2.** S_N has exactly two one-dimensional unitary representations: the trivial representation and the sign representation.

**Proof.**

Let c: S_N → U(1) be a one-dimensional unitary representation.

*Step 1:* S_N is generated by transpositions τ = (ij), which satisfy τ² = e.

*Step 2:* For any transposition τ, c(τ)² = c(τ²) = c(e) = 1, so c(τ) ∈ {±1}.

*Step 3:* All transpositions in S_N are conjugate. If τ₁ = (ij) and τ₂ = (kl), there exists σ ∈ S_N such that τ₂ = στ₁σ⁻¹.

*Step 4:* For any conjugate elements, c(στ₁σ⁻¹) = c(σ)c(τ₁)c(σ⁻¹) = c(τ₁) (since U(1) is abelian).

*Step 5:* Therefore all transpositions have the same image under c: either c(τ) = +1 for all τ, or c(τ) = −1 for all τ.

*Case c(τ) = +1:* Every permutation is a product of transpositions, so c(π) = 1 for all π. This is the trivial representation.

*Case c(τ) = −1:* If π = τ₁τ₂⋯τ_k (product of k transpositions), then c(π) = (−1)^k. Since the parity (even/odd) of k depends only on π (not on the specific factorization), c(π) = sgn(π). This is the sign representation.

No other one-dimensional representations exist. □

---

## Acknowledgments

This research was conducted independently. I thank the related online communities for critical feedback on early drafts, particularly regarding circularity concerns and related derivations.

**AI Assistance Disclosure:** This work was developed with assistance from AI language models including Claude (Anthropic), ChatGPT (OpenAI), Gemini (Google), Grok (xAI), and Perplexity. These tools were used for drafting, editing, literature review, and exploring mathematical formulations. All substantive claims, arguments, and errors remain the author's responsibility.

---

## References

Duck, I., and Sudarshan, E. C. G. (1997). *Pauli and the Spin-Statistics Theorem*. World Scientific.

Longmire, J. D. (2025). Logic Realism and the Born Rule: Determinate Identity as Ontological Constraint on Physical Reality. Working paper. https://github.com/jdlongmire/logic-realism-theory

Masanes, L., and Müller, M. P. (2011). A Derivation of Quantum Theory from Physical Requirements. *New Journal of Physics*, 13, 063001.

Messiah, A. M. L., and Greenberg, O. W. (1964). Symmetrization Postulate and Its Experimental Foundation. *Physical Review*, 136(1B), B248–B267.

Pauli, W. (1940). The Connection Between Spin and Statistics. *Physical Review*, 58(8), 716–722.

Streater, R. F., and Wightman, A. S. (1964). *PCT, Spin and Statistics, and All That*. Benjamin.

---

*Human-curated, AI-enabled.*
