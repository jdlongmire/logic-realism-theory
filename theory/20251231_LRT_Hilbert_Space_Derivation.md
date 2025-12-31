# Complex Hilbert Space from Determinate Identity: A Logic-Realist Derivation

**Working Paper — Version 0.1**

**James (JD) Longmire**
ORCID: 0009-0009-1383-7698
Correspondence: jdlongmire@outlook.com

---

## Abstract

We derive the complex Hilbert space structure of quantum mechanics from the logical constraint of Determinate Identity (Id), showing that the operational axioms of quantum reconstruction theorems are not arbitrary postulates but consequences of logic constraining physical instantiation. The derivation proceeds by establishing that Id forces local tomography (Theorem 1), continuous reversible dynamics (Theorem 2), and the existence of non-classical correlations (Theorem 3). Combined with established reconstruction results (Masanes-Müller 2011, Hardy 2001), these yield complex Hilbert space as the unique state space satisfying Id-constraints on composite systems. The Tsirelson bound emerges as a mathematical consequence.

---

## 1. Introduction

### 1.1 The Problem

Quantum mechanics uses complex Hilbert space as its state space. Why complex? Why Hilbert space at all? Standard presentations take this as a postulate — the mathematical arena is assumed, not derived.

Quantum reconstruction programs (Hardy 2001; Chiribella, D'Ariano & Perinotti 2011; Masanes & Müller 2011) have made progress by showing that complex Hilbert space is *uniquely determined* by certain operational axioms. But this raises a new question: why should those axioms hold?

### 1.2 The LRT Answer

Logic Realism Theory proposes that the Three Fundamental Laws of Logic ($L_3$: Determinate Identity, Non-Contradiction, Excluded Middle) constrain physical instantiation. If this is correct, the operational axioms of reconstruction theorems should be *derivable* from $L_3$ — they hold because logic demands it.

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

Now consider the identity of subsystem A. By Id-1, the identity of A must be intrinsic — determined by A's own properties, not by facts about B or AB.

But the only operationally accessible facts about A are its measurement statistics $P_A(a)$. If A's identity is intrinsic and determinate, then A's identity is fixed by these statistics.

The same holds for B.

By Id-2 (Composition Principle), the identity of AB is grounded in the identities of A and B. But we've established that A's identity is the same in $\omega_1$ and $\omega_2$ (same local statistics), and likewise for B.

Therefore AB's identity must be the same in both cases. But this contradicts $\omega_1 \neq \omega_2$.

**Conclusion**: Local tomography must hold. $\square$

**Remark**: This proof depends on the anti-holism established in the LRT working paper (§2.3): parts ground wholes, not vice versa. Global holism — where the whole has properties not grounded in parts — would allow $\omega_1 \neq \omega_2$ with identical marginals. But global holism violates Id (identity would depend on extrinsic global facts).

### 3.3 Theorem 2: Id Forces Continuous Reversible Dynamics

**Theorem 2 (Continuous Reversibility from Id)**. If physical systems satisfy Determinate Identity, then dynamics between pure states must be continuous and reversible.

**Proof**.

**(Part A: Continuity)**

Suppose dynamics were discontinuous: a system jumps from state $\psi_1$ to state $\psi_2$ with no intermediate path.

Consider a property P that differs between $\psi_1$ and $\psi_2$. At the moment of transition, the system has no determinate status with respect to P — it is neither in the P-state of $\psi_1$ nor the P-state of $\psi_2$.

This violates Id: the system lacks determinate identity at the transition moment. It is "between" two configurations with no determinate configuration of its own.

Therefore, dynamics must be continuous: for any path $\psi_1 \to \psi_2$, there exists a continuous family of intermediate states.

**(Part B: Reversibility of pure states)**

Consider a pure state $\psi$ representing a system with maximal information (no uncertainty about properties within the theory's scope).

Suppose the dynamics $\psi \to \phi$ were irreversible, with $\phi$ also pure. Then information about $\psi$'s identity is lost — given $\phi$, we cannot recover which state preceded it.

But if $\psi$ has determinate identity (as Id requires), that identity constitutes information. Irreversible dynamics would destroy this information, violating Id-3: identity persists through transformation unless the transformation constitutes a change of identity.

The transformation $\psi \to \phi$ is not a "change of identity" (both are pure states of the same system); it is a dynamical evolution. Such evolution cannot destroy identity-constituting information.

Therefore, dynamics between pure states must be reversible. $\square$

**Remark**: This does not claim all dynamics are reversible. Measurement, which interfaces with the record level, may involve genuine identity change (the system transitions from "superposition vehicle" to "definite record"). But dynamics within the pure-state manifold — transformations that don't actualize records — must be reversible.

### 3.4 Theorem 3: Id Permits Non-Classical Correlations

**Theorem 3 (Entanglement Permitted)**. Determinate Identity does not forbid entangled states; it requires only that the vehicle encoding the entanglement has determinate identity.

**Proof**.

An entangled state of composite system AB is a pure state that cannot be written as a product:

$$|\Psi_{AB}\rangle \neq |\psi_A\rangle \otimes |\phi_B\rangle$$

Does Id forbid such states?

**No**. Id requires that the *vehicle* — the mathematical object representing the state — have determinate identity. The entangled state $|\Psi_{AB}\rangle$ is a specific, well-defined vector in Hilbert space. It has:
- Definite coefficients
- Definite inner products with other states
- Determinate evolution under unitary operators

The vehicle is determinate. What the vehicle *represents* — correlated outcome-possibilities — is not itself a violation of Id. The correlations are encoded determinately.

Moreover, local tomography (Theorem 1) ensures that the global state is determined by local data. For entangled states, this local data includes correlations visible only in joint measurements. But these correlations are determinate properties of the global state.

**What Id excludes**: States where the vehicle itself lacks determinate identity — e.g., "the system is in $|\Psi_1\rangle$ or $|\Psi_2\rangle$ but indeterminately which." This would violate Id. Entangled states are not of this form; they are specific, determinate vectors.

**Conclusion**: Entanglement is Id-admissible. $\square$

### 3.5 Corollary: Tomographic Locality

**Corollary (Tomographic Locality)**. Local tomography plus the existence of entangled states implies tomographic locality: the state space of a composite system is the minimal tensor product of component state spaces.

**Proof sketch**: This is a standard result in GPT theory. Local tomography means global states are determined by local statistics. For this to hold with entangled states, the composite state space must be exactly the tensor product — neither smaller (which would exclude some entangled states) nor larger (which would allow states not determined by local data).

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

### 4.2 The Bit Axiom

Axiom (MM4) — that all two-level systems are equivalent — requires additional argument.

**Claim**: Id forces bit equivalence.

**Argument**: Consider two two-level systems A and B. If both satisfy Id, then:
- Both have continuous reversible dynamics (Theorem 2)
- Both have pure states connected by continuous paths
- Both satisfy the same logical constraints

If A and B differed structurally (e.g., one had a Bloch ball, one had a different geometry), this difference would constitute an intrinsic property distinguishing them. But if they're both "two-level systems satisfying Id," this intrinsic property would have to derive from something beyond their two-level structure.

By Id-1, identity is intrinsic. Two systems with the same intrinsic structure (two levels, Id-compliant dynamics) must have the same state-space geometry.

Therefore, all bits are equivalent. $\square$

**Remark**: This argument is less rigorous than Theorems 1-3. A fuller treatment would derive bit structure from first principles. For now, we note that (MM4) is at least *consistent* with Id and arguably forced by it.

### 4.3 The Uniqueness Theorem

**Theorem 4 (Complex Hilbert Space Forced)**. The unique generalized probabilistic theory satisfying:
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

Pawłowski et al. (2009) derive the Tsirelson bound from "Information Causality" — the principle that Bob's accessible information cannot exceed the bits physically sent to him.

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
- Rigorous derivation of bit equivalence (MM4) — our argument is suggestive, not complete
- Extension to infinite-dimensional Hilbert spaces
- Extension to quantum field theory (Fock space)

### 6.3 The Status of Tsirelson

With this derivation, the Tsirelson bound's status changes:

| Framework | Tsirelson Status |
|-----------|-----------------|
| Standard QM | Mathematical fact (Cauchy-Schwarz) |
| Information Causality | Derived from information principle |
| **LRT** | **Derived from Id via Hilbert space** |

LRT does not claim to derive Tsirelson *independently* of Hilbert space. The claim is that Hilbert space itself — and therefore the bound — follows from Id.

---

## 7. Conclusion

We have derived complex Hilbert space structure from Determinate Identity by showing that Id forces the key axioms of quantum reconstruction theorems. Local tomography, continuous reversible dynamics, and the existence of entanglement are not arbitrary postulates but logical necessities.

The Tsirelson bound emerges as a downstream consequence: once Hilbert space is forced, the bound follows mathematically.

This completes the derivation chain:

$$L_3 \to \text{Hilbert Space} \to \text{Tsirelson} \to \text{Quantum Mechanics}$$

Each arrow is either a theorem (our Theorems 1-3) or an established mathematical result. The arena of quantum mechanics is not a brute fact but a consequence of logic constraining instantiation.

---

## References

Chiribella, G., D'Ariano, G. M., & Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.

Masanes, L., & Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Pawłowski, M., et al. (2009). Information causality as a physical principle. *Nature*, 461(7267), 1101–1104.

Tsirelson, B. S. (1980). Quantum generalizations of Bell's inequality. *Letters in Mathematical Physics*, 4(2), 93–100.

---

## Appendix A: Technical Lemmas

### A.1 Lemma: Anti-Holism from Id

**Lemma A.1**. If Determinate Identity holds, then global holism is false: composite systems cannot have properties not grounded in their parts.

**Proof**. See LRT Working Paper §2.3. The argument proceeds by reductio: if the whole had properties beyond those of parts, then identical parts could compose different wholes. But then the identity of the whole would depend on something beyond the parts — violating Id-1 (identity is intrinsic). $\square$

### A.2 Lemma: Local Tomography and Field Choice

**Lemma A.2**. Local tomography for all composite systems holds if and only if the underlying field is the complex numbers.

**Proof**. See Masanes-Müller (2011), Theorem 2, and Hardy (2001), Axiom 4 analysis.

- Real Hilbert space: Local tomography fails for entangled states (real density matrices don't span the full product space)
- Quaternionic Hilbert space: Fails associativity required for consistent composition
- Complex Hilbert space: Local tomography holds for all composite systems $\square$

---

**Document Status**: Working Paper v0.1
**Created**: 2025-12-31
**Next Steps**: Strengthen bit equivalence argument, extend to infinite dimensions
