# S12: Product Effects (H1) — Deriving Composite System Product Structure from L<sub>3</sub>

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Supports:** Step 3 (Local Tomography)
**Addresses:** The H1_product_effects placeholder in Lean formalization; grounds H × H → H structure

---

## Abstract

This supplement derives the product structure $\mathcal{H}_A \otimes \mathcal{H}_B$ for composite quantum systems from L<sub>3</sub> constraints within Logic Realism Theory. The standard quantum formalism assumes that composite systems form tensor products, but this composition rule is typically postulated rather than derived. We show that the tensor product structure is the unique composition rule compatible with (1) Determinate Identity for subsystems (Step 2), (2) local tomography (H2 from Step 3), and (3) the Physical Proposition Criterion (PPC). The derivation proceeds in four stages: establishing that each subsystem must have determinate state space structure, showing that joint effects must factorize over product states, proving that non-factorizing composition rules violate L<sub>3</sub>, and demonstrating uniqueness. This grounds the `product_factorizes` axiom in the Lean formalization.

---

## 1. The Problem

### 1.1 What Needs Grounding

The Lean formalization in `Step3_LocalTomography.lean` includes the structure:

```lean
structure ProductEffectProb (sys : BipartiteSystem) where
  prob : sys.AB.State → ProductEffect sys → ℝ
  prob_range : ∀ ρ e, 0 ≤ prob ρ e ∧ prob ρ e ≤ 1
  product_factorizes : ∀ (ρA : sys.A.State) (ρB : sys.B.State) (e : ProductEffect sys),
    prob (sys.product ρA ρB) e = e.effectA.prob ρA * e.effectB.prob ρB
```

The `product_factorizes` axiom asserts that for product states, joint probabilities factor:

$$P(e_A \otimes e_B \mid \rho_A \otimes \rho_B) = P(e_A \mid \rho_A) \cdot P(e_B \mid \rho_B)$$

This is the defining property of the tensor product composition. Standard quantum mechanics postulates it; LRT must derive it from L<sub>3</sub>.

### 1.2 The Composition Question

Given two physical systems A and B with state spaces $\mathcal{S}_A$ and $\mathcal{S}_B$, what determines the state space $\mathcal{S}_{AB}$ of the composite?

Logically, several options exist:

- **Option 1 (Cartesian):** $\mathcal{S}_{AB} = \mathcal{S}_A \times \mathcal{S}_B$ — joint states are ordered pairs
- **Option 2 (Tensor):** $\mathcal{S}_{AB} = \mathcal{S}_A \otimes \mathcal{S}_B$ — joint states include entangled states beyond product states
- **Option 3 (Holistic):** $\mathcal{S}_{AB}$ contains states with no decomposition into subsystem contributions
- **Option 4 (Restricted):** $\mathcal{S}_{AB} \subsetneq \mathcal{S}_A \otimes \mathcal{S}_B$ — some entangled states forbidden

### 1.3 What LRT Must Show

LRT must derive that Option 2 (tensor product) is the unique composition rule compatible with L<sub>3</sub>. Specifically:

1. Product states exist and satisfy factorization
2. Entangled states exist (the composite is not merely Cartesian)
3. No holistic states exist (all states decompose via local tomography)
4. No restriction applies (all tensor product states are admissible)

---

## 2. Determinate Identity and Product States

### 2.1 Subsystem Determinacy

**Premise (Step 2):** Every actual configuration $c \in A_\Omega$ satisfies Determinate Identity.

Applied to composite systems: if system AB is actual, then subsystems A and B must each have determinate identity. This is not optional. If A lacked determinate identity, AB would inherit this failure, violating L<sub>3</sub>.

**Consequence:** For any joint state $\rho_{AB}$, there exist well-defined marginal states $\rho_A$ and $\rho_B$ capturing the determinate identity of each subsystem.

### 2.2 Product States as Base Case

**Definition (Product State):** A joint state $\rho_{AB}$ is a *product state* if $\rho_{AB} = \rho_A \otimes \rho_B$ for some subsystem states $\rho_A$, $\rho_B$. This means: the joint state is fully determined by the independent specification of subsystem states.

**Claim:** Product states must exist in any L<sub>3</sub>-admissible composite system.

**Argument:**
1. By Determinate Identity, subsystems A and B have determinate states.
2. If A and B are prepared independently (no interaction creating correlations), their joint state must reflect this independence.
3. Independence means: specifying $\rho_A$ and $\rho_B$ suffices to determine $\rho_{AB}$.
4. This is exactly the defining property of a product state.

The existence of product states is not a postulate but a consequence of Determinate Identity applied to independently prepared subsystems.

*[Epistemic Status: ESTABLISHED — follows from Determinate Identity + operational preparation]*

### 2.3 Product Factorization from L<sub>3</sub>

**Claim:** For product states, joint probabilities factorize.

**Argument:**

Let $\rho_A \otimes \rho_B$ be a product state. Let $e_A$ and $e_B$ be local effects (measurements on A and B respectively).

The joint probability $P(e_A \otimes e_B \mid \rho_A \otimes \rho_B)$ is the probability that both A yields $e_A$ and B yields $e_B$.

By Excluded Middle applied to each subsystem:
- Either $e_A$ obtains for A or it doesn't
- Either $e_B$ obtains for B or it doesn't

For a product state (independent preparation):
- The occurrence of $e_A$ depends only on $\rho_A$
- The occurrence of $e_B$ depends only on $\rho_B$

**No cross-dependence is permitted for product states.** If the probability of $e_A$ depended on $\rho_B$ for a product state, then:
- Either $\rho_B$ affects $e_A$'s occurrence (violation of independence)
- Or there is a hidden holistic fact determining the joint probability (violation of H1)

By Identity: the probability $P(e_A \mid \rho_A)$ is what it is, independent of context. For a product state, context includes no information about B beyond "B exists in state $\rho_B$." But for a product state, "B exists in state $\rho_B$" provides no information relevant to A's outcome — that is what "product" means.

Therefore:

$$P(e_A \otimes e_B \mid \rho_A \otimes \rho_B) = P(e_A \mid \rho_A) \cdot P(e_B \mid \rho_B)$$

This is the `product_factorizes` property.

*[Epistemic Status: ARGUED — depends on L<sub>3</sub> applied to independence and the definition of product states]*

---

## 3. Entanglement and the Tensor Product

### 3.1 Why Cartesian Composition Fails

The Cartesian product $\mathcal{S}_A \times \mathcal{S}_B$ contains only product states — no correlations beyond what marginals determine.

**Claim:** Pure Cartesian composition violates L<sub>3</sub> for quantum systems.

**Argument:**

Consider preparing two particles via a process that conserves total spin. The preparation produces correlations: if A is spin-up, B is spin-down, and vice versa.

Under Cartesian composition, the joint state would be:
$$\rho_{AB} = (\rho_A, \rho_B)$$

where $\rho_A$ and $\rho_B$ are the marginal states (each maximally mixed for the singlet).

But the correlation "opposite spins" is a determinate fact under L<sub>3</sub>:
- By Identity, the correlation has determinate content
- By Non-Contradiction, either opposite spins obtain or they don't
- By Excluded Middle, there is a fact of the matter

This correlation is not captured by the marginals alone. The marginals say each particle is maximally mixed; they do not encode the perfect anti-correlation.

By the Physical Proposition Criterion (S1), if the correlation is a physical fact (determinate, non-contradictory, bivalent), it must be operationally distinguishable. It is: Bell-type measurements distinguish correlated from uncorrelated pairs.

Therefore, the joint state must encode the correlation. Cartesian products cannot encode correlations beyond marginals. Cartesian composition is inadequate.

*[Epistemic Status: ARGUED — depends on applying PPC to correlations]*

### 3.2 Tensor Product as Minimal Extension

The tensor product $\mathcal{H}_A \otimes \mathcal{H}_B$ extends the Cartesian product minimally:

- Contains all product states $|\psi_A\rangle \otimes |\phi_B\rangle$
- Contains superpositions of product states (entangled states)
- Superpositions encode correlations not reducible to marginals

**Claim:** The tensor product is the minimal composition rule that:
1. Contains product states (from §2.2)
2. Satisfies product factorization (from §2.3)
3. Represents all L<sub>3</sub>-admissible correlations (from §3.1)

**Argument (Sketch):**

The joint effect space for a bipartite system must allow effects $e_A \otimes e_B$ acting locally. Local tomography (H2) requires that the joint state be determined by all such local effect probabilities.

If we parameterize states by their probabilities on a tomographically complete set of effects:
- Product states: probabilities factorize
- Entangled states: probabilities exhibit non-factorizing correlations

The space of probability assignments satisfying:
- Non-negativity
- Normalization
- Factorization on product states
- Local tomography

is exactly the space of density matrices on $\mathcal{H}_A \otimes \mathcal{H}_B$.

This is the content of the Masanes-Müller reconstruction (Step 4), applied to the composition question. The tensor product is not postulated; it is the unique structure satisfying the constraints.

*[Epistemic Status: ESTABLISHED — Masanes-Müller (2011) with local tomography input from Step 3]*

---

## 4. Excluding Holistic Composition

### 4.1 The Holistic Alternative

A *holistic* composition rule would allow joint states with properties not determined by subsystem states or their relations.

**Example:** Suppose $\mathcal{S}_{AB}$ contained a state $\sigma$ such that:
- Marginals $\sigma_A$, $\sigma_B$ are well-defined
- Some property P holds of $\sigma$ but is not determined by ($\sigma_A$, $\sigma_B$, relations)

### 4.2 Why Holism Violates L<sub>3</sub>

**Claim:** Holistic states violate L<sub>3</sub>.

**Argument (from S2, §3):**

By H1 (Metaphysical Supervenience): the composite is nothing over and above subsystems + relations. Any composite property supervenes on the supervenience base.

Suppose property P is holistic — not determined by the supervenience base.

Then P is either:
- (a) A physical fact (satisfies L<sub>3</sub>)
- (b) Not a physical fact (fails L<sub>3</sub>)

If (a): By PPC (S1), P must be operationally distinguishable. If distinguishable, P makes a difference to some measurement outcome. But measurements on AB are local (H2 — local tomography). Local measurements access only subsystem properties + correlations. Therefore P affects local outcomes iff P supervenes on the supervenience base. Contradiction.

If (b): P is not a physical fact. The "holistic state" carrying P is not a physical state. It is a formal construction with no physical content.

Either way, holistic states are excluded from A_Ω.

*[Epistemic Status: ARGUED — depends on H1 → H2 bridge from S2]*

---

## 5. Uniqueness of the Tensor Product Rule

### 5.1 The Uniqueness Claim

**Theorem:** The tensor product $\mathcal{H}_A \otimes \mathcal{H}_B$ is the unique composition rule for quantum systems compatible with L<sub>3</sub>.

### 5.2 Proof Outline

We eliminate alternatives:

**(1) Cartesian products:** Fail to represent correlations (§3.1). Violate PPC for correlated states.

**(2) Holistic compositions:** Fail H1 → H2 (§4.2). Violate supervenience.

**(3) Restricted tensor products:** Suppose some entangled states were forbidden. A restriction $\mathcal{S}_{AB} \subsetneq \mathcal{H}_A \otimes \mathcal{H}_B$ would mean:
- Some superpositions of product states are "non-physical"
- But superpositions arise from preparation procedures (interference, etc.)
- If a preparation procedure produces state $|\Psi\rangle$, that state must be in $\mathcal{S}_{AB}$
- By Determinate Identity, $|\Psi\rangle$ has determinate identity; by PPC, it is physically real
- No L<sub>3</sub>-based criterion excludes specific entangled states

**(4) Super-quantum extensions:** Suppose $\mathcal{S}_{AB} \supsetneq \mathcal{H}_A \otimes \mathcal{H}_B$. This would add states beyond the tensor product — "super-quantum" correlations. But:
- Independent composition (H2) bounds dimension: $\dim(\mathcal{S}_{AB}) = \dim(\mathcal{S}_A) \cdot \dim(\mathcal{S}_B)$
- This is exactly the tensor product dimension
- Super-quantum theories violate this bound (e.g., PR boxes)
- Therefore L<sub>3</sub> excludes super-quantum correlations

**Conclusion:** Only the tensor product survives.

*[Epistemic Status: ARGUED — depends on Steps 2-3 and independent composition constraint]*

---

## 6. Formal Statement for Lean

### 6.1 The Grounding Result

The Lean axiom:

```lean
product_factorizes : ∀ (ρA : sys.A.State) (ρB : sys.B.State) (e : ProductEffect sys),
    prob (sys.product ρA ρB) e = e.effectA.prob ρA * e.effectB.prob ρB
```

is grounded by the following derivation chain:

| Step | Content | Epistemic Status |
|------|---------|------------------|
| 1 | Subsystems have Determinate Identity | ESTABLISHED (Step 2) |
| 2 | Independent preparation ⇒ product states exist | ESTABLISHED |
| 3 | Product states satisfy independence ⇒ factorization | ARGUED |
| 4 | L<sub>3</sub>-correlations require entanglement | ARGUED |
| 5 | Holistic states violate H1 → H2 | ARGUED |
| 6 | Tensor product is unique L<sub>3</sub>-compatible composition | ARGUED |

### 6.2 Tier Classification

The `product_factorizes` property is:

- **Not Tier 1:** It is not a primitive assumption about L<sub>3</sub> or I<sub>∞</sub>
- **Tier 2:** It is derived from the L<sub>3</sub> framework via Steps 2-3
- **Confidence:** MEDIUM — depends on the H1 → H2 bridge and PPC

The Lean formalization correctly axiomatizes this as a Tier 2 input. This supplement provides the prose derivation grounding that axiomatization.

---

## 7. Connection to Other Steps

### 7.1 Upstream Dependencies

| Dependency | Source | Status |
|------------|--------|--------|
| Determinate Identity | Step 2 | ESTABLISHED |
| Physical Proposition Criterion | S1 | ARGUED |
| H1 (Metaphysical Supervenience) | S2, Step 3 | ESTABLISHED |
| H2 (Local Tomography) | S2, Step 3 | ARGUED |

### 7.2 Downstream Consumers

| Consumer | How Used |
|----------|----------|
| Step 4 (Masanes-Müller) | Tensor product input to reconstruction |
| Step 5 (PVM structure) | Product effects → PVM on composite space |
| Step 6 (Gleason/Born) | Probabilities on tensor product Hilbert space |

### 7.3 Related Supplements

- **S1 (PPC Derivation):** Provides the operational determinacy principle used in §3-4
- **S2 (H1-H2 Bridge):** Provides the supervenience-to-tomography argument used in §4
- **S8 (Lean Step 3 Strategy):** Strategy document this supplement grounds

---

## 8. Open Questions

### 8.1 Infinite-Dimensional Case

The derivation assumes finite-dimensional Hilbert spaces. For infinite dimensions:
- Tensor products exist (completed if necessary)
- Local tomography requires care with unbounded operators
- The H1 → H2 bridge may need additional continuity assumptions

**Status:** OPEN — extension to infinite dimensions not required for core derivation but needed for full QFT embedding.

### 8.2 Multiple Subsystems

For systems with more than two subsystems:
- Does the tensor product rule iterate? A ⊗ B ⊗ C = (A ⊗ B) ⊗ C = A ⊗ (B ⊗ C)?
- Associativity is a property of the tensor product but should be derivable

**Claim:** Associativity follows from repeated application of the two-system result.

**Sketch:** If A, B, C each have Determinate Identity, then so do (A,B), (B,C), and (A,B,C). The composition (A ⊗ B) ⊗ C and A ⊗ (B ⊗ C) must agree because both represent the same L<sub>3</sub>-admissible joint state structure.

**Status:** ARGUED — not fully developed here.

### 8.3 Real vs. Complex

The derivation is field-agnostic at the composition level. The choice of ℂ over ℝ is fixed by Step 4 (Masanes-Müller) and empirical input (Renou et al., 2021), not by the composition rule itself.

---

## 9. Summary

| Section | Content | Status |
|---------|---------|--------|
| §2 | Product states from Determinate Identity | ESTABLISHED |
| §3 | Tensor product from correlation requirements | ARGUED |
| §4 | Holistic states excluded by H1 → H2 | ARGUED |
| §5 | Tensor product uniqueness | ARGUED |
| §6 | Formal grounding of `product_factorizes` | ARGUED |

The tensor product composition rule $\mathcal{H}_A \otimes \mathcal{H}_B$ is not a postulate but a derived consequence of L<sub>3</sub>. The derivation chain proceeds:

$$L_3 \to \text{Determinate Identity} \to \text{Product states exist} \to \text{Factorization on products}$$

$$L_3 + \text{PPC} \to \text{Correlations physical} \to \text{Entanglement required} \to \text{Tensor product minimal extension}$$

$$\text{H1} \to \text{H2} \to \text{Holism excluded} \to \text{Tensor product unique}$$

The `product_factorizes` axiom in the Lean formalization is thereby grounded in the prose derivation. Its Tier 2 status reflects the ARGUED steps in the H1 → H2 bridge.

---

## References

Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Hardy, L. (2001). Quantum theory from five reasonable axioms. *arXiv:quant-ph/0101012*.

Masanes, L. and Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Popescu, S. and Rohrlich, D. (1994). Quantum nonlocality as an axiom. *Foundations of Physics*, 24(3), 379-385.

Renou, M. O., et al. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600(7890), 625-629.

---

*Supplement S12 | Logic Realism Theory Project | 2026-03-13*
