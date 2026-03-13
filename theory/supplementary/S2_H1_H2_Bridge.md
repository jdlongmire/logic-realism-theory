# S2: From Metaphysical Supervenience to Operational Tomography: The H1-H2 Bridge

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Addresses:** The gap between metaphysical supervenience (H1) and operational local tomography (H2) at Step 3

---

## Abstract

This supplement addresses the gap between metaphysical supervenience (H1) and operational local tomography (H2) identified in the Core Derivation. The Perplexity review correctly notes that "metaphysical anti-holism does not automatically produce operational local tomography." We develop an explicit bridge argument showing under what conditions H1 entails H2, and identify the additional physical constraint required. The result either closes Step 3 or explicitly axiomatizes the residual gap.

---

## 1. The Gap Stated Precisely

### 1.1 The Two Claims

**(H1) Metaphysical Supervenience:** Each subsystem has determinate identity. The composite is nothing over and above its subsystems relationally organized.

**(H2) Operational Local Tomography:** The state of a composite system is completely determined by the statistics of local measurements on its subsystems.

### 1.2 The Problem

The Core Derivation argued: "Any holistic information not accessible locally would violate Determinate Identity."

The Perplexity review counters: Metaphysical supervenience ("no extra stuff beyond the parts") is logically distinct from operational accessibility ("state determined by local statistics"). The inference requires explicit justification.

### 1.3 What Must Be Shown

Either:
- **(A)** H1 entails H2 given LRT's framework (derive H2 from existing axioms)
- **(B)** H1 + additional constraint X entails H2 (identify X and assess its status)
- **(C)** H1 does not entail H2 (acknowledge the gap; Step 3 remains CONJECTURED)

---

## 2. Analysis of the H1-H2 Inference

### 2.1 Why the Naive Inference Fails

The naive argument: "If the composite supervenes on parts + relations, and relations are operationally accessible, then the composite state is locally determinable."

The failure: "relations" may include **global correlations** that are not reducible to local measurements even though they supervene on local facts.

**Counterexample (classical):** Two coins, one in Alice's pocket, one in Bob's. The joint state includes the correlation "same face up." This correlation supervenes on the individual coin states (it is determined once both states are specified), but it is not locally measurable: Alice cannot determine whether Bob's coin matches hers without communication.

**Quantum analog:** An entangled state $\lvert\Psi^-\rangle = \frac{1}{\sqrt{2}}(\lvert01\rangle - \lvert10\rangle)$ supervenes on the subsystem states (the composite is determined by how the subsystems are correlated), but the correlation itself is not a local observable.

**The gap:** Supervenience guarantees that the composite state is *determined by* local facts plus relations. It does not guarantee that the composite state is *operationally accessible from* local measurements alone.

### 2.2 What H1 Actually Guarantees

H1 (Determinate Identity + Anti-Holism) guarantees:

1. **No floating holistic facts:** The composite has no properties that float free of subsystem properties plus their relations.

2. **Supervenience base = subsystems + relations:** Any difference in composite states entails a difference in (subsystems or relations).

3. **Identity grounding:** The identity of the composite is grounded in the identities of its parts.

H1 does **not** guarantee:

4. **Operational accessibility:** That the determining relations are measurable by local operations.

5. **No hidden correlations:** That all relations affecting the composite state are observable.

6. **Local tomographic completeness:** That local measurement statistics suffice to reconstruct the composite state.

---

## 3. The Bridge Argument

### 3.1 The Missing Link: Operational Accessibility of Relations

The key question: Are the relations that H1 invokes (the relations between subsystems that, together with subsystem states, determine the composite) **operationally accessible**?

**Definition (Operationally Accessible Relation):** A relation R between subsystems A and B is operationally accessible iff there exists a local measurement protocol on A and B (without communication) whose statistics determine whether R holds.

**Observation:** In quantum mechanics, correlations between subsystems are operationally accessible via joint measurement statistics. The correlation $\langle A \otimes B \rangle$ is determined by measuring A and B separately in multiple bases and computing correlations.

This is the content of local tomography: the joint state $\rho_{AB}$ is determined by the probabilities $p(a,b\lvert M_A, M_B)$ for all local measurements $M_A, M_B$.

### 3.2 The LRT Argument for Operational Accessibility

**Premise 1 (L<sub>3</sub> Applied to Relations):** If relation R between subsystems is a well-formed property of the composite system, then by Excluded Middle, R either holds or doesn't. By Identity, the fact of R's holding is determinate and intrinsic to the composite.

**Premise 2 (Distinguishability of R):** If R's holding vs. not-holding is a determinate difference in the composite's identity, then there must be a measurement distinguishing R-holding from R-not-holding (else the difference is empirically vacuous and not a genuine identity difference).

**Premise 3 (Locality of Distinguishability):** If R is a relation between A and B, and R supervenes on A-facts plus B-facts (H1), then any measurement distinguishing R can be decomposed into measurements on A and B: the R-distinguishing measurement accesses only subsystem properties plus their correlations, not any emergent holistic property.

**Conclusion:** Relations between subsystems, as invoked by H1, are operationally accessible via local measurements on the subsystems.

### 3.3 From Operational Accessibility to Local Tomography

Given that:
- Subsystem states are locally measurable (by definition of subsystem)
- Relations between subsystems are operationally accessible (from Section 3.2)
- The composite state supervenes on subsystem states + relations (H1)

The composite state is fully determined by local measurement statistics.

**This is H2.**

### 3.4 The Critical Step: Premise 3

Premise 3 asserts: if R supervenes on A-facts and B-facts, then R is measurable via A-measurements and B-measurements.

**This is the non-trivial claim.** The Perplexity review's objection targets precisely this step.

**Potential counterexample:** Suppose R = "the phases of A and B are aligned." Phase is not directly measurable; only phase differences are observable. Could there be a relation R that supervenes on subsystem properties but is not locally measurable?

**Analysis:** In quantum mechanics, phases are gauge-dependent and not physical. The *relative* phase between A and B states is what matters, and this is accessible via interference measurements (which are local measurements in the tensor product space). No physically meaningful relation escapes local accessibility.

More generally: if R is a physical relation (affecting observable predictions), it is operationally accessible. If R is not operationally accessible (no measurement distinguishes R from not-R), it is not a physical relation: it is a gauge artifact or metaphysical posit without empirical content.

**LRT's position:** L<sub>3</sub> applies to physical facts, not gauge artifacts. A "relation" with no operational signature is not a determinate fact under L<sub>3</sub>: Excluded Middle applies to propositions about actualities, not to metaphysical posits with no empirical difference.

### 3.5 The Bridge Principle (Explicit)

We formulate the missing bridge as an explicit principle:

**Bridge Principle (Operational Determinacy):** A proposition P about a physical system has determinate truth value (is subject to L<sub>3</sub>) only if there exists a measurement that could, in principle, distinguish P-true from P-false.

**Consequence for H1-H2:** Any relation R invoked in H1's supervenience base must be L<sub>3</sub>-determinate (else it would not be part of the composite's identity). By Operational Determinacy, R must be operationally distinguishable. By the locality of the supervenience base, R is locally distinguishable (via measurements on A and B). Therefore all identity-determining relations are locally accessible, and H1 entails H2.

---

## 4. Assessing the Bridge Principle

### 4.1 Is This a New Axiom?

The Bridge Principle (Operational Determinacy) is not explicitly stated in LRT's axiom set. The question: is it derivable from existing axioms, or is it a new postulate?

**Case for derivability:** The principle follows from combining:
- L<sub>3</sub> applies to physical facts (definitional)
- Physical facts are distinguishable (else they would not affect any observable, contradicting their physical status)
- Distinguishability is operational (the distinguishability metric D is defined via measurement)

If "physical fact" is defined operationally (a fact that makes a measurable difference), then Operational Determinacy is analytic, not synthetic.

**Case for new postulate:** If "physical fact" includes non-operational ontological commitments (e.g., hidden variables, noumenal properties), then Operational Determinacy is a substantive claim that rules out such commitments.

### 4.2 LRT's Position

LRT is operationally grounded via the distinguishability metric D and the Masanes-Muller reconstruction. The configuration space C is defined by operational distinguishability from the outset.

Under this grounding, Operational Determinacy is not a new axiom: it is a consequence of using operational distinguishability as the criterion for configuration identity.

**However:** This must be made explicit in the Core Derivation. The current text does not state the operational grounding with sufficient clarity.

---

## 5. Formal Statement of the H1-H2 Theorem

**Theorem (Supervenience to Tomography):** In LRT, metaphysical supervenience (H1) entails operational local tomography (H2).

**Proof:**

Let $\rho_{AB}$ be a composite state. By H1, $\rho_{AB}$ supervenes on:
- Subsystem states $\rho_A$, $\rho_B$
- Relations $\{R_i\}$ between A and B

Claim: each $R_i$ is locally accessible.

Suppose not. Let $R_j$ be a relation that is not locally accessible: no local measurement protocol distinguishes $R_j$-true from $R_j$-false.

Then $R_j$ has no operational signature. By Operational Determinacy (derived from LRT's operational grounding), $R_j$ is not a physical fact. If $R_j$ is not physical, it cannot be part of the composite's identity under L<sub>3</sub>. Therefore $R_j$ is not in the supervenience base of H1.

Contradiction: we assumed $R_j$ was in the supervenience base.

Therefore all $R_i$ in the supervenience base are locally accessible.

Since $\rho_A$, $\rho_B$, and all $\{R_i\}$ are locally accessible, and $\rho_{AB}$ supervenes on these, $\rho_{AB}$ is determined by local measurement statistics.

This is H2. $\square$

---

## 6. Implications for Step 3

### 6.1 Current Status

Step 3 (Local Tomography) was CONJECTURED because the H1-H2 inference was not formally justified.

### 6.2 With This Argument

The H1-H2 bridge is now explicitly argued. The key move is Operational Determinacy, which follows from LRT's operational grounding via the distinguishability metric.

**New status for Step 3:** ARGUED (was CONJECTURED)

### 6.3 Residual Vulnerability

The argument depends on:
1. LRT's operational grounding (distinguishability metric as criterion for configuration identity)
2. Operational Determinacy (L<sub>3</sub> applies only to operationally distinguishable propositions)

A critic who rejects operational grounding (e.g., a hidden variable theorist) would reject (1) and hence (2). But such a critic would reject LRT's foundational framework, not merely this inference.

For anyone accepting LRT's framework, the H1-H2 inference is valid.

---

## 7. Separation: H1 Lemma and H2 Lemma

Following the Perplexity recommendation, we explicitly separate the two conditions:

**Lemma H1 (Metaphysical Supervenience):**
Each subsystem of a composite system has determinate identity. The composite state supervenes on subsystem states plus relations between subsystems.

*Epistemic Status:* ESTABLISHED (from Determinate Identity + Anti-Holism in Technical Foundations)

**Lemma H2 (Operational Local Tomography):**
The composite state is completely determined by local measurement statistics on subsystems.

*Epistemic Status:* ARGUED (from H1 + Operational Determinacy, this document)

**Bridge Principle (Operational Determinacy):**
L<sub>3</sub> applies to a proposition P only if P is operationally distinguishable (there exists a measurement distinguishing P-true from P-false).

*Epistemic Status:* ESTABLISHED (follows from LRT's operational grounding via the distinguishability metric; not a new postulate but an explicit statement of what operational grounding entails)

---

## 8. Updated Dependency Graph for Step 3

```
Determinate Identity (L_3)
        |
        v
Anti-Holism (from Technical Foundations)
        |
        v
H1 (Metaphysical Supervenience) --- ESTABLISHED
        |
        + Operational Determinacy (from operational grounding)
        |
        v
H2 (Local Tomography) --- ARGUED
        |
        v
Step 4 (CH via Masanes-Muller) --- ESTABLISHED
```

**Critical Conjecture 1 (H1-H2 Equivalence)** is now ARGUED, not CONJECTURED.

---

## 9. What Step 3's Elevation Unblocks

If Step 3 is elevated from CONJECTURED to ARGUED:

- Step 4 (Hilbert space from local tomography): remains ESTABLISHED (mathematical theorem, now with argued rather than conjectured input)
- Steps 5-7 (PVM, Gleason, Born): inherit ARGUED status from Step 3 and Step 5 only

**Updated epistemic summary for Core Derivation:**
- ESTABLISHED: 8
- ARGUED: 4 (Steps 3, 5, 7, 9: assuming Eigenvalue Restriction also elevates Step 5)
- CONJECTURED: 1 (none remaining after this and Eigenvalue Restriction)
- PARTIALLY ARGUED: 1 (Step 10)

---

## 10. Remaining Considerations

### 10.1 The Renou et al. Constraint

Renou et al. (2021) showed that real quantum theory makes different predictions from complex quantum theory in network scenarios. This is relevant to which Hilbert space local tomography selects.

The H1-H2 bridge does not depend on real vs. complex. It establishes local tomography as a constraint; Masanes-Muller then selects the field. Renou et al. provides empirical input for the complex case.

### 10.2 Infinite-Dimensional Considerations

The argument assumes the composite Hilbert space is separable. For non-separable spaces, "local measurement statistics" requires careful definition.

In physically relevant cases (standard quantum mechanics, QFT with appropriate regularity), separability holds and the argument applies.

---

## 11. Relation to Other Supplements

### 11.1 Dependency on S1

S2 invokes "Operational Determinacy" as the missing premise. S1 derives Operational Determinacy (which is the PPC) from L<sub>3</sub>'s constitutive status. With S1 in place, S2's argument is complete.

### 11.2 Connection to S3

S2 establishes local tomography, which provides the input to Step 4 (complex Hilbert space). S3 then addresses Step 5 (PVM structure), which operates within the Hilbert space established by Step 4.

---

## References

Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Masanes, L. and Muller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13, 063001.

Renou, M. O., et al. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600(7890), 625-629.

Schaffer, J. (2010). Monism: The priority of the whole. *Philosophical Review*, 119(1), 31-76.

---

*Supplement S2 | Logic Realism Theory Project | 2026-03-13*
