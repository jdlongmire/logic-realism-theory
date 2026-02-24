---
layout: default
title: "Definitions & Glossary"
permalink: /definitions/
description: "Complete glossary of Logic Realism Theory terminology including L₃ constraints, I∞, AΩ, vehicle-invariance, and key concepts for understanding the logical foundations of quantum mechanics."
keywords:
  - logic realism theory glossary
  - L3 logical laws
  - quantum ontology definitions
  - vehicle-invariance
  - logical foundations of physics
image: /assets/images/lrt-banner.png
---

<div class="topic-header">
  <h1>Definitions & Glossary</h1>
  <p>Key Terminology for Logic Realism Theory</p>
</div>

This glossary provides plain-language definitions alongside formal notation for all core concepts in Logic Realism Theory. Each term links to detailed discussion in the relevant papers and topic pages.

---

## Core Framework

### L₃ (The Three Logical Laws)

**Plain language:** The three fundamental laws of classical logic—Determinate Identity, Non-Contradiction, and Excluded Middle—treated as ontological constraints on what can be physically instantiated, not merely rules of inference.

**Formal:** $L_3 := \{\text{Id}, \text{NC}, \text{EM}\}$

**Significance:** These constraints define the boundary between what is representable and what is instantiable. They are the logical foundations of physics.

[Full discussion →]({{ site.baseurl }}/topics/l3-constraints/)

---

### I∞ (Representable Configuration Space)

**Plain language:** The space of all possible specifications or descriptions, including contradictions, impossibilities, and configurations that violate logical laws. Everything that can be written down or imagined, whether or not it could exist.

**Formal:** $I_\infty$ — the unconstrained space of all representable configurations

**Example:** "A square circle" is in $I_\infty$ but not in $A_\Omega$. It can be specified but not instantiated.

**Significance:** Distinguishes what can be represented from what can be real.

---

### AΩ (Admissible Configuration Space)

**Plain language:** The subset of representable configurations that satisfy the L₃ constraints. Only configurations in this space can be physically instantiated as stable records.

**Formal:** $A_\Omega := \{ i \in I_\infty : L_3(i) \}$

**Relationship:** $A_\Omega \subset I_\infty$ — the admissible is a proper subset of the representable

**Significance:** Physics operates exclusively within $A_\Omega$. Quantum mechanics describes how configurations cross from potential ($I_\infty$) to actual ($A_\Omega$).

---

### Instantiation

**Plain language:** The process by which a configuration becomes a determinate, stable physical record. The transition from potential to actual.

**Constraint:** Only $L_3$-compliant configurations can be instantiated. Contradictions cannot become records.

**Relationship to measurement:** What quantum mechanics calls "measurement" or "collapse" is the actualization of outcomes in $A_\Omega$.

---

## Vehicle-Content Distinction

### Vehicle

**Plain language:** The mathematical representation or description used to specify a configuration. Different bases, decompositions, or coordinate systems are different vehicles for the same content.

**Example:** A quantum state $\lvert\psi\rangle$ can be written in the position basis, momentum basis, or energy basis. Each is a different vehicle for the same physical content.

**Key insight:** Vehicles are conventional; content is physical.

[Full discussion →]({{ site.baseurl }}/topics/vehicle-content/)

---

### Content

**Plain language:** The physical configuration itself, independent of how it is described or decomposed. What remains invariant across all equivalent vehicles.

**Formal:** Content is what satisfies Determinate Identity—it is determinately what it is regardless of description.

---

### Vehicle-Invariance

**Plain language:** The principle that probability assignments cannot depend on the choice of mathematical representation. If two bases describe the same physical situation, they must yield the same probabilities.

**Formal:** For any unitary $U$: $p(i) = p(Ui)$ when $U$ represents a mere change of description

**Consequence:** Combined with Gleason's theorem, vehicle-invariance forces the Born rule ($\lvert\psi\rvert^2$) as the unique probability measure.

---

## Derived Structures

### Born Rule

**Plain language:** The rule that probability equals the squared amplitude of the quantum state. In LRT, this is derived from vehicle-invariance rather than postulated.

**Formal:** $P(\phi \mid \psi) = \lvert\langle\phi\mid\psi\rangle\rvert^2$

**Derivation:** Determinate Identity → Vehicle-invariance → Gleason's theorem → Born rule

[Full discussion →]({{ site.baseurl }}/topics/born-rule/)

---

### Complex Hilbert Space

**Plain language:** The mathematical space in which quantum states live, using complex numbers (not just real numbers). In LRT, this structure is derived from the requirement that composite systems be fully characterized by local measurements.

**Derivation:** Determinate Identity → Local tomography → Complex field requirement

**Why complex:** Real Hilbert space allows entanglement without interference; only complex Hilbert space permits the interference patterns that local tomography requires.

[Full discussion →]({{ site.baseurl }}/topics/hilbert-space/)

---

### Symmetrization Postulate

**Plain language:** The rule that quantum states of identical particles must be either symmetric (bosons) or antisymmetric (fermions). In LRT, this follows from Determinate Identity applied to particles that lack individual identity.

**Derivation:** If particles lack distinguishing marks, permuting labels cannot change physical content.

---

### Tsirelson Bound

**Plain language:** The maximum correlation strength achievable in quantum mechanics, approximately 2.83 (or $2\sqrt{2}$). In LRT, this bound emerges from the Hilbert space structure itself.

**Formal:** $\lvert\langle CHSH \rangle\rvert \leq 2\sqrt{2}$

**Significance:** Classical physics allows correlations up to 2; quantum mechanics allows up to $2\sqrt{2}$ but no higher. LRT explains why.

[Full discussion →]({{ site.baseurl }}/topics/tsirelson-bound/)

---

## Interface Concepts

### Interface

**Plain language:** The boundary or transition zone between the representable ($I_\infty$) and the instantiated ($A_\Omega$). Quantum mechanics describes how information crosses this interface.

**Motto:** "It from Bit, Bit from Fit" — physical structure (It) emerges from informational structure (Bit), which emerges from logical admissibility (Fit).

---

### Constraint Energy

**Plain language:** A speculative extension proposing that enforcing L₃ constraints has energetic consequences. Configurations "closer" to logical boundaries may involve different energy costs.

**Status:** Programmatic conjecture, not derived result.

---

### Logical Admissibility

**Plain language:** The property of satisfying the L₃ constraints. A configuration is logically admissible if and only if it can be instantiated without contradiction.

**Test:** Can this configuration be recorded as a determinate, stable fact? If yes, it is admissible.

---

## Methodological Terms

### Lakatosian Research Programme

**Plain language:** A framework for evaluating scientific theories developed by philosopher Imre Lakatos. A programme has a "hard core" of central commitments and a "protective belt" of auxiliary hypotheses that can be modified.

**LRT structure:**
- **Hard core:** L₃ as constraints on physical instantiation
- **Protective belt:** Vehicle-invariance formulation, specific derivations, interface criteria

---

### Novel Prediction

**Plain language:** A prediction that was not used to construct the theory and that other approaches do not make. LRT's novel predictions include the requirement for complex (not real) quantum mechanics, confirmed by Renou et al. (2021).

---

## Related Frameworks

### Ontic Structural Realism (OSR)

**Plain language:** A philosophy of physics holding that structure is ontologically fundamental—what exists are relations and patterns, not individual objects with intrinsic properties.

**Relationship to LRT:** LRT is compatible with structural realism but adds the constraint that structure must be $L_3$-compliant to be instantiated.

---

### Wheeler's "It from Bit"

**Plain language:** John Archibald Wheeler's proposal that physical reality (It) emerges from information (Bit). LRT grounds this in logical constraints: Bit from Fit.

[Full discussion →]({{ site.baseurl }}/topics/wheeler/)

---

## Quick Reference Table

| Symbol | Name | Plain Language |
|--------|------|----------------|
| $L_3$ | Three Logical Laws | Identity + Non-Contradiction + Excluded Middle |
| $I_\infty$ | Representable Space | Everything specifiable, including impossibilities |
| $A_\Omega$ | Admissible Space | Only what satisfies $L_3$; the instantiable |
| Id | Determinate Identity | Things are what they are, independent of description |
| NC | Non-Contradiction | Nothing both is and isn't the same property |
| EM | Excluded Middle | For any well-defined property, either it holds or it doesn't |
| $\lvert\psi\rvert^2$ | Born Rule | Probability from squared amplitude |

---

<div class="nav-links">
  <a href="{{ site.baseurl }}/topics/">← Topic Index</a>
  <a href="{{ site.baseurl }}/cite/">How to Cite →</a>
</div>
