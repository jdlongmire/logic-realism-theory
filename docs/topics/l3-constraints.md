---
layout: default
title: "The L₃ Constraints"
---

<div class="topic-header">
  <h1>The L₃ Constraints</h1>
  <p>The Three Fundamental Laws of Logic as Physical Constraints</p>
</div>

The **Three Fundamental Laws of Logic** ($L_3$) form the ontological foundation of Logic Realism Theory:

## Determinate Identity (Id)

Every instantiated configuration is determinately what it is, independent of description or decomposition.

$$\text{For any descriptions } d, d' \text{ of the same configuration: } d(i) = d'(i) = i$$

This is not the trivial claim that identity is reflexive ($i = i$). It is the substantive claim that instantiated configurations have determinate identity: they are self-identical in a way that does not depend on how they are described, measured, or decomposed.

**Consequences:**
- Vehicle-invariance (probability assignments cannot depend on basis choice)
- Permutation symmetry for identical particles
- Local tomography (composite states determined by local measurements)

## Non-Contradiction (NC)

No instantiated configuration simultaneously possesses and lacks a property in the same respect.

$$\neg(P(i) \land \neg P(i))$$

The "in the same respect" qualification is essential. An electron can have spin-up relative to the z-axis and spin-down relative to a rotated axis. But it cannot have spin-up *and* spin-down relative to the same measurement basis.

**Consequences:**
- Mutually exclusive measurement outcomes
- Boolean structure of actualized records

## Excluded Middle (EM)

For any well-defined property $P$ applicable to an instantiated configuration, either the configuration possesses $P$ or it lacks $P$.

$$P(i) \lor \neg P(i)$$

This is a constraint on instantiation for sharply specified properties, not a claim about what an agent can know or prove. The law applies to instantiated configurations with respect to well-defined properties.

**Consequences:**
- Determinate measurement outcomes
- Temporal ordering from joint inadmissibility

---

## The Two Domains

The $L_3$ constraints define a boundary between two domains:

**$I_\infty$ (Representable):** All specifications, including contradictions and impossibilities. No constraint.

**$A_\Omega$ (Instantiable):** The subset satisfying $L_3$. Only these configurations can be physically instantiated as stable records.

$$A_\Omega := \{ i \in I_\infty : L_3(i) \}$$

This is the foundational relationship: physics proceeds because its outputs are $L_3$-shaped.

---

## Related Papers

<div class="paper-grid">
  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2026-position-paper/">Position Paper</a></h3>
    <p>Full development of the $L_3$ framework establishing the foundational ontology.</p>
    <a href="{{ site.baseurl }}/papers/2026-position-paper/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2025-born-rule/">Born Rule Derivation</a></h3>
    <p>Vehicle-invariance from Determinate Identity forces the $|\psi|^2$ probability measure.</p>
    <a href="{{ site.baseurl }}/papers/2025-born-rule/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2025-hilbert-space/">Hilbert Space Derivation</a></h3>
    <p>Local tomography from Determinate Identity selects complex Hilbert space.</p>
    <a href="{{ site.baseurl }}/papers/2025-hilbert-space/" class="card-link">Read Paper →</a>
  </div>
</div>
