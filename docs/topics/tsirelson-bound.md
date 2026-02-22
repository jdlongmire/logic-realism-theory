---
layout: default
title: "Tsirelson Bound"
permalink: /topics/tsirelson-bound/
---

<div class="topic-header">
  <h1>Tsirelson Bound</h1>
  <p>Why Quantum Correlations Are Limited to $2\sqrt{2}$</p>
</div>

The **Tsirelson bound** constrains correlations in Bell-type experiments:

$$S = |E(a,b) - E(a,b') + E(a',b) + E(a',b')| \leq 2\sqrt{2} \approx 2.83$$

This bound is a **mathematical consequence** of Hilbert space structure—and in Logic Realism Theory, Hilbert space structure is itself derived from Determinate Identity.

---

## The Correlation Hierarchy

Bell-type experiments measure correlations between distant measurements. The bounds form a hierarchy:

| Bound | Value | Theory |
|-------|-------|--------|
| Classical (local hidden variables) | $S \leq 2$ | Bell inequality |
| **Quantum (Hilbert space)** | $S \leq 2\sqrt{2}$ | **Tsirelson bound** |
| Algebraic maximum (PR-box) | $S \leq 4$ | No-signaling only |

Nature obeys the quantum bound. But why $2\sqrt{2}$ and not $4$?

---

## Derivation from Hilbert Space

The Tsirelson bound follows from the inner product structure of Hilbert space. For observables A, B with eigenvalues $\pm 1$:

$$|⟨A \otimes B⟩| \leq \|A\| \cdot \|B\| = 1$$

The Cauchy-Schwarz inequality on the Hilbert space inner product yields:

$$S \leq 2\sqrt{2}$$

This is a **mathematical fact** about Hilbert space—not an empirical observation that could have been otherwise.

---

## The LRT Derivation Chain

The complete derivation chain is:

```
L₃ (specifically Determinate Identity)
    ↓ [Theorem: Anti-holism]
Local Tomography
    ↓ [Masanes-Müller reconstruction]
Complex Hilbert Space
    ↓ [Cauchy-Schwarz inequality]
Tsirelson Bound: S ≤ 2√2
```

Each step is either:
- A theorem from Id (our derivations)
- An established mathematical result (reconstruction theorems, Cauchy-Schwarz)

---

## What PR-Boxes Would Violate

**Popescu-Rohrlich (PR) boxes** are hypothetical systems saturating the algebraic maximum $S = 4$. They would satisfy no-signaling but violate the Tsirelson bound.

In LRT terms, PR-boxes would violate **local tomography**:

- Two PR-box states could have identical local statistics
- But differ in their global correlation structure
- This means parts would not determine wholes

PR-boxes exhibit exactly the **global holism** that Determinate Identity rules out. If the whole has properties not grounded in parts, identity becomes extrinsic—violating Id.

---

## What This Means

The Tsirelson bound is not a separate postulate or unexplained fact. It is a **downstream consequence** of Determinate Identity applied to composite systems.

Correlations cannot exceed $2\sqrt{2}$ because:

1. Id forces local tomography (parts ground wholes)
2. Local tomography forces complex Hilbert space
3. Hilbert space structure mathematically caps correlations at $2\sqrt{2}$

**Prediction:** Any observation of correlations exceeding the Tsirelson bound would falsify the $L_3$ constraint framework.

---

## Comparison with Information Causality

Pawlowski et al. (2009) derive the Tsirelson bound from **Information Causality**—the principle that Bob's accessible information cannot exceed the bits physically sent to him.

| Aspect | Information Causality | LRT |
|--------|----------------------|-----|
| Derives Tsirelson? | Yes | Yes |
| Assumes Hilbert space? | No | No (derives it) |
| Core principle | Information access limit | Determinate Identity |
| Type | Operational | Ontological |

These approaches are **complementary**:
- Information Causality shows *what* is ruled out (super-quantum correlations)
- LRT shows *why* nature has the arena it does (complex Hilbert space satisfies Id)

---

## Related Papers

<div class="paper-grid">
  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2025-hilbert-space/">Hilbert Space Paper</a></h3>
    <p>Derives complex Hilbert space from Id; Tsirelson bound follows mathematically.</p>
    <a href="{{ site.baseurl }}/papers/2025-hilbert-space/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2026-position-paper/">Position Paper</a></h3>
    <p>The $L_3$ framework and anti-holism principle (parts ground wholes).</p>
    <a href="{{ site.baseurl }}/papers/2026-position-paper/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2026-it-from-bit/">It from Bit</a></h3>
    <p>Entanglement as global constraint satisfaction, not spooky action.</p>
    <a href="{{ site.baseurl }}/papers/2026-it-from-bit/" class="card-link">Read Paper →</a>
  </div>
</div>
