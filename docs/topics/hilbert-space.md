---
layout: default
title: "Complex Hilbert Space"
permalink: /topics/hilbert-space/
image: /assets/images/lrt-banner.png
---

<div class="topic-header">
  <h1>Complex Hilbert Space</h1>
  <p>Why Local Tomography Selects Complex Numbers</p>
</div>

Quantum mechanics uses **complex Hilbert space** as its state space. Why complex? Why Hilbert space at all? In Logic Realism Theory, this is not a postulate but a **theorem**—derived from Determinate Identity via local tomography requirements.

---

## The Problem

Standard presentations take the mathematical arena as a postulate. Quantum reconstruction programs (Hardy 2001, Masanes-Müller 2011) show that complex Hilbert space is *uniquely determined* by certain operational axioms.

LRT goes further: those axioms are themselves **derivable from Determinate Identity**. They hold because logic demands it.

---

## Axioms Forced by Id

| Reconstruction Axiom | Forced by |
|---------------------|-----------|
| Local tomography | Id + anti-holism |
| Continuous reversible dynamics | Id + continuity of identity |
| Non-trivial correlations | Id permits entanglement |
| Tomographic locality | Consequence of local tomography |

---

## Theorem 1: Id Forces Local Tomography

**Local tomography** states that the state of a composite system is completely determined by the statistics of local measurements on its components.

**Proof sketch:**

Suppose local tomography fails. Then there exist two distinct global states $\omega_1 \neq \omega_2$ with identical local statistics on both subsystems A and B.

By Id, the identity of A must be intrinsic—determined by A's own properties. The only operationally accessible facts about A are its measurement statistics. If A's identity is intrinsic and determinate, it is fixed by these statistics.

The same holds for B.

By the Composition Principle (parts ground wholes), the identity of AB is grounded in A and B. But we've established that A's identity is the same in $\omega_1$ and $\omega_2$, and likewise for B.

Therefore AB's identity must be the same—contradicting $\omega_1 \neq \omega_2$.

**Conclusion:** Local tomography must hold.

---

## Theorem 2: Id Forces Continuous Reversible Dynamics

**Continuity:** If dynamics were discontinuous (system jumps from $\psi_1$ to $\psi_2$ with no intermediate path), the system would lack determinate identity at the transition moment. This violates Id.

**Reversibility:** Consider pure state $\psi$ with maximal information. If dynamics $\psi \to \phi$ were irreversible (with $\phi$ also pure), information about $\psi$'s identity is lost. But if $\psi$ has determinate identity, that identity constitutes information. Irreversible dynamics would destroy this, violating Id.

**Conclusion:** Dynamics between pure states must be continuous and reversible.

---

## Why Complex (Not Real or Quaternionic)?

Local tomography specifically forces the **complex field**:

- **Real Hilbert space** fails local tomography for entangled states. Real density matrices don't span the full product space; correlations involving imaginary phases are inaccessible to local measurements.

- **Quaternionic Hilbert space** violates associativity constraints required for consistent composition.

- **Complex Hilbert space** is the unique field where local tomography holds for all composite systems.

**The derivation chain:**

$$\text{Id} \Rightarrow \text{Local Tomography} \Rightarrow \text{Complex Field}$$

---

## Experimental Confirmation

This theoretical prediction has been experimentally confirmed. **Renou et al. (2021)** designed a Bell-like network scenario that distinguishes real from complex quantum mechanics.

Their result: real quantum mechanics is ruled out. Only complex Hilbert space describes nature.

LRT predicted this: real QM would allow globally distinct states with identical local parts, violating Determinate Identity.

---

## The Uniqueness Theorem

**Theorem (Masanes-Müller 2011):** The unique generalized probabilistic theory satisfying:
- Local tomography
- Continuous reversible dynamics
- Existence of entanglement
- Bit equivalence
- Tomographic locality

is **quantum mechanics over the complex numbers**.

Given our derivation of these axioms from Id, complex Hilbert space becomes a **theorem of $L_3$**.

---

## Consequences

Once complex Hilbert space is established:

- The **Born rule** follows from vehicle-invariance (via Gleason's theorem)
- The **Tsirelson bound** ($S \leq 2\sqrt{2}$ for CHSH) follows mathematically
- **Quantum correlations** are constrained but not maximal

The arena of quantum mechanics is not a brute fact but a **consequence of logic constraining instantiation**.

---

## Related Papers

<div class="paper-grid">
  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2025-hilbert-space/">Hilbert Space Paper</a></h3>
    <p>Full derivation from Determinate Identity via local tomography and reconstruction theorems.</p>
    <a href="{{ site.baseurl }}/papers/2025-hilbert-space/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2026-position-paper/">Position Paper</a></h3>
    <p>The $L_3$ framework establishing Id as ontological constraint.</p>
    <a href="{{ site.baseurl }}/papers/2026-position-paper/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2025-born-rule/">Born Rule Paper</a></h3>
    <p>How the Born rule follows once Hilbert space structure is established.</p>
    <a href="{{ site.baseurl }}/papers/2025-born-rule/" class="card-link">Read Paper →</a>
  </div>
</div>
