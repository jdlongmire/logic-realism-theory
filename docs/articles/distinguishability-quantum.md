---
layout: default
title: "Why Distinguishability Requires Quantum Mechanics"
permalink: /articles/distinguishability-quantum/
date: 2026-02-22
author: "James (JD) Longmire"
image: /assets/images/lrt-banner.png
description: "How the requirement that physical outcomes be distinguishable leads inevitably to Hilbert space and quantum structure"
---

<div class="topic-header">
  <h1>Why Distinguishability Requires Quantum Mechanics</h1>
  <p class="article-meta">February 2026 | Intermediate</p>
</div>

If you want to distinguish two things, they have to differ *somehow*.

This sounds trivial. Of course distinguishable things differ. When you take this requirement seriously and ask what mathematical structure is needed for outcomes to be genuinely distinguishable, something surprising happens.

You get quantum mechanics.

---

## The Problem of Vehicle-Invariance

The first article introduced **vehicle-invariance**: whatever is true about a physical outcome must be true regardless of how you describe it. If detector A fires, that fact shouldn't depend on whether you wrote down "A fired" or "the first detector registered a click" or "outcome α occurred."

This seems obvious. But it creates a mathematical problem.

Different descriptions use different labels, different orderings, different conventions. Yet they must all assign the same *structure* to the physical situation. The physics can't depend on the language.

**Vehicle-invariance is the formal version of Determinate Identity.** If an outcome is genuinely itself (if it has determinate identity), swapping labels or changing notation can't change what's physically true about it.

So what mathematical structures respect vehicle-invariance?

---

## Why Probabilities Get Constrained

Here's where quantum mechanics enters.

Suppose you have a physical system with multiple possible outcomes. You want to assign probabilities to those outcomes. What rules must those probabilities follow if they're vehicle-invariant?

**Gleason's Theorem** (1957) answers this question for systems with at least three distinguishable outcomes. It proves that the *only* way to assign probabilities while respecting vehicle-invariance is:

$$P(\text{outcome}) = |\langle \psi | \text{outcome} \rangle|^2$$

This is the Born rule, the fundamental probability law of quantum mechanics.

The derivation doesn't assume quantum mechanics or postulate Hilbert space. It asks: what probability assignments are compatible with vehicle-invariance? And the answer is: the Born rule probabilities, assigned via vectors in Hilbert space.

**Distinguishability forces the Born rule.**

---

## Why Complex Numbers?

Quantum mechanics uses complex numbers. Why not real numbers? Why not quaternions?

This question has a precise answer, and it comes from distinguishability again.

**Local tomography** is the requirement that if you can distinguish two systems separately, you can distinguish their combination using only local measurements. You shouldn't need global access to tell apart things you could tell apart piece by piece.

This is another form of vehicle-invariance. If system A differs from system A' and system B differs from system B', then the combined system (A, B) should differ from (A', B') in a way detectable by examining A and B separately.

Hardy (2001), Chiribella et al. (2011), and Masanes & Müller (2011) showed that **local tomography selects complex Hilbert space**.

- Real Hilbert space fails local tomography. Some distinctions require global access.
- Quaternionic Hilbert space has the same problem.
- Complex Hilbert space (the quantum mechanical choice) is the unique structure that passes.

**Distinguishability forces complex numbers.**

---

## The Symmetrization Postulate

Quantum mechanics distinguishes two kinds of particles: bosons and fermions. Bosons can share quantum states; fermions can't (Pauli exclusion). This follows from Identity.

If two particles are truly identical (genuinely indistinguishable in principle), what happens when you swap them?

For a system to have determinate identity, the swap can't produce a new, distinguishable state. The swapped configuration must relate to the original in one of exactly two ways:

- **Same state:** ψ(1,2) = ψ(2,1) → bosons
- **Opposite sign:** ψ(1,2) = -ψ(2,1) → fermions

These are the only options compatible with determinacy plus linearity. Any other relation would let you distinguish "swapped" from "not swapped" for particles that are supposed to be indistinguishable: a violation of Identity.

**Distinguishability (plus its limits) forces the boson/fermion distinction.**

---

## What We've Derived

Starting from a single requirement (that physical outcomes be genuinely distinguishable, that they have determinate identity), we've derived:

1. **The Born rule** (via Gleason's theorem)
2. **Complex Hilbert space** (via local tomography)
3. **Bosons and fermions** (via symmetrization from Identity)

These aren't the *only* features of quantum mechanics. Specific Hamiltonians, coupling constants, and field content remain empirical. The *framework* (the mathematical arena in which quantum physics operates) emerges from Identity alone.

---

## The Representation-Instantiation Connection

This is where the instantiation barrier becomes vivid.

In $I_\infty$ (the representable), you can describe probability assignments that violate Gleason's theorem. You can specify systems using real or quaternionic Hilbert spaces. You can imagine particles that are "a little bit indistinguishable." The representations exist.

These configurations can't be *instantiated*. When you try to realize them as physical systems with stable, distinguishable outcomes, the $L_3$ constraint kicks in. Only $L_3$-admissible structures (Born rule probabilities, complex Hilbert space, proper symmetrization) make it through the barrier.

The quantum formalism isn't arbitrary. It's the unique mathematical structure for representing systems whose outcomes must be genuinely distinguishable.

---

## Common Questions

**"Didn't Gleason assume Hilbert space?"**

Gleason's original theorem did assume the system lives in Hilbert space. That assumption itself derives from more basic requirements. The reconstruction theorems (Hardy, Chiribella et al.) show that Hilbert space is *forced* by operational constraints including local tomography. So the argument is:

Local tomography → Hilbert space → Gleason's theorem → Born rule

The chain starts from distinguishability, not from assuming quantum mechanics.

**"What about pilot-wave theories or many-worlds?"**

LRT operates at the framework level. Bohmian mechanics, many-worlds, and Copenhagen all operate within the same mathematical structure: complex Hilbert space with Born rule probabilities. LRT explains why that structure, not which interpretation of it is correct.

**"Can you derive the Schrödinger equation?"**

The time evolution aspect (unitary dynamics) is more constrained by symmetry requirements than by $L_3$ alone. Stone's theorem connects continuous symmetry to self-adjoint generators. The arena in which time evolution occurs (complex Hilbert space) is $L_3$ derived.

---

## The Deeper Pattern

What we're seeing is a pattern: **constraints on existence generate mathematical structure**.

Classical physics assumed any consistent mathematical description could in principle be instantiated. LRT says only $L_3$-admissible configurations can cross the instantiation barrier. That constraint, far from being empty, *forces* the quantum formalism.

The $L_3$ laws are the gatekeepers of existence. Quantum mechanics is what happens when you ask: what can exist?

---

## Next in the Series

This article showed how distinguishability leads to quantum structure. The next article, **"The Born Rule Is Not Optional,"** examines the probability derivation in more detail: why Gleason's theorem has the force it does, and what the $\lvert\psi\rvert^2$ rule actually represents.

For the full technical treatment, see the [Position Paper](/logic-realism-theory/papers/2026-position-paper/). For concept-by-concept breakdowns, explore [Topics](/logic-realism-theory/topics/).

---

*Logic Realism Theory was developed by James (JD) Longmire. This article is part of the LRT documentation at [jdlongmire.github.io/logic-realism-theory](https://jdlongmire.github.io/logic-realism-theory).*
