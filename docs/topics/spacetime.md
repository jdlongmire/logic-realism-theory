---
layout: default
title: "Spacetime Structure"
permalink: /topics/spacetime/
---

<div class="topic-header">
  <h1>Spacetime Structure</h1>
  <p>Temporal Ordering from Joint Inadmissibility</p>
</div>

If $L_3$ constrains physical instantiation, that constraint applies to **spacetime itself**—not just to configurations within spacetime. Logic Realism Theory derives key spacetime features from Determinate Identity.

---

## The Problem

General relativity assumes rather than derives several structural features:

- **Lorentzian signature:** Why (3,1) rather than (4,0) or (2,2)?
- **Temporal ordering:** Why is there a distinguished "timelike" direction?
- **Causal structure:** Why can't effects precede causes?
- **CTC exclusion:** Why are closed timelike curves problematic?

Can these be derived from more fundamental constraints?

---

## Temporal Ordering from Joint Inadmissibility

**Definition:** Two configurations $c_1, c_2 \in A_\Omega$ are **jointly admissible** if their conjunction is also admissible: $c_1 \land c_2 \in A_\Omega$.

They are **jointly inadmissible** if: $c_1 \land c_2 \notin A_\Omega$

For example: "particle at position $x_1$" and "same particle at position $x_2 \neq x_1$" are individually admissible but jointly inadmissible (at the same time).

**Theorem (Temporal Ordering):** If two $L_3$-admissible configurations are jointly inadmissible but both are instantiated, then they must be temporally ordered.

**Proof sketch:** If both $c_1$ and $c_2$ are instantiated but cannot be co-instantiated, there must be an ordering relation: "$c_1$ before $c_2$" or "$c_2$ before $c_1$."

**Conclusion:** Time emerges as the logical sequencing necessitated by joint inadmissibility. It is not an additional postulate but the structure that permits individually-admissible configurations to both be instantiated.

---

## Lorentzian Signature

**Heuristic argument:** If temporal ordering arises from joint inadmissibility and spatial separation permits joint admissibility, then the metric signature must be Lorentzian.

- **Timelike separation:** Sequential instantiation of jointly-inadmissible configurations
- **Spacelike separation:** Possible co-instantiation of jointly-admissible configurations
- **Lorentzian signature (3,1):** Encodes exactly this asymmetry

Other signatures fail:
- **(4,0) Euclidean:** No distinguished temporal direction; cannot represent the asymmetry
- **(2,2) Split:** Two "timelike" directions; would permit multiple independent temporal orderings

---

## CTC Exclusion

**Theorem (CTC Exclusion):** Closed timelike curves violate Determinate Identity.

**Proof:** On a CTC, event $e$ is in its own causal past. The "first" occurrence of configuration $c_e$ has identity $i_1$; the "second" occurrence (after the loop) has identity $i_2$. But they are the same event: $i_1 = i_2$.

Is $i_1$ causally prior to $i_2$, or $i_2$ prior to $i_1$? On a CTC, both. This violates antisymmetry of causal ordering:

$$i_1 < i_2 \text{ and } i_2 < i_1 \Rightarrow i_1 \neq i_2$$

Yet $i_1 = i_2$ by assumption. **Contradiction.**

**Conclusion:** CTCs violate Id. Spacetimes containing CTCs are not in $A_\Omega$.

---

## Singularity Constraints

**Theorem (Identity Preservation):** If Determinate Identity holds, then no physical process can destroy identity-constituting information.

**Implications for singularities:**

If a configuration evolves to a singularity where it "ceases to exist":
- **Option A:** Identity is destroyed (no successor) → Violates Id
- **Option B:** Identity transforms into new configuration → Compatible with Id

**Conclusion:** Physical singularities cannot destroy identity. Either:
1. Singularities are not genuine endpoints (information escapes)
2. Singularities involve identity transformation (not destruction)
3. Classical singularities are artifacts of incomplete physics

This aligns with modern views from AdS/CFT, but LRT provides a **logical** reason: Id forbids information destruction.

---

## Identity Continuity

For a system to persist through time, successive configurations must satisfy **bounded distinguishability**:

**Lemma:** The configuration at $t_2$ must be sufficiently similar to the configuration at $t_1$ for there to be a determinate fact that they are the same system.

If configurations $c_1$ and $c_2$ share no properties grounding identity across time, there is no fact that $c_2$ is the *continuation* of $c_1$.

**Consequence:** Physical evolution cannot change configurations arbitrarily fast. There is a maximal rate of change compatible with identity preservation—leading to **quadratic identity strain** structure.

---

## What Remains

These results are **programmatic**—rigorous formalization requires additional development. Open questions:

- Can Einstein's field equations be derived from $L_3$ + vehicle-invariance?
- How does $L_3$ constrain quantum gravity?
- What does $L_3$ imply for cosmological initial conditions?

---

## Related Papers

<div class="paper-grid">
  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2025-gr-extension/">GR Extension Paper</a></h3>
    <p>Full development of spacetime implications: temporal ordering, CTC exclusion, identity strain.</p>
    <a href="{{ site.baseurl }}/papers/2025-gr-extension/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2026-position-paper/">Position Paper</a></h3>
    <p>Joint inadmissibility and temporal ordering in the core framework.</p>
    <a href="{{ site.baseurl }}/papers/2026-position-paper/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2026-it-from-bit/">It from Bit</a></h3>
    <p>Identity continuity and bounded distinguishability constraints.</p>
    <a href="{{ site.baseurl }}/papers/2026-it-from-bit/" class="card-link">Read Paper →</a>
  </div>
</div>
