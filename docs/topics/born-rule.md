---
layout: default
title: "Born Rule Derivation"
---

<div class="topic-header">
  <h1>Born Rule Derivation</h1>
  <p>Why Probability Equals the Squared Amplitude</p>
</div>

The **Born rule** states that the probability of measuring outcome $\phi$ given state $\psi$ is:

$$P(\phi|\psi) = \lvert\langle\phi|\psi\rangle\rvert^2$$

In Logic Realism Theory, this is not a postulate but a **theorem**—derived from Determinate Identity applied to representational vehicles.

---

## The Derivation Strategy

The derivation proceeds in four steps:

1. **Vehicle-invariance requirement:** Determinate Identity (Id) applied to representational vehicles
2. **Measure structure:** Vehicle-invariance generates additivity and non-contextuality constraints
3. **Gleason's theorem:** These constraints uniquely determine the measure form
4. **Born rule:** The $\lvert\psi\rvert^2$ form emerges as the unique solution

---

## Vehicle-Invariance: The Core Requirement

A quantum state $|\psi\rangle$ is a representational vehicle encoding outcome-possibilities. For any measurement context with possible outcomes $\{\phi_i\}$, the state assigns probabilities.

**Key insight:** A single physical situation can be described using different bases, different decompositions, different mathematical representations—all equivalent in the sense that they describe the same measurement event.

**Vehicle-invariance** is the requirement that these equivalent descriptions assign the same total probability weight to the event:

$$P_d(E|\psi) = P_{d'}(E|\psi)$$

for any descriptions $d$, $d'$ that both represent event $E$.

This is not a physical assumption. It is a **logical requirement from Id**: if the representational vehicle determinately characterizes the physical situation, then probability assignments that vary with mere representational choice would violate that determinacy.

---

## Ontological Nullity and Logic Pressure

Id-Strong implies that to lack determinate identity is to be **nothing**. We call this limiting condition—where no configuration satisfies Id, NC, or EM—**Ontological Nullity** ($\emptyset_L$). In $\emptyset_L$ there is no stable domain of states, no consistent event algebra, no nontrivial modal partition.

**Logic Pressure** is the formal expression of how physical systems are "pushed away" from $\emptyset_L$:

> If a physical situation failed Id at the vehicle level, its identity would collapse into $\emptyset_L$: there would be no fact of the matter about how it is poised toward outcomes.

Vehicle-weight invariance **is** this logic pressure made mathematically precise: the total measure over admissible continuations must be independent of descriptive decomposition, on pain of indeterminate identity. This is why Id **forces** additivity and non-contextuality rather than merely recommending them.

---

## From Vehicle-Invariance to Gleason's Theorem

Vehicle-invariance immediately generates two constraints:

### Additivity

Consider a measurement with outcomes $\{\phi_1, \phi_2, \phi_3\}$. The event "outcome is $\phi_1$ or $\phi_2$" can be described as:
- A single composite outcome $E = \{\phi_1, \phi_2\}$
- The disjunction of two separate outcomes

Vehicle-invariance requires these assign the same probability:

$$P(E|\psi) = P(\phi_1|\psi) + P(\phi_2|\psi)$$

### Non-Contextuality

The probability assigned to a projector cannot depend on which other projectors it is measured alongside. This is non-contextuality of the *measure*, not of *values*.

---

## Gleason's Theorem

**Gleason's theorem (1957):** In Hilbert spaces of dimension $\geq 3$, any probability measure satisfying additivity and non-contextuality must have the form:

$$P(P_\phi|\psi) = \text{Tr}(\rho P_\phi)$$

For pure states, $\rho = |\psi\rangle\langle\psi|$, giving:

$$P(P_\phi|\psi) = \lvert\langle\phi|\psi\rangle\rvert^2$$

**This is the Born rule.** The $\lvert\psi\rvert^2$ form is the unique probability measure satisfying the constraints that vehicle-invariance imposes.

---

## Why the Squared Magnitude?

Three reasons converge:

**From inner product structure:** The Born rule uses $\langle\phi|\psi\rangle$, which encodes distinguishability (possibly negative or complex). The squared magnitude converts this to probability (real, non-negative).

**From normalization:** For $|\psi\rangle = \sum_i c_i |\phi_i\rangle$, normalization gives $\sum_i \lvert c_i\rvert^2 = 1$. This matches probability normalization exactly when $P(\phi_i|\psi) = \lvert c_i\rvert^2$.

**From Gleason's uniqueness:** Given additivity and non-contextuality, the exponent 2 is not chosen but **forced**. Any other exponent would violate one of these constraints.

---

## Comparison with Other Approaches

| Approach | Born Rule Status | Justification |
|----------|------------------|---------------|
| Copenhagen | Postulated | "It works" |
| Many-Worlds | Derived? | Decision-theoretic (contested) |
| Bohmian | Emergent | Quantum equilibrium (conditional) |
| GRW | Modified | Stochastic collapse postulate |
| **LRT** | **Derived** | **Vehicle-invariance (Id)** |

The LRT derivation is:
- **Rigorous:** Uses Gleason's theorem
- **Unconditional:** Not dependent on equilibrium assumptions
- **Grounded:** Based on logical constraints, not decision theory

---

## Physical Interpretation

The Born rule derivation reveals its physical meaning. The rule is a consequence of requiring that:

1. **Quantum states are determinate vehicles** (Id applied to representation)
2. **Vehicles encode probability structure** (outcomes are $L_3$-admissible but which actualizes is probabilistic)
3. **Probability assignments are vehicle-invariant** (don't vary with representational choice)

The $\lvert\langle\phi|\psi\rangle\rvert^2$ form emerges as the **unique way to assign probabilities** that respects these requirements.

In ontological terms, Determinate Identity functions as a **prohibition against $\emptyset_L$**: a universe with macroscopic records cannot realize the null state where identity, consistency, and modal structure all fail. The Born rule is the unique probability measure that respects this prohibition while remaining compatible with Hilbert-space kinematics.

---

## Related Papers

<div class="paper-grid">
  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2025-born-rule/">Born Rule Paper</a></h3>
    <p>Full technical derivation from vehicle-weight invariance via Gleason's theorem.</p>
    <a href="{{ site.baseurl }}/papers/2025-born-rule/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2026-position-paper/">Position Paper</a></h3>
    <p>Framework establishing Id as ontological constraint on physical instantiation.</p>
    <a href="{{ site.baseurl }}/papers/2026-position-paper/" class="card-link">Read Paper →</a>
  </div>

  <div class="paper-card">
    <h3><a href="{{ site.baseurl }}/papers/2025-hilbert-space/">Hilbert Space Paper</a></h3>
    <p>Why complex Hilbert space—the arena where Gleason's theorem applies.</p>
    <a href="{{ site.baseurl }}/papers/2025-hilbert-space/" class="card-link">Read Paper →</a>
  </div>
</div>
