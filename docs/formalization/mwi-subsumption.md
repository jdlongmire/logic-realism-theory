# MWI Derivations and LRT Subsumption Analysis

**Author**: James D. Longmire (research synthesis by AI assistant)
**Date**: 2026-03-17
**Status**: Working document

---

## Executive Summary

This document analyzes how Logic Realism Theory (LRT) relates to and subsumes the various Many-Worlds Interpretation (MWI) derivations of the Born rule. We map the Deutsch-Wallace decision-theoretic axioms to L₃ constraints, showing that LRT's approach:

1. **Grounds** the axioms that MWI derivations must assume
2. **Eliminates** the need for decision-theoretic machinery
3. **Resolves** the probability problem that plagues MWI
4. **Derives** Born rule from 3FLL rather than from agent rationality postulates

---

## 1. Overview of MWI Born Rule Derivations

### 1.1 The MWI Probability Problem

The core challenge for MWI: if all branches exist deterministically, what does "probability" mean? Four major approaches have been proposed:

| Author(s) | Year | Approach | Core Principle |
|-----------|------|----------|----------------|
| Deutsch | 1999 | Decision theory | Rational betting behavior |
| Wallace | 2010 | Formal decision theory | Six rationality axioms |
| Sebens-Carroll | 2014 | Self-locating uncertainty | Epistemic Separability Principle |
| Vaidman | 2020 | Measure of existence | Born-Vaidman rule |

### 1.2 Key References

- **Deutsch (1999)**: "Quantum Theory of Probability and Decisions", *Proc. Roy. Soc. A* 455:3129–3137
- **Wallace (2010)**: "A Formal Proof of the Born Rule from Decision-Theoretic Assumptions", in *Many Worlds?* (Oxford)
- **Sebens & Carroll (2014)**: "Self-Locating Uncertainty and the Origin of Probability in Everettian Quantum Mechanics", *BJPS* 69:25–74
- **Vaidman (2020)**: Stanford Encyclopedia of Philosophy entry on Many-Worlds Interpretation

---

## 2. Deutsch-Wallace Decision-Theoretic Axioms

### 2.1 Wallace's Six Formal Axioms

Wallace's 2010 proof develops Deutsch's 1999 approach into a rigorous derivation:

| Axiom | Definition | Rationality Assumption |
|-------|------------|------------------------|
| **Ordering** | Preferences ≻^ψ form a total ordering on acts | Transitive, consistent preferences |
| **Diachronic Consistency** | Present preferences align with future preferences across branches | Coherent agency through time |
| **Macrostate Indifference** | Preferences depend only on macrostates, not microstates | Agents can't distinguish micro-details |
| **Branching Indifference** | Indifference to branching structure itself | Branching has no intrinsic value |
| **State Supervenience** | Preferences depend only on actual final states | Counterfactual branches irrelevant |
| **Solution Continuity** | Small perturbations preserve preference ordering | No infinitely precise preferences |

### 2.2 Sebens-Carroll Epistemic Separability Principle (ESP)

**ESP-QM**: An agent's self-locating credences should depend only on the reduced density matrix of the part of the multiverse where they have self-locating uncertainty.

**Key Claim**: In the period between branching and observation, there exists genuine uncertainty about which branch one occupies. ESP then uniquely determines Born-rule credences.

### 2.3 Vaidman's Measure of Existence

**Born-Vaidman Rule**: An observer should set subjective probability of outcome in proportion to the total *measure of existence* of all worlds with that outcome.

**Measure of existence** μᵢ = |αᵢ|²: quantifies a world's "ability to interfere" with other worlds in gedanken experiments.

---

## 3. Mapping Wallace Axioms to L₃ Constraints

### 3.1 The Core Mapping

LRT's three fundamental laws (L₃) — Identity (LOI), Non-Contradiction (LNC), and Excluded Middle (LEM) — provide a more fundamental grounding for each Wallace axiom:

| Wallace Axiom | L₃ Constraint | LRT Analysis |
|---------------|---------------|--------------|
| **Ordering** | LOI (A = A) | A rational preference ordering requires that each alternative has determinate identity. If A is not self-identical, we cannot compare A with B. Ordering presupposes LOI. |
| **Diachronic Consistency** | LOI | The agent-through-time must maintain identity across the decision process. Without LOI, there is no persisting agent whose preferences can be "consistent." |
| **Macrostate Indifference** | LNC | Macrostate equivalence requires that if two microstates are "the same" macrostate, they cannot also be "different" in any decision-relevant way. LNC grounds this identity. |
| **Branching Indifference** | LEM | Either branching has value or it doesn't. If indifferent, then branching itself contributes nothing to preference — a determinate fact about the decision structure. |
| **State Supervenience** | LOI + LNC | The final state is what it is (LOI), and preferences cannot simultaneously depend and not depend on hypothetical branches (LNC). |
| **Solution Continuity** | LEM | Preferences are either ordered or not; continuity ensures the ordering is robust and well-defined. |

### 3.2 Key Insight: L₃ Is More Fundamental

The Wallace axioms describe *rational agent behavior*. But LRT shows these behaviors are forced by something deeper: **logical necessity**.

- Wallace must **assume** rational agents exist and have these properties
- LRT **derives** that any actualized agent must have these properties, because they follow from L₃
- L₃ is transcendentally necessary (denying it presupposes it)

This shifts the burden from "are these reasonable axioms?" to "can you deny L₃?" — a much stronger position.

---

## 4. How LRT Subsumes MWI Branching

### 4.1 The Branching Structure in LRT Terms

MWI postulates universal wave function evolution with branching under decoherence. In LRT terms:

**MWI View**:
- Ψ_universe evolves unitarily
- Decoherence creates branches: Ψ → Σ αᵢ |branch_i⟩
- All branches exist; probability arises from... (this is the problem)

**LRT View**:
- A_Ω = L₃(I∞): actualized domain is logical filtration of information space
- Superposition respects L₃; it distributes actuality across compatible configurations
- The state |ψ⟩ = α|0⟩ + β|1⟩ is a *third state*, neither |0⟩ nor |1⟩
- Measurement resolves this via EM (A ∨ ¬A): exactly one outcome actualizes

### 4.2 LRT's Resolution of the MWI Probability Problem

**The MWI Problem**: If all branches exist, why do we observe Born statistics?

**MWI Attempts**:
1. Deutsch-Wallace: "Rational agents *should* bet according to Born weights"
2. Sebens-Carroll: "Rational credences about self-location follow Born rule"
3. Vaidman: "Measure of existence" weights branches

**All share a common deficiency**: They derive probability from agent behavior/credences, not from physical structure.

**LRT Resolution**:

1. **Probability is ontological, not epistemological**
   - Born rule follows from Gleason's theorem on frame functions
   - Frame functions are constrained by L₃:
     - FF1 (Normalization) ← LEM (completeness: A ∨ ¬A)
     - FF2 (Basis Independence) ← LOI (state identity)
     - FF3 (Additivity) ← LNC (orthogonal = exclusive)

2. **No branching ontology required**
   - LRT derives the quantum formalism without postulating multiple worlds
   - The mathematical structure of superposition and probability emerges from L₃ constraints
   - What appears as "branches" in the wave function are *logically compatible configurations* weighted by their degree of actualization

3. **Actualization is binary, not weighted**
   - A(c) ∈ {0, 1}: configurations are actualized or not
   - The Born weights |αᵢ|² describe the *structure of pre-measurement states*
   - Measurement triggers actualization via EM: exactly one outcome becomes actual
   - Records (measurement outcomes) are determinate facts in the one actualized domain

### 4.3 Why LRT Doesn't Need "Many Worlds"

| MWI Claim | LRT Analysis |
|-----------|--------------|
| "All branches exist equally" | Superposition describes one state, not many worlds |
| "We need to explain why we see some branches more" | Born weights describe state structure, not branch counting |
| "Probability is about rational credence" | Probability is about logical constraints on actualization |
| "Branching is physical" | Branching is decoherence; actualization is L₃-constrained |

**Core difference**: MWI takes the wave function as fundamental and struggles to derive probability. LRT takes L₃ as fundamental and derives both the wave function structure and probability from it.

---

## 5. Born Rule: LRT vs MWI Derivations

### 5.1 Comparison of Derivation Strategies

| Approach | Starting Point | Key Move | Status |
|----------|----------------|----------|--------|
| **Standard QM** | Postulate | Born rule is axiom | No derivation |
| **Deutsch 1999** | Decision theory | Rational betting → Born | Circular (hidden prob. assumptions) |
| **Wallace 2010** | 6 rationality axioms | Representation theorem | Assumes what it proves (critics argue) |
| **Sebens-Carroll** | ESP-QM | Self-locating uncertainty | ESP-QM already encodes Born rule (critics argue) |
| **Vaidman** | Measure of existence | Born-Vaidman rule | μᵢ = |αᵢ|² is postulated, not derived |
| **LRT** | 3FLL (L₃) | Gleason + MaxEnt | Non-circular: FF1-FF3 from L₃ |

### 5.2 LRT's Non-Circular Derivation Chain

```
3FLL (pure logic)
  ↓
Hilbert space ℋ (Steps 0-4)
  ↓
Frame function axioms FF1-FF3 (from EM, ID, NC)
  ↓
Gleason: μ(P) = Tr(ρP) [Tier 2 axiom]
  ↓
MaxEnt: ρ = |ψ⟩⟨ψ| for pure states
  ↓
Born rule: p(x) = |⟨x|ψ⟩|² = ‖Pψ‖²
```

**Why this is non-circular**:
1. We don't presuppose ρ or |ψ⟩ at the start
2. FF1-FF3 are derived independently from L₃
3. Gleason provides mathematical structure given those constraints
4. Born rule is OUTPUT at end, not INPUT at beginning

### 5.3 Addressing Common MWI Objections to Probability

| Objection | MWI Response | LRT Response |
|-----------|--------------|--------------|
| "What does probability mean if all outcomes occur?" | Credence about self-location | Only one outcome actualizes (EM constraint) |
| "Why should agents care about branch weights?" | Rationality axioms | Branch weights = structure of pre-actualized state |
| "Isn't measure of existence ad hoc?" | It's what interferes | It emerges from Gleason + frame function constraints |
| "Why squared amplitudes?" | Representation theorem | Only form satisfying L₃ constraints in Hilbert space |

---

## 6. LRT Advantages Over MWI

### 6.1 Parsimony

**MWI postulates**:
- Universal wave function
- Unitary-only evolution
- Branching structure
- Decision-theoretic principles for probability

**LRT postulates**:
- L₃ (transcendentally necessary — cannot be denied)
- I∞ (information space exists — transcendentally necessary)
- A (primitive action — transcendentally necessary)
- R1-R4 (regularity assumptions, natural defaults)

LRT's primitives are *unfalsifiable in a stronger sense*: denying them is self-refuting. MWI's branching ontology is a metaphysical addition.

### 6.2 Definiteness of Outcomes

**MWI**: All outcomes occur; why we experience definite outcomes is explained by decoherence + selective attention to "our" branch.

**LRT**: Outcomes are genuinely definite because EM (A ∨ ¬A) forces exactly one configuration to be actualized. Records are determinate facts in A_Ω.

### 6.3 No "Probability Problem"

**MWI** must explain why rational agents should assign Born-rule credences in a deterministic multiverse. This requires elaborate decision-theoretic machinery.

**LRT** derives probability as degree of actualization from logical constraints. No agent behavior postulates required.

### 6.4 Grounded Axioms

Every MWI derivation starts with axioms that can be questioned (Why these rationality conditions? Why ESP? Why measure of existence = |α|²?).

LRT starts with L₃, which cannot be coherently questioned. The rest follows.

---

## 7. How LRT "Subsumes" MWI

### 7.1 Subsumption Claim

**LRT subsumes MWI** in the following sense:

1. **Shared formalism**: Both use complex Hilbert space, unitary evolution, Born rule
2. **LRT grounds what MWI assumes**: The decision-theoretic axioms follow from L₃
3. **LRT eliminates MWI's branching ontology**: Superposition is one state, not many worlds
4. **LRT resolves MWI's probability problem**: No need for credence-based derivations

### 7.2 Mathematical Correspondence

MWI and LRT agree on the mathematics:
- States: rays in complex Hilbert space
- Evolution: Schrödinger equation
- Measurement: Born rule
- Composition: tensor products

They differ on **interpretation and grounding**:

| Aspect | MWI | LRT |
|--------|-----|-----|
| Ontology | Many equally-real worlds | One actualized domain A_Ω |
| Superposition | Multiple branches coexisting | One state with distributed actuality |
| Probability | Agent credences about self-location | Logical structure of actualization |
| Measurement | Branching event | EM-driven actualization |
| Born rule | Derived from rationality | Derived from L₃ via Gleason |

### 7.3 What MWI Gets Right (and LRT Preserves)

- Universal wave function evolution (until measurement)
- Decoherence explains emergence of classical behavior
- No collapse mystery (in LRT: actualization, not collapse)
- Deterministic underlying dynamics

### 7.4 What MWI Gets Wrong (and LRT Corrects)

- **Branching ontology**: Multiplying worlds without necessity
- **Probability grounding**: Requiring agent rationality postulates
- **Definiteness**: Struggling to explain why we see definite outcomes
- **Parsimony**: Adding structure beyond what's required

---

## 8. Critical Assessment

### 8.1 Criticisms of MWI Derivations (from Literature)

**Deutsch 1999** (per Barnum et al. 1999):
- Contains "hidden probabilistic assumptions"
- Does not derive probability from non-probabilistic premises

**Wallace 2010** (per various critics):
- State Supervenience is questioned: does it already encode Born rule?
- Branching Indifference: why should agents be indifferent to branching?

**Sebens-Carroll 2014** (per Dawid & Friederich 2021):
- ESP-QM "can only be motivated by the empirical success of quantum mechanics"
- "ESP-QM cannot have the status of a meta-theoretical principle"

**Vaidman 2020**:
- Measure of existence μ = |α|² is postulated, not derived
- Why should agents weight concern by measure?

### 8.2 LRT's Claimed Advantages

1. **Non-circular**: Derives Born rule from independent logical constraints
2. **Transcendentally grounded**: L₃ cannot be coherently denied
3. **Parsimonious**: No branching ontology required
4. **Determinism + Definiteness**: Actualization is binary and EM-constrained

### 8.3 Open Questions for LRT

1. **Decoherence story**: How does LRT's actualization relate to decoherence?
2. **Relativistic extension**: Does L₃-grounded physics extend to QFT?
3. **Measurement trigger**: What precisely triggers EM-actualization?

---

## 9. Conclusion

### 9.1 Summary

LRT subsumes MWI derivations by:

1. **Grounding the axioms**: Wallace's rationality axioms follow from L₃
2. **Eliminating branching ontology**: One world, not many
3. **Deriving Born rule logically**: Via Gleason + frame functions from L₃
4. **Resolving probability problem**: Probability = logical structure, not credence

### 9.2 Key Result

**The Deutsch-Wallace axioms are derivative, not fundamental.**

Each axiom can be shown to follow from L₃ constraints:
- Ordering ← LOI (determinate identity required)
- Diachronic Consistency ← LOI (agent identity through time)
- Macrostate Indifference ← LNC (same macrostate = same state)
- Branching Indifference ← LEM (branching either matters or doesn't)
- State Supervenience ← LOI + LNC (final state is determinate)
- Solution Continuity ← LEM (ordering is determinate)

LRT thus provides the **metaphysical foundation** that MWI derivations implicitly assume.

### 9.3 Implications

1. **For MWI proponents**: LRT shows you can keep the formalism while abandoning many-worlds ontology
2. **For foundations researchers**: L₃-grounded approaches may resolve long-standing interpretational debates
3. **For LRT development**: The MWI literature provides a rich source of technical results to integrate

---

## References

### MWI Derivations
- Deutsch, D. (1999). Quantum theory of probability and decisions. *Proc. Roy. Soc. A*, 455, 3129–3137.
- Wallace, D. (2010). A formal proof of the Born rule from decision-theoretic assumptions. arXiv:0906.2718.
- Sebens, C.T., & Carroll, S.M. (2014). Self-locating uncertainty and the origin of probability in Everettian quantum mechanics. *BJPS*, 69, 25–74.
- Vaidman, L. (2020). Many-Worlds Interpretation of Quantum Mechanics. *Stanford Encyclopedia of Philosophy*.

### Critical Analyses
- Barnum, H., et al. (1999). Quantum probability from decision theory? arXiv:quant-ph/9907024.
- Dawid, R., & Friederich, S. (2021). Epistemic Separability and Everettian Branches. *BJPS*, 73(3).

### LRT Sources
- Longmire, J.D. (2025). The Transcendental Argument for Being: Foundations of Logic Realism Theory.
- Longmire, J.D. (2025). Logic Realism Theory: Technical Foundations. DOI: 10.5281/zenodo.17831883.

### Mathematical Foundations
- Gleason, A.M. (1957). Measures on the closed subspaces of a Hilbert space. *J. Math. Mech.*, 6(6), 885–893.
- Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.
- Chiribella, G., D'Ariano, G.M., & Perinotti, P. (2011). Informational derivation of quantum theory. *Phys. Rev. A*, 84, 012311.
