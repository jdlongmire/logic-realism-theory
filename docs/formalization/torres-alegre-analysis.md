# Torres Alegre 2025: Causal Derivation of the Born Rule

**arXiv:** 2512.12636
**Title:** Deriving the Born rule from causal structure
**Author:** Torres Alegre (2025)
**Analysis Date:** 2026-03-17
**Purpose:** LRT Step 6 formalization support

---

## Executive Summary

Torres Alegre (2025) proves that the Born rule is the **unique probability assignment** compatible with relativistic causality (no-signaling) in generalized probabilistic theories (GPTs) with purification. The key insight is that **steering**—non-classical correlations arising from measurement on entangled systems—acts as a "causality enforcer" that uniquely selects the linear mapping Φ(p) = p.

**LRT Relevance:** This provides a non-circular, causal derivation of the Born rule that can strengthen Step 6's frame function approach. The no-signaling constraint maps directly to L₃ (Excluded Middle) constraints on information propagation.

---

## Paper Structure

### Abstract (verbatim)

> Within finite-dimensional generalized probabilistic theories (GPTs), we distinguish between the geometric transition probability τ(ψ,φ), defined as the maximum probability of accepting φ when the state is ψ, and the predictive probability P(φ|ψ) assigned to measurement outcomes. We ask what functional relationship P = Φ(τ) is compatible with relativistic causality. We prove that in any GPT satisfying purification, and therefore admitting steering, the only such relationship consistent with no-signaling is the identity Φ(p) = p. Any strictly convex or concave deviation from linearity enables superluminal signaling through steering scenarios. We provide an explicit qubit example showing how nonlinear probability rules generate detectable signaling channels. Combined with standard reconstruction results, this yields the Born rule |⟨φ|ψ⟩|² as the unique causally consistent probability assignment. Our analysis clarifies the distinction between geometric structure and probabilistic prediction in quantum theory, and identifies steering as the mechanism enforcing the Born rule.

---

## Five Foundational Axioms (GPT Framework)

Torres Alegre builds on the standard GPT framework with five axioms:

| Axiom | Name | Formulation | LRT Mapping |
|-------|------|-------------|-------------|
| **A1** | Causality | Outcome probabilities depend only on local preparation and measurement, not future events | L₃: temporal direction determined |
| **A2** | Tomography | Systems can be fully characterized by sufficiently many measurements | L₃: complete resolvability |
| **A3** | Purification | Every mixed state can be obtained by tracing out a reference system from a pure state | L₃ consistency on composites |
| **A4** | No-Signaling | Marginal probability of one party's measurement is independent of distant measurements | L₂ + L₃: no contradiction via distant action |
| **A5** | Local Distinguishability | Distinct product states can be distinguished through local operations | L₁: identity preserved under locality |

---

## Main Theorem

**Theorem (Torres Alegre 2025):**
Under axioms A1-A5, the only functional relationship P = Φ(τ) between geometric transition probability τ and predictive probability P that is consistent with no-signaling is the **identity** Φ(p) = p.

**Proof Strategy:**
1. Assume Φ(p) deviates from linearity (strictly convex or concave)
2. Construct steering scenario where Alice's measurement affects Bob's conditional state
3. Show that nonlinear Φ produces a detectable correlation pattern at Bob's location
4. This violates no-signaling (Alice can encode information in her measurement choice)
5. Therefore Φ must be linear: Φ(p) = p

**Consequence:**
For quantum mechanics with τ(ψ,φ) = |⟨φ|ψ⟩|² (overlap), we get:
- P(φ|ψ) = |⟨φ|ψ⟩|² (Born rule)

---

## Steering as Causality Enforcer

The paper identifies **steering** as the mechanism that enforces the Born rule:

**Steering Setup:**
- Alice and Bob share entangled state |ψ⟩_AB
- Alice measures in basis {|a⟩}
- Bob's conditional state depends on Alice's outcome (steering)
- If Φ ≠ identity, Bob's statistics leak information about Alice's choice

**Key Lemma:**
In steering scenarios, nonlinear probability rules Φ create signaling channels:
- Alice measures in basis {|a⟩} vs {|a'⟩}
- Bob's average outcome probabilities differ depending on Alice's basis choice
- This difference is detectable → superluminal signaling

**Why This Matters:**
- Steering uses entanglement + measurement choice
- No direct interaction between Alice and Bob
- Causality (no-signaling) is the constraint that selects Φ = identity

---

## Mapping to LRT L₃ Constraints

### L₃ and No-Signaling

LRT's Excluded Middle (L₃: ∀A: A ∨ ¬A) has direct correspondence to no-signaling:

| L₃ Principle | No-Signaling Requirement |
|--------------|--------------------------|
| **Definiteness:** Every proposition has determinate truth value | **Marginal independence:** Bob's outcome exists independent of Alice's choice |
| **No middle ground:** A or not-A, no third option | **No intermediate signaling:** Alice either signals (violation) or doesn't (Φ = identity) |
| **Binary resolution:** Each measurement yields one outcome | **Single outcome:** Each local measurement has definite result |

### L₂ and Non-Contradiction

LRT's Non-Contradiction (L₂: ∀A: ¬(A ∧ ¬A)) underlies the impossibility proof:

| L₂ Principle | Causal Consistency |
|--------------|-------------------|
| **No contradiction:** Cannot have A and not-A | **No simultaneous signaling/non-signaling:** Either Φ = identity or signaling |
| **Exclusive outcomes:** Orthogonal projections are mutually exclusive | **Exclusive information channels:** Can't have both local hidden variables AND nonlocal signaling |

### L₁ and Local Distinguishability

LRT's Identity (L₁: ∀A: A = A) maps to local distinguishability:

| L₁ Principle | Distinguishability |
|--------------|-------------------|
| **Self-identity:** A is determinately A | **Local identity:** Product states have determinate local character |
| **Distinguishability:** A ≠ B when A and B have different properties | **Tomographic locality:** Local measurements suffice to distinguish product states |

---

## Lemmas for Step 6 Formalization

Torres Alegre provides several key lemmas that can strengthen LRT Step 6:

### Lemma 1: Nonlinearity Implies Signaling

**Statement:** If Φ: [0,1] → [0,1] is strictly convex or concave, then there exists a steering scenario where Alice can signal to Bob.

**LRT Use:** This can replace or supplement the current frame function approach. Instead of deriving Born rule via Gleason + MaxEnt, we can derive it from L₃ (no-signaling) directly.

**Lean Structure:**
```lean
axiom nonlinearity_implies_signaling :
  ∀ (Φ : ℝ → ℝ), StrictlyConvex Φ ∨ StrictlyConcave Φ →
  ∃ (steering_scenario : SteeringScenario), CanSignal steering_scenario Φ
```

### Lemma 2: Steering in Purified GPTs

**Statement:** Any GPT satisfying purification admits steering correlations.

**LRT Use:** Purification is already derivable from L₃ in LRT (compositionality forces purification for consistency). This lemma connects to existing Track 2.3 material.

**Lean Structure:**
```lean
axiom purification_admits_steering :
  ∀ (G : GPT), Purification G → AdmitsSteering G
```

### Lemma 3: Linearity Uniquely Avoids Signaling

**Statement:** The only function Φ: [0,1] → [0,1] satisfying Φ(0) = 0, Φ(1) = 1, and no-signaling is Φ(p) = p.

**LRT Use:** This is the core theorem. It proves Born rule uniqueness from causality alone.

**Lean Structure:**
```lean
axiom linearity_from_causality :
  ∀ (Φ : ℝ → ℝ), Φ 0 = 0 → Φ 1 = 1 → NoSignaling Φ →
  ∀ p, Φ p = p
```

---

## Lean Formalization Strategy

### Phase 1: GPT Infrastructure (Tier 2)

Define the GPT framework using Mathlib's existing structures:

```lean
/-- Generalized Probabilistic Theory axioms (Tier 2 infrastructure) -/
structure GPTAxioms where
  /-- A1: Causality - probabilities depend on local preparations -/
  causality : LocalProbabilityDepends state measurement
  /-- A2: Tomography - measurements characterize states -/
  tomography : MeasurementsCharacterize states
  /-- A3: Purification - mixed states are marginals of pure states -/
  purification : MixedStatesPurify
  /-- A4: No-signaling - marginals independent of distant choices -/
  no_signaling : MarginalsIndependent
  /-- A5: Local distinguishability -/
  local_dist : ProductStatesDistinguishable
```

### Phase 2: Steering Definitions

```lean
/-- Steering scenario: Alice-Bob bipartite system with entanglement -/
structure SteeringScenario where
  alice_basis : Fin n → State
  bob_measurements : List Measurement
  shared_state : BipartiteState
  is_entangled : IsEntangled shared_state

/-- Signaling: Alice's choice affects Bob's statistics -/
def CanSignal (scenario : SteeringScenario) (Φ : ℝ → ℝ) : Prop :=
  ∃ (alice_choice₁ alice_choice₂ : AliceMeasurement),
    BobStatistics scenario alice_choice₁ Φ ≠ BobStatistics scenario alice_choice₂ Φ
```

### Phase 3: Main Theorem

```lean
/-- Torres Alegre 2025: Born rule from causal consistency -/
theorem born_rule_from_causality
    (G : GPTAxioms)
    (Φ : ℝ → ℝ)
    (h_boundary : Φ 0 = 0 ∧ Φ 1 = 1)
    (h_no_signal : ∀ scenario, ¬CanSignal scenario Φ) :
    ∀ p ∈ Set.Icc 0 1, Φ p = p := by
  -- Proof via contradiction:
  -- 1. Assume Φ ≠ identity
  -- 2. Then Φ is strictly convex or concave on some interval
  -- 3. By nonlinearity_implies_signaling, there exists signaling scenario
  -- 4. This contradicts h_no_signal
  sorry -- TIER 2: Full proof requires convex analysis
```

### Phase 4: Integration with Step 6

```lean
/-- Alternative Born rule derivation via Torres Alegre -/
theorem born_rule_torres_alegre :
    ∃ (br : BornRule H),
      (∀ P ψ, br.prob P ψ = projectionProbability P ψ) ∧
      CausallyConsistent br := by
  -- Use linearity_from_causality to show projectionProbability
  -- is the unique causally consistent probability rule
  exact ⟨canonicalBornRule, fun _ _ => rfl, born_causality_consistent⟩
```

---

## Comparison: Torres Alegre vs Current Step 6

| Aspect | Current Step 6 (Gleason+MaxEnt) | Torres Alegre (Causal) |
|--------|--------------------------------|------------------------|
| **Starting point** | Frame functions FF1-FF3 | GPT axioms A1-A5 |
| **Core mechanism** | Gleason's theorem forces Tr(ρP) | Steering + no-signaling forces Φ = p |
| **MaxEnt role** | Selects pure states ρ = |ψ⟩⟨ψ| | Not needed |
| **Circularity** | Claims non-circular; MaxEnt may assume probabilities | Non-circular; pure logical/causal |
| **LRT connection** | FF1-FF3 from 3FLL (claimed) | A4 (no-signaling) from L₃ directly |
| **Lean complexity** | Requires Gleason formalization | Requires steering/GPT formalization |

### Recommendation

**Maintain both approaches:**
1. **Gleason+MaxEnt** (current Track 2.1-2.7): Established, connects to existing literature
2. **Torres Alegre (new Track 2.X)**: Cleaner L₃ connection, no MaxEnt dependency

**Add Torres Alegre as alternative derivation:**
```lean
/-- Two independent Born rule derivations -/
theorem born_rule_dual_derivation :
    BornRuleGleasonMaxEnt ↔ BornRuleCausalConsistency :=
  ⟨gleason_implies_causal, causal_implies_gleason⟩
```

---

## Identified Gaps and Future Work

### Gap 1: Steering Formalization

Torres Alegre uses steering scenarios that require:
- Bipartite state space formalization
- Conditional state computation after Alice's measurement
- Statistical distinguishability of Bob's outcomes

**Mathlib status:** Partial support via `InnerProductSpace`, `TensorProduct`, need custom steering definitions.

### Gap 2: Convexity Arguments

The impossibility proof uses:
- Strict convexity/concavity of Φ
- Intermediate value arguments
- Continuity assumptions

**Mathlib status:** Good support in `Mathlib.Analysis.Convex`

### Gap 3: GPT to QM Bridge

Torres Alegre works in abstract GPT framework. Need:
- GPT → Hilbert space specialization theorem
- Transition probability τ = |⟨φ|ψ⟩|² for complex Hilbert space
- Masanes-Müller reconstruction connection

**LRT status:** Partially addressed in Step 3 (Hilbert space derivation)

---

## Action Items

### Immediate (Lean formalization)

1. **Define `SteeringScenario` structure** in `Step6_BornRule.lean`
2. **Add `NoSignaling` predicate** connecting to L₃
3. **State Torres Alegre main theorem** as Tier 2 axiom (pending full proof)
4. **Add alternative `born_rule_causal` theorem** using Torres Alegre

### Short-term (Theory documentation)

5. **Update Step 6 docstring** to mention dual derivation routes
6. **Add Torres Alegre citation** to `Step6_BornRule.lean` header
7. **Cross-reference** with `arxiv-survey-20260317.md`

### Medium-term (Research)

8. **Formal proof of GPT axioms from L₃**: Show A1-A5 derive from 3FLL
9. **Steering-based L₃ proof**: Direct L₃ → no-signaling → Born rule chain
10. **Compare with Yang-Fullwood (2509.08323)**: Categorical structure may simplify proofs

---

## Conclusion

Torres Alegre (2025) provides a powerful alternative derivation of the Born rule that:

1. **Avoids Gleason/MaxEnt machinery** - works directly from causal structure
2. **Maps cleanly to LRT L₃** - no-signaling is L₃ constraint on distant measurements
3. **Identifies steering as enforcement mechanism** - explains *why* Born rule, not just *that*
4. **Is formalizable in Lean** - requires GPT infrastructure but no exotic mathematics

This analysis recommends **adding Torres Alegre as a parallel derivation route** in Step 6, strengthening the non-circularity claims and providing a more direct connection to LRT's foundational L₃ constraints.

---

**References**

- Torres Alegre (2025). "Deriving the Born rule from causal structure." arXiv:2512.12636
- Yang-Fullwood (2025). "Born rule as natural transformation." arXiv:2509.08323
- Agrawal-Wilson (2025). "Process-theoretic Born derivation." arXiv:2511.21355
- LRT Step 6: `formalization/LrtFormalization/Step6_BornRule.lean`
- LRT arxiv survey: `docs/formalization/arxiv-survey-20260317.md`
