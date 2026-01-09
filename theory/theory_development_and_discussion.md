# LRT Development Notes: Bell Tests, Quantum Computing, and Contextual Actuality

**Extracted from research discussions (January 2026)**

---

## 1. Bell Tests and LRT Compatibility

### The Challenge

Bell's theorem shows that you cannot have all three of:
1. **Locality**: Alice's outcome is independent of Bob's setting choice
2. **Measurement-setting independence**: Settings are free, not pre-correlated with hidden variables
3. **Pre-existing determinate values**: For each possible setting pair, outcomes are already definite

LRT forces determinate facts for settings actually chosen and outcomes actually recorded. The question: does LRT require determinate values for *counterfactual* (unmeasured) settings?

### Contextual Actuality Principle

**Principle (Contextual Actuality):** The three fundamental laws of logic (L₃) apply to propositions about outcomes within a *realized context*. LRT does not require that propositions about unperformed measurements have definite truth-values.

**Formalization:**
- A *context* is a specification of which measurements are actually performed in a run (e.g., Alice chooses setting a₁, Bob chooses setting b₂)
- For each run and chosen pair (a, b), there is a definite, logically crisp outcome pair (A, B)
- There is no globally defined table assigning values to all counterfactual settings

### Theorem (Bell Compatibility)

**Theorem 1.** Classical logic applied consistently to actualized outcomes is compatible with Bell inequality violations, provided one does not require global pre-assignment of values for unmeasured observables.

**Proof sketch:**
1. Bell's theorem requires a global hidden-variable assignment λ that determines outcomes for *all* possible measurements
2. LRT only requires L₃-consistency for *actual* outcomes in each run
3. The quantum state provides correlations across spacelike-separated regions via its nonlocal structure
4. Each realized history is local (definite local facts); the *blueprint* (quantum state) is nonlocal
5. No contradiction arises because unmeasured observables are not assigned truth values

**Consequence:** LRT accepts Bell violations as manifestations of nonlocal logical structure in the entangled state, without requiring "spooky action" or hidden variables.

---

## 2. Wigner's Friend and Context-Bound Facts

### The Scenario

- Inside lab: Friend measures a qubit and records "up" in a notebook
- Outside lab: Wigner treats lab+qubit as a coherent quantum system and may perform an interference measurement

### LRT Resolution

**Friend's context:** If measurement inside lab is completed and decohered, propositions like "Friend's record says 'up'" are legitimate classical facts satisfying L₃.

**Wigner's context:** If Wigner performs a measurement incompatible with treating Friend as classical, the context is different. LRT forbids treating both:
- "Friend has a definite classical record"
- "Lab+system is in a pure superposition enabling interference"

as jointly realized facts in the same context.

**Principle:** Logic is classical *inside* a context. We do not force a single Boolean assignment across incompatible contexts simultaneously.

This aligns with the Ontic Booleanity theorem (MVS paper §5): L₃ constraints are ontic for actual tokens, but tokens are context-relative.

---

## 3. Quantum Gates as Logical Transformers

### Single-Qubit Example

Consider a Hadamard gate H followed by Z-basis measurement.

**Blueprint:**
- Input propositions: I₀ ("input is |0⟩"), I₁ ("input is |1⟩")
- Output propositions: O₀ ("detector reads 0"), O₁ ("detector reads 1")
- Probability map: p(Oᵢ | Iⱼ) determined by H matrix and Born rule

**LRT Reading:**
- **Identity:** Each run realizes exactly one of {O₀, O₁}
- **Non-Contradiction:** No run has both O₀ and O₁ true
- **Excluded Middle:** For the performed measurement, one of {O₀, O₁} is true

The gate+measurement is a *logical transformer*: it maps definite input facts to a probability distribution over definite output facts.

### Two-Qubit Entangling Gate

CNOT between control C and target T, followed by Z-basis measurements on both.

**Blueprint:**
- Input propositions: I₀₀, I₀₁, I₁₀, I₁₁ ("CT starts as 00, 01, 10, 11")
- Output propositions: Oₐᵦ ("C measures a, T measures b")
- Probability map: p(Oₐᵦ | Iᵢⱼ) from CNOT matrix

**LRT Reading:**
- Every run yields one sharp pair (a, b)
- Entangled states (e.g., from H+CNOT) encoded as correlation patterns (only 00 or 11 occur)
- Not "both 00 and 11 realized in one run"

An entangling gate is a structured logical constraint on pairs of outcomes.

### Quantum Error Correction

Stabilizer codes can be rephrased as sets of logical constraints (stabilizer propositions) that must hold for valid code states.

- Noise produces histories that violate constraints
- Error correction identifies and corrects violations while preserving logical structure
- A logical qubit is a protected equivalence class of outcome propositions

**LRT Perspective:** Focus on designing codes that preserve logical relations between qubits, treating decoherence as logical constraint failure.

---

## 4. The Blueprint Principle

### Definition

**Blueprint Principle:** For any well-defined experimental configuration C, the quantum formalism assigns:
1. A Hilbert space H_C
2. A set of observables and measurement operators {Mᵢ}
3. A dynamical law (unitary evolution) determining state evolution

This defines a *blueprint*: a set {Oᵢ} of mutually exclusive, exhaustive outcome propositions with Born probabilities p_i = ⟨ψ|Pᵢ|ψ⟩.

### Outcome Realism

**Principle (Outcome Realism):** Each individual run of an experiment realizes exactly one outcome proposition Oᵢ, which obeys L₃.

### Relation to MVS

The blueprint is R(I)—the space of representable configurations. Each run instantiates one element of L(I)—the L₃-admissible actualization. The Minimal Viable Set is the structure of what can actually occur.

---

## 5. Proposed Theorems for Formalization

### Theorem 1: Bell Compatibility (stated above)

Classical logic for actualized outcomes is compatible with Bell violations without global value assignment.

### Theorem 2: Logical Reformulation

**Theorem 2.** Any quantum setup can be reformulated as a finite set of logically consistent outcome propositions with Born probabilities, with no surplus ontology.

**Proof sketch:**
1. Fix a measurement basis (decoherence selects pointer basis)
2. Outcome propositions {Oᵢ} partition the outcome space
3. Each Oᵢ is mutually exclusive with all others (NC)
4. Exactly one Oᵢ true per run (EM)
5. Each Oᵢ is self-identical across references (Id)
6. Born rule provides probability measure over {Oᵢ}
7. No additional ontology (trajectories, branches, collapse dynamics) required

### Conjecture: QFT Extension

**Conjecture.** LRT + QFT unifies logical realism with relativistic causality: the nonlocal logical structure of the quantum field respects Lorentz invariance at the level of observable correlations while each local measurement yields L₃-consistent outcomes.

---

## 6. Comparison Table

| Interpretation | Hidden Variables | Multiple Worlds | New Dynamics | L₃ Status |
|----------------|------------------|-----------------|--------------|-----------|
| Copenhagen | No | No | No (pragmatic) | Agnostic |
| Bohmian | Yes (trajectories) | No | Yes (guiding wave) | Classical for particles |
| Many-Worlds | No | Yes (all branches real) | No | Fails (all outcomes "true") |
| Collapse Models | No | No | Yes (stochastic) | Classical after collapse |
| **LRT** | **No** | **No** | **No** | **Ontic constraint** |

LRT is distinguished by treating L₃ as *constitutive* physical constraints rather than epistemic limits or emergent features.

---

## 7. Key Takeaways

1. **Bell tests are compatible with LRT** via Contextual Actuality—L₃ applies to actual outcomes, not counterfactuals

2. **Quantum gates are logical transformers** mapping input propositions to output probability distributions

3. **The Blueprint Principle** captures the quantum formalism as defining possibility space; each run samples one L₃-consistent history

4. **Error correction** can be understood as protecting logical constraints against decoherence

5. **No surplus ontology** is required: no hidden variables, no branching, no new dynamics

---

## 8. Integration Opportunities

| Content | Target Paper | Section |
|---------|--------------|---------|
| Contextual Actuality | MVS or Position Paper | Bell tests |
| Theorem 1 (Bell Compatibility) | Technical Foundations | New appendix |
| Gates as Logical Transformers | New paper: "LRT and Quantum Computing" | Core |
| Blueprint Principle | Position Paper | §2 clarification |
| Error Correction | New paper or QFT Statistics | Extension |

---

## References

- Pan, Jian-Wei et al. (2024). Tunable Einstein-Bohr recoiling-slit gedankenexperiment. *Physical Review Letters*.
- Bell, J.S. (1964). On the Einstein Podolsky Rosen paradox. *Physics*.
- Kochen, S. & Specker, E.P. (1967). The problem of hidden variables in quantum mechanics. *Journal of Mathematics and Mechanics*.
- Longmire, J.D. (2025). Logic Realism Theory papers. Zenodo.

---

*Extracted and organized from Perplexity research discussion, January 2026*
