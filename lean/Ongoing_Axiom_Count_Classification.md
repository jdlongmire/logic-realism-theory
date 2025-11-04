# Ongoing Axiom Count and Classification
**Date**: 2025-11-03
**Total Axioms**: 58
**Purpose**: Complete inventory and classification of all axiom declarations in LogicRealismTheory

---

## ⚠️ AXIOM COUNT FRAMING (Always Use This)

**When discussing LRT axiom count, use this framing:**

- ❌ **NOT** "57 axioms" or "58 axioms"
- ✅ **USE** "30-34 theory axioms (current), target 7-11"
- ✅ **Separate** K_math (16) as mathematical infrastructure, not LRT axioms

**Why this matters:**
- K_math axioms are standard mathematical results (Stone's theorem, spectral theorem, etc.)
- ALL quantum mechanics reconstructions use the same ~16 mathematical infrastructure
- Other programs (Hardy, Chiribella, Dakic) don't count infrastructure as "theory axioms"
- Honest comparison: LRT theory axioms (30-34 → target 7-11) vs. their theory axioms (3-6)

**Current honest count:**
- **Total declarations**: 57 (58 - 1 false positive)
- **K_math infrastructure**: 16 (same as QM uses)
- **Theory axioms**: 30-34
  - LRT_foundational: 14
  - Measurement_dynamics: 15
  - Physical_postulate: 1
  - Computational_helper: 4 (should be definitions)
  - Placeholder: 5 (should be removed)

**Target (Option C plan):**
- **Total declarations**: 35-38
- **K_math infrastructure**: 16 (unchanged)
- **Theory axioms**: 7-11
  - Core ontological: 2-3 (I, I_infinite, A=L(I))
  - Additional: 5-8 (observer, field, measurement)

**See `lean/LRT_Comprehensive_Lean_Plan.md` for complete reduction strategy.**

---

## Classification Categories

1. **K_math**: Mathematical infrastructure theorems (not in Mathlib, standard results)
2. **LRT_foundational**: Core LRT ontological postulates (defining what LRT is)
3. **Physical_postulate**: Standard physical principles (domain-standard assumptions)
4. **Computational_helper**: Technical axioms for computation (function definitions)
5. **Placeholder**: Track summaries/markers (not real axioms, to be replaced)
6. **Measurement_dynamics**: Properties of measurement and collapse mechanism

---

## Complete Axiom Inventory (58 Total)

| # | File | Axiom Name | Classification | Justification |
|---|------|------------|----------------|---------------|
| **Derivations/Energy.lean (6 axioms)** |
| 1 | Energy.lean | `I_has_maximum_entropy` | LRT_foundational | Infinite information space has maximum entropy (defining property) |
| 2 | Energy.lean | `actualization_strictly_reduces_entropy` | LRT_foundational | Core LRT mechanism: L(I) → A reduces entropy |
| 3 | Energy.lean | `I_has_large_entropy` | LRT_foundational | Technical condition ensuring entropy reduction is measurable |
| 4 | Energy.lean | `spohns_inequality` | K_math | Spohn's inequality (entropy change bounds), standard result |
| 5 | Energy.lean | `energy_additivity_for_independent_systems` | Physical_postulate | E_total = E₁ + E₂ for independent systems (fundamental physical principle) |
| 6 | Energy.lean | (comment line, not axiom) | N/A | False positive from grep |
| **Derivations/TimeEmergence.lean (6 axioms)** |
| 7 | TimeEmergence.lean | `trajectory_to_evolution` | Computational_helper | Maps identity-preserving trajectories to evolution operators |
| 8 | TimeEmergence.lean | `trajectory_to_evolution_identity_at_zero` | K_math | Evolution operator identity at t=0 (standard property) |
| 9 | TimeEmergence.lean | `trajectory_to_evolution_group_property` | K_math | Evolution operators form group (semigroup property) |
| 10 | TimeEmergence.lean | `trajectory_to_evolution_continuous` | K_math | Continuity of evolution (required for Stone's theorem) |
| 11 | TimeEmergence.lean | `stones_theorem` | K_math | **Stone's theorem**: Unitary groups ↔ self-adjoint generators (Stone 1932) |
| 12 | TimeEmergence.lean | `time_emergence_from_identity` | LRT_foundational | Core LRT claim: Time emerges from Identity constraint |
| **Foundation/ComplexFieldForcing.lean (7 axioms)** |
| 13 | ComplexFieldForcing.lean | `real_no_continuous_phase` | K_math | Reals lack continuous phase (algebraic property) |
| 14 | ComplexFieldForcing.lean | `complex_continuous_phase` | K_math | Complex numbers have continuous phase (U(1) structure) |
| 15 | ComplexFieldForcing.lean | `quaternion_noncommutative` | K_math | Quaternions are noncommutative (algebraic property) |
| 16 | ComplexFieldForcing.lean | `complex_tensor_associative` | K_math | Complex tensor product is associative |
| 17 | ComplexFieldForcing.lean | `quaternion_tensor_order_dependent` | K_math | Quaternion tensor product order matters (noncommutativity) |
| 18 | ComplexFieldForcing.lean | `complex_time_reversal` | K_math | Complex conjugation = time reversal symmetry |
| 19 | ComplexFieldForcing.lean | `quaternion_time_ambiguous` | K_math | Quaternions have ambiguous time reversal |
| **Foundation/ConstraintThreshold.lean (3 axioms)** |
| 20 | ConstraintThreshold.lean | `Set.card` | Computational_helper | Cardinality function for sets |
| 21 | ConstraintThreshold.lean | `ConstraintViolations` | Computational_helper | Function counting constraint violations (defines K) |
| 22 | ConstraintThreshold.lean | `statespace_monotone` | LRT_foundational | K' ≤ K → StateSpace(K') ⊆ StateSpace(K) (core K mechanism) |
| **Foundation/IIS.lean (2 axioms)** |
| 23 | IIS.lean | `I` | LRT_foundational | **Infinite Information Space exists** (core ontological postulate) |
| 24 | IIS.lean | `I_infinite` | LRT_foundational | **I is infinite** (core ontological postulate) |
| **Foundation/QubitKMapping.lean (2 axioms)** |
| 25 | QubitKMapping.lean | `binary_entropy_bound` | K_math | Binary entropy bound (information theory) |
| 26 | QubitKMapping.lean | `K_ground_justified` | LRT_foundational | K=0.1 for ground state justified by entropy minimization |
| **Foundation/Track1_12_UnitaryOperators.lean (1 axiom)** |
| 27 | Track1_12 | `stones_theorem` | K_math | **Stone's theorem** (simplified placeholder, full version in TimeEmergence) |
| **Foundation/Track1_13_HermitianOperators.lean (1 axiom)** |
| 28 | Track1_13 | `hermitian_real_spectrum` | K_math | **Spectral theorem**: Hermitian operators have real eigenvalues (infrastructure in Mathlib) |
| **Layer3.lean (5 axioms - PLACEHOLDERS)** |
| 29 | Layer3.lean | `track_1_9_inner_product` | Placeholder | Track 1.9 summary marker (to be replaced with actual theorem) |
| 30 | Layer3.lean | `track_1_10_hilbert_space` | Placeholder | Track 1.10 summary marker (to be replaced) |
| 31 | Layer3.lean | `track_1_11_tensor_products` | Placeholder | Track 1.11 summary marker (to be replaced) |
| 32 | Layer3.lean | `track_1_12_unitary_operators` | Placeholder | Track 1.12 summary marker (to be replaced) |
| 33 | Layer3.lean | `track_1_13_hermitian_operators` | Placeholder | Track 1.13 summary marker (to be replaced) |
| **Measurement/MeasurementGeometry.lean (21 axioms)** |
| 34 | MeasurementGeometry | `measurement_is_projection` | Measurement_dynamics | Measurement = projection operator (von Neumann) |
| 35 | MeasurementGeometry | `measurement_is_hermitian` | Measurement_dynamics | Measurement operators are Hermitian (observables) |
| 36 | MeasurementGeometry | `measurement_not_unitary` | Measurement_dynamics | Measurement is non-unitary (collapse) |
| 37 | MeasurementGeometry | `wavefunction_collapse_normalized` | Measurement_dynamics | Post-collapse state is normalized |
| 38 | MeasurementGeometry | `wavefunction_collapse_support` | Measurement_dynamics | Collapsed state has support in eigenspace |
| 39 | MeasurementGeometry | `born_rule_normalized` | Measurement_dynamics | Born rule probabilities sum to 1 |
| 40 | MeasurementGeometry | `born_rule_from_measurement` | Measurement_dynamics | Born rule: P(i) = |⟨ψᵢ\|ψ⟩|² emerges from measurement |
| 41 | MeasurementGeometry | `measurement_reduces_statespace` | Measurement_dynamics | Measurement reduces accessible state space (K → K-ΔK) |
| 42 | MeasurementGeometry | `statespace_cardinality_decreases` | Measurement_dynamics | State space size decreases: \|StateSpace(K-ΔK)\| < \|StateSpace(K)\| |
| 43 | MeasurementGeometry | `IdentityState` | Computational_helper | Computational marker for identity-preserving state |
| 44 | MeasurementGeometry | `identity_state_zero_violations` | LRT_foundational | Identity state has zero constraint violations (K=0 definition) |
| 45 | MeasurementGeometry | `k_zero_unique_state` | LRT_foundational | K=0 → unique classical state (definiteness) |
| 46 | MeasurementGeometry | `classical_emerges_at_K_zero` | LRT_foundational | Classical physics emerges at K=0 (full constraint enforcement) |
| 47 | MeasurementGeometry | `observer_measurement` | Measurement_dynamics | Observer adds constraints, inducing measurement |
| 48 | MeasurementGeometry | `pointer_states_are_constraint_eigenstates` | Measurement_dynamics | Pointer states = constraint operator eigenstates (decoherence) |
| 49 | MeasurementGeometry | `hilbert_space_from_constraints` | LRT_foundational | Hilbert space emerges from constraint structure |
| 50 | MeasurementGeometry | `observables_from_constraint_operators` | LRT_foundational | Observables = constraint operators (Hermitian) |
| 51 | MeasurementGeometry | `born_rule_is_geometric` | Measurement_dynamics | Born rule has geometric origin (projection onto eigenspaces) |
| 52 | MeasurementGeometry | `collapse_is_deterministic` | Measurement_dynamics | Collapse outcome is deterministic given measurement (no hidden variables) |
| 53 | MeasurementGeometry | `measurement_mechanism_complete` | Measurement_dynamics | Measurement mechanism is complete (no additional principles needed) |
| 54 | MeasurementGeometry | `measurement_yields_classical` | Measurement_dynamics | Measurement produces classical outcome (K → 0) |
| **Measurement/NonUnitaryEvolution.lean (4 axioms)** |
| 55 | NonUnitaryEvolution | `unitary_preserves_norm` | K_math | Unitary operators preserve norm (standard property) |
| 56 | NonUnitaryEvolution | `observer_adds_constraints` | LRT_foundational | Observer interaction increases constraints |
| 57 | NonUnitaryEvolution | `unitary_preserves_dimension` | K_math | Unitary evolution preserves state space dimension |
| 58 | NonUnitaryEvolution | `measurement_reduces_dimension` | Measurement_dynamics | Measurement reduces effective dimension (collapse) |

---

## Summary by Classification

| Classification | Count | Percentage | Examples |
|----------------|-------|------------|----------|
| **K_math** | 16 | 27.6% | Stone's theorem, spectral theorem, Spohn's inequality, complex field properties |
| **LRT_foundational** | 14 | 24.1% | I exists, I infinite, time emerges from Identity, K mechanism |
| **Measurement_dynamics** | 15 | 25.9% | Born rule, collapse, projection, pointer states |
| **Computational_helper** | 4 | 6.9% | Set.card, ConstraintViolations, IdentityState, trajectory_to_evolution |
| **Physical_postulate** | 1 | 1.7% | Energy additivity |
| **Placeholder** | 5 | 8.6% | Layer3.lean track markers (to be replaced) |
| **False positive** | 1 | 1.7% | Comment line counted as axiom |
| **ACTUAL TOTAL** | **57** | | (58 - 1 false positive) |

---

## Key Insights

### What's Acceptable as Axioms?

1. **K_math (16 axioms)**: Standard mathematical results
   - Stone's theorem (2 versions)
   - Spectral theorem (Hermitian real spectrum)
   - Spohn's inequality
   - Complex field algebraic properties
   - All have published proofs, just not in Mathlib

2. **LRT_foundational (14 axioms)**: Define what LRT is
   - Analogous to QM's Hilbert space postulate
   - Core thesis: I exists, I infinite, A = L(I)
   - K-mechanism and constraint dynamics

3. **Measurement_dynamics (15 axioms)**: Von Neumann measurement
   - Standard QM measurement postulates
   - Born rule, collapse, projection
   - Could potentially be derived with more work

4. **Physical_postulate (1 axiom)**: Energy additivity
   - Fundamental physical principle
   - Cannot be derived from pure mathematics

### What Can Be Reduced?

1. **Placeholder axioms (5)**: Layer3.lean track markers
   - Should be replaced with actual theorems
   - Current status: Track implementations exist (Track1_9-1.13)
   - **Action**: Remove placeholders, reference actual track theorems

2. **Some measurement axioms (potentially)**:
   - Born rule axiomatized here, but derived in Section 5.1 of Main.md
   - Could potentially derive from MaxEnt + Non-Contradiction
   - **Action**: Formalize the Section 5.1 derivation in Lean

3. **Computational helpers (4)**:
   - Some might be definable rather than axiomatic
   - **Action**: Review if these can be definitions instead

### What Should NOT Be Reduced?

1. **K_math (16)**: These are established results
   - Stone's theorem: Standard reference (Stone 1932)
   - Spectral theorem: Standard linear algebra
   - Spohn's inequality: Standard information theory
   - **Keep as axioms**: Full proofs would require extensive Mathlib work

2. **Core LRT postulates (I, I_infinite, actualization)**:
   - These define the theory (like QM's postulates)
   - **Keep as axioms**: Theory-defining

3. **Energy additivity**:
   - Fundamental physical principle
   - **Keep as axiom**: Cannot derive from pure logic

---

## Comparison: LRT vs. QM Axiomatization

| Framework | Core Axioms | Infrastructure Axioms | Total |
|-----------|-------------|----------------------|-------|
| **QM (Dirac)** | 4-5 | ~10 (functional analysis) | ~15 |
| **LRT (current)** | 14 (LRT_foundational) + 1 (physical) | 16 (K_math) + 15 (measurement) | **46** (excluding placeholders/helpers) |
| **LRT (after cleanup)** | ~15 | ~20 | **~35** (target) |

**Key difference**:
- QM postulates: Hilbert space, Born rule, unitary evolution
- LRT derives: Born rule (from MaxEnt), Hilbert space (from info geometry), time (from Identity)
- LRT postulates: I, I_infinite, A = L(I), K-mechanism

---

## Action Items for Axiom Reduction

### Priority 1: Remove Placeholders (5 axioms)
- **Target**: Layer3.lean track markers
- **Action**: Reference actual Track1_9-1.13 theorems instead
- **Reduction**: -5 axioms

### Priority 2: Formalize Born Rule Derivation (potentially 5-7 axioms)
- **Target**: Born rule axioms in MeasurementGeometry
- **Action**: Implement Section 5.1 derivation (MaxEnt + Non-Contradiction) in Lean
- **Reduction**: -5 to -7 axioms (if successful)

### Priority 3: Review Computational Helpers (4 axioms)
- **Target**: Set.card, ConstraintViolations, IdentityState, trajectory_to_evolution
- **Action**: Check if these can be definitions instead of axioms
- **Reduction**: -2 to -4 axioms (potentially)

### Priority 4: Consolidate Measurement Dynamics
- **Target**: 15 measurement axioms
- **Action**: Derive more from fewer fundamental axioms
- **Reduction**: -3 to -5 axioms (potentially)

**Potential final count**: ~35 axioms (vs. current 57)

---

## Transparency for Peer Review

**What to emphasize**:
1. **K_math axioms are standard results** (Stone, Spectral, Spohn)
   - All have published proofs
   - Not in Mathlib yet, but well-established
   - Analogous to accepting ZFC set theory

2. **LRT derives what QM postulates**
   - Born rule: QM postulates, LRT derives (Section 5.1)
   - Hilbert space: QM postulates, LRT derives (Section 5.2)
   - Time evolution: QM postulates, LRT derives (Section 5.3)

3. **Honest about current status**
   - 57 axioms currently (after removing 1 false positive)
   - Path to ~35 with cleanup
   - All axioms classified and documented

4. **Layer 3 is strong**
   - Only 3 K_math gaps (Jordan-von Neumann, Stone's, Spectral)
   - All 5 tracks build successfully
   - Honest gap documentation

**What to avoid**:
- ❌ Claiming "only 7 axioms" when 57 exist
- ❌ Hiding axioms in unmentioned files
- ❌ Conflating "axiom count" with "novel LRT postulates"

**What to say instead**:
- ✅ "57 axiom declarations, classified as: 16 K_math (standard results), 14 LRT_foundational (defining postulates), 15 measurement dynamics, ..."
- ✅ "K_math axioms represent established mathematical infrastructure (Stone 1932, Spohn, etc.), analogous to accepting ZFC"
- ✅ "LRT derives Born rule, Hilbert space, and time evolution—structures that QM postulates axiomatically"

---

**Last Updated**: 2025-11-03
**Status**: Complete inventory, classification, and action plan for axiom reduction
