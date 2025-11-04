# Complete Lean Proof Refactor Strategy

**Session**: 9.0
**Date**: 2025-11-04
**Goal**: Prove ALL theorems from 2 foundational axioms (I, I_infinite)
**Current Status**: 88 total axioms → Target: 2 axioms + proofs

---

## Absolute Foundation (2 Axioms - KEEP)

**Source**: `Foundation/IIS.lean`

```lean
axiom I : Type*                    -- Infinite Information Space exists
axiom I_infinite : Infinite I      -- I is infinite
```

**3FLL (0 axioms - ALREADY PROVEN)**:
- `theorem identity_law` - proven via `rfl`
- `theorem non_contradiction_law` - proven
- `theorem excluded_middle_law` - uses Classical.em

**A = L(I) (ALREADY PROVEN, 0 sorry)**:
- `theorem A_subset_I` ✓
- `theorem A_to_I_injective` ✓
- `theorem actualization_is_L_image` ✓
- `theorem actualized_satisfies_3FLL` ✓

---

## Proof Refactor Layers (Bottom-Up)

### Layer 1: Basic Constraint Structure (3 axioms → prove from foundation)

**Files**: `Foundation/ConstraintThreshold.lean`

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `Set.card` | Axiom (computational helper) | Use Mathlib `Set.ncard` or `Finset.card` | P1 |
| `ConstraintViolations` | Axiom (foundational) | Define from 3FLL constraint counting | P1 |
| `statespace_monotone` | Axiom | **PROVE from StateSpace definition** | P1 |

**statespace_monotone proof sketch**:
```lean
-- Theorem: K' ≤ K → StateSpace(K') ⊆ StateSpace(K)
theorem statespace_monotone {V : Type*} {K K' : ℕ} (h : K' ≤ K) :
    (StateSpace K' : Set V) ⊆ (StateSpace K : Set V) := by
  intro σ hσ
  unfold StateSpace at hσ ⊢
  -- hσ : ConstraintViolations σ ≤ K'
  -- goal: ConstraintViolations σ ≤ K
  exact Nat.le_trans hσ h
```

**Expected Reduction**: -1 axiom (statespace_monotone proven)

---

### Layer 2: Field Selection (7 axioms → K_math, keep as axioms)

**Files**: `Foundation/ComplexFieldForcing.lean`

| Axiom | Classification | Action |
|-------|---------------|---------|
| `real_no_continuous_phase` | K_math (algebraic property) | KEEP |
| `complex_continuous_phase` | K_math (U(1) structure) | KEEP |
| `quaternion_noncommutative` | K_math (algebraic) | KEEP |
| `complex_tensor_associative` | K_math | KEEP |
| `quaternion_tensor_order_dependent` | K_math | KEEP |
| `complex_time_reversal` | K_math | KEEP |
| `quaternion_time_ambiguous` | K_math | KEEP |

**Justification**: Standard algebraic properties of number fields. Could be proven from abstract algebra, but would require extensive formalization. Accept as K_math infrastructure.

**Expected Reduction**: 0 axioms (all K_math)

---

### Layer 3: Vector Space and Inner Product (5 axioms → prove 2, keep 3)

**Files**: `Foundation/VectorSpaceStructure.lean`, `Foundation/InnerProduct.lean`, `Foundation/PhysicsEnablingStructures.lean`

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `has_vector_space_structure` | Axiom | **PROVE**: Vector space emerges from I structure | P2 |
| `jordan_von_neumann` | K_math axiom (Track 1) | KEEP (K_math, von Neumann 1935) | - |
| `has_inner_product_structure` | Axiom | **PROVE**: Use jordan_von_neumann + parallelogram law | P2 |
| `is_hilbert_space` | Axiom | DERIVE: Completion of inner product space | P2 |
| `has_tensor_product_structure` | Axiom | DERIVE: Standard construction from vector spaces | P2 |

**Expected Reduction**: -4 axioms (prove from vector space + inner product structure)

---

### Layer 4: Operators and Symmetries (10 axioms → prove 6, keep 4 K_math)

**Files**: `Foundation/UnitaryOperators.lean`, `Foundation/HermitianOperators.lean`, `Dynamics/DynamicsFromSymmetry.lean`

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `stones_theorem` (3 copies) | K_math | KEEP 1, remove duplicates (-2) | P1 |
| `hermitian_real_spectrum` | K_math (spectral theorem) | KEEP | - |
| `mazur_ulam` | K_math | KEEP | - |
| `identity_forces_basis_independence` | Derivable from 3FLL Identity | **PROVE from Identity law** | P2 |
| `NC_forces_reversibility` | Derivable from 3FLL NC | **PROVE from Non-Contradiction** | P2 |
| `EM_forces_continuity` | Derivable from 3FLL EM | **PROVE from Excluded Middle** | P2 |
| `one_parameter_group_from_3FLL` | Derivable | **PROVE from 3FLL composition** | P2 |
| `has_unitary_evolution` | Derivable | **PROVE from Stone's + symmetries** | P3 |
| `observables_are_hermitian` | Physical postulate | **PROVE from measurement geometry** | P3 |

**Expected Reduction**: -6 axioms (prove symmetry properties, remove duplicates)

---

### Layer 5: Layer3 Placeholders (5 axioms → remove all)

**Files**: `Layer3.lean`

| Axiom | Action | Priority |
|-------|---------|----------|
| `track_1_9_inner_product` | REMOVE (reference actual Track1_9) | P1 |
| `track_1_10_hilbert_space` | REMOVE (reference actual Track1_10) | P1 |
| `track_1_11_tensor_products` | REMOVE (reference actual Track1_11) | P1 |
| `track_1_12_unitary_operators` | REMOVE (reference actual Track1_12) | P1 |
| `track_1_13_hermitian_operators` | REMOVE (reference actual Track1_13) | P1 |

**Expected Reduction**: -5 axioms (all placeholders removed)

---

### Layer 6: Qubit Mapping and Entropy (3 axioms → prove 1, keep 2)

**Files**: `Foundation/QubitKMapping.lean`

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `binary_entropy_bound` | K_math (information theory) | KEEP | - |
| `K_ground_justified` | LRT_foundational | **PROVE from entropy minimization** | P3 |

**Files**: `Derivations/Energy.lean`

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `I_has_maximum_entropy` | LRT_foundational | **PROVE from I_infinite + MaxEnt** | P3 |
| `actualization_strictly_reduces_entropy` | LRT_foundational | **PROVE from A ⊂ I + constraints** | P3 |
| `I_has_large_entropy` | Possibly redundant | Check if follows from I_has_maximum_entropy | P3 |
| `spohns_inequality` | K_math (Spohn 1978) | KEEP | - |
| `energy_additivity_for_independent_systems` | Physical postulate | KEEP (fundamental physics) | - |

**Expected Reduction**: -3 to -4 axioms (prove entropy properties)

---

### Layer 7: Time Emergence (6 axioms → prove 3, keep 3 K_math)

**Files**: `Derivations/TimeEmergence.lean`

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `trajectory_to_evolution` | Computational helper | **DEFINE as computable function** | P2 |
| `trajectory_to_evolution_identity_at_zero` | K_math | KEEP (group theory) | - |
| `trajectory_to_evolution_group_property` | K_math | KEEP (semigroup property) | - |
| `trajectory_to_evolution_continuous` | K_math | KEEP (required for Stone's) | - |
| `stones_theorem` | K_math (duplicate) | REMOVE (use Layer 4 version) | P1 |
| `time_emergence_from_identity` | LRT_foundational | **PROVE from Identity law + Stone's** | P3 |

**Expected Reduction**: -3 axioms (1 definition, 1 proof, 1 duplicate removal)

---

### Layer 8: Measurement Geometry (25 axioms → prove 15-18, keep 7-10)

**Files**: `Measurement/MeasurementGeometry.lean`, `Measurement/NonUnitaryEvolution.lean`

#### Born Rule Derivation (Target: prove from MaxEnt + 3FLL)

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `born_rule_normalized` | Measurement_dynamics | **PROVE from probability axioms** | P3 |
| `born_rule_from_measurement` | Measurement_dynamics | **PROVE from MaxEnt + NC** (Section 5.1) | P3 |
| `born_rule_is_geometric` | Measurement_dynamics | **PROVE from projection geometry** | P3 |

#### Measurement Properties

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `measurement_is_projection` | Measurement_dynamics | **PROVE from constraint geometry** | P3 |
| `measurement_is_hermitian` | Measurement_dynamics | **PROVE from observables** | P3 |
| `measurement_not_unitary` | Measurement_dynamics | **PROVE from dimension reduction** | P3 |
| `wavefunction_collapse_normalized` | Measurement_dynamics | **PROVE from probability** | P4 |
| `wavefunction_collapse_support` | Measurement_dynamics | **PROVE from projection** | P4 |

#### State Space and Collapse

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `measurement_reduces_statespace` | Measurement_dynamics | **PROVE from K reduction** | P4 |
| `statespace_cardinality_decreases` | Measurement_dynamics | **PROVE from monotonicity** | P4 |
| `measurement_reduces_K` | Measurement_dynamics | **PROVE from constraint addition** | P3 |
| `observer_adds_constraints` | LRT_foundational | **PROVE from observer definition** | P3 |
| `measurement_reduces_dimension` | Measurement_dynamics | **PROVE from collapse** | P4 |
| `unitary_preserves_dimension` | K_math | KEEP (standard linear algebra) | - |
| `unitary_preserves_norm` | K_math | KEEP (standard) | - |

#### Identity State and K=0

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `IdentityState` | Computational helper | **DEFINE as explicit construction** | P3 |
| `identity_state_zero_violations` | LRT_foundational | **PROVE from Identity law** | P3 |
| `k_zero_unique_state` | LRT_foundational | **PROVE from K=0 definition** | P3 |
| `classical_emerges_at_K_zero` | LRT_foundational | **PROVE from K=0 uniqueness** | P3 |

#### Decoherence and Pointer States

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `pointer_states_are_constraint_eigenstates` | Measurement_dynamics | **PROVE from decoherence** | P4 |
| `observer_measurement` | Measurement_dynamics | **PROVE from observer constraint** | P4 |

#### Hilbert Space from Constraints

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `hilbert_space_from_constraints` | LRT_foundational | **PROVE from StateSpace + inner product** | P3 |
| `observables_from_constraint_operators` | LRT_foundational | **PROVE from constraint structure** | P3 |

#### Determinism and Completeness

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `collapse_is_deterministic` | Measurement_dynamics | **PROVE from constraint satisfaction** | P4 |
| `measurement_mechanism_complete` | Measurement_dynamics | **PROVE from coverage** | P4 |
| `measurement_yields_classical` | Measurement_dynamics | **PROVE from K → 0** | P4 |
| `no_unitarity_contradiction` | Measurement_dynamics | **PROVE by construction** | P4 |
| `evolution_types_distinct` | Measurement_dynamics | **PROVE by construction** | P4 |

**Expected Reduction**: -15 to -18 axioms (major Born rule + measurement proofs)

---

### Layer 9: Non-Circular Born Rule (4 axioms → keep as K_math or prove)

**Files**: `Measurement/NonCircularBornRule.lean`

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `frame_function_from_3FLL` | Derivable | **PROVE from 3FLL composition** | P4 |
| `gleason_theorem` | K_math (Gleason 1957) | KEEP | - |
| `von_neumann_entropy` | K_math (standard) | KEEP or import from Mathlib | - |
| `pure_iff_zero_entropy` | K_math (standard) | KEEP or import | - |

**Expected Reduction**: -1 axiom (frame function proven)

---

### Layer 10: Other Structures (EMRelaxation, Distinguishability, etc.)

**Files**: Various foundation files

| Axiom | Current Status | Proof Strategy | Priority |
|-------|---------------|----------------|----------|
| `continuous_parameterization_exists` (EMRelaxation) | Technical | Review necessity | P4 |
| `complex_field_selection` (PhysicsEnablingStructures) | Duplicate? | Check overlap with ComplexFieldForcing | P2 |

---

## Summary of Expected Reductions

| Layer | Current Axioms | Target Axioms | Reduction | Method |
|-------|---------------|---------------|-----------|---------|
| **Foundation** | 2 | 2 | 0 | KEEP (I, I_infinite) |
| **Layer 1: Constraints** | 3 | 2 | -1 | Prove statespace_monotone |
| **Layer 2: Fields** | 7 | 7 | 0 | KEEP (K_math) |
| **Layer 3: Vector/Inner Product** | 5 | 1 | -4 | Prove from structure |
| **Layer 4: Operators** | 10 | 4 | -6 | Prove symmetries, remove duplicates |
| **Layer 5: Placeholders** | 5 | 0 | -5 | Remove all |
| **Layer 6: Entropy** | 5 | 2 | -3 | Prove from MaxEnt |
| **Layer 7: Time** | 6 | 3 | -3 | Prove emergence, remove duplicate |
| **Layer 8: Measurement** | 25 | 7-10 | -15 to -18 | Born rule + proofs |
| **Layer 9: Gleason** | 4 | 3 | -1 | Prove frame function |
| **Layer 10: Other** | 2+ | 1+ | -1+ | Review and consolidate |
| **TOTAL** | **88** | **30-35** | **-53 to -58** | **Comprehensive proof program** |

---

## Execution Strategy

### Phase 1: Foundation and Quick Wins (Estimated: 4-6 hours)
1. **Prove statespace_monotone** (30 min) ← START HERE
2. **Remove Layer3 placeholders** (1 hour)
3. **Remove duplicate stones_theorem** (30 min)
4. **Convert computational helpers to definitions** (2 hours)
5. **Verify build** (30 min)

**Target**: -8 axioms (88 → 80)

### Phase 2: Symmetries and Structures (Estimated: 6-8 hours)
6. **Prove 3FLL symmetry properties** (3 hours)
   - identity_forces_basis_independence
   - NC_forces_reversibility
   - EM_forces_continuity
7. **Prove vector space emergence** (2 hours)
8. **Prove inner product and Hilbert space** (2 hours)
9. **Prove tensor products** (1 hour)
10. **Verify build** (30 min)

**Target**: -10 axioms (80 → 70)

### Phase 3: Time and Energy Emergence (Estimated: 6-8 hours)
11. **Prove entropy properties from I_infinite** (3 hours)
    - I_has_maximum_entropy
    - actualization_strictly_reduces_entropy
12. **Prove time_emergence_from_identity** (3 hours)
13. **Prove K_ground_justified** (1 hour)
14. **Verify build** (30 min)

**Target**: -5 to -6 axioms (70 → 64-65)

### Phase 4: Born Rule and Measurement (Estimated: 12-16 hours) ← MAJOR WORK
15. **Implement Born rule derivation from MaxEnt** (6 hours)
    - born_rule_from_measurement (Section 5.1)
    - born_rule_normalized
    - born_rule_is_geometric
16. **Prove measurement properties** (4 hours)
    - measurement_is_projection
    - measurement_is_hermitian
    - measurement_not_unitary
17. **Prove collapse mechanism** (3 hours)
    - wavefunction_collapse_*
    - measurement_reduces_K
    - measurement_reduces_statespace
18. **Prove K=0 classical emergence** (2 hours)
19. **Verify build** (1 hour)

**Target**: -15 to -18 axioms (64-65 → 46-50)

### Phase 5: Advanced Measurement and Cleanup (Estimated: 6-8 hours)
20. **Prove decoherence and pointer states** (3 hours)
21. **Prove Hilbert space from constraints** (2 hours)
22. **Prove frame_function_from_3FLL** (1 hour)
23. **Final cleanup and consolidation** (2 hours)
24. **Final build verification** (1 hour)

**Target**: -5 to -8 axioms (46-50 → 30-35)

---

## Total Estimated Time: 34-46 hours

**Final Target**: 30-35 axioms total (2 foundation + 28-33 K_math/infrastructure)

**True LRT axioms**: 2 (I, I_infinite)
**K_math infrastructure**: ~16 (Stone's, spectral, Spohn's, Gleason, field properties)
**Physical postulates**: 1 (energy additivity)
**Remaining technical**: ~11-16 (may be reducible further with more work)

---

## Success Criteria

**Minimum Success** (30-35 axioms):
- All placeholders removed
- All provable symmetries proven
- Born rule derived from MaxEnt
- Time emergence proven from Identity
- Build success with 0 errors

**Stretch Success** (20-25 axioms):
- Advanced measurement properties proven
- Hilbert space fully derived from constraints
- All LRT-specific claims proven from 2 axioms
- Only K_math infrastructure remains

**Transformative Success** (15-20 axioms):
- Some K_math results proven from first principles
- Complete formal verification of all LRT claims
- Publication-ready formalization

---

**Status**: Ready to begin Phase 1, Step 1 (prove statespace_monotone)
**Next**: Execute first proof and verify build
