# S8: Lean 4 Formalization Strategy for Step 3 (Local Tomography)

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Type:** Formalization Specification (no Lean code; strategy only)
**Addresses:** H1 to H2 bridge formalization; Step 3 proof obligations

---

## Abstract

This supplement develops the formalization strategy for Step 3 (local tomography) in Lean 4. Step 3 bridges metaphysical supervenience (H1) to operational local tomography (H2) via the Physical Proposition Criterion (PPC). The strategy identifies required type signatures, Mathlib dependencies, proof obligations, and staging. The target is a machine-verifiable proof that H1 + PPC entails H2 within LRT's type-theoretic framework. This document is a specification; actual Lean code follows in a separate implementation phase.

---

## 1. The Formalization Target

### 1.1 What Must Be Proven

**Main Theorem (Step 3):** In LRT, metaphysical supervenience (H1) entails operational local tomography (H2).

**Formal Statement (target):**
```
theorem step3_local_tomography :
  H1_metaphysical_supervenience S → H2_local_tomography S
```

where `S` is a composite system type satisfying LRT's base constraints.

### 1.2 Dependency Chain

The proof requires formalizing:
1. **L<sub>3</sub> constitutive status** (already in `D0_1_ThreeFundamentalLaws.lean`)
2. **I<sub>∞</sub> distinguishability structure** (already in `D0_2_InformationSpace.lean`)
3. **Physical Proposition Criterion (PPC)** (new: from S1)
4. **Metaphysical Supervenience (H1)** (new: from S2)
5. **Operational Local Tomography (H2)** (new: from S2)
6. **H1 + PPC → H2 bridge** (new: the main theorem)

### 1.3 Epistemic Status of Components

| Component | Source | Current Status | Target Status |
|-----------|--------|----------------|---------------|
| L<sub>3</sub> | D0_1 | ESTABLISHED (Lean) | — |
| I<sub>∞</sub> + Infinite | D0_2 | ESTABLISHED (Lean) | — |
| Distinguishability metric D | S1 | ARGUED (prose) | ESTABLISHED (Lean) |
| PPC | S1 | ARGUED (prose) | ESTABLISHED (Lean) |
| H1 | S2 | ESTABLISHED (Lean-ready) | ESTABLISHED (Lean) |
| H2 | S2 | ARGUED (prose) | ESTABLISHED (Lean) |
| H1 → H2 | S2 | ARGUED (prose) | ESTABLISHED (Lean) |

---

## 2. Type Signatures (Specification)

### 2.1 Core Types

```lean
/-- A composite system with subsystems A and B -/
structure CompositeSystem (A B : Type*) where
  joint_state : Type*
  subsystem_A : A
  subsystem_B : B
  relations : Set (A × B → Prop)
```

```lean
/-- State space with distinguishability metric -/
structure DistinguishableSpace where
  Carrier : Type*
  D : Carrier → Carrier → ℝ≥0  -- distinguishability metric
  D_zero_iff_eq : ∀ s₁ s₂, D s₁ s₂ = 0 ↔ s₁ = s₂
  D_symm : ∀ s₁ s₂, D s₁ s₂ = D s₂ s₁
  D_triangle : ∀ s₁ s₂ s₃, D s₁ s₃ ≤ D s₁ s₂ + D s₂ s₃
```

```lean
/-- A physical proposition (satisfies L₃ via PPC) -/
structure PhysicalProposition (S : DistinguishableSpace) where
  P : S.Carrier → Prop
  P_true_state : S.Carrier
  P_false_state : S.Carrier
  operationally_distinguishable : S.D P_true_state P_false_state > 0
```

### 2.2 Measurement Structures

```lean
/-- A measurement on a state space -/
structure Measurement (S : DistinguishableSpace) where
  outcomes : Type*
  outcome_finite : Finite outcomes  -- or at least decidable
  prob : S.Carrier → outcomes → ℝ≥0
  prob_sum_one : ∀ s, ∑ o, prob s o = 1
```

```lean
/-- Local measurements on a composite system -/
structure LocalMeasurements (A B : DistinguishableSpace) where
  meas_A : Set (Measurement A)
  meas_B : Set (Measurement B)
  meas_A_nonempty : meas_A.Nonempty
  meas_B_nonempty : meas_B.Nonempty
```

```lean
/-- Joint measurement statistics from local measurements -/
def joint_statistics
    (A B : DistinguishableSpace)
    (joint : A.Carrier × B.Carrier)
    (M_A : Measurement A)
    (M_B : Measurement B) :
    M_A.outcomes × M_B.outcomes → ℝ≥0 :=
  fun (oA, oB) => M_A.prob joint.1 oA * M_B.prob joint.2 oB
  -- Note: This factorization is provisional; entanglement requires careful treatment
```

### 2.3 H1 and H2 Definitions

```lean
/-- H1: Metaphysical Supervenience -/
def H1_metaphysical_supervenience
    (A B : DistinguishableSpace)
    (S : CompositeSystem A.Carrier B.Carrier) : Prop :=
  ∀ s₁ s₂ : S.joint_state,
    (∀ R ∈ S.relations, R (S.subsystem_A, S.subsystem_B)) →
    -- Composite state supervenes on subsystem states + relations
    True  -- Placeholder for full supervenience condition
```

```lean
/-- H2: Operational Local Tomography -/
def H2_local_tomography
    (A B : DistinguishableSpace)
    (S : CompositeSystem A.Carrier B.Carrier) : Prop :=
  ∀ s₁ s₂ : S.joint_state,
    (∀ (M_A : Measurement A) (M_B : Measurement B),
      joint_statistics A B (A_state_of s₁, B_state_of s₁) M_A M_B =
      joint_statistics A B (A_state_of s₂, B_state_of s₂) M_A M_B) →
    s₁ = s₂
  -- Distinct joint states yield distinct local measurement statistics
```

### 2.4 Physical Proposition Criterion

```lean
/-- PPC: Operational Determinacy -/
def PPC (S : DistinguishableSpace) (P : S.Carrier → Prop) : Prop :=
  ∃ s_true s_false : S.Carrier,
    P s_true ∧ ¬P s_false ∧ S.D s_true s_false > 0
```

```lean
/-- A relation is physically real iff it satisfies PPC -/
def physically_real_relation
    (A B : DistinguishableSpace)
    (R : A.Carrier × B.Carrier → Prop) : Prop :=
  ∃ joint : DistinguishableSpace,  -- composite space
    PPC joint (fun s => R (project_A s, project_B s))
```

---

## 3. Mathlib Dependencies

### 3.1 Required Imports

```lean
import Mathlib.Topology.MetricSpace.Basic        -- Metric space foundations
import Mathlib.Analysis.InnerProductSpace.Basic  -- Hilbert space (for Step 4 link)
import Mathlib.LinearAlgebra.TensorProduct.Basic -- Composite systems
import Mathlib.MeasureTheory.Measure.MeasureSpace -- Probability measures
import Mathlib.Data.Real.NNReal                  -- Non-negative reals
import Mathlib.Logic.Basic                       -- Classical logic
```

### 3.2 Mathlib Structures to Use

| LRT Concept | Mathlib Structure | Notes |
|-------------|-------------------|-------|
| Distinguishability metric D | `MetricSpace` or custom `DistinguishableSpace` | D satisfies metric axioms |
| Probability distributions | `MeasureTheory.ProbabilityMeasure` | For measurement statistics |
| Tensor products | `TensorProduct` | Composite system states |
| Projections | `LinearMap.proj` | Subsystem extraction |
| Finite sums | `Finset.sum` | Probability normalization |

### 3.3 Gap Analysis

**Available in Mathlib:**
- Classical logic (L<sub>3</sub> in `D0_1`)
- Metric spaces and topology
- Tensor products over ℂ
- Measure theory foundations

**Must Define for LRT:**
- `DistinguishableSpace` (custom; wraps metric with LRT interpretation)
- `PhysicalProposition` (new; embeds PPC)
- `H1_metaphysical_supervenience` (new; supervenience predicate)
- `H2_local_tomography` (new; tomographic completeness)
- Operational accessibility (relation between D > 0 and local measurement)

**External Theorems Required:**
- None for H1 → H2 bridge itself (pure logic given definitions)
- Masanes-Müller (E1) only enters at Step 4, not Step 3

---

## 4. Proof Obligations

### 4.1 Main Theorem

**Target:**
```lean
theorem step3_H1_implies_H2
    (A B : DistinguishableSpace)
    (S : CompositeSystem A.Carrier B.Carrier)
    (h_supervenience : H1_metaphysical_supervenience A B S)
    (h_ppc : ∀ R ∈ S.relations, physically_real_relation A B R) :
    H2_local_tomography A B S
```

**Proof sketch (formalization target):**

1. Assume `s₁ ≠ s₂` (contrapositive approach)
2. By H1, some subsystem state or relation differs
3. Case: subsystem state differs → local measurement distinguishes (by D > 0 for subsystems)
4. Case: relation R differs → by `h_ppc`, R satisfies PPC → operationally distinguishable → expressible via local measurements (key lemma)
5. Either way, local statistics differ → H2 holds

### 4.2 Supporting Lemmas

**Lemma 4.2.1 (Relation Accessibility):**
```lean
lemma relation_locally_accessible
    (A B : DistinguishableSpace)
    (R : A.Carrier × B.Carrier → Prop)
    (h_physical : physically_real_relation A B R) :
    ∃ (M_A : Measurement A) (M_B : Measurement B),
      -- R-true and R-false yield different joint statistics
      True  -- Placeholder
```

*Proof obligation:* Show that PPC for R (distinguishability of R-states) entails local measurement distinction. This is the critical step.

**Lemma 4.2.2 (Supervenience Decomposition):**
```lean
lemma supervenience_decomposition
    (A B : DistinguishableSpace)
    (S : CompositeSystem A.Carrier B.Carrier)
    (s₁ s₂ : S.joint_state)
    (h_supervenience : H1_metaphysical_supervenience A B S)
    (h_ne : s₁ ≠ s₂) :
    (A_state_of s₁ ≠ A_state_of s₂) ∨
    (B_state_of s₁ ≠ B_state_of s₂) ∨
    (∃ R ∈ S.relations, R differs between s₁ and s₂)
```

*Proof obligation:* Unpack H1 to show that composite difference implies component or relational difference.

**Lemma 4.2.3 (Subsystem Distinguishability):**
```lean
lemma subsystem_distinguishable_implies_local_stat_diff
    (A : DistinguishableSpace)
    (a₁ a₂ : A.Carrier)
    (h_ne : a₁ ≠ a₂) :
    ∃ M : Measurement A, M.prob a₁ ≠ M.prob a₂
```

*Proof obligation:* D > 0 implies some measurement distinguishes. This follows from D's definition via measurements.

### 4.3 Dependency Graph

```
D0_1 (L₃)
    ↓
D0_2 (I∞, Infinite)
    ↓
DistinguishableSpace (new, uses D from S1)
    ↓
PhysicalProposition + PPC (new, from S1)
    ↓
H1_metaphysical_supervenience (new, from S2)
    ↓
physically_real_relation (new)
    ↓
Lemma: relation_locally_accessible (critical)
    ↓
Lemma: supervenience_decomposition
    ↓
Lemma: subsystem_distinguishable_implies_local_stat_diff
    ↓
step3_H1_implies_H2 (main theorem)
    ↓
H2_local_tomography
```

---

## 5. Staging Plan

### 5.1 Phase 1: Foundation Extensions

**Files to create:**
- `LogicRealismTheory/Structures/DistinguishableSpace.lean`
- `LogicRealismTheory/Structures/PhysicalProposition.lean`

**Content:**
- `DistinguishableSpace` structure with D metric
- `PhysicalProposition` with operational distinguishability condition
- PPC predicate
- Basic lemmas about distinguishability

**Estimated effort:** 1-2 days

### 5.2 Phase 2: Composite System Structures

**Files to create:**
- `LogicRealismTheory/Structures/CompositeSystem.lean`
- `LogicRealismTheory/Structures/LocalMeasurement.lean`

**Content:**
- `CompositeSystem` structure with relations
- `Measurement` and `LocalMeasurements` structures
- `joint_statistics` definition
- `physically_real_relation` predicate

**Estimated effort:** 2-3 days

### 5.3 Phase 3: H1 and H2 Definitions

**Files to create:**
- `LogicRealismTheory/Step3/Supervenience.lean`
- `LogicRealismTheory/Step3/LocalTomography.lean`

**Content:**
- `H1_metaphysical_supervenience` definition
- `H2_local_tomography` definition
- Equivalence lemmas if applicable

**Estimated effort:** 1-2 days

### 5.4 Phase 4: Bridge Lemmas

**Files to create:**
- `LogicRealismTheory/Step3/BridgeLemmas.lean`

**Content:**
- `relation_locally_accessible` (critical lemma)
- `supervenience_decomposition`
- `subsystem_distinguishable_implies_local_stat_diff`

**Estimated effort:** 3-5 days (main intellectual work)

### 5.5 Phase 5: Main Theorem

**Files to create:**
- `LogicRealismTheory/Step3/LocalTomographyTheorem.lean`

**Content:**
- `step3_H1_implies_H2` theorem
- Integration with Step 4 (forward reference to Masanes-Müller)

**Estimated effort:** 1-2 days

### 5.6 Total Estimated Effort

| Phase | Days | Critical? |
|-------|------|-----------|
| Phase 1 | 1-2 | Foundation |
| Phase 2 | 2-3 | Structure |
| Phase 3 | 1-2 | Definition |
| Phase 4 | 3-5 | **Critical** |
| Phase 5 | 1-2 | Integration |
| **Total** | **8-14** | — |

---

## 6. Critical Challenges

### 6.1 The Relation Accessibility Gap

The hardest part: showing that if R is a physically real relation (satisfies PPC), then R is locally accessible.

**The argument (from S2):**
1. R satisfies PPC → R-true and R-false are operationally distinguishable (D > 0)
2. R supervenes on A-states + B-states (by H1)
3. Any measurement distinguishing R accesses only A-properties and B-properties
4. Therefore R is locally accessible

**Formalization challenge:** Step 3 is informal. "Accesses only" must be defined type-theoretically.

**Proposed approach:** Define `locally_expressible` for measurements:

```lean
def locally_expressible
    (A B : DistinguishableSpace)
    (M : Measurement (TensorProduct A B)) : Prop :=
  ∃ (M_A : Measurement A) (M_B : Measurement B),
    ∀ (a : A.Carrier) (b : B.Carrier),
      M.prob (a ⊗ b) = (composition of M_A.prob and M_B.prob)
```

Then prove: measurements on composite systems satisfying supervenience are locally expressible.

### 6.2 Tensor Product Handling

Composite states in quantum mechanics form tensor products. The formalization must handle:
- Non-separable (entangled) states
- Partial trace for marginals
- LOCC (local operations + classical communication)

**Proposed approach:** Use Mathlib's `TensorProduct` for the algebraic structure. Define local tomography as: distinct tensor states yield distinct local marginal statistics.

### 6.3 Circularity Risk

**Risk:** H2 (local tomography) is used to derive Hilbert space (Step 4). If H2's definition presupposes Hilbert space structure, circularity occurs.

**Mitigation:** Define H2 in terms of `DistinguishableSpace` (pre-Hilbert), not `InnerProductSpace`. The Masanes-Müller reconstruction (Step 4) then shows that any locally tomographic GPT satisfying additional axioms is a Hilbert space theory.

**Verification:** Ensure `H2_local_tomography` uses only:
- `DistinguishableSpace` (metric, not inner product)
- `Measurement` (probability distributions, not PVMs)
- `joint_statistics` (product form, not trace)

---

## 7. Open Questions

### 7.1 Scope of Formalization

**Q1:** Should we formalize H1 → H2 for finite-dimensional systems only, or attempt the general case?

**Recommendation:** Start finite-dimensional. Infinite dimensions introduce measure-theoretic subtleties not essential to the H1 → H2 logic.

### 7.2 Relation Representation

**Q2:** How to represent "relations between subsystems" in `CompositeSystem`?

**Options:**
- (a) `Set (A × B → Prop)` — all relations
- (b) `Set (A × B → Bool)` — decidable relations
- (c) Custom `Relation` type with PPC constraint built in

**Recommendation:** Use (a) with a separate `physically_real_relation` predicate. This matches S2's structure.

### 7.3 Measurement Completeness

**Q3:** What measurements are "all physically admissible measurements" in D's definition?

**Options:**
- (a) All mathematically definable functions `S → Prob(Outcomes)`
- (b) A restricted class (e.g., arising from PVMs after Hilbert space derivation)
- (c) Axiomatize as "sufficiently rich" without specifying

**Recommendation:** Use (c) at Step 3; refine after Step 4 establishes Hilbert space.

---

## 8. Connection to Other Steps

### 8.1 Upstream Dependencies

| Dependency | File | Status |
|------------|------|--------|
| L<sub>3</sub> (classical logic) | `D0_1_ThreeFundamentalLaws.lean` | Complete |
| I<sub>∞</sub>, Infinite | `D0_2_InformationSpace.lean` | Complete |
| PPC derivation | S1 (prose) | ARGUED |

### 8.2 Downstream Consumers

| Consumer | Depends On | Notes |
|----------|------------|-------|
| Step 4 (Masanes-Müller) | H2 (local tomography) | Import `H2_local_tomography` |
| Step 5 (PVM structure) | Hilbert space from Step 4 | No direct Step 3 dependency |
| Masanes-Müller axiom | `ExternalTheorems.lean` | Already axiomatized |

### 8.3 Parallel Work

S8 (this strategy) can proceed in parallel with:
- S9 (if targeting time structure, Steps 8-10)
- S10 (if targeting dynamics, Steps 11-13)

Step 3 formalization is a prerequisite for formalizing Steps 4-7.

---

## 9. Summary

### 9.1 Formalization Deliverables

| File | Content | Priority |
|------|---------|----------|
| `Structures/DistinguishableSpace.lean` | D metric, basic lemmas | P1 |
| `Structures/PhysicalProposition.lean` | PPC, physically_real | P1 |
| `Structures/CompositeSystem.lean` | Composite, relations | P1 |
| `Structures/LocalMeasurement.lean` | Measurement, joint_statistics | P1 |
| `Step3/Supervenience.lean` | H1 definition | P2 |
| `Step3/LocalTomography.lean` | H2 definition | P2 |
| `Step3/BridgeLemmas.lean` | relation_locally_accessible, etc. | P2 (critical) |
| `Step3/LocalTomographyTheorem.lean` | step3_H1_implies_H2 | P3 |

### 9.2 Success Criteria

1. **Compilation:** All files compile without `sorry` (except axioms classified Tier 2)
2. **Theorem proven:** `step3_H1_implies_H2` proven from definitions
3. **No circularity:** H2 defined without presupposing Hilbert space
4. **Tier compliance:** No new Tier 1 axioms introduced
5. **Documentation:** Each file has header matching STANDARD_FILE_HEADER.md

### 9.3 Risks and Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Relation accessibility gap too hard | Medium | High | Weaken to "locally accessible for all physically real R" as axiom |
| Tensor product complications | Low | Medium | Restrict to finite dimensions |
| Circularity with Hilbert space | Low | High | Strict separation of DistinguishableSpace from InnerProductSpace |

---

## 10. Next Steps

1. **Review S1 and S2** to ensure prose definitions are formalizable
2. **Create `Structures/DistinguishableSpace.lean`** (Phase 1)
3. **Test `PhysicalProposition` definition** against S1's examples
4. **Prototype `relation_locally_accessible`** to assess difficulty
5. **Iterate on type signatures** as needed

---

## References

Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Hardy, L. (2001). Quantum theory from five reasonable axioms. *arXiv:quant-ph/0101012*.

Masanes, L. and Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Renou, M. O., et al. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600(7890), 625-629.

---

*Supplement S8 | Logic Realism Theory Project | 2026-03-13*
