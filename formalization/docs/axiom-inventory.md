# LRT Formalization: Axiom Inventory

**Date:** 2026-03-17
**Scope:** `formalization/` directory (not `lean/`)
**Purpose:** Categorize all axioms to enable reduction to minimal primitive set

---

## Summary

| Category | Count | Target |
|----------|-------|--------|
| **PRIMITIVE** (truly fundamental) | 3 | Keep all |
| **DERIVABLE** (can become theorem) | 10 | Reduce to 0 |
| **EXTERNAL** (established math/physics) | 28 | Keep as imports |
| **TOTAL** | 41 | Target: 3 primitives + external imports |

---

## Category Definitions

- **PRIMITIVE:** Truly fundamental LRT axioms that cannot be derived and constitute the theory's distinctive claims
- **DERIVABLE:** Currently axiomatized but could in principle be proven as theorems with additional work
- **EXTERNAL:** Established mathematical theorems or physics results imported as axioms (standard practice)

---

## Detailed Inventory

### PRIMITIVE (3 axioms) - Keep

These are the irreducible core of LRT. They cannot be derived and define what makes LRT distinctive.

| # | Axiom | File | Line | Justification |
|---|-------|------|------|---------------|
| P1 | `I : Type*` | Step0_Primitives.lean | 54 | The Infinite Information Space exists (ontological primitive) |
| P2 | `I_infinite : Infinite I` | Step0_Primitives.lean | 57 | I is infinite (structural property of I) |
| P3 | `bridge_principle` | Step1_Constitution.lean | 67 | X grounds A_Omega (grounding relation, philosophical input) |

**Notes:**
- P1 and P2 are essentially one conceptual primitive (the existence of an infinite distinguishability substrate)
- P3 is the metaphysical bridge connecting logical structure to actuality

---

### DERIVABLE (10 axioms) - Target for elimination

These are currently axiomatized but the files indicate they are derivable or have partial proofs.

| # | Axiom | File | Line | Reduction Path |
|---|-------|------|------|----------------|
| D1 | `config_separation` | Step0_Primitives.lean | 273 | Derivable from I being "formally specifiable" - Stone-type separation |
| D2 | `lrt_satisfies_h1` | Step3_LocalTomography.lean | 373 | **Already has theorem `lrt_derives_h1`** - convert to theorem |
| D3 | `lrt_satisfies_h2` | Step3_LocalTomography.lean | 379 | **Already has theorem `lrt_derives_h2`** - convert to theorem |
| D4 | `K_eq_2_open` | Step3_LocalTomography.lean | 467 | Via OPN-005 path: Boolean + purification + CDP |
| D5 | `lrt_forces_k_equals_2` | Step3_LocalTomography.lean | 475 | Duplicate of D4 - consolidate |
| D6 | `evolution_preserves_distinguishability` | Step7_Unitarity.lean | 116 | Derivable from L3 + inner product structure |
| D7 | `evolution_bijective` | Step7_Unitarity.lean | 126 | Derivable from unitarity |
| D8 | `evolution_preserves_norm` | Step7_Unitarity.lean | 134 | Derivable from unitarity |
| D9 | `boolean_determination_encoded` | Step4/Purification.lean | 170 | **Already proven as theorem** - axiom label is misleading |
| D10 | `encoding_gives_purification` | Step4/Purification.lean | 211 | **Already proven as theorem** - axiom label is misleading |

**Priority order for elimination:**
1. D2, D3: Already have derivation theorems, just need axiom removal
2. D9, D10: Already proven, just incorrectly labeled
3. D6, D7, D8: Routine physics derivations
4. D4, D5: K=2 route via OPN-005
5. D1: Requires formal separation axiom derivation

---

### EXTERNAL (28 axioms) - Keep as imports

These are established mathematical theorems or well-vetted physics results. Standard practice in formal verification is to import these rather than re-derive.

#### Mathematical Theorems (17)

| # | Axiom | File | Line | Source |
|---|-------|------|------|--------|
| E1 | `hardy_reconstruction` | Step3_LocalTomography.lean | 212 | Hardy 2001, CDP 2011 |
| E2 | `stones_theorem` | Step9_EnergyAction.lean | 53 | Reed-Simon, Functional Analysis |
| E3 | `gleason_theorem` | Step6_BornRule.lean | 140 | Gleason 1957 |
| E4 | `von_neumann_entropy` | Step6_BornRule.lean | 157 | von Neumann 1932 |
| E5 | `proj_norm_le` | Step6_BornRule.lean | 303 | Standard functional analysis |
| E6 | `born_rule_completeness` | Step6_BornRule.lean | 346 | Spectral theory |
| E7 | `wigner_theorem` | Step7_Unitarity.lean | 106 | Wigner 1931 |
| E8 | `noether_theorem` | Step9_EnergyAction.lean | 147 | Noether 1918 |
| E9 | `spectral_idempotent_of_bool_spectrum` | Step5/EigenvalueRestriction.lean | 253 | Functional calculus |
| E10 | `QuantumStateSpace.ofCPH` | Step4/Hardy.lean | 50 | Representation theorem |
| E11 | `step4_hilbert_space` | Step4/Hardy.lean | 161 | Consequence of Hardy |
| E12 | `faithful_representation` | Step4/Boolean.lean | 125 | Stone representation |
| E13 | `eigenvalue_outcome_correspondence` | Step4/Boolean.lean | 169 | Spectral postulate |
| E14 | `complete_events_form_pvm` | Step4/Boolean.lean | 241 | Boolean algebra to projection lattice |
| E15 | `no_hiding_theorem` | Step4/Purification.lean | 101 | Braunstein-Pati 2007 |
| E16 | `cdp_purification_k2` | Step4/Purification.lean | 284 | CDP 2011 |
| E17 | `schrodinger_from_stone` | Step10_Schrodinger.lean | 80 | Direct from Stone's theorem |

#### Physics/Temporal Structure (11)

| # | Axiom | File | Line | Source |
|---|-------|------|------|--------|
| E18 | `planck_constant` | Step9_EnergyAction.lean | 92 | Empirical constant |
| E19 | `planck_constant_pos` | Step9_EnergyAction.lean | 93 | Physical constraint |
| E20 | `stationary_phase_principle` | Step9_EnergyAction.lean | 123 | Path integral formalism |
| E21 | `actualization_ordering` | Step8_TemporalEmergence.lean | 47 | LRT temporal emergence |
| E22 | `time_embedding` | Step8_TemporalEmergence.lean | 67 | Ordering → ℝ |
| E23 | `time_embedding_mono` | Step8_TemporalEmergence.lean | 69 | Monotonicity |
| E24 | `time_embedding_dense` | Step8_TemporalEmergence.lean | 76 | Dense range |
| E25 | `evolution_matches_actualization` | Step8_TemporalEmergence.lean | 94 | Time-evolution correspondence |
| E26 | `time_arrow` | Step8_TemporalEmergence.lean | 158 | Direction of time |
| E27 | `time_evolution_group` | Step7_Unitarity.lean | 167 | One-parameter group |
| E28 | `event_operator_has_bool_spectrum` | Step5/EigenvalueRestriction.lean | 289 | Physics interpretation |

**Note:** E21-E26 and E28 could be considered DERIVABLE with more work but are currently treated as physics input.

---

## Reduction Path to 5 Primitives

### Current State: 41 axioms

### Phase 1: Clean up already-derived axioms (Week 1)
**Target: 31 axioms**

| Action | Axioms Removed | New Count |
|--------|----------------|-----------|
| Remove `lrt_satisfies_h1` (already derived) | 1 | 40 |
| Remove `lrt_satisfies_h2` (already derived) | 1 | 39 |
| Consolidate `K_eq_2_open` + `lrt_forces_k_equals_2` | 1 | 38 |
| Remove `boolean_determination_encoded` (already theorem) | 1 | 37 |
| Remove `encoding_gives_purification` (already theorem) | 1 | 36 |
| Derive evolution axioms from unitarity | 3 | 33 |

### Phase 2: Derive K=2 via OPN-005 (Week 2-3)
**Target: 31 axioms**

The K=2 derivation relies on the chain:
```
Boolean spectrum → Purification → K=2 (CDP import)
```

The CDP import (E16) remains external. The `K_eq_2_open` axiom becomes a theorem.

### Phase 3: Derive config_separation (Week 4)
**Target: 30 axioms**

`config_separation` can be derived from the philosophical claim that I is "formally specifiable":
- Formally specifiable = describable by properties
- Properties = events
- Therefore distinct configurations differ on some event

### Final State: 3 PRIMITIVE + 27 EXTERNAL

| Category | Count | List |
|----------|-------|------|
| PRIMITIVE | 3 | I, I_infinite, bridge_principle |
| EXTERNAL | 27 | Mathematical/physics imports |

---

## Minimal Primitive Set Analysis

### Candidate: 3-Primitive Set

1. **I : Type*** — The infinite information space
2. **I_infinite : Infinite I** — Infinitude of I
3. **bridge_principle** — X grounds A_Omega

### Can we reduce further?

**Option A: Combine P1+P2 into one**
```lean
axiom I_exists : ∃ (I : Type*), Infinite I
```
This is semantically equivalent but less clean for dependent types.

**Option B: Derive bridge_principle?**
The bridge principle states that A_Omega is non-empty given X. This is a philosophical claim (something exists) that cannot be derived from pure logic. It must remain a primitive.

**Conclusion:** 3 primitives is likely minimal for LRT.

---

## Comparison with lean/ Directory

The `lean/` directory has a similar structure with additional axioms for:
- D0_2_InformationSpace.lean (I, I_infinite)
- D1_3_LocalTomography.lean (operational_determinacy, distinguishable_implies_local)
- D1_8_UniqueNextState.lean (ActionPrimitive, A_dynamic, A_functional, S_injective_axiom)
- D2_Energy.lean (fermis_golden_rule, lindblad_dephasing_rate, energy_additivity)
- D3_Schrodinger.lean (mazur_ulam, stones_theorem)
- ExternalTheorems.lean (8 reconstruction theorems)

The `formalization/` directory is more streamlined and should be the reference.

---

## Recommendations

### Immediate Actions

1. **Convert D2 and D3 to theorems** - They already have derivation theorems; remove the axiom declarations
2. **Consolidate K=2 axioms** - Merge `K_eq_2_open` and `lrt_forces_k_equals_2` into one
3. **Remove mislabeled axioms** - `boolean_determination_encoded` and `encoding_gives_purification` are theorems, not axioms

### Medium-term Actions

4. **Derive evolution preservation axioms** - D6, D7, D8 from unitarity + inner product
5. **Complete OPN-005** - Full derivation of K=2 via Boolean-purification route
6. **Derive config_separation** - From I being formally specifiable

### Long-term Actions

7. **Formalize more external theorems** - Replace axioms with Mathlib imports where possible
8. **Document traceability** - Each external axiom should cite specific literature

---

## Appendix: Full Axiom List by File

### Step0_Primitives.lean (3 axioms)
- `I : Type*` — PRIMITIVE
- `I_infinite : Infinite I` — PRIMITIVE
- `config_separation` — DERIVABLE

### Step1_Constitution.lean (1 axiom)
- `bridge_principle` — PRIMITIVE

### Step3_LocalTomography.lean (5 axioms)
- `hardy_reconstruction` — EXTERNAL
- `lrt_satisfies_h1` — DERIVABLE (has theorem)
- `lrt_satisfies_h2` — DERIVABLE (has theorem)
- `K_eq_2_open` — DERIVABLE
- `lrt_forces_k_equals_2` — DERIVABLE (duplicate)

### Step4/Hardy.lean (2 axioms)
- `QuantumStateSpace.ofCPH` — EXTERNAL
- `step4_hilbert_space` — EXTERNAL

### Step4/Boolean.lean (3 axioms)
- `faithful_representation` — EXTERNAL
- `eigenvalue_outcome_correspondence` — EXTERNAL
- `complete_events_form_pvm` — EXTERNAL

### Step4/Purification.lean (2 axioms)
- `no_hiding_theorem` — EXTERNAL
- `cdp_purification_k2` — EXTERNAL

### Step5/EigenvalueRestriction.lean (2 axioms)
- `spectral_idempotent_of_bool_spectrum` — EXTERNAL
- `event_operator_has_bool_spectrum` — EXTERNAL

### Step6_BornRule.lean (4 axioms)
- `gleason_theorem` — EXTERNAL
- `von_neumann_entropy` — EXTERNAL
- `proj_norm_le` — EXTERNAL
- `born_rule_completeness` — EXTERNAL

### Step7_Unitarity.lean (5 axioms)
- `wigner_theorem` — EXTERNAL
- `evolution_preserves_distinguishability` — DERIVABLE
- `evolution_bijective` — DERIVABLE
- `evolution_preserves_norm` — DERIVABLE
- `time_evolution_group` — EXTERNAL

### Step8_TemporalEmergence.lean (6 axioms)
- `actualization_ordering` — EXTERNAL
- `time_embedding` — EXTERNAL
- `time_embedding_mono` — EXTERNAL
- `time_embedding_dense` — EXTERNAL
- `evolution_matches_actualization` — EXTERNAL
- `time_arrow` — EXTERNAL

### Step9_EnergyAction.lean (5 axioms)
- `stones_theorem` — EXTERNAL
- `planck_constant` — EXTERNAL
- `planck_constant_pos` — EXTERNAL
- `stationary_phase_principle` — EXTERNAL
- `noether_theorem` — EXTERNAL

### Step10_Schrodinger.lean (1 axiom)
- `schrodinger_from_stone` — EXTERNAL

---

*Generated by Claude Code axiom audit agent*
