# LRT Formalization: Axiom Inventory

**Date:** 2026-03-21 (Post-Axiom Reduction Campaign — Final)
**Scope:** `formalization/` directory
**Purpose:** Complete inventory of axioms after reduction campaign

---

## Summary

| Category | Count | Target | Achieved |
|----------|-------|--------|----------|
| **PRIMITIVE** (truly fundamental) | 3 | Keep all | ✅ |
| **DERIVABLE** (can become theorem) | 0 | Reduce to 0 | ✅ |
| **EXTERNAL** (established math/physics) | 19 | Keep as imports | ✅ |
| **TOTAL** | 22 | — | ✅ |

**Achievement:** 50% axiom reduction (44 → 22)

---

## Category Definitions

- **PRIMITIVE:** Truly fundamental LRT axioms that cannot be derived and constitute the theory's distinctive claims
- **DERIVABLE:** Currently axiomatized but could in principle be proven as theorems — **ALL CONVERTED**
- **EXTERNAL:** Established mathematical theorems or physics results imported as axioms (standard practice)

---

## Detailed Inventory

### PRIMITIVE (3 axioms) — Keep

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

### DERIVABLE (0 axioms) — All Converted!

All previously DERIVABLE axioms have been converted to theorems:

| Former Axiom | File | Status | Issue |
|--------------|------|--------|-------|
| `spectral_correspondence` | Step5/EigenvalueOutcome.lean | **THEOREM** | #38 |
| `born_rule_completeness` | Step6_BornRule.lean | **THEOREM** | #40 |
| `proj_norm_le` | Step6_BornRule.lean | **THEOREM** | — |
| `spectral_idempotent_of_bool_spectrum` | Step5/EigenvalueRestriction.lean | **THEOREM** | — |
| `event_operator_has_bool_spectrum` | Step5/EigenvalueRestriction.lean | **STRUCTURE** | — |
| `evolution_preserves_norm` | Step7_Unitarity.lean | **THEOREM** | — |
| `evolution_group_composition` | Step7_Unitarity.lean | **THEOREM** | — |
| `evolution_identity` | Step7_Unitarity.lean | **THEOREM** | — |
| `time_evolution_family` | Step7_Unitarity.lean | **DEFINITION** | — |
| `actualization_ordering` | Step8_TemporalEmergence.lean | **THEOREM** | — |
| `time_embedding` | Step8_TemporalEmergence.lean | **DEFINITION** | — |
| `time_embedding_strict_mono` | Step8_TemporalEmergence.lean | **THEOREM** | — |
| `evolution_matches_actualization` | Step8_TemporalEmergence.lean | **THEOREM** | — |

---

### EXTERNAL (19 axioms) — Keep as imports

These are established mathematical theorems or well-vetted physics results. Standard practice in formal verification is to import these rather than re-derive.

#### Quantum Information Theory (6)

| # | Axiom | File | Line | Source |
|---|-------|------|------|--------|
| E1 | `hardy_reconstruction` | Step3_LocalTomography.lean | 212 | Hardy 2001, CDP 2011 |
| E2 | `product_effects_separate_states` | Step3_LocalTomography.lean | 476 | Tomographic completeness |
| E3 | `QuantumStateSpace.ofCPH` | Step4/Hardy.lean | 50 | Representation theorem |
| E4 | `step4_hilbert_space` | Step4/Hardy.lean | 161 | Consequence of Hardy |
| E5 | `no_hiding_theorem` | Step4/Purification.lean | 235 | Braunstein-Pati 2007 |
| E6 | `cdp_purification_k2` | Step4/Purification.lean | 508 | CDP 2011 |

#### Born Rule / Entropy (4)

| # | Axiom | File | Line | Source |
|---|-------|------|------|--------|
| E7 | `gleason_theorem` | Step6_BornRule.lean | 197 | Gleason 1957 |
| E8 | `von_neumann_entropy` | Step6_BornRule.lean | 214 | von Neumann 1932 |
| E9 | `maxent_forces_pure_state` | Step6_BornRule.lean | 234 | Jaynes 1957 |
| E10 | `nonlinearity_implies_signaling` | Step6_BornRule.lean | 804 | Torres Alegre 2025 |

#### Unitarity / Time Evolution (2)

| # | Axiom | File | Line | Source |
|---|-------|------|------|--------|
| E11 | `hamiltonian` | Step7_Unitarity.lean | 143 | Generator existence |
| E12 | `hamiltonian_isSelfAdjoint` | Step7_Unitarity.lean | 153 | Stone 1932 |

#### Functional Analysis / Operator Theory (5)

| # | Axiom | File | Line | Source |
|---|-------|------|------|--------|
| E13 | `stones_theorem` | Step9_EnergyAction.lean | 141 | Stone 1932 |
| E14 | `noether_theorem` | Step9_EnergyAction.lean | 263 | Noether 1918 |
| E15 | `schrodinger_from_stone` | Step10_Schrodinger.lean | 170 | Stone → Schrödinger |
| E16 | `hamiltonian_generates_unitary` | Step10_Schrodinger.lean | 96 | exp(iHt) is unitary |
| E17 | `hamiltonian_generates_group_mul` | Step10_Schrodinger.lean | 128 | Group law |

#### Physical Constants (2)

| # | Axiom | File | Line | Source |
|---|-------|------|------|--------|
| E18 | `planck_constant` | Step9_EnergyAction.lean | 189 | Empirical constant ℏ |
| E19 | `planck_constant_pos` | Step9_EnergyAction.lean | 190 | ℏ > 0 |

---

## Axiom Count by File

| File | Axioms | Category |
|------|--------|----------|
| Step0_Primitives.lean | 2 | PRIMITIVE |
| Step1_Constitution.lean | 1 | PRIMITIVE |
| Step2_DeterminateIdentity.lean | 0 | — |
| Step3_LocalTomography.lean | 2 | EXTERNAL |
| Step4/Hardy.lean | 2 | EXTERNAL |
| Step4/Boolean.lean | 0 | — |
| Step4/Purification.lean | 2 | EXTERNAL |
| Step5/EigenvalueRestriction.lean | 0 | — |
| Step5/EigenvalueOutcome.lean | 0 | — |
| Step6_BornRule.lean | 4 | EXTERNAL |
| Step7_Unitarity.lean | 2 | EXTERNAL |
| Step8_TemporalEmergence.lean | 0 | — |
| Step9_EnergyAction.lean | 4 | EXTERNAL |
| Step10_Schrodinger.lean | 3 | EXTERNAL |
| **Total** | **22** | — |

---

## Minimal Primitive Set Analysis

### The 3-Primitive Set

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

**Conclusion:** 3 primitives is the minimum for LRT.

---

## Reduction Timeline

| Date | Total | Change |
|------|-------|--------|
| Baseline | 44 | Initial count |
| 2026-03-17 | 41 | Initial audit |
| 2026-03-20 AM | 31 | Consolidation |
| 2026-03-21 AM | 24 | Step 5/7/8 reductions |
| **2026-03-21 Final** | **22** | spectral_correspondence, born_rule_completeness |

---

## Key Achievements

1. **50% reduction** in total axioms (44 → 22)
2. **0 REMAINING axioms** — all derivable axioms converted to theorems
3. **Clean separation** — 3 PRIMITIVE (LRT-specific) + 19 EXTERNAL (standard math)
4. **Two key theorems derived:**
   - `spectral_correspondence` (Issue #38)
   - `born_rule_completeness` (Issue #40)

---

*Final inventory update: 2026-03-21*
*Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>*
