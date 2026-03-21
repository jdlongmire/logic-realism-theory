# Axiom Audit Phase 2 — formalization/

**Date:** 2026-03-17
**Scope:** All `axiom` declarations in `formalization/LrtFormalization/*.lean`
**Total axioms found:** 43

---

## Summary

| Category | Count | Description |
|----------|-------|-------------|
| **PRIMITIVE** | 3 | Core LRT commitments (cannot be derived) |
| **EXTERNAL** | 16 | Established mathematical results (Tier 2) |
| **DERIVABLE** | 24 | Could potentially become theorems |

---

## Category Definitions

- **PRIMITIVE**: Foundational axioms that define LRT's ontological commitments. These cannot be derived without circular reasoning; they ARE the theory.

- **EXTERNAL**: Well-established mathematical theorems from literature (Stone, Gleason, Wigner, etc.). Axiomatized because full proofs require infrastructure beyond current Mathlib. Could be proven in principle with sufficient formalization effort.

- **DERIVABLE**: Axioms that encode derivation steps within LRT. These represent gaps that could be filled with additional proof work, either by strengthening the derivation chain or by proving intermediate lemmas.

---

## Detailed Axiom Inventory

### PRIMITIVE (3 axioms)

These are the irreducible commitments of LRT.

| File | Line | Axiom | Justification |
|------|------|-------|---------------|
| Step0_Primitives.lean | 54 | `I : Type*` | The Infinite Information Space I∞ — core primitive |
| Step0_Primitives.lean | 57 | `I_infinite : Infinite I` | I∞ is infinite — definitional property |
| Step1_Constitution.lean | 67 | `bridge_principle (X : Step0.X) : Nonempty (A_Omega X)` | X grounds A_Ω — the metaphysical bridge |

**Notes:**
- `I` and `I_infinite` together define the information substrate. No derivation possible — this IS Tier 1.
- `bridge_principle` is the philosophical claim that X constitutes A_Ω. Not derivable within mathematics alone.

---

### EXTERNAL (16 axioms)

Established mathematical theorems axiomatized for practical reasons.

#### Stone's Theorem & Functional Analysis

| File | Line | Axiom | Status | Path to Theorem |
|------|------|-------|--------|-----------------|
| Step9_EnergyAction.lean | 53 | `stones_theorem` | EXTERNAL | Requires unbounded operator theory. Standard in Reed-Simon. |
| Step5/EigenvalueRestriction.lean | 253 | `spectral_idempotent_of_bool_spectrum` | EXTERNAL | Functional calculus for bounded operators. Finite-dim case proven (line 201). |

#### Gleason's Theorem & Born Rule

| File | Line | Axiom | Status | Path to Theorem |
|------|------|-------|--------|-----------------|
| Step6_BornRule.lean | 140 | `gleason_theorem` | EXTERNAL | Requires measure theory on projection lattices. Gleason 1957. |
| Step6_BornRule.lean | 157 | `von_neumann_entropy` | EXTERNAL | Matrix logarithm infrastructure needed. von Neumann 1932. |
| Step6_BornRule.lean | 303 | `proj_norm_le` | EXTERNAL | Standard projection contraction. Provable with norm API. |
| Step6_BornRule.lean | 346 | `born_rule_completeness` | EXTERNAL | Spectral measure theory for partitions. |

#### Wigner & Symmetry Theorems

| File | Line | Axiom | Status | Path to Theorem |
|------|------|-------|--------|-----------------|
| Step7_Unitarity.lean | 106 | `wigner_theorem` | EXTERNAL | Wigner 1931. Norm-preserving linear maps → unitary. |
| Step9_EnergyAction.lean | 147 | `noether_theorem` | EXTERNAL | Standard field theory result. |
| Step9_EnergyAction.lean | 123 | `stationary_phase_principle` | EXTERNAL | Asymptotic analysis result. |

#### Hardy & Reconstruction

| File | Line | Axiom | Status | Path to Theorem |
|------|------|-------|--------|-----------------|
| Step3_LocalTomography.lean | 212 | `hardy_reconstruction` | EXTERNAL | Hardy 2001. H1 + H2 → CP(H). Core reconstruction theorem. |
| Step4/Hardy.lean | 50 | `QuantumStateSpace.ofCPH` | EXTERNAL | CPHStructure → QuantumStateSpace extraction. |
| Step4/Hardy.lean | 161 | `step4_hilbert_space` | EXTERNAL | Universe metavariable workaround. |

#### Purification & No-Hiding

| File | Line | Axiom | Status | Path to Theorem |
|------|------|-------|--------|-----------------|
| Step4/Purification.lean | 141 | `no_hiding_theorem` | EXTERNAL | Braunstein-Pati 2007. Quantum info cannot vanish. |
| Step4/Purification.lean | 364 | `cdp_purification_k2` | EXTERNAL | CDP 2011. Purification + H1 → K=2. |

#### Planck Constant

| File | Line | Axiom | Status | Path to Theorem |
|------|------|-------|--------|-----------------|
| Step9_EnergyAction.lean | 92-93 | `planck_constant`, `planck_constant_pos` | EXTERNAL | Physical constant. Cannot be derived. |

---

### DERIVABLE (24 axioms)

Axioms that encode derivation gaps. Prioritized by estimated effort.

#### Priority 1: Low-Hanging Fruit (5 axioms)

These could become theorems with modest effort.

| File | Line | Axiom | Effort | Path to Theorem |
|------|------|-------|--------|-----------------|
| Step4/Purification.lean | 224 | `trivial_schmidt_normalized` | LOW | Prove ∑(if n=0 then 1 else 0)² = 1. Tsum API. |
| Step3_LocalTomography.lean | 475 | `lrt_forces_k_equals_2` | LOW | `HardyK = 2` by definition (line 410: `def HardyK : ℕ := 2`). Trivial. |
| Step5/EigenvalueRestriction.lean | 289 | `event_operator_has_bool_spectrum` | MEDIUM | Proven in Step4/Boolean.lean via `eigenvalue_outcome_correspondence`. Unify. |
| Step8_TemporalEmergence.lean | 166 | `time_arrow` | LOW | Construct `TimeArrow` witness directly (direction = 1). |
| Step3_LocalTomography.lean | 379 | `lrt_satisfies_h2` | LOW | Already proven as `lrt_derives_h2` (line 353). Make theorem. |

#### Priority 2: Medium Effort (9 axioms)

Require additional structure or lemmas.

| File | Line | Axiom | Effort | Path to Theorem |
|------|------|-------|--------|-----------------|
| Step0_Primitives.lean | 273 | `config_separation` | MEDIUM | Stone-type separation. Needs Event algebra structure. |
| Step3_LocalTomography.lean | 373 | `lrt_satisfies_h1` | MEDIUM | Proven as `lrt_derives_h1` (line 322) but with explicit bridge assumptions. |
| Step3_LocalTomography.lean | 467 | `K_eq_2_open` | MEDIUM | Two routes available: Boolean-interference or Boolean-purification. |
| Step4/Boolean.lean | 127 | `faithful_representation` | MEDIUM | Stone representation theorem for Boolean algebras. |
| Step4/Boolean.lean | 171 | `eigenvalue_outcome_correspondence` | MEDIUM | Core bridge. Needs state-to-Hilbert map formalization. |
| Step4/Boolean.lean | 243 | `complete_events_form_pvm` | MEDIUM | Boolean algebra homomorphism to projection lattice. |
| Step7_Unitarity.lean | 116 | `evolution_preserves_distinguishability` | MEDIUM | From L₃ + orthogonality structure. |
| Step7_Unitarity.lean | 126 | `evolution_bijective` | MEDIUM | Microscopic reversibility. Physical principle. |
| Step7_Unitarity.lean | 134 | `evolution_preserves_norm` | MEDIUM | Probability conservation. From Born rule. |

#### Priority 3: Significant Effort (7 axioms)

Require substantial infrastructure or new approaches.

| File | Line | Axiom | Effort | Path to Theorem |
|------|------|-------|--------|-----------------|
| Step4/Purification.lean | 240 | `boolean_determination_encoded_axiom` | HIGH | Needs tensor product formalization, Schmidt decomposition. |
| Step4/Purification.lean | 287 | `encoding_gives_purification_axiom` | HIGH | EncodedDetermination → PurificationPrinciple. Universe issues. |
| Step4/Purification.lean | 335 | `boolean_implies_purification` | HIGH | OPN-005 main theorem. Combines above two. |
| Step4/Purification.lean | 412 | `k2_via_purification` | HIGH | Combined K=2 derivation via Route B. |
| Step8_TemporalEmergence.lean | 47 | `actualization_ordering` | HIGH | LinearOrder on ActualizationEvent. Philosophical commitment. |
| Step8_TemporalEmergence.lean | 70-86 | `time_embedding`, `time_embedding_mono`, `time_embedding_strict_mono` | HIGH | Embedding into ℝ. Requires order theory. |
| Step8_TemporalEmergence.lean | 106 | `evolution_matches_actualization` | HIGH | Links U(t) to actualization. Deep conceptual. |
| Step10_Schrodinger.lean | 147 | `schrodinger_from_stone` | HIGH | Full Stone → Schrödinger requires unbounded operator theory. |
| Step7_Unitarity.lean | 167 | `time_evolution_group` | HIGH | Existence of unitary group. Follows from Stone. |

---

## Recommended Actions

### Immediate (can be done now)

1. **Eliminate `lrt_forces_k_equals_2`** — Replace with `rfl` since `HardyK = 2` by definition.
2. **Eliminate `lrt_satisfies_h2`** — Replace with `lrt_derives_h2`.
3. **Prove `trivial_schmidt_normalized`** — Simple tsum calculation.
4. **Construct `time_arrow`** — Direct witness construction.
5. **Unify `event_operator_has_bool_spectrum`** — Reference Step4/Boolean derivation.

### Short-term (next sprint)

1. **Strengthen `lrt_satisfies_h1`** — Make `lrt_derives_h1` the canonical version.
2. **Prove `config_separation`** — Define adequate Event algebra structure.
3. **Formalize `eigenvalue_outcome_correspondence`** — Core Boolean-to-spectrum bridge.

### Long-term (research directions)

1. **K=2 derivation** — Complete either OPN-004 (interference) or OPN-005 (purification) route.
2. **Temporal emergence** — Strengthen philosophical justification or accept as Tier 2.
3. **Stone's theorem** — Wait for Mathlib unbounded operator theory or accept as Tier 2.

---

## Axiom Count Evolution

| Phase | Primitives | External | Derivable | Total |
|-------|------------|----------|-----------|-------|
| Phase 2 (now) | 3 | 16 | 24 | 43 |
| After immediate actions | 3 | 16 | 19 | 38 |
| Target | 3 | ~12 | ~5 | ~20 |

---

## Appendix: Full Axiom List by File

### Step0_Primitives.lean (3 axioms)
```lean
axiom I : Type*                           -- PRIMITIVE
axiom I_infinite : Infinite I             -- PRIMITIVE
axiom config_separation : ...             -- DERIVABLE
```

### Step1_Constitution.lean (1 axiom)
```lean
axiom bridge_principle : Nonempty (A_Omega X)  -- PRIMITIVE
```

### Step3_LocalTomography.lean (5 axioms)
```lean
axiom hardy_reconstruction : ...          -- EXTERNAL
axiom lrt_satisfies_h1 : ...              -- DERIVABLE (proven)
axiom lrt_satisfies_h2 : ...              -- DERIVABLE (proven)
axiom K_eq_2_open : ...                   -- DERIVABLE
axiom lrt_forces_k_equals_2 : ...         -- DERIVABLE (trivial)
```

### Step4/Hardy.lean (2 axioms)
```lean
axiom QuantumStateSpace.ofCPH : ...       -- EXTERNAL
axiom step4_hilbert_space : ...           -- EXTERNAL
```

### Step4/Boolean.lean (3 axioms)
```lean
axiom faithful_representation : ...        -- DERIVABLE
axiom eigenvalue_outcome_correspondence : ... -- DERIVABLE
axiom complete_events_form_pvm : ...       -- DERIVABLE
```

### Step4/Purification.lean (7 axioms)
```lean
axiom no_hiding_theorem : ...              -- EXTERNAL
axiom trivial_schmidt_normalized : ...     -- DERIVABLE (easy)
axiom boolean_determination_encoded_axiom : ... -- DERIVABLE
axiom encoding_gives_purification_axiom : ... -- DERIVABLE
axiom boolean_implies_purification : ...   -- DERIVABLE
axiom cdp_purification_k2 : ...            -- EXTERNAL
axiom k2_via_purification : ...            -- DERIVABLE
```

### Step5/EigenvalueRestriction.lean (2 axioms)
```lean
axiom spectral_idempotent_of_bool_spectrum : ... -- EXTERNAL
axiom event_operator_has_bool_spectrum : ... -- DERIVABLE (unified)
```

### Step6_BornRule.lean (4 axioms)
```lean
axiom gleason_theorem : ...                -- EXTERNAL
axiom von_neumann_entropy : ...            -- EXTERNAL
axiom proj_norm_le : ...                   -- EXTERNAL
axiom born_rule_completeness : ...         -- EXTERNAL
```

### Step7_Unitarity.lean (5 axioms)
```lean
axiom wigner_theorem : ...                 -- EXTERNAL
axiom evolution_preserves_distinguishability : ... -- DERIVABLE
axiom evolution_bijective : ...            -- DERIVABLE
axiom evolution_preserves_norm : ...       -- DERIVABLE
axiom time_evolution_group : ...           -- DERIVABLE
```

### Step8_TemporalEmergence.lean (5 axioms)
```lean
axiom actualization_ordering : ...         -- DERIVABLE (philosophical)
axiom time_embedding : ...                 -- DERIVABLE
axiom time_embedding_mono : ...            -- DERIVABLE
axiom time_embedding_strict_mono : ...     -- DERIVABLE
axiom evolution_matches_actualization : ... -- DERIVABLE
axiom time_arrow : ...                     -- DERIVABLE (easy)
```

### Step9_EnergyAction.lean (5 axioms)
```lean
axiom stones_theorem : ...                 -- EXTERNAL
axiom planck_constant : ℝ                  -- EXTERNAL
axiom planck_constant_pos : ...            -- EXTERNAL
axiom stationary_phase_principle : ...     -- EXTERNAL
axiom noether_theorem : ...                -- EXTERNAL
```

### Step10_Schrodinger.lean (1 axiom)
```lean
axiom schrodinger_from_stone : ...         -- EXTERNAL (HIGH priority)
```

---

*Generated by Claude Code axiom audit*
