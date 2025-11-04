# Complete Lean Proof Refactor Strategy (Revised: Tier-Based)

**Session**: 9.0
**Date**: 2025-11-04 (Revised)
**Goal**: Prove LRT-specific theorems from foundational axioms using established math tools
**Framework**: 3-Tier Axiom Classification System (see AXIOM_CLASSIFICATION_SYSTEM.md)

---

## The 3-Tier Framework

### Tier 1: LRT Specific (2-3 axioms) - FOUNDATIONAL
### Tier 2: Established Math Tools (~16 axioms) - KEEP AS AXIOMS
### Tier 3: Universal Physics Assumptions (1 axiom) - KEEP AS AXIOM

**Key Insight**: We should NOT try to prove Stone's theorem, spectral theorem, etc. from scratch. These are established results (Tier 2) that we use as building blocks, following standard practice in quantum foundations (Hardy 2001, Chiribella et al. 2011).

**Focus**: Prove LRT-specific claims (currently axiomatized) from Tier 1 foundation using Tier 2 tools.

---

## Tier 1: LRT Specific (Foundational Axioms)

**Source**: `Foundation/IIS.lean`

```lean
axiom I : Type*                    -- Infinite Information Space exists
axiom I_infinite : Infinite I      -- I is infinite
```

**Status**: KEEP - These define what LRT *is*

**3FLL (0 axioms - ALREADY PROVEN)**:
- `theorem identity_law` - proven via `rfl`
- `theorem non_contradiction_law` - proven
- `theorem excluded_middle_law` - uses Classical.em

**A = L(I) (ALREADY PROVEN, 0 sorry)**:
- `theorem A_subset_I` ✓
- `theorem A_to_I_injective` ✓
- `theorem actualization_is_L_image` ✓
- `theorem actualized_satisfies_3FLL` ✓

**Count**: 2 foundational axioms (I, I_infinite)

---

## Tier 2: Established Math Tools (Keep as Axioms)

These are well-known theorems with published proofs. We axiomatize them following standard practice. Each will be documented with literature references.

**K_math axioms to KEEP** (~16 total):

| Axiom | Reference | Why Keep |
|-------|-----------|----------|
| `stones_theorem` (multiple copies) | Stone (1932) | Unitary groups ↔ generators. Full proof requires ~300 lines of functional analysis |
| `hermitian_real_spectrum` | von Neumann (1932), Spectral theorem | Standard Hilbert space infrastructure |
| `jordan_von_neumann` | von Neumann & Jordan (1935) | Parallelogram law → inner product. Full proof ~500 lines |
| `gleason_theorem` | Gleason (1957) | Probability measures on Hilbert space. Major theorem in QM foundations |
| `von_neumann_entropy` definitions | von Neumann (1932) | Standard quantum entropy, in Mathlib partially |
| `spohns_inequality` | Spohn (1978) | Entropy change bounds, information theory |
| `binary_entropy_bound` | Shannon (1948) | Information theory infrastructure |
| `mazur_ulam` | Mazur & Ulam (1932) | Isometries are affine, functional analysis |
| Complex field properties (7 axioms) | Standard algebra | Algebraic properties of ℂ, ℍ |

**Action**: Add Tier 2 documentation headers with literature references to each

**Count**: ~16 axioms (established results, not novel LRT claims)

---

## Tier 3: Universal Physics Assumptions (Keep as Axioms)

**Physical postulates used across all physics**:

| Axiom | Used By | Why Keep |
|-------|---------|----------|
| `energy_additivity_for_independent_systems` | All physics (QM, stat mech, thermodynamics) | Cannot derive from pure math, fundamental extensivity |

**Action**: Add Tier 3 documentation

**Count**: 1 axiom (domain-standard physical assumption)

---
## LRT-Specific Theorems to Prove

**The Real Work**: Prove ~30-35 LRT claims (currently axiomatized) from Tier 1 using Tier 2 tools.

**Categories**:
- **A**: Constraint dynamics (statespace_monotone ✅ DONE, 2-3 more)
- **B**: 3FLL symmetries (4 theorems from identity_law, non_contradiction_law, excluded_middle_law)
- **C**: Hilbert space emergence (5 theorems - Section 5.2 claims)
- **D**: Time/energy emergence (3-4 theorems - Section 5.3 claims)
- **E**: Born rule (8 theorems - Section 5.1 derivation)
- **F**: Measurement dynamics (8 theorems - Section 5.4 K-mechanism)
- **G**: Cleanup (remove 5-7 placeholders/duplicates)

**Total**: ~30-35 axioms → proven theorems

---

## Revised Target (Honest & Realistic)

**Current**: 88 formal axiom declarations

**Target**:
- **Tier 1 (LRT Specific)**: 2 axioms (I, I_infinite)
- **Tier 2 (Established Math Tools)**: ~16 axioms (Stone's, Gleason's, etc.)
- **Tier 3 (Universal Physics)**: 1 axiom (energy additivity)
- **LRT Theorems**: ~30-35 proven (not axiomatized)
- **Total Axioms**: ~19

**Paper Claim**: "LRT has 2 foundational axioms, uses ~16 established mathematical results as building blocks (Stone's theorem, spectral theorem, etc.), and 1 standard physical assumption. From these, LRT proves ~30-35 theorems including Born rule, Hilbert space structure, time evolution, and measurement collapse."

---

## Execution: 8 Phases (45-62 hours)

1. **Documentation** (2-3h): Add tier headers, remove placeholders
2. **Low-hanging fruit** (3-4h): Prove simple claims
3. **3FLL symmetries** (6-8h): Prove from 3FLL theorems
4. **Hilbert space** (8-12h): Formalize Section 5.2
5. **Time/energy** (6-8h): Formalize Section 5.3
6. **Born rule** (10-14h): Formalize Section 5.1 ← HARDEST
7. **Measurement** (8-10h): Formalize Section 5.4
8. **Verification** (2-3h): Final checks

---

## Success Criteria

**Minimum**: Tier docs complete, 5-10 theorems proven, builds
**Stretch**: 15-20 theorems proven, 3FLL symmetries done
**Transformative**: 25-30 theorems proven, Born rule derived, ~19 axioms total

---

**Status**: Ready for Phase 1 (Documentation)
**Progress**: 1 theorem proven (statespace_monotone ✅)
**Next**: Add Tier documentation to all axioms
