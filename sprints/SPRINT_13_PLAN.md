# Sprint 13: Axiom Reframing - Option C Implementation (Phase 1)

**Created**: 2025-11-03
**Duration**: 2 weeks
**Objective**: Implement Option C - Honest accounting with roadmap to 2-3 core axioms
**Follows**: Sprint 12 (verification cleanup)

---

## Sprint Goal

**Primary**: Establish honest axiom accounting and begin formalizing key derivations
**Success Criteria**:
- ✓ Accurate axiom count documented (theory vs. infrastructure)
- ✓ Computational helpers converted to definitions
- ✓ Placeholders removed
- ✓ At least 2 major derivations formalized as theorems
- ✓ Main.md Section 7 updated with Option C framing
- ✓ Roadmap document created for path to 2-3 core axioms

---

## Current State Analysis (From LLM Team Review)

### Axiom Count Breakdown (57 total declarations)
- **K_math**: 16 (mathematical infrastructure - DON'T count as LRT axioms)
- **LRT_foundational**: 14 (core postulates - REDUCE to 2-3)
- **Measurement_dynamics**: 15 (measurement properties - DERIVE from core)
- **Computational_helper**: 4 (should be definitions, NOT axioms)
- **Physical_postulate**: 1 (energy additivity - investigate if derivable)
- **Placeholder**: 5 (remove)

### Target Counts
- **Current honest count**: 30-34 theory-specific axioms (excluding K_math)
- **After Sprint 13**: ~20-25 theory axioms
- **Ultimate goal**: 2-3 core axioms + derivations

---

## Sprint 13 Tracks

### Track 1: Quick Wins - Reclassification (Priority 1, Week 1)

**Objective**: Reduce axiom count by 9 through reclassification

#### Task 1.1: Convert Computational Helpers to Definitions (-4 axioms)
**Files**:
- `ConstraintThreshold.lean`: Set.card, ConstraintViolations
- `MeasurementGeometry.lean`: IdentityState
- `TimeEmergence.lean`: trajectory_to_evolution

**Action**:
```lean
-- Change from:
axiom Set.card : ...

-- To:
def Set.card : ... := ...
```

**Verification**: Each must have an actual implementation, not just type signature
**Effort**: 4-8 hours
**Owner**: Sprint 13 Track 1

#### Task 1.2: Remove Layer3.lean Placeholders (-5 axioms)
**File**: `Layer3.lean`

**Current**:
```lean
axiom track_1_9_inner_product : True
axiom track_1_10_hilbert_space : True
-- etc.
```

**Action**: Replace with references to actual theorems
```lean
-- References to actual formalized tracks
theorem layer3_inner_product_complete : True :=
  InnerProduct.track_1_9_complete

theorem layer3_hilbert_space_complete : True :=
  HilbertSpace.track_1_10_complete
```

**Effort**: 2-4 hours
**Owner**: Sprint 13 Track 1

**Track 1 Result**: -9 axioms (57 → 48 total, 30-34 theory → 21-25 theory)

---

### Track 2: Formalize Time Emergence Derivation (Priority 2, Week 1-2)

**Objective**: Convert `axiom time_emergence_from_identity` to `theorem`

#### Background
- Main.md Section 5.3 claims time emerges from Identity constraint
- Currently marked as axiom in Lean
- LLM team: "This MUST be a theorem"

#### Task 2.1: Review Paper Derivation
**File**: `Logic_Realism_Theory_Main.md` Section 5.3
**Action**: Extract the derivation logic
- Identity constraint + continuous transformations → time parameter
- How does constraint enforcement require ordering?
- Connection to Stone's theorem (unitary groups)

**Effort**: 4-6 hours
**Owner**: Sprint 13 Track 2

#### Task 2.2: Formalize in Lean
**File**: `Derivations/TimeEmergence.lean`

**Current**:
```lean
axiom time_emergence_from_identity :
  "Time emerges from Identity constraint"
```

**Target**:
```lean
theorem time_emergence_from_identity :
  IdentityConstraint → ∃ (t : ℝ), ContinuousEvolution t := by
  -- Proof steps:
  -- 1. Identity requires continuous state preservation
  -- 2. Continuous preservation → parameter family
  -- 3. Parameter family + reversibility → time
  sorry -- Initial implementation
```

**Effort**: 12-20 hours
**Owner**: Sprint 13 Track 2
**Risk**: Medium - May require additional lemmas

**Track 2 Result**: -1 axiom if successful, major credibility boost

---

### Track 3: Formalize Born Rule Derivation (Priority 3, Week 2)

**Objective**: Convert `axiom born_rule_from_measurement` to `theorem`

#### Background
- Main.md Section 5.1 derives Born rule from MaxEnt + Non-Contradiction
- Currently 3+ axioms related to Born rule
- This is a KEY claim of LRT superiority

#### Task 3.1: Review Paper Derivation
**File**: `Logic_Realism_Theory_Main.md` Section 5.1
**Action**: Extract MaxEnt + consistency → |⟨ψ|φ⟩|² derivation
- MaxEnt on constraint-preserving distributions
- Non-Contradiction constraint
- Geometric projection interpretation

**Effort**: 6-8 hours
**Owner**: Sprint 13 Track 3

#### Task 3.2: Formalize MaxEnt Framework
**File**: `Measurement/MaxEntBornRule.lean` (new file)

**Structure**:
```lean
-- Maximum entropy principle
axiom maxent_principle :
  ConstrainedDistribution → MaximizeEntropy

-- Non-contradiction constraint
axiom consistency_constraint :
  MeasurementOutcome → NoContradiction

-- Derivation
theorem born_rule_from_maxent_consistency :
  maxent_principle → consistency_constraint →
  ∀ ψ φ, P(ψ→φ) = |⟨ψ|φ⟩|² := by
  -- Multi-step proof
  sorry -- Initial implementation
```

**Effort**: 16-24 hours
**Owner**: Sprint 13 Track 3
**Risk**: High - Complex derivation

**Track 3 Result**: -3 to -5 axioms if successful (Born rule + related)

---

### Track 4: Documentation and Framing (Priority 4, Week 2)

**Objective**: Update all documentation with Option C framing

#### Task 4.1: Create Axiom Roadmap Document
**File**: `lean/AXIOM_ROADMAP.md` (new)

**Content**:
```markdown
# LRT Axiom Reduction Roadmap

## Current State (Post-Sprint 13)
- Theory axioms: ~20-25 (excluding mathematical infrastructure)
- Mathematical infrastructure: 16 (Stone's, spectral, etc.)
- Status: In progress toward minimal core

## Core Ontological Axioms (Target: 2-3)
1. Infinite Information Space I exists
2. I is infinite
3. Actualization A = L(I) reduces entropy

## Derivation Status

### Formalized (Theorems)
- ✓ Time emergence from Identity (Sprint 13)
- ✓ Born rule from MaxEnt + consistency (Sprint 13)
- [ ] Hilbert space from constraint geometry (Sprint 14)
- [ ] Complex numbers from phase + compositionality (Sprint 14)
- [ ] Observables as Hermitian operators (Sprint 14)

### Currently Postulated (To Be Derived)
- Measurement dynamics (15 axioms → reduce to 5-8)
- Some constraint properties

## Comparison to Other QM Reconstructions
[Table comparing Hardy, Chiribella, Dakic, LRT]

## Timeline
- Sprint 13 (current): 30-34 → 20-25 theory axioms
- Sprint 14: 20-25 → 12-15 theory axioms
- Sprint 15: 12-15 → 5-8 theory axioms (+ 2-3 core)
```

**Effort**: 6-8 hours
**Owner**: Sprint 13 Track 4

#### Task 4.2: Update Main.md Section 7
**File**: `Logic_Realism_Theory_Main.md`

**Current Section 7.4** (outdated):
- Claims "~7 axioms" (actually 57)
- Incomplete status

**New Section 7.4 - Option C Framing**:
```markdown
## 7.4 Formal Verification Status

### Overview
Logic Realism Theory has been formalized in Lean 4 with rigorous gap accounting.
The formalization is work-in-progress toward a minimal core of 2-3 ontological axioms.

### Current Axiom Count (Post-Sprint 13)
**Total declarations**: 48 (reduced from 57)
- Mathematical infrastructure: 16 (Stone's theorem, spectral theorem, etc.)
  - *Note: Not counted as LRT axioms - same infrastructure used by all QM theories*
- LRT theory axioms: ~20-25
  - Core ontological: 2-3 (I exists, I infinite, A = L(I))
  - Derived structures: 5-8 (formalized as theorems)
  - Measurement dynamics: 10-12 (reduction in progress)

### Formalized Derivations
LRT derives key QM structures that other reconstructions postulate:
- ✓ **Time emergence**: Proven from Identity constraint (TimeEmergence.lean)
- ✓ **Born rule**: Proven from MaxEnt + Non-Contradiction (MaxEntBornRule.lean)
- ⧗ **Hilbert space**: Derivation in progress (target: Sprint 14)
- ⧗ **Complex field**: Derivation in progress (target: Sprint 14)

### Comparison to QM Reconstruction Programs
| Program | Core Axioms | What They Derive |
|---------|-------------|------------------|
| Hardy (2001) | 5 | QM formalism |
| Chiribella et al. (2011) | 6 | QM formalism |
| Dakic-Brukner (2009) | 3-4 | QM formalism |
| **LRT (target)** | **2-3** | **QM formalism + why QM** |
| **LRT (current)** | **20-25** | *Reduction in progress* |

### Roadmap
Full derivation roadmap: See `lean/AXIOM_ROADMAP.md`
- Sprint 13: Formalize time emergence, Born rule
- Sprint 14: Formalize Hilbert space, complex field, observables
- Sprint 15: Consolidate measurement dynamics

### Mathematical Infrastructure (K_math)
LRT uses 16 standard mathematical results:
- Stone's theorem (1932)
- Spectral theorem (finite dimensions in Mathlib)
- Spohn's inequality
- Complex field algebraic properties
- Binary entropy bounds

*All have published proofs; marked as axioms in Lean pending Mathlib coverage*

### Build Status
- Total files: 20 active
- Total lines: 5,288
- Sorry count: 4 (Jordan-von Neumann, 3 measurement properties)
- Build: ✓ All files compile successfully
```

**Effort**: 8-10 hours
**Owner**: Sprint 13 Track 4

#### Task 4.3: Update LogicRealismTheory.lean Build Status
**File**: `LogicRealismTheory.lean`

Update comment block with Option C framing:
```lean
-- Gap analysis (see lean/AXIOM_ROADMAP.md):
--   Theory axioms (current): ~20-25 (reduction in progress)
--   Mathematical infrastructure: 16 (K_math - not counted as LRT axioms)
--   Target: 2-3 core ontological axioms + derivations
--   Status: See lean/AXIOM_ROADMAP.md for detailed roadmap
```

**Effort**: 1-2 hours
**Owner**: Sprint 13 Track 4

#### Task 4.4: Create Comparison Table Document
**File**: `theory/QM_Reconstruction_Comparison.md` (new)

**Content**: Detailed comparison with Hardy, Chiribella, Dakic-Brukner
- Axiom counts
- What each derives vs. postulates
- Mathematical infrastructure used
- LRT's position: more ambitious (derives more) but honest about current state

**Effort**: 4-6 hours
**Owner**: Sprint 13 Track 4

**Track 4 Result**: Complete Option C framing documentation

---

## Sprint 13 Schedule

### Week 1: Quick Wins + Time Emergence
- **Days 1-2**: Track 1 (reclassification, -9 axioms)
- **Days 3-5**: Track 2 (time emergence formalization)

### Week 2: Born Rule + Documentation
- **Days 1-3**: Track 3 (Born rule formalization)
- **Days 4-5**: Track 4 (documentation updates)

---

## Sprint 13 Deliverables

1. ✓ Reduced axiom count: 57 → ~48 declarations, 30-34 → 20-25 theory
2. ✓ Computational helpers converted to definitions (4 axioms)
3. ✓ Placeholders removed (5 axioms)
4. ✓ Time emergence formalized as theorem (1 axiom → theorem)
5. ✓ Born rule formalized as theorem (3-5 axioms → theorem)
6. ✓ `lean/AXIOM_ROADMAP.md` created
7. ✓ Main.md Section 7.4 updated with Option C framing
8. ✓ `theory/QM_Reconstruction_Comparison.md` created
9. ✓ All documentation honest and defensible

---

## Success Criteria

**Minimum (Sprint 13 Complete)**:
- [ ] Axiom count ≤ 48 (theory ≤ 25)
- [ ] All computational helpers are definitions
- [ ] All placeholders removed
- [ ] Time emergence OR Born rule formalized
- [ ] Main.md updated with Option C framing
- [ ] Roadmap document complete

**Stretch (Strong Progress)**:
- [ ] Both time emergence AND Born rule formalized
- [ ] Axiom count ≤ 45 (theory ≤ 22)
- [ ] QM comparison document complete
- [ ] All documentation peer-review ready

---

## Risk Analysis

**Risk 1: Derivations Too Complex for 2-Week Timeline**
- **Likelihood**: Medium-High
- **Impact**: Medium (can defer to Sprint 14)
- **Mitigation**: Start with skeleton proofs (sorry placeholders), document derivation logic

**Risk 2: Some "Axioms" Can't Actually Be Converted to Definitions**
- **Likelihood**: Low
- **Impact**: Low (adjust count, document why)
- **Mitigation**: Careful review before conversion

**Risk 3: Born Rule Derivation Has Gaps**
- **Likelihood**: Medium
- **Impact**: High (major LRT claim)
- **Mitigation**: Consult LLM team on derivation viability before formalizing

---

## Sprint 13 vs. Sprint 14-15

**Sprint 13 (this plan)**: Establish Option C framing, quick wins, begin derivations
**Sprint 14** (future): Formalize Hilbert space, complex field, observables
**Sprint 15** (future): Consolidate measurement dynamics, reach 5-8 + (2-3 core)

---

**Created**: 2025-11-03
**Status**: Ready to start after Sprint 12
**Dependencies**: Sprint 12 (sorrys eliminated, basic cleanup done)
**Next**: Sprint 14 (Hilbert space + complex field derivations)
