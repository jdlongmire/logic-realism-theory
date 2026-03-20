# Sprint 14.3: Type B Axiom Elimination

**Sprint Goal**: Systematically prove all remaining Type B axioms (provable with moderate effort, 1-2 hours each)

**Starting Count**: 134 axioms
**Target Reduction**: ~10-15 axioms (Type B axioms identified)
**Target Count**: 119-124 axioms

**Sprint Duration**: Continue until complete (estimated 15-25 hours)

---

## Type B Axiom Inventory

### ConstraintAccumulation.lean (3 axioms) ⚠️ HIGH PRIORITY

**Status**: Module has been partially worked (4/7 axioms proved)

1. **mvt_for_constraint** (Line 409)
   - Type: Mean Value Theorem application
   - Difficulty: Low (Mathlib has `exists_hasDerivAt_eq_slope`)
   - Estimate: 30 minutes
   - Strategy: Find correct Mathlib theorem name and apply

2. **visibility_small_epsilon** (Line 375)
   - Type: Taylor series approximation
   - Difficulty: Moderate
   - Estimate: 1-2 hours
   - Strategy: Use `Real.abs_exp_sub_one_sub_id_le` + algebraic manipulation

3. **chsh_quantum_limit** (Line 707)
   - Type: Small parameter analysis
   - Difficulty: Moderate
   - Estimate: 1-2 hours
   - Strategy: Taylor expansion of C(ε) for small ε, bound calculation

### BornRuleNonCircularity.lean (6-8 axioms) ⚠️ MEDIUM PRIORITY

**Status**: Needs assessment - some may be Type B, others Type C

**Definitely Type B**:

4. **left_multiplication_is_permutation_matrix** (Line 495)
   - Type: Linear algebra (permutation matrices)
   - Difficulty: Low-Moderate
   - Estimate: 1 hour
   - Strategy: Show left multiplication by group element → permutation matrix

5. **permutation_matrix_is_unitary** (Line 526)
   - Type: Linear algebra property
   - Difficulty: Low
   - Estimate: 30 minutes
   - Strategy: Permutation matrices are orthogonal → unitary

**Potentially Type B** (need assessment):

6. **kendall_tau_is_metric** (Line 164)
   - Type: Metric axioms (symmetry, triangle inequality, etc.)
   - Difficulty: Moderate-High
   - Estimate: 2-3 hours
   - Assessment needed: Check if triangle inequality is provable

7. **distance_preserving_iff_automorphism** (Line 219)
   - Type: Group automorphism theory
   - Difficulty: Moderate-High
   - Estimate: 2-3 hours
   - Assessment needed: May require representation theory

8. **left_multiplication_preserves_distance** (Line 281)
   - Type: Group action on metric space
   - Difficulty: Moderate
   - Estimate: 1-2 hours
   - Strategy: Show distance is Cayley graph metric (invariant under left mult)

9. **left_multiplication_preserves_entropy** (Line 309)
   - Type: Entropy invariance
   - Difficulty: High (may be Type C)
   - Estimate: 3-4 hours or Type C
   - Assessment needed: Check if provable or requires additional structure

### ConstraintThreshold.lean (1 axiom) ⚠️ LOW PRIORITY

10. **inversion_count_equals_word_length** (Line 237)
    - Type: Coxeter group theory (standard result)
    - Difficulty: Moderate-High
    - Estimate: 2-3 hours
    - Note: This is a well-known theorem in Coxeter group theory
    - Assessment: May be Type C (literature result)

---

## Confirmed Type C Axioms (Strategic/Foundational)

These are **NOT** in scope for this sprint:

### Dynamics Module (18 axioms)
- All Fisher geometry, convergence theorem, quantum dynamics axioms
- Literature-supported (Caticha, Belkin & Niyogi, Braunstein & Caves)

### Foundations Module (5 axioms)
- Three Fundamental Laws (3)
- Information space axioms (2)

### QuantumEmergence Module (~80 axioms)
- Hilbert space projection lattice (~27)
- Born rule & Gleason's theorem (~17)
- Measurement mechanism (~22)
- Bell inequality (~3)

### LogicField/Operator (5 axioms)
- Logic field decomposition (foundational)

### Indistinguishability (14 axioms)
- Operator algebras (bosonic/fermionic CCR/CAR)
- Philosophical axioms (3FLL epistemic)

### LogicRealism (7 axioms)
- Orthomodular lattice, Gleason, non-distributivity

---

## Sprint Execution Plan

### Phase 1: Quick Wins (Est. 2-3 hours)
1. mvt_for_constraint ✓ (Mathlib lookup)
2. left_multiplication_is_permutation_matrix ✓
3. permutation_matrix_is_unitary ✓

### Phase 2: Moderate Difficulty (Est. 4-6 hours)
4. visibility_small_epsilon ✓ (Taylor series)
5. chsh_quantum_limit ✓ (small parameter)
6. left_multiplication_preserves_distance ✓

### Phase 3: Assessment & High Difficulty (Est. 8-12 hours)
7. kendall_tau_is_metric (assess triangle inequality)
8. distance_preserving_iff_automorphism (assess complexity)
9. left_multiplication_preserves_entropy (assess Type B vs C)
10. inversion_count_equals_word_length (assess Coxeter theory)

### Phase 4: Documentation & Commit
- Update axiom count tracking
- Document which axioms were proved vs reclassified as Type C
- Final commit with comprehensive session summary

---

## Success Metrics

**Minimum Success**: 5 axioms proved (134 → 129)
**Target Success**: 10 axioms proved (134 → 124)
**Stretch Goal**: 15 axioms proved (134 → 119)

**Quality Requirements**:
- All proofs build successfully
- Proofs are well-documented with strategy comments
- No regressions in existing code
- Clear commit messages for each axiom

---

## Risk Mitigation

**Risk**: Some "Type B" axioms turn out to be Type C
**Mitigation**: Quick assessment phase before diving deep. If >2 hours with no progress, reclassify as Type C and document.

**Risk**: Mathlib API changes or missing theorems
**Mitigation**: Search Mathlib docs, use `exact?` tactic, consult Zulip if stuck >30 minutes

**Risk**: Proof complexity explodes
**Mitigation**: Break into lemmas, use `sorry` to outline proof structure first, then fill in

---

## Current Status (Session 1 - ~2 hours)

**Phase**: Assessment Complete, Pivoting Strategy
**Axioms Proved**: 0 (reassessment phase)
**Current Count**: 138 axioms (recount shows higher than initial estimate)
**Build Status**: ✅ Succeeds

### Session 1 Findings

**Type B → Type C Reclassifications** (Infrastructure Complexity):

1. **mvt_for_constraint** (ConstraintAccumulation.lean:409)
   - **Status**: Reclassified Type B → Type C
   - **Reason**: Mathlib MVT API complexity exceeds initial estimate
   - **Issues Encountered**:
     - Theorem name ambiguity (exists_hasDerivAt_eq_slope vs exists_deriv_eq_slope)
     - Hypothesis mismatch (axiom lacks ε > 0 requirement)
     - Predicate conversion challenges (HasDerivAt ↔ HasDerivWithinAt ↔ deriv)
   - **Time Investment**: 1 hour
   - **Revised Estimate**: 2-3 hours with careful Mathlib exploration

2. **left_multiplication_is_permutation_matrix** (BornRuleNonCircularity.lean:495)
   - **Status**: Deferred (needs infrastructure work)
   - **Reason**: Requires linear algebra infrastructure for TransformationMatrix

3. **permutation_matrix_is_unitary** (BornRuleNonCircularity.lean:526)
   - **Status**: Deferred (axiom malformed)
   - **Reason**: Current statement claims ALL transformations are unitary (incorrect)
   - **Action Needed**: Fix axiom statement before attempting proof

**Phase 2 Axioms** (Assessment):
- visibility_small_epsilon: Taylor series + exponential bounds (Type B/C boundary)
- chsh_quantum_limit: Small parameter analysis (Type B/C boundary)
- Both require substantial Mathlib infrastructure for inequality bounds

### Key Insights

1. **Type B Classification Too Optimistic**: Many "moderate complexity" axioms have hidden infrastructure barriers
2. **Mathlib API Learning Curve**: Time investment in API exploration exceeds proof time
3. **Strategic Pivot Needed**: Focus on axioms with clearer proof paths or accept Type C classification

### Recommendations

**Short Term** (This Sprint):
- Focus on axioms with computational validation and clear literature support
- Accept some axioms as strategically justified rather than proved
- Prioritize axiom reduction in modules with highest axiom density

**Medium Term** (Next Sprints):
- Dedicated Mathlib infrastructure learning phase
- Team consultation on proof strategies for complex axioms
- Consider alternative proof approaches (computational reflection, decision procedures)

**Next Task**: Strategic reassessment - identify genuinely provable Type B axioms or pivot to documentation/validation
