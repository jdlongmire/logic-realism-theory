# ISSUE 007: All-Work Survey Findings

**Created**: 2025-12-02 (Session 36.0)
**Status**: OPEN
**Priority**: HIGH (multiple actionable items)
**Source**: Comprehensive survey of ~392 files across 5 folders

---

## Summary

Session 36.0 conducted a comprehensive survey of all past and archived work to identify overlooked nuggets and ideas. This issue tracks the findings and action items for resurrection.

**Survey Scope**:
- theory/ (121 files)
- lean/ (28 files)
- notebooks/ (31 files)
- approach_2_reference/ (202 files)
- archive/ (10 files)

**Full Details**: `theory/all-work-survey.md`

---

## Critical Findings

### 1. Incorrectly Archived Documents

Two documents were archived but should be active:

| Document | Location | Action |
|----------|----------|--------|
| COMPUTATIONAL_VALIDATION_SPRINT.md | archive/ | Move to sprints/ |
| LRT_Current_Comparison_Scorecard.md | archive/ | Move to theory/ or root |

**Status**: PENDING

---

### 2. Phase 4 Mechanism Gap (CRITICAL)

**Location**: `theory/derivations/Measurement_to_K_enforcement_Derivation.md`

**Issue**: Phase 4 (stabilization) mechanism is UNKNOWN. Could scale as:
- beta (information spreading)
- beta^2 (thermalization)
- beta^3 (higher-order process)

**Impact**: Changes K_enforcement predictions by ~15%, affects T2/T1 ratio

**Action**: Research and formalize 4 candidate mechanisms:
1. Quantum Zeno effect
2. Information spreading
3. Heat flow / thermalization
4. Landauer erasure

**Status**: OPEN - Research needed

---

### 3. Lean Formalization Gaps

**Current Status**:
- Structure: ~85% complete
- Proofs: ~15% complete
- Sorry count: 55 across 7 files

**Quick Wins** (can be completed in single session):

| File | Sorry Count | Effort | Impact |
|------|-------------|--------|--------|
| TimeEmergence.lean | 1 | 30 min | Core theorem unlocked |
| NonUnitaryEvolution.lean | 6 | 1.5-2 hrs | Peer review objection resolved |
| Energy.lean | 5 | 2-3 hrs | Energy derivation complete |

**Blocker**: Universe polymorphism in TimeEmergence.lean line 338
- **Fix**: Refactor stones_theorem axiom (remove existentials)

**Orphaned Files** (not imported, need decision):
- GeometricStructure.lean (220 lines)
- EMRelaxation.lean (297 lines)
- VectorSpaceStructure.lean (352 lines)

**Status**: OPEN - Multiple sub-tasks

---

### 4. Transferable Proofs from Earlier Framework

**Source**: approach_2_reference/lean/

| Component | Lines | Sorry | Action |
|-----------|-------|-------|--------|
| MeasurementMechanism.lean | 302 | 0 | Port to current lean/ |
| Born rule theorem | ~50 | 0 | Port to current lean/ |
| K=0 classical emergence | ~20 | 0 | Reference in paper |
| ConstraintAccumulation.lean | 821 | 0 | Adapt for current framework |

**Status**: OPEN - Import tasks

---

### 5. Overlooked Paper Content

**Ideas not in current papers**:

| Idea | Source | Target |
|------|--------|--------|
| Consciousness framework (dual-access) | LRT_Metaphysical_Architecture.md | Philosophy paper |
| Fractal decoherence mechanism | LRT_Hierarchical_Emergence_Framework.md | Main paper |
| Landauer floor prediction | V3_Branch2_Synthesis_Analysis.md | Predictions section |
| "Energy as work of instantiation" | Branch-2 synthesis | Intuitive framing |

**Status**: OPEN - Integration tasks

---

### 6. Equal Phase Weighting Derivation

**Current Status**: ~30% derived (symmetry + parsimony arguments only)

**Issue**: Coupling theory does NOT predict equal weighting
- K_ID scales as 1/beta^2
- K_EM scales as (ln 2)/beta
- Different physical processes have different coupling orders

**Impact**: ~15% uncertainty in overall model

**Action**: Either:
1. Strengthen derivation with additional arguments
2. Accept as phenomenological with sensitivity analysis

**Status**: OPEN - Decision needed

---

## Action Items by Priority

### Immediate (This Week)

- [ ] Move COMPUTATIONAL_VALIDATION_SPRINT.md to sprints/
- [ ] Move LRT_Current_Comparison_Scorecard.md to theory/
- [ ] Fix TimeEmergence.lean universe polymorphism (30 min)

### Short-Term (1-2 Weeks)

- [ ] Complete NonUnitaryEvolution.lean proofs (1.5-2 hrs)
- [ ] Complete Energy.lean derivation proofs (2-3 hrs)
- [ ] Import measurement structure from approach_2
- [ ] Decide on orphaned Lean files (archive or integrate)
- [ ] Execute Path3_T1_vs_T2_QuTiP_Validation.ipynb

### Medium-Term (2-4 Weeks)

- [ ] Research Phase 4 stabilization mechanism
- [ ] Strengthen parallelogram law derivation
- [ ] Extract consciousness framework for philosophy paper
- [ ] Integrate fractal decoherence into main paper
- [ ] Decide on equal weighting: derive or accept phenomenological

### Research Questions

- [ ] Phase 4 mechanism: What physical process?
- [ ] State-dependent K: How does |psi> map to K for qubits?
- [ ] Beta origin: Derivable from bath properties + IIS?
- [ ] K(d) generalization: Extend K(N)=N-2 to Hilbert spaces?

---

## Acceptance Criteria

This issue can be closed when:

1. [ ] All incorrectly archived documents moved to correct locations
2. [ ] TimeEmergence.lean fix implemented
3. [ ] Decision made on Phase 4 mechanism (derive or document gap)
4. [ ] Decision made on equal weighting (derive or accept)
5. [ ] All high-priority Lean sorries resolved (TimeEmergence, NonUnitaryEvolution, Energy)
6. [ ] Key transferable proofs from approach_2 ported or documented as future work
7. [ ] Paper content gaps documented with integration plan

---

## Related Issues

- ISSUE 003: Lean 4 Formalization (PLANNED)
- ISSUE 005: Variational Framework (OPEN)
- ISSUE 006: Bit as Fundamental (OPEN)

---

## Session Log Reference

- Session 36.0: Survey conducted
- Full findings: `theory/all-work-survey.md`

---

*Created Session 36.0 - Tracking all-work survey action items*
