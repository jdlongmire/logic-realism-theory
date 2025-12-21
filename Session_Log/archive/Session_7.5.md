# Session 7.5 - Axiom Framing Strategy and Documentation Cleanup

**Date**: 2025-11-03
**Session Type**: Strategic Planning + Documentation Cleanup
**Status**: Complete

---

## Session Overview

This session focused on establishing the correct axiom count framing strategy for LRT (Option C) based on LLM team consultation, cleaning up documentation, and preparing comprehensive sprint plans for axiom reduction.

---

## Major Accomplishments

### 1. Layer 3 File Consolidation ✓
**Issue**: Inconsistent naming with "Track" prefix on Layer 3 files
**Resolution**: Consolidated to simple descriptive names
- Removed Track prefix from 5 Layer 3 files (InnerProduct, HilbertSpace, TensorProducts, UnitaryOperators, HermitianOperators)
- Updated all imports in affected files
- Deleted old InnerProduct.lean placeholder
- All files build successfully (6008 jobs)

### 2. Axiom Count Strategic Analysis ✓
**Critical Discovery**: Major discrepancy between claimed and actual axiom counts
- Main.md Section 7 claimed "~7 axioms"
- Actual count: 57 declarations (30-34 theory + 16 infrastructure + bugs)
- Compared to other QM reconstructions (Hardy: 5, Chiribella: 6, Dakic: 3-4)

**Key Question**: Should LRT claim 2-3 core axioms or be honest about 30-34 current count?

### 3. LLM Team Consultation ✓
**Consultation**: `lrt_axiom_framing_strategy_20251103.txt`
**Team Response**: Unanimous recommendation for **Option C - Staged Approach**

**Quality Scores**:
- Grok: 0.70 (detailed analysis, recommended Option C)
- Gemini: 0.55 (strong practical advice, recommended Option C)
- ChatGPT: 0.41 (conservative, recommended Option B→C)

**Consensus**:
- ❌ Option A (Bold 2-3 axioms): Too risky without formalized derivations
- ❌ Option B (Honest 20-25): Safe but less competitive
- ✅ **Option C (Staged)**: Honest about current 30-34, clear path to 7-11

### 4. Option C Roadmap Created ✓
**Documents Created**:
- `sprints/SPRINT_13_PLAN.md` - Phase 1: Quick wins + key derivations (2 weeks)
- `sprints/SPRINT_14_PLAN.md` - Phase 2: Structural derivations (2-3 weeks)
- `sprints/SPRINT_15_PLAN.md` - Phase 3: Measurement consolidation (2-3 weeks)
- `lean/LRT_Comprehensive_Lean_Plan.md` - Complete overview (moved from sprints/)

**Axiom Reduction Journey**:
```
Current:  57 declarations (30-34 theory + 16 infrastructure + 9 bugs)
Sprint 13: 48 declarations (20-25 theory + 16 infrastructure)
Sprint 14: 40-42 declarations (12-15 theory + 16 infrastructure)
Sprint 15: 35-38 declarations (7-11 theory + 16 infrastructure)
```

**Target**: 2-3 core ontological axioms + 5-8 additional theory axioms

### 5. Lean Folder Cleanup ✓
**Archived** (to `lean/archive/session_docs/`):
- LLM_CONSULTATION_BRIEF_Measurement_Refactoring.md
- MEASUREMENT_REFACTORING_NOTES.md
- REFACTORING_DECISION_20251030.md

**Deleted** (no archival value):
- build_output.log, build_output.txt, build_output_after_fix.log (3 build logs)
- AXIOMS.md (superseded by comprehensive classification)
- DEVELOPMENT.md (superseded by comprehensive plan)

**Result**: Clean lean folder with only current documentation

### 6. Axiom Count Framing Documentation ✓
**Added prominent section to `lean/Ongoing_Axiom_Count_Classification.md`**:
- ⚠️ **AXIOM COUNT FRAMING (Always Use This)**
- ❌ NOT "57 axioms" or "58 axioms"
- ✅ USE "30-34 theory axioms (current), target 7-11"
- ✅ Separate K_math (16) as mathematical infrastructure

**Why this matters**:
- K_math = standard results (Stone's, spectral theorems) ALL QM uses
- Other programs don't count infrastructure as "theory axioms"
- Honest comparison: LRT theory (30-34 → 7-11) vs. their theory (3-6)

### 7. CLAUDE.md Restructuring ✓
**Major Rewrite**: 718 lines → 103 lines (85% reduction)

**New Structure**:
- **Section 1: Critical Artifacts** - All documents to reference
- **Section 2: Critical Protocols** - Essential procedures

**Key Improvements**:
- Axiom framing moved to source documents (no duplication)
- Session startup order fixed (session log first, then relevant guides)
- Git commit protocol corrected (incremental commits naturally)
- README update requirement added for major sessions
- Removed stale specific numbers (points to current sources)
- Lean, scannable, evergreen

### 8. Documentation Updates ✓
**Files Updated**:
- `lean/LogicRealismTheory.lean` - Added Layer 3 imports, updated build status
- `lean/Main.lean` - Added documentation pointing to actual source code
- `lean/Ongoing_Axiom_Count_Classification.md` - Added axiom count framing section
- `CLAUDE.md` - Completely restructured (85% reduction)

---

## Key Decisions Made

### Decision 1: Option C - Staged Approach
**Rationale**: LLM team unanimous recommendation
- Honest about current state (30-34 theory axioms)
- Clear roadmap to 7-11 theory axioms (2-3 core + 5-8 additional)
- Competitive with Hardy/Chiribella/Dakic while more ambitious
- Peer-review defensible

### Decision 2: Axiom Count Framing
**Framing**: Always separate theory axioms from mathematical infrastructure
- **NOT**: "57 axioms"
- **USE**: "30-34 theory axioms (current), target 7-11"
- **Infrastructure**: 16 K_math axioms (same as all QM uses)

### Decision 3: Sprint Plan Scope
**Timeline**: 6-8 weeks (3 sprints)
**Effort**: ~205-301 hours total
**Feasibility**: Achievable with honest assessment of risks

---

## Files Created/Modified

### Created (7 new files)
1. `sprints/SPRINT_13_PLAN.md` - Option C Phase 1
2. `sprints/SPRINT_14_PLAN.md` - Option C Phase 2
3. `sprints/SPRINT_15_PLAN.md` - Option C Phase 3
4. `lean/LRT_Comprehensive_Lean_Plan.md` - Complete roadmap
5. `lean/archive/session_docs/` - New archive directory
6. `multi_LLM/consultation/lrt_axiom_framing_strategy_20251103.txt` - Team consultation
7. `Session_Log/Session_7.5.md` - This session log

### Modified (4 files)
1. `lean/LogicRealismTheory.lean` - Layer 3 imports + build status
2. `lean/Main.lean` - Documentation comments
3. `lean/Ongoing_Axiom_Count_Classification.md` - Axiom count framing section
4. `CLAUDE.md` - Complete restructure (718 → 103 lines)

### Renamed (6 files)
1. `Track1_9_InnerProduct.lean` → `InnerProduct.lean`
2. `Track1_10_HilbertSpace.lean` → `HilbertSpace.lean`
3. `Track1_11_TensorProducts.lean` → `TensorProducts.lean`
4. `Track1_12_UnitaryOperators.lean` → `UnitaryOperators.lean`
5. `Track1_13_HermitianOperators.lean` → `HermitianOperators.lean`
6. `OPTION_C_ROADMAP_SUMMARY.md` → `LRT_Comprehensive_Lean_Plan.md` (also moved sprints/ → lean/)

### Deleted (8 files)
1. Old `InnerProduct.lean` (47 lines, placeholder)
2. `build_output.log` (build log)
3. `build_output.txt` (build log)
4. `build_output_after_fix.log` (build log)
5. `AXIOMS.md` (superseded)
6. `DEVELOPMENT.md` (superseded)
7. Old `Track1_9_InnerProduct.lean` (replaced)
8. `CLAUDE_LEAN.md` (became CLAUDE.md)

### Archived (3 files)
1. `LLM_CONSULTATION_BRIEF_Measurement_Refactoring.md` → `archive/session_docs/`
2. `MEASUREMENT_REFACTORING_NOTES.md` → `archive/session_docs/`
3. `REFACTORING_DECISION_20251030.md` → `archive/session_docs/`

---

## Git Activity

**Commits Made**: 8
1. Consolidate Layer 3 files: Remove Track prefix
2. Update LogicRealismTheory.lean: Add Layer 3 imports
3. Add documentation comments to Main.lean
4. Create Option C implementation roadmap (Sprints 13-15)
5. Move and rename roadmap to lean folder
6. Clean up lean root folder: Archive + delete
7. Add Lean formalization status to CLAUDE.md
8. Replace CLAUDE.md with lean restructured version

**All commits pushed to GitHub** ✓

---

## Current Status

### Lean Formalization
- **Total files**: 20 active (1 deprecated)
- **Total lines**: 5,288
- **Sorry count**: 4
- **Axiom count**: 57 declarations
  - K_math: 16 (infrastructure)
  - Theory: 30-34 (target: 7-11)
- **Build**: ✓ All files compile successfully

### Documentation
- ✓ CLAUDE.md restructured (lean, evergreen)
- ✓ Axiom count framing documented
- ✓ Option C roadmap complete (Sprints 13-15)
- ✓ Lean folder cleaned up
- ✓ All references updated

### Next Priorities
1. **Sprint 12** (if needed): Eliminate sorrys, reduce basic axiom count
2. **Sprint 13**: Quick wins + time emergence + Born rule derivations
3. **Sprint 14**: Hilbert space + complex field + observables derivations
4. **Sprint 15**: Measurement consolidation → final 7-11 theory axioms

---

## Key Insights

### 1. Axiom Counting is a Framing Problem
**Discovery**: Different counting methods yield wildly different numbers
- Raw declarations: 57
- Theory-only: 30-34
- After reduction: 7-11 (2-3 core + 5-8 additional)
- Honest comparison requires separating infrastructure from theory

### 2. LLM Team Provides Valuable Strategic Input
**Value**: Independent multi-model consensus prevents overclaiming
- All 3 LLMs independently recommended Option C
- Prevented potential Option A (2-3 axioms) overreach without proofs
- Validated transparent, staged approach

### 3. Documentation Debt Accumulates Fast
**Observation**: Old CLAUDE.md had 718 lines, much outdated
- 85% reduction possible by pointing to source docs instead of duplicating
- Static content > dynamic content in protocol documents
- Regular cleanup prevents information fragmentation

### 4. Honest Assessment > Aggressive Claims
**Principle**: Better to be honest about 30-34 axioms with clear path to 7-11 than to claim 2-3 without proofs
- Peer reviewers WILL check the Lean code
- GitHub makes all axiom declarations public
- Transparency builds credibility

---

## Lessons Learned

### What Worked Well
1. **LLM team consultation** - Provided independent validation of strategy
2. **Structured sprint planning** - Clear 3-sprint roadmap with effort estimates
3. **Documentation consolidation** - Eliminated duplication, established sources of truth
4. **File naming cleanup** - Simple descriptive names > Track prefix
5. **Progressive commits** - Regular commits prevented context loss

### What to Improve
1. **Earlier axiom audits** - Discrepancy (7 vs 57) should have been caught sooner
2. **Documentation maintenance** - Need regular cleanup to prevent 700+ line files
3. **Framing consistency** - Should have established axiom count language earlier

---

## Next Session Priorities

### Immediate (Sprint 12 or 13)
1. Decide: Sprint 12 (basic cleanup) or jump to Sprint 13 (Option C Phase 1)?
2. If Sprint 13:
   - Remove 5 placeholder axioms
   - Convert 4 computational helpers to definitions
   - Begin time emergence formalization
   - Begin Born rule formalization

### Strategic
1. Execute Option C roadmap (Sprints 13-15)
2. Update Main.md Section 7 with honest axiom accounting
3. Prepare peer review documentation
4. Continue LLM team consultations for complex derivations

---

## References

### Documents Created This Session
- `lean/LRT_Comprehensive_Lean_Plan.md` - Complete Option C roadmap
- `sprints/SPRINT_13_PLAN.md` - Phase 1 plan
- `sprints/SPRINT_14_PLAN.md` - Phase 2 plan
- `sprints/SPRINT_15_PLAN.md` - Phase 3 plan

### Key Consultation
- `multi_LLM/consultation/lrt_axiom_framing_strategy_20251103.txt`
- Team quality scores: Grok 0.70, Gemini 0.55, ChatGPT 0.41
- Unanimous recommendation: Option C

### Updated Documentation
- `CLAUDE.md` - Restructured, 85% reduction
- `lean/Ongoing_Axiom_Count_Classification.md` - Added framing section
- `lean/LogicRealismTheory.lean` - Layer 3 complete
- `lean/Main.lean` - Documentation added

---

## Session Statistics

**Duration**: Full session
**Commits**: 8
**Files created**: 7
**Files modified**: 4
**Files renamed**: 6
**Files deleted**: 8
**Files archived**: 3
**Lines added**: ~2,000+
**Lines removed**: ~1,000+
**Net documentation**: Leaner, clearer, more maintainable

---

**Session 7.5 Complete**
**Status**: All commits pushed to GitHub ✓
**Next**: Start new session following updated CLAUDE.md protocol
**Ready for**: Sprint 13 (Option C Phase 1) or Sprint 12 (if basic cleanup needed first)
