# Measurement Module Refactoring Notes

**Date**: 2025-10-30
**Session**: 5.2
**Status**: PLANNING (refactoring deferred for next session with LLM team)

---

## Problem Statement

We have three measurement-related Lean files with significant duplication:
- `Measurement/Common.lean` (169 lines, created Session 11.2)
- `Measurement/MeasurementGeometry.lean` (509 lines)
- `Measurement/NonUnitaryEvolution.lean` (216 lines)

**Current Build Status**:
- ✅ Common.lean: Not imported (orphaned)
- ✅ MeasurementGeometry.lean: Imported, builds successfully, 1 sorry
- ⚠️ NonUnitaryEvolution.lean: Commented out due to duplicate definitions with MeasurementGeometry

**Duplicate Definitions** (across modules):
1. `ConstraintViolations` axiom
2. `StateSpace` definition
3. `statespace_monotone` axiom
4. `MeasurementOperator` structure
5. `measurement_is_projection` axiom
6. `measurement_is_hermitian` axiom
7. `measurement_not_unitary` axiom
8. `wavefunction_collapse_normalized` axiom
9. `wavefunction_collapse_support` axiom
10. `wavefunction_collapse` definition
11. `measurement_probability` definition
12. `ConstraintAddition` structure

---

## Type Signature Mismatch (Root Cause)

**Common.lean approach** (low-level):
```lean
noncomputable def wavefunction_collapse {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post) (amplitude : V → ℂ) : V → ℂ
```
- Takes bare amplitude function `V → ℂ`
- Returns bare amplitude function `V → ℂ`

**MeasurementGeometry.lean approach** (high-level):
```lean
noncomputable def wavefunction_collapse {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
    (M : MeasurementOperator V K_pre K_post)
    (ψ_pre : PreMeasurementState V K_pre) : PostMeasurementState V K_post
```
- Takes structured `PreMeasurementState` (has `.amplitude`, `.normalized`, `.support`)
- Returns structured `PostMeasurementState`

**Issue**: Cannot directly replace high-level calls with low-level functions without wrapper conversions.

---

## Approach_2 Reference Architecture

From `approach_2_reference/lean/LFT_Proofs/PhysicalLogicFramework/`:

### Module Structure

```
Foundations/
  ├── InformationSpace.lean
  └── ConstraintThreshold.lean        # Defines StateSpace, ConstraintViolations

QuantumEmergence/
  ├── QuantumCore.lean
  └── MeasurementMechanism.lean       # ONE comprehensive measurement module
```

### Key Insight

**Approach_2 does NOT use a separate "Common.lean"**. Instead:
- Base definitions (StateSpace, ConstraintViolations) go in `Foundations/ConstraintThreshold.lean`
- ALL measurement logic consolidated in ONE module: `QuantumEmergence/MeasurementMechanism.lean`
- Uses high-level structured types (`PreMeasurementState`, `PostMeasurementState`)
- No duplication because there's only ONE measurement module

### Approach_2's MeasurementMechanism.lean

```lean
import PhysicalLogicFramework.Foundations.ConstraintThreshold
import PhysicalLogicFramework.QuantumEmergence.QuantumCore

namespace PhysicalLogicFramework.QuantumEmergence

-- Defines everything in ONE place:
structure MeasurementOperator (K_pre K_post : ℕ) where ...
structure PreMeasurementState (K : ℕ) where ...
structure PostMeasurementState (K : ℕ) where ...

def wavefunction_collapse ... : PostMeasurementState K_post := ...
def measurement_probability ... : ℝ := ...

-- No duplicates, no separate modules
```

---

## Attempted Refactoring (Session 5.2)

### Attempt 1: Automatic Refactoring

**Strategy**: Remove duplicates from MeasurementGeometry and NonUnitaryEvolution, have them import Common.lean

**Result**: ❌ FAILED
- Type signature mismatches (low-level `V → ℂ` vs high-level `PreMeasurementState`)
- Missing namespace declarations
- Missing variable declarations
- Function calls expecting different parameter types
- Build errors: ~10 compilation failures

**Scripts created** (for reference):
- `scripts/refactor_measurement_geometry.py` (removed 81 lines)
- `scripts/refactor_nonunitary_evolution.py` (removed 39 lines)
- `scripts/fix_measurement_calls.py` (attempted type fixes)

**Outcome**: Reverted all changes via `git checkout`

---

## Recommended Solution (For Next Session)

### Option A: Follow Approach_2 Pattern (RECOMMENDED)

**Strategy**: Consolidate everything into ONE comprehensive measurement module

1. **Move base definitions** to `Foundation/` module:
   - `ConstraintViolations` axiom
   - `StateSpace` definition
   - `statespace_monotone` axiom

2. **Create ONE measurement module** (choose one approach):
   - **Option A1**: Enhance `Measurement/MeasurementGeometry.lean` to be comprehensive
   - **Option A2**: Merge content into `Measurement/Common.lean` and rename to `Measurement/Mechanism.lean`

3. **Archive NonUnitaryEvolution.lean**:
   - Extract unique content (QuantumState, UnitaryOperator, unitary_preserves_K theorem)
   - Move to separate module if needed (e.g., `Measurement/UnitaryEvolution.lean`)
   - Or integrate into comprehensive module

4. **Result**: ONE import in `LogicRealismTheory.lean`:
   ```lean
   import LogicRealismTheory.Measurement.Mechanism
   ```

### Option B: Type-Safe Wrapper Approach

**Strategy**: Keep Common.lean with low-level functions, add high-level wrappers

1. **Common.lean**: Low-level functions (`V → ℂ` signatures)
2. **MeasurementGeometry.lean**: High-level wrappers calling Common.lean functions
3. **Wrapper pattern**:
   ```lean
   def wavefunction_collapse_hl {V : Type*} [Fintype V] [DecidableEq V] {K_pre K_post : ℕ}
       (M : MeasurementOperator V K_pre K_post)
       (ψ_pre : PreMeasurementState V K_pre) : PostMeasurementState V K_post :=
     let ψ_post_raw := Common.wavefunction_collapse M ψ_pre.amplitude
     ⟨ψ_post_raw, proof_normalized, proof_support⟩
   ```

---

## Next Session TODO

### Preparation

1. ✅ **Review approach_2 architecture** (DONE - documented above)
2. **Consult LLM team** on best refactoring strategy:
   - Question: "Given type signature mismatch and duplication, should we consolidate into ONE module (approach_2 pattern) or use low-level/high-level split with wrappers?"
   - Provide: This document + current file contents
   - Get: Architectural recommendation + implementation strategy

### Implementation (After LLM Consultation)

3. **Execute chosen strategy**:
   - If Option A: Consolidation
     - Create or enhance ONE comprehensive module
     - Move base defs to Foundation
     - Archive or integrate NonUnitaryEvolution
   - If Option B: Wrapper approach
     - Keep Common.lean low-level
     - Add high-level wrappers in MeasurementGeometry
     - Ensure NonUnitaryEvolution uses correct approach

4. **Verify build**:
   - All 10 modules import successfully
   - 0 duplicate definition errors
   - Build succeeds: `lake build LogicRealismTheory`

5. **Update documentation**:
   - Update LogicRealismTheory.lean status comments
   - Run `scripts/count_sorry.py` for final count
   - Document final architecture

---

## Files Reference

**Current State** (Session 5.2 end):
- ✅ `lean/LogicRealismTheory.lean` - Status updated, accurate build info
- ✅ `lean/LogicRealismTheory/Measurement/Common.lean` - Exists but not imported
- ✅ `lean/LogicRealismTheory/Measurement/MeasurementGeometry.lean` - Active, builds
- ⚠️ `lean/LogicRealismTheory/Measurement/NonUnitaryEvolution.lean` - Commented out
- ✅ `scripts/count_sorry.py` - Accurate sorry counter (excludes comments)

**Approach_2 Reference**:
- `approach_2_reference/lean/LFT_Proofs/PhysicalLogicFramework/QuantumEmergence/MeasurementMechanism.lean`
- `approach_2_reference/lean/LFT_Proofs/PhysicalLogicFramework/Foundations/ConstraintThreshold.lean`

---

## Lessons Learned

1. **Type signatures matter**: Low-level (`V → ℂ`) vs high-level (`PreMeasurementState`) require careful planning
2. **Approach_2 is simpler**: ONE comprehensive module > multiple small modules with duplication
3. **Automatic refactoring insufficient**: Type mismatches require manual architectural decisions
4. **LLM team valuable**: Complex architectural decisions benefit from multi-LLM consultation
5. **Build verification critical**: Restore original state when refactoring fails

---

**Status**: Ready for LLM team consultation and implementation in next session
