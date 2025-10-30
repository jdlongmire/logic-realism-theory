# Sprint 11: Lean Proof Cleanup - Axiom Justification & Sorry Elimination

**Sprint Duration**: 2-3 weeks
**Sprint Goal**: Achieve clean Lean build with justified axioms and zero sorry statements
**Priority**: HIGH (Blocking for formal proof claims)

---

## Axiom Approach (from AXIOMS.md)

Axioms in this formalization fall into **two acceptable categories**:

1. **Foundational postulates** - Theory-defining assumptions that establish what LRT is (analogous to quantum mechanics' Hilbert space postulate)

2. **Established results** - Well-known mathematical or physical principles whose formal proofs would require extensive Mathlib development without adding physical insight

**Any axiom that doesn't fit these categories must be proven or removed.**

---

## Current Baseline (2025-10-29, Session 4.2)

**Build Status**: ❌ FAILED

**Module Status** (9 total .lean files):
- ✅ Foundation/IIS.lean (2 axioms, builds)
- ✅ Foundation/Actualization.lean (0 axioms, builds)
- ⚠️  Foundation/QubitKMapping.lean (2 axioms, builds but has tactic issues)
- ✅ Operators/Projectors.lean (0 axioms, builds)
- ✅ Derivations/Energy.lean (5 axioms, builds)
- ✅ Derivations/TimeEmergence.lean (6 axioms, builds)
- ✅ Derivations/RussellParadox.lean (0 axioms, builds)
- ❌ Measurement/MeasurementGeometry.lean (23 axioms, COMPILATION ERRORS)
- ⚠️  Measurement/NonUnitaryEvolution.lean (12 axioms, 3 sorry statements, builds)

**Counts**:
- **Total axioms**: 51
- **Sorry statements**: 3 (target: 0)
- **Compilation errors**: ~20 errors in MeasurementGeometry.lean

---

## Sprint Objectives

### Objective 1: Fix Compilation Errors (Week 1, Priority 1)

**Target**: All 9 modules build successfully

**Tasks**:

1. **Fix MeasurementGeometry.lean compilation errors** (Sessions 11.1-11.3)
   - Type synthesis errors (implicit arguments)
   - Syntax errors (deprecated `λ` syntax)
   - Typeclass synthesis failures (missing instances)
   - Function application errors (missing definitions)
   - **Decision point**: If >15 hours debugging with no progress, comment out module and move forward with 8 modules

2. **Verify clean build** (Session 11.3)
   ```bash
   cd lean && lake build
   ```
   - **Success metric**: Build exits with code 0

---

### Objective 2: Eliminate Sorry Statements (Week 1-2, Priority 2)

**Target**: Zero sorry statements across all modules

**Tasks**:

1. **Identify all sorry locations** (Session 11.4)
   - NonUnitaryEvolution.lean: 3 sorry statements
   - Run: `grep -rn "^ *sorry$" LogicRealismTheory/`
   - Document what each sorry is trying to prove

2. **Eliminate each sorry** (Sessions 11.4-11.6)
   - For each sorry:
     - **Option A**: Complete the proof if feasible
     - **Option B**: Convert to axiom if it fits axiom approach (foundational or established result)
     - **Option C**: Remove the theorem if not essential

3. **Verify zero sorry** (Session 11.6)
   ```bash
   grep -r "^ *sorry$" LogicRealismTheory/ | wc -l
   ```
   - **Success metric**: Returns 0

---

### Objective 3: Axiom Audit & Justification (Week 2-3, Priority 3)

**Target**: Every axiom justified as either foundational or established result

**Strategy**: Audit all 51 axioms, prove or remove those that don't fit the two categories

**Tasks**:

1. **Axiom Inventory** (Session 11.7)
   - List all 51 axioms with their locations
   - Categorize each axiom:
     - ✅ **Foundational postulate** (KEEP - document why)
     - ✅ **Established result** (KEEP - document source/reference)
     - ❌ **Provable from other axioms** (PROVE - convert to theorem)
     - ❌ **Unjustified** (REMOVE or justify)

2. **Review Foundation axioms** (Session 11.8)
   - **IIS.lean** (2 axioms):
     - `axiom I : Type*` - Foundational: Information space exists
     - `axiom I_infinite : Infinite I` - Foundational: Information space is infinite
     - **Action**: Justify as foundational postulates, add documentation

   - **QubitKMapping.lean** (2 axioms):
     - Review both axioms
     - Determine if foundational or established
     - Attempt to prove if neither
     - **Action**: Justify, prove, or remove

3. **Review Derivation axioms** (Session 11.9)
   - **Energy.lean** (5 axioms):
     - Review each axiom
     - Determine if established result (e.g., thermodynamic principles)
     - Check if provable from foundation
     - **Action**: Justify each or convert to theorem

   - **TimeEmergence.lean** (6 axioms):
     - Review each axiom (includes Stone's theorem)
     - Stone's theorem: Established result (keep with reference)
     - Other axioms: Review and justify
     - **Action**: Justify or prove

4. **Review Measurement axioms** (Session 11.10-11.11)
   - **MeasurementGeometry.lean** (23 axioms):
     - High axiom count suggests many may be provable
     - Systematically review each
     - Look for duplicates or derivable axioms
     - **Action**: Reduce through proofs or justify as established

   - **NonUnitaryEvolution.lean** (12 axioms):
     - Review after sorry elimination
     - Determine which are foundational vs. provable
     - **Action**: Justify or prove

5. **Prove unjustified axioms** (Sessions 11.12-11.13)
   - For each axiom marked as "provable":
     - Attempt proof using available lemmas
     - Convert `axiom` → `theorem` with proof
     - Update module documentation
   - **Goal**: Minimize axioms to only those matching the two categories

6. **Document remaining axioms** (Session 11.14)
   - For each remaining axiom, add clear documentation:
     - Category (foundational or established)
     - Justification (why it's not proven)
     - Reference (for established results)
   - Update module comments to explain axiom choices

---

### Objective 4: Final Verification (Week 3, Priority 4)

**Target**: Clean build with all axioms justified, zero sorry statements

**Tasks**:

1. **Full build verification** (Session 11.15)
   ```bash
   cd lean && lake build 2>&1 | tee sprint11_final_build.log
   ```
   - Verify: Exit code 0
   - Verify: No warnings about sorry

2. **Axiom verification** (Session 11.15)
   ```bash
   # Count total axioms
   grep -r "^axiom" LogicRealismTheory/ | wc -l

   # List all axioms
   grep -r "^axiom" LogicRealismTheory/
   ```
   - Review list: Verify each axiom is documented
   - Ensure each fits foundational or established category

3. **Sorry verification** (Session 11.15)
   ```bash
   grep -r "^ *sorry$" LogicRealismTheory/ | wc -l
   ```
   - Verify: Returns 0

4. **Documentation sync** (Session 11.16)
   - Update LogicRealismTheory.lean header comments
   - Verify AXIOMS.md approach statement is accurate
   - Ensure each module has clear axiom documentation

5. **Git commit and push** (Session 11.16)
   - Commit message: Document axiom count, sorry count, justification approach
   - Push to GitHub

---

## Session Breakdown

### Phase 1: Compilation Fixes (Week 1, Sessions 11.1-11.3)

**Session 11.1: MeasurementGeometry Error Analysis**
- Read MeasurementGeometry.lean completely
- Categorize all ~20 errors by type
- Create fix priority list
- Begin fixing type synthesis errors

**Session 11.2: MeasurementGeometry Syntax & Type Fixes**
- Fix deprecated syntax (`λ` → `fun`)
- Add explicit type annotations
- Fix declaration keywords
- Target: 75% error reduction

**Session 11.3: MeasurementGeometry Final Fixes & Verification**
- Add missing typeclass instances
- Define missing functions
- Resolve remaining errors
- Run full build: `lake build`
- **Decision**: If still failing after 15 hours, comment out module

### Phase 2: Sorry Elimination (Week 1-2, Sessions 11.4-11.6)

**Session 11.4: Sorry Analysis**
- Locate all 3 sorry statements in NonUnitaryEvolution.lean
- Document what each theorem claims
- Identify needed lemmas and proof strategy
- Decide: Prove, axiomatize, or remove?

**Session 11.5: Sorry Resolution (Part 1)**
- Work on 2 of 3 sorry statements
- Attempt proofs or convert to axioms (if justified)
- Document decisions

**Session 11.6: Sorry Resolution (Part 2) & Verification**
- Complete remaining sorry statement
- Verify: `grep -r "^ *sorry$" LogicRealismTheory/ | wc -l` returns 0
- Update module documentation

### Phase 3: Axiom Audit (Week 2-3, Sessions 11.7-11.14)

**Session 11.7: Axiom Inventory**
- List all 51 axioms across all modules
- Categorize each:
  - Foundational postulate
  - Established result
  - Provable
  - Unjustified
- Create prioritized list for proving/justifying

**Session 11.8: Foundation Axioms**
- Review IIS.lean (2 axioms) - justify as foundational
- Review QubitKMapping.lean (2 axioms) - justify or prove
- Add documentation for justified axioms

**Session 11.9: Derivation Axioms**
- Review Energy.lean (5 axioms)
- Review TimeEmergence.lean (6 axioms)
- Justify as established results or prove
- Add references for established results

**Session 11.10-11.11: Measurement Axioms**
- Review MeasurementGeometry.lean (23 axioms)
- Review NonUnitaryEvolution.lean (12 axioms)
- High axiom count suggests many provable
- Systematically prove or justify each

**Session 11.12-11.13: Axiom Elimination**
- For each "provable" axiom:
  - Write proof
  - Convert axiom → theorem
  - Verify build still works
- Target: Eliminate all unjustified axioms

**Session 11.14: Axiom Documentation**
- For each remaining axiom:
  - Add clear comment explaining category
  - Add justification or reference
  - Update module documentation
- Ensure consistency with AXIOMS.md approach

### Phase 4: Final Verification (Week 3, Sessions 11.15-11.16)

**Session 11.15: Full Verification**
- Run full build multiple times
- Verify zero sorry statements
- Verify zero compilation errors
- Count and review all axioms
- Generate verification report

**Session 11.16: Documentation & Commit**
- Update LogicRealismTheory.lean header
- Verify AXIOMS.md is accurate
- Write comprehensive commit message
- Push to GitHub
- Update Session_Log/Session_11.16.md

---

## Verification Commands

```bash
# Full build
cd lean && lake build

# Count axioms
cd lean && grep -r "^axiom" LogicRealismTheory/ | wc -l

# List all axioms with context
cd lean && grep -B2 -A1 "^axiom" LogicRealismTheory/

# Count axioms by file
cd lean && for file in LogicRealismTheory/**/*.lean; do
  count=$(grep -c "^axiom" "$file" 2>/dev/null || echo "0")
  if [ "$count" -gt 0 ]; then
    echo "$file: $count axioms"
  fi
done

# Count sorry statements
cd lean && grep -r "^ *sorry$" LogicRealismTheory/ | wc -l

# Find sorry locations
cd lean && grep -rn "^ *sorry$" LogicRealismTheory/

# Check build status
cd lean && lake build 2>&1 | tail -20
```

---

## Success Criteria

**Sprint 11 is COMPLETE when**:
- ✅ All modules compile without errors (`lake build` exits 0)
- ✅ Zero sorry statements in all modules
- ✅ Every axiom is justified as either:
  - **Foundational postulate** (with clear documentation), OR
  - **Established result** (with reference/justification)
- ✅ All unjustified axioms have been proven and converted to theorems
- ✅ Each axiom has clear documentation in its module
- ✅ Changes committed and pushed to GitHub

**Key Difference from Original Plan**: We are NOT targeting an arbitrary axiom count (e.g., <15 or <45). Instead, we accept ANY number of axioms that fit the two justified categories. The goal is justification, not minimization.

---

## Risk Mitigation

**Risk 1: MeasurementGeometry errors too deep**
- **Mitigation**: Time-box to 15 hours debugging
- **Fallback**: Comment out module, continue with 8 modules in main build

**Risk 2: Sorry proofs require advanced techniques**
- **Mitigation**: Convert to axiom if fits established result category
- **Fallback**: Remove theorem if not essential

**Risk 3: Many axioms are actually foundational**
- **Mitigation**: This is acceptable per AXIOMS.md approach
- **Action**: Document clearly why each is foundational

**Risk 4: Proving axioms requires new Mathlib work**
- **Mitigation**: If proof would require extensive Mathlib development, axiomatize as established result with reference
- **Action**: Document why Mathlib proof is deferred

---

**Created**: 2025-10-29, Session 4.2 (revised)
**Status**: PLANNED (not yet started)
**Blocking**: Formal proof claims, paper Section 9 (Lean formalization)
**Next Action**: Session 11.1 - Begin MeasurementGeometry.lean error analysis
