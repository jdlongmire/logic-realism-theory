# Lean Development Protocol

This document defines the protocol for maintaining the Lean codebase as part of CI/CD.

## Progressive Update Protocol

### When Adding New Lean Modules

**Every time you create a new .lean file**, you MUST update:

1. ✅ **Root module** (`LogicRealismTheory.lean`)
2. ✅ **Module README** (in the module's folder)
3. ✅ **Repository README** (root `README.md`)

**This is NOT optional** - it's part of the development workflow.

---

## Step 1: Update Root LogicRealismTheory.lean

**File:** `lean/LogicRealismTheory.lean`

**When:** After creating ANY new .lean file in `LogicRealismTheory/`

**How:**

1. Add import statement in the appropriate section
2. Keep imports organized by category
3. Follow existing format

**Example:**

```lean
-- This module serves as the root of the `LogicRealismTheory` library.
-- Import modules here that should be built as part of the library.

-- Foundation
import LogicRealismTheory.Foundation.IIS
import LogicRealismTheory.Foundation.Actualization
import LogicRealismTheory.Foundation.NewModule  -- ← ADD NEW IMPORT

-- Operators
import LogicRealismTheory.Operators.Projectors

-- Derivations
import LogicRealismTheory.Derivations.Energy
import LogicRealismTheory.Derivations.TimeEmergence
import LogicRealismTheory.Derivations.RussellParadox
```

**Categories:**
- `Foundation/` - Core definitions (IIS, actualization, constraints)
- `Operators/` - Logical operators (projectors, filters)
- `Derivations/` - Derived results (energy, time, paradoxes)
- `Realizations/` - Physical realizations (quantum, spacetime)

**Verification:**
```bash
cd lean && lake build
```

If it builds, imports are correct. If not, fix before committing.

---

## Step 2: Update Module README

**Location:** Each module folder should have a `README.md`

**When:** After adding new .lean file OR completing a proof

**Structure:**

```markdown
# [Module Name]

## Purpose
[What this module formalizes]

## Files

### [FileName].lean
- **Status:** [Complete / In Progress / Exploratory]
- **Sorry Count:** [N]
- **Key Definitions:**
  - `def1`: [Description]
  - `def2`: [Description]
- **Key Theorems:**
  - `theorem1`: [Statement]
  - `theorem2`: [Statement]
- **Dependencies:** [Other modules imported]

## Build Status
- Last verified: [Date]
- Builds successfully: [Yes/No]
```

**Example:**

```markdown
# Foundation

## Purpose
Core definitions for Logic Realism Theory's foundational concepts.

## Files

### IIS.lean
- **Status:** In Progress
- **Sorry Count:** 3
- **Key Definitions:**
  - `InfiniteInformationSpace`: The space of all possible states
  - `LogicalConstraint`: Constraints from 3FLL
- **Key Theorems:**
  - `constraint_reduces_dimensionality`: sorry
- **Dependencies:** Mathlib.Data.Set.Basic

### Actualization.lean
- **Status:** Complete
- **Sorry Count:** 0
- **Key Definitions:**
  - `Actualize`: Process of selection by logical operators
  - `ActualizedState`: States that satisfy all constraints
- **Key Theorems:**
  - `actualization_is_unique`: Actualized states are determined uniquely ✓
- **Dependencies:** LogicRealismTheory.Foundation.IIS

## Build Status
- Last verified: 2025-10-26
- Builds successfully: Yes
```

---

## Step 3: Update Repository README

**File:** `README.md` (root)

**When:** After completing a module OR achieving milestone

**Section to update:** "Lean 4 Formal Proofs"

**Keep updated:**
- Module count
- Sorry count (use `grep -r sorry lean/LogicRealismTheory | wc -l`)
- Key accomplishments
- Build status

**Before updating README, run audit:**
```bash
# Count sorry statements
echo "Foundation:"
grep -c sorry lean/LogicRealismTheory/Foundation/*.lean 2>/dev/null || echo "0"
echo "Operators:"
grep -c sorry lean/LogicRealismTheory/Operators/*.lean 2>/dev/null || echo "0"
echo "Derivations:"
grep -c sorry lean/LogicRealismTheory/Derivations/*.lean 2>/dev/null || echo "0"

# Verify builds
cd lean && lake build
```

---

## Step 4: Commit Protocol

**Every commit touching .lean files MUST:**

1. ✅ Include updated `LogicRealismTheory.lean` (if new module)
2. ✅ Include updated module README (if sorry count changed)
3. ✅ Include build verification in commit message

**Commit message format:**
```
[Module]: [Description]

Changes:
- [File1.lean]: [What changed]
- [File2.lean]: [What changed]

Sorry count: [Before] → [After]
Build status: ✓ Verified

Updated:
- LogicRealismTheory.lean (added import)
- Foundation/README.md (sorry count)
```

**Example:**
```
Foundation: Prove constraint_reduces_dimensionality theorem

Changes:
- IIS.lean: Completed proof of constraint_reduces_dimensionality
- IIS.lean: Added helper lemma finite_constraints_compose

Sorry count: 3 → 2
Build status: ✓ Verified (lake build successful)

Updated:
- LogicRealismTheory.lean (no changes needed, already imported)
- Foundation/README.md (sorry count 3 → 2)
```

---

## CI/CD Integration

### Pre-commit Checks (Manual for now, automate later)

**Before every commit with .lean changes:**

```bash
# 1. Verify build
cd lean && lake build
if [ $? -ne 0 ]; then
  echo "ERROR: Build failed. Fix before committing."
  exit 1
fi

# 2. Check if LogicRealismTheory.lean needs update
echo "New .lean files not imported:"
find lean/LogicRealismTheory -name "*.lean" -type f | while read file; do
  module=$(echo $file | sed 's|lean/||' | sed 's|/|.|g' | sed 's|.lean||')
  grep -q "import $module" lean/LogicRealismTheory.lean || echo "  - $module"
done

# 3. Check sorry counts
echo "Sorry counts by module:"
for dir in Foundation Operators Derivations Realizations; do
  count=$(grep -r sorry lean/LogicRealismTheory/$dir 2>/dev/null | wc -l)
  echo "  $dir: $count"
done
```

### Automated Checks (Future GitHub Actions)

**TODO: Set up GitHub Action for:**
- Automated `lake build` on every PR
- Sorry count tracking (fail if increases without justification)
- Import verification (ensure all .lean files imported)
- README consistency checks

---

## Directory Structure Maintenance

### Current Structure

```
lean/
├── LogicRealismTheory.lean          ← ROOT: Import ALL modules here
├── lakefile.lean                     ← Build configuration
├── DEVELOPMENT.md                    ← THIS FILE (protocol)
└── LogicRealismTheory/
    ├── Foundation/
    │   ├── README.md                 ← Module documentation
    │   ├── IIS.lean
    │   └── Actualization.lean
    ├── Operators/
    │   ├── README.md
    │   └── Projectors.lean
    ├── Derivations/
    │   ├── README.md
    │   ├── Energy.lean
    │   ├── TimeEmergence.lean
    │   └── RussellParadox.lean
    └── Realizations/
        └── README.md
```

### Rules

1. **ONE README per folder** - Document all .lean files in that folder
2. **Organize by concept** - Foundation, Operators, Derivations, Realizations
3. **Root imports ALL** - LogicRealismTheory.lean imports every module
4. **No orphan files** - Every .lean must be imported or documented as exploratory

---

## Sorry Management

### Acceptable Reasons for `sorry`

✅ **Acceptable (temporary):**
- Proof is complex, needs more time
- Waiting on external mathlib lemmas
- Exploratory work (mark file as "Exploratory" in README)

❌ **Not acceptable (must fix before claiming "complete"):**
- "I'll prove this later" (how much later?)
- "It's obviously true" (prove it!)
- "Too hard" (get help from multi-LLM team)

### Protocol for Reducing Sorry Count

**When starting work session:**
1. Check current sorry count: `grep -r sorry lean/LogicRealismTheory | wc -l`
2. Pick ONE sorry to resolve
3. Get help if stuck (multi-LLM consultation)
4. Update README when resolved
5. Commit with "Sorry count: N → N-1"

**Goal:** Reduce by at least 1 per week

---

## Module Development Workflow

### Creating New Module

1. **Create file:** `lean/LogicRealismTheory/[Category]/[Name].lean`
2. **Add header comment:**
   ```lean
   /-!
   # [Module Name]

   This module formalizes [description].

   ## Main definitions
   - `Def1`: [description]

   ## Main theorems
   - `theorem1`: [statement]

   ## References
   - Paper: [section/page]
   - Notebook: [if applicable]
   -/
   ```
3. **Implement definitions** (can use sorry for theorems initially)
4. **Update LogicRealismTheory.lean** (add import)
5. **Update module README** (add entry for new file)
6. **Verify build:** `cd lean && lake build`
7. **Commit** (following commit protocol above)

### Completing Proofs

1. **Before:** Note sorry count
2. **Prove:** Replace sorry with proof
3. **Verify:** `lake build` succeeds
4. **Update README:** Sorry count decreases
5. **Commit:** Include before/after sorry count

---

## Quality Standards

### Definition of "Complete Module"

A module is "complete" when:
- ✅ Sorry count = 0
- ✅ `lake build` succeeds
- ✅ All definitions have docstrings
- ✅ All theorems have statements and proofs
- ✅ README documents all files
- ✅ Root LogicRealismTheory.lean imports it

### Definition of "In Progress Module"

A module is "in progress" when:
- ⚠️ Sorry count > 0 (documented in README)
- ✅ `lake build` succeeds (even with sorrys)
- ✅ README lists which theorems need proofs
- ✅ Root LogicRealismTheory.lean imports it

### Definition of "Exploratory Module"

A module is "exploratory" when:
- 🔬 Testing ideas, may be deleted
- ⚠️ May not build
- ⚠️ May not be imported in root
- ✅ Documented in README as "Exploratory"

---

## Integration with Session Logs

**When working on Lean modules:**

1. Document in session log which modules you worked on
2. Note before/after sorry counts
3. Reference specific theorems proved
4. Link to commits

**Session log entry example:**
```markdown
### Lean Work (Session 2.6)

**Modules modified:**
- Foundation/IIS.lean: Proved constraint_reduces_dimensionality
- Foundation/Actualization.lean: Added helper lemmas

**Sorry count:**
- Before: 5 (Foundation: 3, Operators: 2)
- After: 3 (Foundation: 1, Operators: 2)

**Build status:** ✓ Verified

**Commits:**
- abc123f: Foundation: Prove constraint_reduces_dimensionality
- def456g: Foundation: Add composition lemmas

**Updated:**
- LogicRealismTheory.lean: No changes (already imported)
- Foundation/README.md: Sorry count 3 → 1
```

---

## Quick Reference

### Daily Workflow Checklist

When working with Lean:
- [ ] Pull latest from GitHub
- [ ] Note current sorry count
- [ ] Make changes to .lean files
- [ ] **Update LogicRealismTheory.lean** (if new module)
- [ ] **Update module README** (if sorry count changed)
- [ ] Verify build: `cd lean && lake build`
- [ ] Commit with protocol-compliant message
- [ ] Push to GitHub

### Before Claiming Module "Complete"

- [ ] Sorry count = 0 in this module
- [ ] `lake build` succeeds
- [ ] LogicRealismTheory.lean imports it
- [ ] README documents all files
- [ ] All theorems have proofs
- [ ] Commit message says "Module complete: [Name]"

---

## Automation TODO

**Future improvements:**
1. GitHub Action for automated `lake build`
2. Pre-commit hook to check LogicRealismTheory.lean
3. Automatic sorry count in PR comments
4. README generation from docstrings
5. Dependency graph visualization

---

**Last Updated:** 2025-10-26
**Status:** Active protocol
**Compliance:** Mandatory for all Lean development
