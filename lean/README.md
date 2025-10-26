# LogicRealismTheory - Lean 4 Formal Proofs

Formal verification of Logic Realism Theory using Lean 4 and Mathlib.

## Quick Links

- **Main Theory Paper:** `../theory/Logic-realism-theory-foundational.md`
- **Prediction Testing (Working Folder):** `../theory/predictions/` ⭐
- **Computational Validation:** `../notebooks/quantum_simulations/`
- **Development Protocol:** `DEVELOPMENT.md` (CI/CD for Lean modules)

## Structure

```
lean/
├── LogicRealismTheory.lean     ← ROOT: Imports all modules
├── DEVELOPMENT.md               ← CI/CD protocol (READ THIS!)
├── lakefile.lean                ← Build configuration
└── LogicRealismTheory/
    ├── Foundation/              ← Core definitions
    │   ├── IIS.lean            (Infinite Information Space)
    │   └── Actualization.lean  (Selection by logical operators)
    ├── Operators/               ← Logical operators
    │   └── Projectors.lean     (3FLL projectors)
    ├── Derivations/             ← Derived results
    │   ├── Energy.lean
    │   ├── TimeEmergence.lean
    │   └── RussellParadox.lean
    └── Realizations/            ← Physical realizations
```

## Current Status

**Build Status:** Run `lake build` to verify
**Sorry Count:** Run audit script in `DEVELOPMENT.md`
**Last Updated:** 2025-10-26

## Integration with Predictions Testing

**IMPORTANT:** This Lean codebase provides formal proofs for LRT's mathematical framework. The computational testing of predictions happens in:

📂 **Working Folder:** `../theory/predictions/`

**Current active test:** Logical State-Dependent Error
- Design: `../theory/predictions/Logical_State_Dependent_Error_Test_Design.md`
- Implementation: `../notebooks/quantum_simulations/` (when Phase 2 begins)
- Status: Multi-LLM approved (quality 0.69, unanimous "Proceed")

## Development Workflow

**MANDATORY READING:** `DEVELOPMENT.md`

### Quick Start

1. **Pull latest:**
   ```bash
   git pull origin master
   ```

2. **Build:**
   ```bash
   cd lean && lake build
   ```

3. **Make changes** to .lean files

4. **Update root import** (if new module):
   Edit `LogicRealismTheory.lean` to add import

5. **Update README** (if sorry count changed):
   Update module README in relevant folder

6. **Verify build:**
   ```bash
   lake build
   ```

7. **Commit with protocol:**
   Follow format in `DEVELOPMENT.md`

### CI/CD Protocol

**Every commit touching .lean files MUST:**
- ✅ Update `LogicRealismTheory.lean` (if new module)
- ✅ Update module README (if sorry count changed)
- ✅ Verify build succeeds
- ✅ Follow commit message format

See `DEVELOPMENT.md` for complete protocol.

## Module Documentation

Each module folder (`Foundation/`, `Operators/`, etc.) should have its own `README.md` documenting:
- Purpose
- Files and their status
- Sorry count per file
- Key definitions and theorems
- Build status

## Build Commands

```bash
# Standard build
lake build

# Clean build
lake clean && lake build

# Get mathlib cache
lake exe cache get

# Build specific module
lake build LogicRealismTheory.Foundation.IIS
```

## Quality Standards

### "Complete" Module
- Sorry count = 0
- Builds successfully
- Imported in LogicRealismTheory.lean
- Documented in module README

### "In Progress" Module
- Sorry count > 0 (documented)
- Builds successfully
- Imported in LogicRealismTheory.lean
- README lists which theorems need proofs

### "Exploratory" Module
- Testing ideas, may be deleted
- May not build or be imported
- Marked as "Exploratory" in README

## Related Work

### Computational Validation
- **Notebooks:** `../notebooks/quantum_simulations/`
- **Current test:** Logical State-Dependent Error (Phase 2 pending)
- **Previous work:** Session 2.5 QEC entropy-error analysis

### Theory Development
- **Working folder:** `../theory/predictions/` ⭐
- **Main paper:** `../theory/Logic-realism-theory-foundational.md`
- **Session logs:** `../Session_Log/`

### Multi-LLM Consultations
- **Location:** `../multi_LLM/consultation/`
- **Latest:** Logical State Error design review (quality 0.69, approved)

## Sorry Management

**Current goal:** Reduce sorry count by ≥1 per week

**Check current count:**
```bash
grep -r sorry LogicRealismTheory/ | wc -l
```

**By module:**
```bash
for dir in Foundation Operators Derivations Realizations; do
  count=$(grep -r sorry LogicRealismTheory/$dir 2>/dev/null | wc -l)
  echo "$dir: $count"
done
```

## Getting Help

**Stuck on a proof?**
1. Check Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/
2. Consult multi-LLM team (see `../multi_LLM/enhanced_llm_bridge.py`)
3. Document the challenge in session log
4. Use `sorry` temporarily, document in README

## Contributing

**Before making changes:**
1. Read `DEVELOPMENT.md` (CI/CD protocol)
2. Check current build status (`lake build`)
3. Note current sorry count
4. Follow update protocol

**After making changes:**
1. Update LogicRealismTheory.lean (if needed)
2. Update module README (if needed)
3. Verify build
4. Commit following protocol
5. Push to GitHub

---

**For questions:** See `DEVELOPMENT.md` or session logs in `../Session_Log/`

**Last Updated:** 2025-10-26
**Maintainer:** Claude Code (Session-based development)
**Status:** Active development
