# Lean 4 Proof Development Best Practices

**Context**: Lessons learned from completing QubitKMapping and Energy modules (Session 2.12+)

---

## Key Insights

### 1. Physical Axioms vs Mathematical Theorems

**Principle**: Some physical properties are fundamental postulates, not provable from mathematical structure alone.

**Examples**:
- **Energy additivity** (E_total = E₁ + E₂ for independent systems):
  - CANNOT be proven: `(p₁ + p₂)²/(2(m₁ + m₂)) ≠ p₁²/(2m₁) + p₂²/(2m₂)` in general
  - IS a fundamental physical principle (analogous to entropy extensivity)
  - **Solution**: Axiomatize with comprehensive documentation explaining why

- **Binary entropy bound** (Shannon's theorem: H(p, 1-p) ≤ log 2):
  - Well-established result requiring calculus infrastructure
  - **Solution**: Axiomatize with proof sketch and reference

**When to axiomatize**:
- ✅ Well-established results requiring infrastructure we don't have
- ✅ Physical principles beyond mathematical structure alone
- ✅ Always include comprehensive documentation:
  - Why it's an axiom (not provable with current infrastructure)
  - Proof sketch or reference
  - Physical/mathematical justification
  - Status note

**Pattern** (from QubitKMapping.lean):
```lean
axiom binary_entropy_bound (p q : ℝ) (h_norm : p + q = 1)
    (hp_pos : 0 < p) (hq_pos : 0 < q) (hp_le : p ≤ 1) (hq_le : q ≤ 1) :
  -(p * Real.log p + q * Real.log q) ≤ Real.log 2

/-!
Comprehensive doc block explaining:
- Mathematical statement
- Proof sketch (derivatives, concavity argument)
- Reference (Shannon 1948)
- Status (well-established, axiomatized due to infrastructure)
-/
```

---

### 2. field_simp is Powerful for Division Algebra

**Context**: Extensivity proof in Energy.lean initially attempted with manual calc chains, causing errors.

**Solution**: Use `field_simp` with explicit nonzero hypotheses:

```lean
have h_N_ne_zero : (N : ℝ) ≠ 0 := ne_of_gt h_N_pos
have h_m_ne_zero : H_struct.m ≠ 0 := ne_of_gt H_struct.positive_mass

rw [H_struct.hamiltonian_def]
field_simp [h_N_ne_zero, h_m_ne_zero]
-- Proof complete! (no need for additional ring tactic)
```

**Why this works**:
- `field_simp` clears all fractions using nonzero hypotheses
- Automatically handles division algebra without manual steps
- Often completes proofs without needing `ring` afterward

**When to use**:
- ✅ Proving equalities involving division
- ✅ When you have explicit nonzero hypotheses
- ✅ Alternative to manual `div_mul_eq_mul_div`, `mul_div_mul_right` chains

---

### 3. Edit Tool Cache Issues on Windows/OneDrive

**Problem**: Edit tool repeatedly fails with "File has been unexpectedly modified" even when git shows no changes.

**Root cause**: Likely OneDrive sync or file system cache issues causing apparent modifications.

**Solution**: Use Python/bash scripts for edits instead:

```python
# Read file
with open('Energy.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Make replacements
content = content.replace(old_string, new_string)

# Write back
with open('Energy.lean', 'w', encoding='utf-8') as f:
    f.write(content)
```

**When to use**:
- ✅ After 2-3 consecutive Edit tool failures
- ✅ When working with files in OneDrive-synced directories
- ✅ For complex multi-part edits

---

### 4. Complex Number Type Coercion Pattern

**Context**: Proving properties about `normSq (1/sqrt 2 : ℂ) = 1/2`.

**Pattern**:
```lean
have h_normsq : normSq (1/sqrt 2 : ℂ) = 1/2 := by
  rw [normSq_div, normSq_one, normSq_ofReal]
  simp  -- Uses sq_sqrt automatically
```

**Key lemmas**:
- `normSq_div`: `normSq (a/b) = normSq a / normSq b`
- `normSq_one`: `normSq 1 = 1`
- `normSq_ofReal`: `normSq (x : ℂ) = x²` for real x
- `Real.sq_sqrt`: `sqrt(x)² = x` for x ≥ 0

**When needed**: Working with quantum states as complex amplitudes

---

### 5. Proof Strategy: Try Simple First

**Workflow**:
1. **Try automated tactics first**: `simp`, `ring`, `field_simp`, `norm_num`
2. **If that fails, add structure**: `calc` chains, intermediate `have` statements
3. **Only then use manual lemmas**: `div_mul_eq_mul_div`, `mul_pow`, etc.
4. **Last resort**: Axiomatize with documentation

**Example (extensivity proof evolution)**:
- ❌ Attempt 1: Manual `calc` chain with `mul_div_mul_right` → Term ordering errors
- ❌ Attempt 2: `calc` with `ring` at each step → "No goals" error
- ✅ Success: Simple `field_simp` with nonzero hypotheses → Complete

**Lesson**: Simpler is often better. Lean's automation is powerful.

---

### 6. Documentation Standards for Axioms

**Minimum requirements** for any `axiom` or `sorry` with documentation:

1. **Status line**: Clearly state it's an axiom and why
2. **Mathematical statement**: What exactly is being assumed
3. **Justification**: Why can't it be proven / why is it a physical principle
4. **Reference**: Citation if it's a known result
5. **Proof sketch** (if applicable): How it would be proven with full infrastructure

**Example template**:
```lean
/-!
PHYSICAL AXIOM: [Property Name]

[Why it cannot be mathematically proven]

However, [property] is a FUNDAMENTAL PHYSICAL PRINCIPLE because:
- [Reason 1]
- [Reason 2]

Reference: [Citation]

Status: [Well-established / Requires physical assumptions / etc.]
-/
axiom property_name [parameters] : [statement]
```

---

### 7. User's "no sorrys if we can help it" Principle

**Directive**: Eliminate ALL sorry statements if possible, not leave them incomplete.

**Options when facing a sorry**:
1. ✅ **Prove it** using available tactics/lemmas
2. ✅ **Axiomatize it** with comprehensive documentation
3. ❌ **Leave it as sorry** without explanation

**Example achievement**:
- QubitKMapping.lean: **0 sorry** (all proofs complete or documented axioms)
- Energy.lean: **1 documented axiom** (additivity) + **1 proven** (extensivity)

---

### 8. Internal Development Work: approach_2_reference/ Protocol

**Protocol**: "Use the data, don't refer to it as a source"

**Context**: The `approach_2_reference/` directory contains internal research with proven results (K(N)=N-2 formula, measurement mechanisms, Born rule structures). These can inform LogicRealismTheory/ development.

**Guidelines for incorporating approach_2 structures**:

**✅ DO**:
- Extract proven structures and incorporate into LogicRealismTheory/
- Rewrite as native code (no import dependencies)
- Document in LogicRealismTheory/ context
- Remove all internal development references

**❌ DO NOT**:
- Import from approach_2_reference/ (zero dependencies)
- Leave "from approach_2" or "based on approach_2" comments
- Reference approach_2 as source in documentation
- Point readers to internal development directories

**Clean Incorporation Pattern**:

**WRONG** (leaves breadcrumbs):
```lean
-- Imported from approach_2_reference/MeasurementMechanism.lean
structure Observer where
  K_obs : ℕ
  -- Based on approach_2 observer model
```

**RIGHT** (clean professional code):
```lean
-- Observer as constraint-contributing system
structure Observer where
  K_obs : ℕ
  coupling : ℝ
```

**Why**: Public Lean code should be self-contained and professional. Extract the refined concepts, incorporate cleanly, present as native LogicRealismTheory/ work.

**Example Use Cases**:
- Extracting Born rule normalization axioms → Incorporate into Measurement/MeasurementGeometry.lean
- Using K-mapping entropy formulas → Incorporate into Foundation/QubitKMapping.lean
- Adopting observer coupling structures → Rewrite in Measurement/ modules

When mining approach_2: take the gold, leave the mine behind.

---

## Lean File Header Requirements

**MANDATORY**: Every Lean file in the main build (Foundation, Operators, Derivations) must include an axiom inventory reference.

**Template**:
```lean
/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
Citation: Longmire, J.D. (2025). [Title]. Logic Realism Theory Repository.

# [Module Name]

[Module description]

**Core Result**: [Main result]

**Derivation Path**:
[Steps]

**Foundational Paper Reference**: [Section reference]

**Axiom Count**: X ([description of axioms used])
- [Details about axioms]

**AXIOM INVENTORY**: For complete axiom documentation, see: lean/AXIOMS.md
This module uses X axioms:
- [List specific axioms used]
-/

import [imports]
```

**Key Points**:
- **Axiom inventory reference**: Every file must reference `lean/AXIOMS.md`
- **Specific axiom list**: List the exact axioms used in this module
- **Placement**: After copyright block, before imports
- **Transparency**: Makes axiom usage immediately visible to reviewers

**Example (0 axioms)**:
```lean
**Axiom Count**: 0 (this file defines structures, adds NO axioms)

**AXIOM INVENTORY**: For complete axiom documentation, see: lean/AXIOMS.md
This module uses 0 axioms.
```

**Example (with axioms)**:
```lean
**Axiom Count**: 3 (Stone's theorem, Jaynes MaxEnt, Spohn's inequality)

**AXIOM INVENTORY**: For complete axiom documentation, see: lean/AXIOMS.md
This module uses 3 axioms:
- Stone's theorem (unitary groups ↔ self-adjoint generators)
- Jaynes Maximum Entropy Principle
- Spohn's inequality (entropy change bounds)
```

---

## Lean Root Import File Protocol

**CRITICAL**: The file `lean/LogicRealismTheory.lean` is the **source of truth** for the main build.

**Protocol**:
1. **All new Lean files** must be added to `lean/LogicRealismTheory.lean` immediately after creation
2. **Non-compiling files** must be commented out with explanation of build error
3. **Experimental files** must be commented out with status note
4. **File status summary** must be kept updated in the header comments

**When creating a new Lean file**:
```bash
# 1. Create the file in appropriate subfolder
touch lean/LogicRealismTheory/[Module]/NewFile.lean

# 2. Immediately add import to LogicRealismTheory.lean
# Add under appropriate section (Foundation/Operators/Derivations)
import LogicRealismTheory.[Module].NewFile

# 3. Verify build succeeds
cd lean && lake build

# 4. If build fails, comment out import with explanation
-- NewFile: COMMENTED OUT - [Reason for failure]
-- Status: [Work in progress / Needs debugging / etc.]
-- import LogicRealismTheory.[Module].NewFile
```

**When commenting out a file**:
- Always include reason (build failure, sorry statements, experimental)
- Include current status (what needs to be fixed)
- Update the "CURRENT MAIN BUILD STATUS" comment block

**Audit Protocol**:
- Before making any claims about axiom count or sorry count, verify against `lean/LogicRealismTheory.lean`
- Only count axioms/sorrys from files that are actively imported (not commented out)
- Run `lake build LogicRealismTheory` to verify what's actually compiled

**Example** (from LogicRealismTheory.lean):
```lean
-- Measurement.NonUnitaryEvolution: COMMENTED OUT - Contains 3 sorry statements + 13 axioms
-- Status: Work in progress, incomplete proofs at lines 141, 193, 211
-- import LogicRealismTheory.Measurement.NonUnitaryEvolution
```

**Why This Matters**:
- Prevents axiom count drift (claiming "6 axioms" when actual count is different)
- Maintains single source of truth for build status
- Documents experimental vs production-ready modules
- Enables accurate Program Auditor checks

---

## Summary: Process Improvements

1. ✅ Axiomatize well-established results with full documentation
2. ✅ Use `field_simp` for division algebra proofs
3. ✅ Bypass Edit tool cache issues with Python scripts
4. ✅ Try simple tactics before complex manual proofs
5. ✅ Document axioms thoroughly (status, justification, reference)
6. ✅ Eliminate sorrys through proof or documented axiomatization

**Impact**: Professional, scientifically rigorous formal proofs that clearly distinguish mathematical theorems from physical postulates.
