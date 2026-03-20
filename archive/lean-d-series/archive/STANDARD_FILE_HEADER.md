# Standard File Header Format for LRT Lean Formalization

**Purpose**: Ensure consistency across all Lean files during refactor

**Exemplar**: `Foundation/IIS.lean`

**Status**: Active standard for all Lean files

---

## Standard Header Template

```lean
/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
Citation: Longmire, J.D. (2025). Logic Realism Theory: A Research Program for Ontological Logic in Informational Reality. Logic Realism Theory Repository.

**Axiom Approach**: See lean/AXIOMS.md for justification of all axioms in this formalization.

# [Module Category]: [Module Name]

[Brief description of what this file establishes/defines/proves]

**Core Concept**: [Key concept this module addresses]

**Axiom Count by Tier**:
- Tier 1 (LRT Specific): X axioms
- Tier 2 (Established Math Tools): Y axioms
- Tier 3 (Universal Physics): Z axioms
- **Total**: N axioms

**Strategy**: [How this module contributes to the overall formalization]

## [Section Title]

[Additional context about what's in this file]

-/

-- Imports
import [required imports]

-- [Additional opens/namespace declarations]
```

---

## Required Elements (All Files MUST Include)

### 1. Copyright and License Block

**Exact text**:
```lean
/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
Citation: Longmire, J.D. (2025). Logic Realism Theory: A Research Program for Ontological Logic in Informational Reality. Logic Realism Theory Repository.
```

**Purpose**: Legal protection and attribution

---

### 2. Axiom Approach Reference

**Exact text**:
```lean
**Axiom Approach**: See lean/AXIOMS.md for justification of all axioms in this formalization.
```

**Purpose**: Points readers to complete axiom documentation

**Note**: Once AXIOMS.md is updated, also reference AXIOM_CLASSIFICATION_SYSTEM.md

---

### 3. Module Title

**Format**:
```lean
# [Category]: [Specific Name]
```

**Examples**:
- `# Foundation: Infinite Information Space (I)`
- `# Derivations: Time Emergence from Identity Constraint`
- `# Measurement: Measurement Geometry and Born Rule`
- `# Operators: Projection Operators for 3FLL`

**Purpose**: Clear hierarchical organization

---

### 4. Brief Description

**Format**: 1-2 sentence summary of what this file does

**Examples**:
- "This file establishes the MINIMAL axiomatic foundation for Logic Realism Theory."
- "This file derives time evolution from the Identity constraint via Stone's theorem."
- "This file proves the Born rule from maximum entropy and non-contradiction."

**Purpose**: Quick understanding of file's role

---

### 5. Core Concept/Thesis (Optional but Recommended)

**Format**:
```lean
**Core Concept**: [Key concept]
**Principle**: [Key equation/principle if applicable]
```

**Examples**:
- `**Core Thesis**: Physical reality emerges from logical filtering of an Infinite Information Space.`
- `**Principle**: A = L(I) where Actualization = Logical filtering of Infinite Information`

**Purpose**: Connect module to broader theory

---

### 6. Axiom Count by Tier ⚠️ **MANDATORY**

**Format**:
```lean
**Axiom Count by Tier**:
- Tier 1 (LRT Specific): X axioms
- Tier 2 (Established Math Tools): Y axioms
- Tier 3 (Universal Physics): Z axioms
- **Total**: N axioms
```

**Example (IIS.lean)**:
```lean
**Axiom Count by Tier**:
- Tier 1 (LRT Specific): 2 axioms (I, I_infinite)
- Tier 2 (Established Math Tools): 0 axioms
- Tier 3 (Universal Physics): 0 axioms
- **Total**: 2 axioms
```

**Example (TimeEmergence.lean - hypothetical after refactor)**:
```lean
**Axiom Count by Tier**:
- Tier 1 (LRT Specific): 0 axioms (imports I, I_infinite from IIS)
- Tier 2 (Established Math Tools): 1 axiom (stones_theorem)
- Tier 3 (Universal Physics): 0 axioms
- **Total**: 1 axiom (established result, not novel LRT claim)
```

**Purpose**: Instant visibility of axiom classification

**Rule**: Update this count whenever axioms are added/removed/proven

---

### 7. Strategy Section

**Format**:
```lean
**Strategy**: [How this module achieves its goals]
```

**Examples**:
- `**Strategy**: Everything else defined or derived using Lean's built-in logic.`
- `**Strategy**: Use Stone's theorem (Tier 2) to derive time evolution from Identity constraint (Tier 1).`
- `**Strategy**: Prove Born rule as theorem from MaxEnt principle (Tier 2) + Non-Contradiction (proven from 3FLL).`

**Purpose**: Explains approach and dependencies

---

### 8. Section Headers (Optional, for longer files)

**Format**:
```lean
## [Section Name]

[Brief description of what's in this section]
```

**Examples**:
- `## The Two Axioms`
- `## 3FLL (Definitions using Lean's built-in logic - NOT axioms)`
- `## Key Theorem: Time Emergence`

**Purpose**: Organize longer files into logical sections

---

## Closing the Header Comment

**Always close with**:
```lean
-/

-- Imports
import [your imports]
```

**Purpose**: Clean separation between header and code

---

## Special Cases

### Files with 0 Axioms (Pure Theorems)

**Example**:
```lean
**Axiom Count by Tier**:
- Tier 1 (LRT Specific): 0 axioms (imports from IIS.lean)
- Tier 2 (Established Math Tools): 0 axioms
- Tier 3 (Universal Physics): 0 axioms
- **Total**: 0 axioms (all theorems proven)

**Imports**: I, I_infinite from Foundation/IIS.lean
```

**Purpose**: Clearly indicates pure derivation, no new assumptions

---

### Files Being Refactored

**During refactor, add note**:
```lean
**Status**: ⚠️ Refactoring in progress (Session 9.X)
**Target**: Convert X axioms to proven theorems
**Current**: Y axioms remain
```

**Remove note when refactor complete**

---

## Examples of Correct Headers

### Example 1: Foundation/IIS.lean (Current - Exemplar)

```lean
/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
Citation: Longmire, J.D. (2025). Logic Realism Theory: A Research Program for Ontological Logic in Informational Reality. Logic Realism Theory Repository.

**Axiom Approach**: See lean/AXIOMS.md for justification of all axioms in this formalization.

# Foundation: Infinite Information Space (I)

This file establishes the MINIMAL axiomatic foundation for Logic Realism Theory.

**Core Thesis**: Physical reality emerges from logical filtering of an Infinite Information Space.
**Principle**: A = L(I) where Actualization = Logical filtering of Infinite Information

**Axiom Count by Tier**:
- Tier 1 (LRT Specific): 2 axioms (I, I_infinite)
- Tier 2 (Established Math Tools): 0 axioms
- Tier 3 (Universal Physics): 0 axioms
- **Total**: 2 axioms

**Strategy**: Everything else defined or derived using Lean's built-in logic.

## The Two Axioms

These are the ONLY axioms in the entire theory. All quantum mechanics, time, energy, measurement,
and even the 3FLL operations are DEFINED or DERIVED.

-/

-- Imports
import Mathlib.Algebra.CharZero.Infinite

-- Import classical logic for excluded middle
open Classical
```

✅ **Perfect** - This is the exemplar!

---

### Example 2: Derivations/TimeEmergence.lean (Hypothetical Target)

```lean
/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
Citation: Longmire, J.D. (2025). Logic Realism Theory: A Research Program for Ontological Logic in Informational Reality. Logic Realism Theory Repository.

**Axiom Approach**: See lean/AXIOMS.md for justification of all axioms in this formalization.

# Derivations: Time Emergence from Identity Constraint

This file derives time evolution from the Identity constraint (Tier 1 axiom) using Stone's theorem
(Tier 2 established result). Physical time emerges as the continuous parameter required for
identity preservation under constraint filtering.

**Core Result**: Schrödinger equation as logical consequence of Identity + continuity

**Axiom Count by Tier**:
- Tier 1 (LRT Specific): 0 axioms (imports I, I_infinite from IIS.lean)
- Tier 2 (Established Math Tools): 1 axiom (stones_theorem)
- Tier 3 (Universal Physics): 0 axioms
- **Total**: 1 axiom (Stone's theorem - established 1932, not novel LRT claim)

**Strategy**:
1. Define identity-preserving trajectory from Tier 1 axioms
2. Use Stone's theorem (Tier 2) to generate unitary evolution
3. Prove time emergence as theorem from (1) and (2)

## Key Theorems

- `time_emergence_from_identity`: Physical time emerges from Identity constraint (THEOREM)
- `unitary_evolution_from_identity`: Unitary evolution follows from identity preservation (THEOREM)

**Stone's Theorem**: Axiomatized (Tier 2) - see documentation below for references

-/

-- Imports
import LogicRealismTheory.Foundation.IIS
import Mathlib.Analysis.Normed.Group.Basic
```

✅ **Correct** - Shows clear tier accounting and strategy

---

### Example 3: Measurement/BornRule.lean (Hypothetical Target)

```lean
/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
Citation: Longmire, J.D. (2025). Logic Realism Theory: A Research Program for Ontological Logic in Informational Reality. Logic Realism Theory Repository.

**Axiom Approach**: See lean/AXIOMS.md for justification of all axioms in this formalization.

# Measurement: Born Rule Derivation from MaxEnt and Non-Contradiction

This file DERIVES the Born rule (p_i = |c_i|²) as a THEOREM from maximum entropy principle
(Tier 2 established result) and Non-Contradiction law (proven from 3FLL, 0 axioms).

**Core Result**: Born rule is a logical consequence, not a postulate

**Axiom Count by Tier**:
- Tier 1 (LRT Specific): 0 axioms (imports I, I_infinite from IIS.lean)
- Tier 2 (Established Math Tools): 1 axiom (Jaynes MaxEnt principle)
- Tier 3 (Universal Physics): 0 axioms
- **Total**: 1 axiom (MaxEnt - Jaynes 1957, not novel LRT claim)

**Strategy**:
1. Use Non-Contradiction (proven in IIS.lean, 0 axioms) to constrain probability distributions
2. Apply Jaynes MaxEnt principle (Tier 2) under normalization constraint
3. Prove Born rule emerges as unique maximum entropy solution (THEOREM)

**Comparison to QM**: Standard QM postulates Born rule. LRT derives it.

## Key Theorem

- `born_rule_from_maxent`: p_i = |⟨ψ_i|ψ⟩|² proven from MaxEnt + NC (THEOREM, not axiom)

-/

-- Imports
import LogicRealismTheory.Foundation.IIS
import LogicRealismTheory.Foundation.Actualization
```

✅ **Correct** - Emphasizes derivation vs. postulation

---

## Common Mistakes to Avoid

### ❌ WRONG: Missing Axiom Count

```lean
/-
# Some Module

This does some stuff.
-/
```

**Problem**: No axiom tier accounting

---

### ❌ WRONG: Vague Axiom Count

```lean
**Axiom Count**: 5 axioms
```

**Problem**: Not broken down by tier. Can't tell LRT-specific from infrastructure.

---

### ❌ WRONG: No Copyright/License

```lean
/-
# Module Name

Description here.
-/
```

**Problem**: Missing legal protection and attribution

---

### ❌ WRONG: Claiming "0 axioms" When Tier 2 Exists

```lean
**Axiom Count**: 0 axioms (derives everything from I and I_infinite)
```

**Problem**: Ignores Stone's theorem declared in the file. Should be:
```lean
**Axiom Count by Tier**:
- Tier 1: 0 axioms (imports from IIS)
- Tier 2: 1 axiom (stones_theorem)
- Total: 1 axiom (established result, not novel LRT claim)
```

---

## Refactor Checklist for Each File

When refactoring a file:

1. [ ] Add/update copyright block
2. [ ] Add/update license
3. [ ] Add/update citation
4. [ ] Add axiom approach reference
5. [ ] Add/update module title (hierarchical format)
6. [ ] Add/update brief description
7. [ ] Add/update core concept (if applicable)
8. [ ] **Add/update axiom count by tier** ⚠️ MANDATORY
9. [ ] Add/update strategy section
10. [ ] Add section headers (if file is long)
11. [ ] Ensure all axioms have tier labels inline
12. [ ] Verify build
13. [ ] Update git commit with header standardization note

---

## Automation Opportunity

**Future**: Could create a Python/shell script to:
1. Count axioms by tier (grep for tier labels)
2. Generate header template with counts pre-filled
3. Validate header format

For now: Manual process, use this document as checklist.

---

**Status**: Active standard for Session 9.X refactor
**Exemplar**: `Foundation/IIS.lean`
**Next**: Apply this format to all files during refactor phases
**Last Updated**: 2025-11-04
