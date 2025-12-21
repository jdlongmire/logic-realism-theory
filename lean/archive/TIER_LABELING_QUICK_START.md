# Tier Labeling Quick Start Guide

**For all contributors working on LRT Lean formalization**

---

## The Rule (One Sentence)

**Every `axiom` declaration must include an inline tier comment.**

---

## The Three Tiers

### Tier 1: LRT Specific
**Novel LRT axioms** - Only 2-3 should exist
```lean
axiom I : Type*                    -- TIER 1: LRT SPECIFIC
axiom I_infinite : Infinite I      -- TIER 1: LRT SPECIFIC
```

### Tier 2: Established Math Tools
**Proven theorems from literature** - Keep as axioms, revisit as Mathlib matures
```lean
axiom stones_theorem : ...         -- TIER 2: ESTABLISHED MATH TOOLS
axiom gleason_theorem : ...        -- TIER 2: ESTABLISHED MATH TOOLS
```

### Tier 3: Universal Physics Assumptions
**Standard across all physics** - Keep as axioms
```lean
axiom energy_additivity : ...      -- TIER 3: UNIVERSAL PHYSICS ASSUMPTIONS
```

---

## Quick Decision Tree

**When you write `axiom [name] : [type]`, ask:**

1. **Can this be proven from existing axioms?**
   - YES → Don't use `axiom`, use `theorem` instead!
   - NO → Continue to step 2

2. **Is this a novel LRT claim?**
   - YES → TIER 1 (but LRT should only have 2-3 total!)
   - NO → Continue to step 3

3. **Is this an established math theorem with published proof?**
   - YES → TIER 2
   - NO → Continue to step 4

4. **Is this a universal physics principle?**
   - YES → TIER 3
   - NO → You need to reconsider if this should be an axiom!

---

## Template: Tier 1 (LRT Specific)

```lean
/--
[Axiom Name]

**TIER 1: LRT SPECIFIC**

**Theory-Defining Assumption**: [What this axiom defines about LRT]

**Justification**: [Why this is necessary]

**Analogous to**: [QM comparison if applicable]

**Status**: Novel LRT foundational axiom

**References**: Logic_Realism_Theory_Main.md Section X.Y
-/
axiom [name] : [type]  -- TIER 1: LRT SPECIFIC
```

**Example**: See `Foundation/IIS.lean` for `I` and `I_infinite`

---

## Template: Tier 2 (Established Math Tools)

```lean
/--
[Theorem Name]

**TIER 2: ESTABLISHED MATH TOOLS**

**Established Result**: [Brief description]

**Original Reference**: [Author (Year), citation]

**Why Axiomatized**: Full proof would require [X lines / infrastructure]
without adding physical insight. Standard practice in quantum foundations.

**Mathlib Status**: [Not yet available / Partial / etc.]

**Proof Exists**: Yes - see [reference to textbook/paper]

**Revisit**: As Mathlib matures, this may become available for import.
-/
axiom [name] : [type]  -- TIER 2: ESTABLISHED MATH TOOLS
```

**Examples to update**:
- `stones_theorem` (Stone 1932)
- `gleason_theorem` (Gleason 1957)
- `hermitian_real_spectrum` (von Neumann 1932)

---

## Template: Tier 3 (Universal Physics)

```lean
/--
[Postulate Name]

**TIER 3: UNIVERSAL PHYSICS ASSUMPTIONS**

**Fundamental Physical Principle**: [Description]

**Justification**: Cannot be derived from mathematics alone

**Used By**: [Other theories using this]

**Status**: Domain-standard physical assumption
-/
axiom [name] : [type]  -- TIER 3: UNIVERSAL PHYSICS ASSUMPTIONS
```

**Example**: `energy_additivity_for_independent_systems` in Energy.lean

---

## Golden Rules

1. **LRT should have only 2-3 Tier 1 axioms** (I, I_infinite, possibly one more)

2. **If you're adding a 4th Tier 1 axiom**, STOP and ask:
   - Can this be proven from I and I_infinite?
   - Is this really LRT-specific or is it established math (Tier 2)?

3. **Tier 2 axioms need literature references**
   - Original paper/book citation
   - Why axiomatized (practical reasons)
   - Note to revisit as Mathlib matures

4. **Every axiom needs a tier label** - No exceptions!

5. **When in doubt**, ask or classify as needing review

---

## What NOT to Do

❌ **WRONG**: Missing tier label
```lean
axiom some_claim : ...
```

❌ **WRONG**: Using `axiom` when theorem is provable
```lean
axiom statespace_monotone : ...  -- This was provable! See ConstraintThreshold.lean
```

❌ **WRONG**: Adding 4th/5th LRT-specific axiom without justification
```lean
axiom new_lrt_claim : ...  -- TIER 1: LRT SPECIFIC
-- ^ Should this really be Tier 1? Can it be proven from I and I_infinite?
```

---

## Revisit Policy for Tier 2

**Periodically (annually or at major Lean releases)**:
1. Check Mathlib changelog for newly added theorems
2. If Tier 2 axiom is now in Mathlib, replace:
   ```lean
   -- OLD
   axiom stones_theorem : ...  -- TIER 2: ESTABLISHED MATH TOOLS

   -- NEW
   -- Previously axiomatized, now available in Mathlib
   import Mathlib.Analysis.Normed.Group.Stone
   ```
3. Document the substitution
4. Verify build
5. Update axiom count tracking

This keeps formalization current as ecosystem matures.

---

## Current Status (Session 9.0)

**Tier 1 (LRT Specific)**: 2 axioms ✅ Properly labeled
- `I : Type*` (IIS.lean)
- `I_infinite : Infinite I` (IIS.lean)

**Tier 2 (Established Math Tools)**: ~16 axioms ⏸️ Need tier labels + documentation

**Tier 3 (Universal Physics)**: 1 axiom ⏸️ Needs tier label + documentation

**LRT Provable Claims**: ~35-40 axioms ⏸️ Should be proven as theorems

**Placeholders**: ~7 ⏸️ Should be removed

---

## See Also

- **AXIOM_CLASSIFICATION_SYSTEM.md**: Full system documentation
- **PROOF_REFACTOR_STRATEGY.md**: Strategy for proving LRT theorems
- **Foundation/IIS.lean**: Example of proper Tier 1 labeling

---

**Last Updated**: 2025-11-04
**Status**: Active protocol for all axiom declarations
