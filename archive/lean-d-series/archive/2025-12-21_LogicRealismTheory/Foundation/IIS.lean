/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0

# Infinite Information Space (IIS)

This module defines the foundational axioms of Logic Realism Theory.
These are the ONLY Tier 1 (LRT-specific) axioms in the entire formalization.

## Correspondence to Technical Paper

Section 2.1-2.2 in:
  Longmire, J.D. (2025). "Logic Realism Theory: Technical Foundations"
  DOI: 10.5281/zenodo.17831883

## Axiom Classification

- **Tier 1 (LRT Specific)**: 2 axioms (defined here)
- **Tier 2 (Established Math)**: See ExternalTheorems.lean
- **Tier 3 (Universal Physics)**: See Dynamics/TimeEvolution.lean

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs

namespace LogicRealismTheory.Foundation

-- ═══════════════════════════════════════════════════════════════════════════════
-- TIER 1 AXIOMS: LRT SPECIFIC (2 total)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Axiom A1: Existence of Infinite Information Space**

The Infinite Information Space I exists as a primitive ontological entity.
I is the space of all possible distinctions - the pre-physical substrate
from which actualized reality emerges.

**Technical Paper Reference:** §2.1, Definition 2.1

TIER 1: LRT SPECIFIC
-/
axiom I : Type

/--
**Axiom A2: Infinite Cardinality of I**

The information space I has infinite cardinality. This ensures that
the space of possible distinctions is not artificially bounded.

**Technical Paper Reference:** §2.1, Axiom A2

TIER 1: LRT SPECIFIC
-/
axiom I_infinite : Infinite I

-- ═══════════════════════════════════════════════════════════════════════════════
-- DERIVED DEFINITIONS (No additional axioms)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A distinction in I is simply an element of the information space. -/
abbrev Distinction := I

/-- A proposition about I is a subset of I. -/
abbrev Proposition := Set I

/-- The logic L(I) is the type of all propositions about I. -/
abbrev L := Set I

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC THEOREMS (Proven from Tier 1 axioms + Lean's logic)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- L(I) is non-empty (contains at least the empty set). -/
theorem L_nonempty : Nonempty L := ⟨∅⟩

/-- L(I) satisfies the law of excluded middle for any proposition. -/
theorem excluded_middle_in_L (P : Set I) (x : I) : x ∈ P ∨ x ∉ P :=
  Classical.em (x ∈ P)

/-- L(I) satisfies non-contradiction for any proposition. -/
theorem non_contradiction_in_L (P : Set I) (x : I) : ¬(x ∈ P ∧ x ∉ P) :=
  fun ⟨h1, h2⟩ => h2 h1

-- ═══════════════════════════════════════════════════════════════════════════════
-- AXIOM COUNT SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- Tier 1 (LRT Specific): 2 axioms
--   - I : Type
--   - I_infinite : Infinite I
--
-- Tier 2 (Established Math): 0 in this file
-- Tier 3 (Universal Physics): 0 in this file
--
-- Theorems proven: 3
--   - L_nonempty
--   - excluded_middle_in_L
--   - non_contradiction_in_L

end LogicRealismTheory.Foundation
