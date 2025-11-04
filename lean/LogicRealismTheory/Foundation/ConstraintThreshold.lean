/-
Copyright (c) 2025 James D. (JD) Longmire. All rights reserved.
Released under Apache 2.0 license.
Authors: James D. (JD) Longmire

**Axiom Approach**: See lean/AXIOMS.md for justification of all axioms in this formalization.
-/

import Mathlib.Data.Fintype.Basic

/-!
# Constraint Threshold Foundations

This module defines the foundational concepts of constraint thresholds in Logic Realism Theory.

**Core Concepts**:
- ConstraintViolations: Counts logical inconsistencies in a configuration
- StateSpace: Valid configurations at a given constraint threshold K
- Monotonicity: Lower thresholds yield smaller state spaces

**Refactoring Context**: This module was created during Session 5.3 refactoring to consolidate
measurement modules. Base definitions extracted from Common.lean into Foundation layer following
the approach_2_reference pattern.

## Main definitions

* `ConstraintViolations σ` - Number of constraint violations for configuration σ
* `StateSpace K` - Set of configurations with at most K violations
* `statespace_monotone` - Axiom: K' ≤ K implies StateSpace K' ⊆ StateSpace K

## Foundational Theory

In Logic Realism Theory, information space I contains all possible configurations. The logical
operator L filters I based on constraint satisfaction. Constraint threshold K determines how many
constraint violations are tolerated, with K=0 being fully consistent with actuality A.

**AXIOM INVENTORY**: For complete axiom documentation, see: lean/AXIOMS.md
This module uses 3 foundational axioms:
- Set.card (cardinality for mathematical infrastructure)
- ConstraintViolations (foundational structure of LRT)
- statespace_monotone (monotonicity principle)
-/

namespace LogicRealismTheory.Foundation

-- ═══════════════════════════════════════════════════════════════════════════
-- FUNDAMENTAL CONSTRAINT THRESHOLD DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════════

/--
Axiomatize Set cardinality (not available in current Mathlib version).

**STATUS**: Mathematical infrastructure axiom
**JUSTIFICATION**: Standard set theory, axiomatized until we upgrade to Mathlib version with Set.ncard
-/
axiom Set.card {α : Type*} : Set α → ℕ

/--
Number of constraint violations for a configuration.

**FOUNDATIONAL AXIOM**: This is the core structure in LRT measurement theory.

**Physical Interpretation**: Each configuration σ in information space I has a certain number
of logical constraint violations. When K=0, the configuration is fully consistent (in actuality A).
As K increases, more "near-miss" configurations are included in the state space.

**Implementation Note**: The specific constraints depend on the physical system being modeled.
This axiom establishes the existence of such a counting function without specifying the
constraint details.
-/
axiom ConstraintViolations {V : Type*} : V → ℕ

/--
State space at constraint threshold K: all configurations with ≤ K violations.

**Definition**: StateSpace K = {σ ∈ V | ConstraintViolations(σ) ≤ K}

**Physical Interpretation**: This is the set of "approximately actual" configurations.
K=0 gives the fully actualized states (A), K>0 gives quantum superpositions in LRT.
-/
def StateSpace {V : Type*} (K : ℕ) : Set V := {σ : V | ConstraintViolations σ ≤ K}

/--
Monotonicity: Lower constraint thresholds yield smaller state spaces.

**THEOREM** (proven from StateSpace definition): K' ≤ K implies StateSpace(K') ⊆ StateSpace(K)

**Proof**: If K' ≤ K, then any configuration σ with ConstraintViolations(σ) ≤ K' also satisfies
ConstraintViolations(σ) ≤ K by transitivity of ≤ on natural numbers.

**Physical Interpretation**: Tightening constraints (lowering K) reduces the allowed configurations.
This is the mechanism of wavefunction collapse in LRT: measurement adds constraints, reducing K.

**Status**: ✅ PROVEN (Session 9.0, Phase 1 Step 1)
**Axiom Count**: -1 (was axiom, now theorem)
-/
theorem statespace_monotone {V : Type*} {K K' : ℕ} (h : K' ≤ K) :
    (StateSpace K' : Set V) ⊆ (StateSpace K : Set V) := by
  -- Prove subset inclusion: ∀ σ ∈ StateSpace(K'), σ ∈ StateSpace(K)
  intro σ hσ
  -- Unfold StateSpace definition
  -- hσ : σ ∈ StateSpace K' means ConstraintViolations σ ≤ K'
  -- goal: σ ∈ StateSpace K means ConstraintViolations σ ≤ K
  unfold StateSpace at hσ ⊢
  -- Apply transitivity: ConstraintViolations σ ≤ K' ≤ K
  exact Nat.le_trans hσ h

end LogicRealismTheory.Foundation
