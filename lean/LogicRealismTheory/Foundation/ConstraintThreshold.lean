/-
Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
Citation: Longmire, J.D. (2025). Logic Realism Theory: A Research Program for Ontological Logic in Informational Reality. Logic Realism Theory Repository.

**Axiom Approach**: See lean/AXIOMS.md for justification of all axioms in this formalization.

# Foundation: Constraint Threshold and K-Mechanism

This module defines the constraint threshold (K) mechanism that distinguishes quantum superposition
from classical definiteness in LRT.

**Core Concept**: K quantifies constraint violations. K=0 → classical (fully constrained, in A).
K>0 → quantum (partially constrained, in I but not yet A).

**Axiom Count by Tier**:
- Tier 1 (LRT Specific): 1 axiom (ConstraintViolations - may be definable in future)
- Tier 2 (Established Math Tools): 1 axiom (Set.card - revisit when Mathlib matures)
- Tier 3 (Universal Physics): 0 axioms
- **Total**: 2 axioms + 1 proven theorem (statespace_monotone)

**Strategy**: Define StateSpace from ConstraintViolations, prove monotonicity from definition.
The K-mechanism is a core LRT concept that explains measurement (K → K-ΔK) vs. unitary evolution (K fixed).

## Key Definitions and Theorems

* `ConstraintViolations σ` - Axiom (Tier 1): Counts constraint violations
* `StateSpace K` - Definition: Configurations with ≤ K violations
* `statespace_monotone` - Theorem: K' ≤ K implies StateSpace(K') ⊆ StateSpace(K) ✅ PROVEN

## Connection to LRT Core Thesis

In A = L(I), the logical operator L enforces constraints (Identity, Non-Contradiction, Excluded Middle).
K measures how many constraints are violated. Full enforcement (K=0) produces classical reality (A).
Partial enforcement (K>0) allows quantum superposition (elements still in I, not fully actualized to A).

-/

-- Imports
import Mathlib.Data.Fintype.Basic

namespace LogicRealismTheory.Foundation

-- ═══════════════════════════════════════════════════════════════════════════
-- AXIOMS (2 total: 1 Tier 1 + 1 Tier 2)
-- ═══════════════════════════════════════════════════════════════════════════

/--
Set cardinality function

**TIER 2: ESTABLISHED MATH TOOLS**

**Established Result**: Set cardinality is standard in set theory and Mathlib.

**Why Axiomatized**: Current Mathlib version doesn't expose Set.ncard in the needed form.
This is a temporary axiom until we upgrade to a Mathlib version with complete set cardinality API.

**Mathlib Status**: Partially available (Finset.card exists, Set.ncard exists but may have
different signature). Will be replaced with direct import when Mathlib API stabilizes.

**Revisit**: Check Mathlib changelog at each Lean 4 update for Set.ncard availability.

**Status**: Temporary mathematical infrastructure axiom (not novel LRT claim)
-/
axiom Set.card {α : Type*} : Set α → ℕ  -- TIER 2: ESTABLISHED MATH TOOLS

/--
Constraint violations counting function

**TIER 1: LRT SPECIFIC**

**Theory-Defining Concept**: This is the core K-mechanism of LRT. Each configuration σ has a
number of logical constraint violations (violations of Identity, Non-Contradiction, Excluded Middle).

**Physical Interpretation**:
- K=0: Configuration fully satisfies all constraints (classical, in A)
- K>0: Configuration violates K constraints (quantum superposition, in I but not A)

**Justification**: The K-threshold is what distinguishes LRT's explanation of quantum vs. classical.
Measurement reduces K (adds constraints). Unitary evolution preserves K.

**May Be Definable**: Future work could define this from 3FLL constraint structure rather than
axiomatize. For now, treated as primitive function establishing the K-mechanism.

**Status**: LRT-specific axiom (core to theory)

**References**: Logic_Realism_Theory_Main.md Section 4.4 (K-Threshold Framework)
-/
axiom ConstraintViolations {V : Type*} : V → ℕ  -- TIER 1: LRT SPECIFIC

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
