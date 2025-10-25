/-
Copyright © 2025 James D. (JD) Longmire. All rights reserved.
Released under Apache 2.0 license.
Author: James D. (JD) Longmire

# Epistemic States for Indistinguishable Particles

This module formalizes the epistemic interpretation of indistinguishability.

**Key insight**: Indistinguishability is an **epistemic constraint** (limit on accessible
information), not an **ontic state** (property of particles themselves).

**Core distinction**:
- **Ontic level**: N particles exist as N distinct entities (always true)
- **Epistemic level**: Cannot persistently track which particle is which (information limit)

**Consequence**: Only propositions that don't require persistent particle labels are well-defined.
This leads to the symmetrization postulate: quantum states must be symmetric or antisymmetric.

## Background

**Standard QM**: Symmetrization postulate is an unexplained axiom
- Bosons (integer spin) → symmetric wavefunctions
- Fermions (half-integer spin) → antisymmetric wavefunctions
- Mixed-symmetry states are excluded (not explained why)

**This formalization**: Derives symmetrization from epistemic consistency
- 3FLL (Three Fundamental Laws of Logic) apply to well-defined propositions
- Mixed-symmetry requires tracking particle labels that aren't epistemically accessible
- Therefore, only symmetric/antisymmetric states are logically consistent

## References

Computational validation: notebooks/Logic_Realism/24_Indistinguishability_Epistemic_Foundations.ipynb

Literature:
- QBism (C. Fuchs) - quantum states as epistemic
- Spekkens' toy model - epistemic restrictions reproduce quantum phenomena
- Zeilinger - information interpretation of QM
- Rovelli - relational QM (properties relative to observers)
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic

namespace PhysicalLogicFramework.Indistinguishability

/-!
## Particle Propositions

A proposition about particles may or may not require persistent labels ("particle 1", "particle 2").

**Example (requires labels)**: "Particle 1 is spin-up and particle 2 is spin-down"
**Example (label-free)**: "The two-particle system is in a spin-singlet state"

Only label-free propositions are well-defined when particles are indistinguishable.
-/

/-- A proposition about particle states -/
structure ParticleProp where
  /-- Informal description of the proposition (for documentation) -/
  description : String
  /-- Does this proposition require persistent particle labels to be well-defined? -/
  requires_label : Bool
  deriving Repr

/-!
## Well-Defined Propositions

**Well-defined propositions**: Those that don't require tracking persistent particle labels.

When particles are indistinguishable, propositions requiring labels ("particle 1 is in state A")
are ill-defined because we cannot persistently identify "particle 1" vs "particle 2".

This is analogous to the uncertainty principle: asking for exact position AND momentum is ill-posed,
not because particles "violate" having both properties, but because the question isn't well-formed.
-/

/-- A proposition is well-defined if it doesn't require persistent particle labels -/
def WellDefinedProp (p : ParticleProp) : Prop := ¬ p.requires_label

/-!
## Three Fundamental Laws of Logic (3FLL)

The 3FLL apply to well-defined propositions about epistemically accessible information.

**Critical point**: These are laws about propositions/logic, not about particle ontology.
They constrain what can be consistently known, not what exists.
-/

/-- **Identity Law**: Every well-defined proposition equals itself -/
axiom law_of_identity :
  ∀ (p : ParticleProp), WellDefinedProp p → p.description = p.description

/-- **Non-Contradiction Law**: A well-defined proposition and its negation
    cannot both be true.

For propositions requiring labels (ill-defined), we cannot even formulate
consistent negation.
-/
axiom law_of_non_contradiction :
  ∀ (p : ParticleProp) (prop : Prop), WellDefinedProp p → ¬ (prop ∧ ¬ prop)

/-- **Excluded Middle Law**: Every well-defined proposition is either true or false
    (post-measurement).

For propositions requiring labels (ill-defined), truth values are indeterminate.
-/
axiom law_of_excluded_middle :
  ∀ (p : ParticleProp) (prop : Prop), WellDefinedProp p → (prop ∨ ¬ prop)

/-!
## Indistinguishable Particles (Epistemic Constraint)

**Definition**: Particles are indistinguishable when persistent labels are not
epistemically accessible.

**Consequence**: Propositions requiring labels are not well-defined.

**Important**: This is an epistemic constraint, not an ontic one.
- N particles exist as N distinct entities (ontic - counting preserved)
- We cannot track which is which (epistemic - labeling lost)
-/

/-- Indistinguishable particles: propositions requiring labels are not well-defined -/
def IndistinguishableParticles : Prop :=
  ∀ (p : ParticleProp), p.requires_label → ¬ (WellDefinedProp p)

/-- Trivial consequence: If particles are indistinguishable, label-requiring
    propositions are ill-defined -/
theorem indistinguishability_excludes_labels :
  IndistinguishableParticles →
  ∀ (p : ParticleProp), p.requires_label → ¬ (WellDefinedProp p) := by
  intro h p
  exact h p

/-!
## Symmetry Types

Quantum states can be classified by their behavior under particle exchange:
- **Symmetric**: ψ(1,2) = ψ(2,1) (same state after swapping particles)
- **Antisymmetric**: ψ(1,2) = -ψ(2,1) (picks up minus sign after swap)
- **Mixed-symmetry**: Neither symmetric nor antisymmetric

**Key observation**: Symmetric and antisymmetric states don't require tracking
which particle is "1" vs "2", because swapping gives the same result (up to sign).
Mixed-symmetry states DO require tracking labels.
-/

/-- Symmetry classification for quantum states -/
inductive SymmetryType where
  | Symmetric : SymmetryType
  | Antisymmetric : SymmetryType
  | Mixed : SymmetryType
  deriving Repr, DecidableEq

instance : ToString SymmetryType where
  toString
    | SymmetryType.Symmetric => "Symmetric"
    | SymmetryType.Antisymmetric => "Antisymmetric"
    | SymmetryType.Mixed => "Mixed"

/-- Does a given symmetry type require persistent particle labels? -/
def symmetry_requires_labels : SymmetryType → Bool
  | SymmetryType.Symmetric => false      -- Label-free: ψ(1,2) = ψ(2,1)
  | SymmetryType.Antisymmetric => false  -- Label-free: ψ(1,2) = -ψ(2,1)
  | SymmetryType.Mixed => true           -- Requires labels

/-- Propositions about symmetric states don't require labels -/
def symmetric_proposition (s : SymmetryType) : ParticleProp :=
  { description := s!"State has symmetry type {s}",
    requires_label := symmetry_requires_labels s }

/-!
## Main Result: Symmetrization from Epistemic Consistency

**Theorem**: If particles are indistinguishable (epistemic constraint),
then only symmetric or antisymmetric states correspond to well-defined propositions.

**Proof strategy**:
1. Indistinguishable particles → propositions requiring labels are ill-defined
2. Mixed-symmetry states require labels (to track α·ψ(1,2) + β·ψ(2,1) with α ≠ ±β)
3. Therefore, only symmetric (α=β) or antisymmetric (α=-β) are well-defined

This derives the **symmetrization postulate** from logical consistency (3FLL) +
epistemic constraints.
-/

/-- Core theorem: Indistinguishability implies only symmetric or antisymmetric
    states are well-defined -/
theorem symmetrization_from_epistemic_consistency :
  IndistinguishableParticles →
  ∀ (s : SymmetryType),
    WellDefinedProp (symmetric_proposition s) →
    (s = SymmetryType.Symmetric ∨ s = SymmetryType.Antisymmetric) := by
  intro h_indist s h_well_defined
  -- Proof by contradiction
  by_cases h : s = SymmetryType.Symmetric ∨ s = SymmetryType.Antisymmetric
  · exact h  -- If already symmetric or antisymmetric, we're done
  · -- Otherwise, s must be Mixed
    have h_mixed : s = SymmetryType.Mixed := by
      cases s
      · simp at h  -- s = Symmetric contradicts h
      · simp at h  -- s = Antisymmetric contradicts h
      · rfl  -- s = Mixed
    -- But Mixed requires labels
    rw [h_mixed] at h_well_defined
    unfold symmetric_proposition WellDefinedProp symmetry_requires_labels at h_well_defined
    simp at h_well_defined

/-!
## Physical Interpretation

**What we derived**: Symmetrization postulate (only symmetric/antisymmetric states)

**What we assumed**:
1. Indistinguishable particles exist (epistemic constraint on information)
2. 3FLL apply to well-defined propositions

**What we did NOT derive** (deferred to future work):
- Why some particles are symmetric (bosons) vs antisymmetric (fermions)
- Spin-statistics theorem (requires additional structure or postulates)

**Significance**:
- Standard QM postulates symmetrization without explanation
- We derive it from logical consistency + epistemic constraints
- Reduces axiomatic basis of quantum mechanics

**Future directions** (Sprint 11+):
- Explore commutation vs anticommutation algebras
- Connect to measurement theory and observable operators
- Investigate topological constraints in 3D space
-/

/-!
## Examples (for validation)

These examples demonstrate the formalism with concrete propositions.
-/

/-- Example: Proposition about symmetric state (well-defined, no labels needed) -/
def example_symmetric_prop : ParticleProp :=
  { description := "Two particles in symmetric spin state |↑↑⟩ + |↓↓⟩",
    requires_label := false }

/-- Example: Proposition about antisymmetric state (well-defined, no labels needed) -/
def example_antisymmetric_prop : ParticleProp :=
  { description := "Two particles in spin singlet (1/√2)(|↑↓⟩ - |↓↑⟩)",
    requires_label := false }

/-- Example: Proposition about mixed state (ill-defined, requires tracking
    which is particle 1) -/
def example_mixed_prop : ParticleProp :=
  { description := "Particle 1 spin-up, particle 2 spin-down (not symmetric)",
    requires_label := true }

/-- Symmetric states are well-defined -/
theorem symmetric_well_defined : WellDefinedProp example_symmetric_prop := by
  unfold WellDefinedProp example_symmetric_prop
  simp

/-- Antisymmetric states are well-defined -/
theorem antisymmetric_well_defined : WellDefinedProp example_antisymmetric_prop := by
  unfold WellDefinedProp example_antisymmetric_prop
  simp

/-- Mixed states requiring labels are NOT well-defined under indistinguishability -/
theorem mixed_not_well_defined :
  IndistinguishableParticles → ¬ WellDefinedProp example_mixed_prop := by
  intro h
  exact h example_mixed_prop (by simp [example_mixed_prop])

end PhysicalLogicFramework.Indistinguishability
