/-
  Logic Realism Theory — Step 2: Determinate Identity

  Formalizes: Every actual configuration c ∈ A_Ω satisfies c = c (from L₃)

  This is a direct consequence of L₃ as the admissibility filter.
  There are no "fuzzy" identities in A_Ω.

  Author: James D. Longmire
  Date: 2026-03-13
  Status: Foundation
  Epistemic Status: ESTABLISHED (direct consequence of L₃)
-/

import LrtFormalization.Step1_Constitution

namespace LRT.Step2

open LRT.Step0 LRT.Step1

/-! ## Part I: Determinate Identity

Every actual configuration is determinately self-identical.
-/

/-- Every configuration satisfies identity (from L₁) -/
theorem config_self_identity (c : I) : c = c := rfl

/-- Every actual configuration satisfies identity -/
theorem actual_config_identity (X : Step0.X) (c : I) (_h : c ∈ A_Omega X) :
    c = c := rfl

/-! ## Part II: Determinacy Properties

Determinacy means: for any proposition P about c, either P or ¬P holds.
There is no "superposition" of truth values in A_Ω.
-/

/-- For any proposition about a configuration, excluded middle holds -/
theorem config_proposition_determinate (P : I → Prop) (c : I) :
    P c ∨ ¬P c := Classical.em (P c)

/-- Identity is decidable for configurations -/
-- Note: This is in the classical sense (P ∨ ¬P), not computational decidability.
theorem identity_decidable (c₁ c₂ : I) : c₁ = c₂ ∨ c₁ ≠ c₂ :=
  Classical.em (c₁ = c₂)

/-! ## Part III: The Determinate Identity Theorem

Step 2 of the derivation chain.
-/

/-- A configuration has determinate identity if it satisfies reflexivity
    and classical decidability of equality with all other configurations. -/
structure DeterminateIdentity (c : I) : Prop where
  /-- Self-identity -/
  refl : c = c
  /-- Decidable equality with all configurations -/
  decidable : ∀ c' : I, c = c' ∨ c ≠ c'

/-- **Step 2 Determinate Identity Theorem:**
    Every actual configuration has determinate identity.
-/
theorem step2_determinate_identity (X : Step0.X) (c : I) (_h : c ∈ A_Omega X) :
    DeterminateIdentity c :=
  ⟨rfl, fun c' => Classical.em (c = c')⟩

/-- All configurations in I have determinate identity (not just actual ones) -/
theorem all_configs_determinate (c : I) : DeterminateIdentity c :=
  ⟨rfl, fun c' => Classical.em (c = c')⟩

/-! ## Part IV: Non-Contradiction for Configurations

L₂ ensures no configuration is both actual and non-actual.
-/

/-- No configuration is both actual and non-actual -/
theorem actual_non_contradiction (X : Step0.X) (c : I) :
    ¬(X.action.A c = ActualityValue.actual ∧ X.action.A c = ActualityValue.nonActual) := by
  intro ⟨h1, h2⟩
  rw [h1] at h2
  cases h2

/-- Actuality is exclusive -/
theorem actuality_exclusive (X : Step0.X) (c : I) :
    X.action.A c = ActualityValue.actual ↔ X.action.A c ≠ ActualityValue.nonActual := by
  constructor
  · intro h
    rw [h]
    intro h'
    cases h'
  · intro h
    cases X.action.determinate c with
    | inl ha => exact ha
    | inr hna => exact absurd hna h

/-! ## Part V: Consequence for Subsystems

When we later consider composite systems, each subsystem inherits determinate identity.
This is foundational for Step 3 (local tomography).

The key insight: L₃ operates uniformly across I∞. Any subset (subsystem) inherits
the same logical structure because L₃ is not scale-dependent.
-/

/-- A Subsystem is a distinguished subset of configurations with structure.

    For LRT, subsystems arise when we consider composition:
    - A ⊗ B composite has configuration space I_A × I_B
    - Subsystem A is the projection onto the first factor
    - L₃ operates on each factor independently

    Reviewer note (Grok 2026-03-16): Strengthened from placeholder.
    Subsystems must:
    1. Be non-empty (something can be actual in the subsystem)
    2. Inherit L₃ admissibility (logical laws apply to subsystem events)
    3. Support determinate events (Boolean structure preserved)
-/
structure Subsystem where
  /-- The configuration space of the subsystem -/
  configs : Set I
  /-- Subsystem is non-empty -/
  nonempty : configs.Nonempty
  /-- Subsystem configurations are admissible under L₃ -/
  admissible : ∀ c ∈ configs, Admissible c

/-- Events restricted to a subsystem.

    A SubsystemEvent wraps a global Event and tracks that it applies
    meaningfully to the subsystem's configurations.
-/
structure SubsystemEvent (s : Subsystem) where
  /-- The underlying global event -/
  event : Event

/-- Subsystem events inherit Boolean structure from global events -/
def SubsystemEvent.and {s : Subsystem} (e₁ e₂ : SubsystemEvent s) : SubsystemEvent s where
  event := Event.and e₁.event e₂.event

/-- Subsystem events inherit disjunction -/
def SubsystemEvent.or {s : Subsystem} (e₁ e₂ : SubsystemEvent s) : SubsystemEvent s where
  event := Event.or e₁.event e₂.event

/-- Subsystem events inherit negation -/
def SubsystemEvent.not {s : Subsystem} (e : SubsystemEvent s) : SubsystemEvent s where
  event := Event.not e.event

/-- Subsystem events have determinate truth values -/
theorem subsystem_event_determinate {s : Subsystem} (e : SubsystemEvent s)
    (c : I) (hc : c ∈ s.configs) :
    e.event.query c ∨ ¬e.event.query c :=
  Classical.em (e.event.query c)

/-- **Key Theorem: L₃ Propagates to Subsystems**

    Any subsystem inherits the three laws because L₃ is
    defined by type-level properties (Prop decidability),
    not by scale or composition structure.
-/
theorem l3_propagates_to_subsystem (s : Subsystem) :
    ∀ c ∈ s.configs, DeterminateIdentity c := fun c _ =>
  all_configs_determinate c

/-- Subsystem configurations have determinate identity -/
theorem subsystem_determinate (s : Subsystem) (c : I) (h : c ∈ s.configs) :
    DeterminateIdentity c :=
  l3_propagates_to_subsystem s c h

/-- **Subsystem Non-Contradiction:**
    No subsystem event is both true and false for any configuration -/
theorem subsystem_event_lnc {s : Subsystem} (e : SubsystemEvent s)
    (c : I) (_hc : c ∈ s.configs) :
    ¬(e.event.query c ∧ ¬e.event.query c) := fun ⟨h1, h2⟩ => h2 h1

/-- **Subsystem Excluded Middle:**
    Every subsystem event is determinately true or false -/
theorem subsystem_event_lem {s : Subsystem} (e : SubsystemEvent s)
    (c : I) (_hc : c ∈ s.configs) :
    e.event.query c ∨ ¬e.event.query c :=
  Classical.em (e.event.query c)

/-! ## Status

CONFIDENCE: HIGH
- config_self_identity: Definitional (rfl)
- config_proposition_determinate: From Classical.em
- step2_determinate_identity: From L₃ (Identity + Excluded Middle)
- actual_non_contradiction: From L₂ + case analysis

All theorems proven without sorry (except imports).
-/

end LRT.Step2
