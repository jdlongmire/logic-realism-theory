/-
WP-LRT-ONTO-0001: proposed finite countermodel
Status: SOURCE DRAFT, NOT LEAN-BUILD VERIFIED.
This is a standalone finite semantic model. It does not instantiate the
infinite type I in Step0; it refutes an unconditional extensional identity
between an admissible domain and an action-selected actual domain.
-/
import Mathlib.Data.Set.Basic

namespace LRT.ONTO.Countermodel

inductive Candidate where
  | u
  | v
  deriving DecidableEq

open Candidate

def admissible : Set Candidate := Set.univ

def obtains : Candidate → Prop
  | .u => True
  | .v => False

def actual : Set Candidate := { c | obtains c }

theorem u_actual : u ∈ actual := by
  trivial

theorem v_admissible : v ∈ admissible := by
  trivial

theorem v_not_actual : v ∉ actual := by
  simp [actual, obtains]

theorem actual_subset_admissible : actual ⊆ admissible := by
  intro c hc
  trivial

theorem actual_ne_admissible : actual ≠ admissible := by
  intro h
  have hv : v ∈ actual := h.symm ▸ v_admissible
  exact v_not_actual hv

end LRT.ONTO.Countermodel
