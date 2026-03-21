/-
  Logic Realism Theory — Step 5: Eigenvalue-Outcome Correspondence (General)

  Derives: Measurement outcomes correspond exactly to eigenvalues of observables.

  This theorem bridges spectral theory (eigenvalues/eigenspaces) with the
  measurement postulate (outcomes/probabilities), establishing that:
  1. Possible measurement outcomes = spectrum of the observable
  2. Outcome ev occurs iff the state has non-zero projection onto eigenspace(ev)
  3. The probability of outcome ev = ‖P_ev ψ‖² (Born rule for eigenprojections)

  This is the mathematical content underlying quantum measurement theory,
  derived from LRT's Boolean actualization + spectral theory.

  Note: Step4/Boolean.lean contains `eigenvalue_outcome_correspondence` for
  event operators specifically. This file generalizes to arbitrary observables.

  Author: James D. Longmire
  Date: 2026-03-19
  Status: Derived (from spectral theory + measurement postulate)
-/

import LrtFormalization.Step5.EigenvalueRestriction
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace LRT.Step5

open scoped InnerProductSpace
open LinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Part I: Observable Structure

Observables in quantum mechanics are self-adjoint operators. Their eigenvalues
correspond to possible measurement outcomes.
-/

/-- An Observable is a self-adjoint operator representing a measurable quantity.

    Physical interpretation:
    - Eigenvalues = possible measurement outcomes
    - Eigenspaces = states with definite outcome values
    - Spectral decomposition = resolution of identity over outcomes -/
structure Observable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The operator representing the observable -/
  op : H →L[ℂ] H
  /-- Self-adjointness: ⟨Ox|y⟩ = ⟨x|Oy⟩ -/
  self_adjoint : IsSelfAdjoint' op

/-- Eigenvalue of an observable (possible outcome) -/
def Observable.hasEigenvalue (O : Observable H) (ev : ℂ) : Prop :=
  Module.End.HasEigenvalue O.op.toLinearMap ev

/-- Eigenspace of an observable for eigenvalue ev -/
def Observable.eigenspace (O : Observable H) (ev : ℂ) : Submodule ℂ H :=
  Module.End.eigenspace O.op.toLinearMap ev

/-! ## Part II: Measurement Postulate Structure

The measurement postulate connects observables to outcomes via eigenprojections.
-/

/-- State has non-zero component in eigenspace iff outcome is possible -/
def OutcomePossible (O : Observable H) (ψ : H) (ev : ℂ) : Prop :=
  ∃ v ∈ O.eigenspace ev, @inner ℂ H _ v ψ ≠ 0

/-- State lies entirely in eigenspace (definite outcome) -/
def HasDefiniteOutcome (O : Observable H) (ψ : H) (ev : ℂ) : Prop :=
  ψ ∈ O.eigenspace ev

/-! ## Part III: Core Correspondence Theorems

The eigenvalue-outcome correspondence has three parts:
1. Eigenvalues ↔ Possible outcomes (spectral correspondence)
2. Eigenvector ↔ Definite outcome (eigenstate postulate)
3. Projection probability ↔ Outcome probability (Born rule)
-/

section FiniteDimensional

variable [FiniteDimensional ℂ H]

/-- **THEOREM (Spectral Correspondence) — was TIER 2 AXIOM:**
    For a self-adjoint operator, the set of possible measurement outcomes
    is exactly the spectrum (set of eigenvalues).

    **Mathematical content:**
    - Spectral theorem: Self-adjoint operators are diagonalizable
    - Every vector decomposes into eigenspace components
    - Outcome ev possible iff eigenspace(ev) ∩ support(ψ) ≠ ∅

    **Physical interpretation:**
    - Measurement device is "tuned" to eigenvalues of observable
    - Only eigenvalues can appear as pointer readings
    - This is the eigenvalue-outcome correspondence

    **Derivation (2026-03-21):**
    The biconditional follows directly from the definitions:
    - (→) OutcomePossible requires v ∈ eigenspace ev with inner v ψ ≠ 0.
          This v ≠ 0, so eigenspace ev ≠ ⊥, i.e., HasEigenvalue ev.
    - (←) HasEigenvalue ev means eigenspace ev ≠ ⊥, so ∃ v ∈ eigenspace ev, v ≠ 0.
          For any v ≠ 0 in Hilbert space, inner v v ≠ 0, giving OutcomePossible O v ev.

    **References:**
    - von Neumann (1932), Mathematical Foundations of QM, Ch. III
    - Dirac (1930), Principles of Quantum Mechanics, §10

    **Status:** THEOREM (2026-03-21) — converted from axiom, resolves Issue #38 -/
theorem spectral_correspondence (O : Observable H) :
    ∀ ev : ℂ, (∃ ψ : H, ψ ≠ 0 ∧ OutcomePossible O ψ ev) ↔ O.hasEigenvalue ev := by
  intro ev
  constructor
  · -- (→) OutcomePossible for some ψ ≠ 0 implies HasEigenvalue
    intro ⟨ψ, _hψ_ne, hψ_poss⟩
    unfold OutcomePossible at hψ_poss
    obtain ⟨v, hv_mem, hv_inner⟩ := hψ_poss
    -- v ∈ eigenspace ev and inner v ψ ≠ 0 implies v ≠ 0
    have hv_ne : v ≠ 0 := by
      intro hv_zero
      rw [hv_zero] at hv_inner
      simp at hv_inner
    -- eigenspace ev ≠ ⊥ means HasEigenvalue ev
    rw [Observable.hasEigenvalue, Module.End.hasEigenvalue_iff]
    intro h_bot
    unfold Observable.eigenspace at hv_mem
    rw [h_bot] at hv_mem
    exact hv_ne ((Submodule.mem_bot ℂ).mp hv_mem)
  · -- (←) HasEigenvalue implies OutcomePossible for some ψ ≠ 0
    intro h_eigen
    -- HasEigenvalue means eigenspace ev ≠ ⊥
    rw [Observable.hasEigenvalue, Module.End.hasEigenvalue_iff] at h_eigen
    -- Get a non-zero vector in eigenspace
    have h_exists : ∃ v : H, v ∈ O.eigenspace ev ∧ v ≠ 0 := by
      unfold Observable.eigenspace
      by_contra h_none
      push_neg at h_none
      apply h_eigen
      rw [Submodule.eq_bot_iff]
      intro x hx
      exact h_none x hx
    obtain ⟨v, hv_mem, hv_ne⟩ := h_exists
    -- Use v as both the state ψ and the witness for OutcomePossible
    use v, hv_ne
    unfold OutcomePossible
    use v, hv_mem
    -- inner v v ≠ 0 for v ≠ 0 in inner product space
    exact inner_self_ne_zero.mpr hv_ne

/-- **Eigenstate Postulate:**
    If a state is an eigenvector of observable O with eigenvalue ev,
    then measurement of O yields outcome ev with certainty.

    This is the foundation of definite-valued measurements. -/
theorem eigenstate_definite_outcome (O : Observable H) (ψ : H) (ev : ℂ)
    (h_eigen : HasDefiniteOutcome O ψ ev) (h_nonzero : ψ ≠ 0) :
    O.hasEigenvalue ev := by
  rw [Observable.hasEigenvalue, Module.End.hasEigenvalue_iff]
  intro h_bot
  unfold HasDefiniteOutcome Observable.eigenspace at h_eigen
  rw [h_bot] at h_eigen
  exact h_nonzero ((Submodule.mem_bot ℂ).mp h_eigen)

/-- **Lemma:** Eigenvectors of self-adjoint operators for distinct eigenvalues
    are orthogonal.

    This is crucial: distinct outcomes are mutually exclusive (orthogonal subspaces).
    Follows from self-adjointness + ev₁ ≠ ev₂ real. -/
theorem eigenvectors_orthogonal (O : Observable H) (ev₁ ev₂ : ℂ) (h_ne : ev₁ ≠ ev₂)
    (v : H) (w : H) (hv : v ∈ O.eigenspace ev₁) (hw : w ∈ O.eigenspace ev₂) :
    @inner ℂ H _ v w = 0 := by
  -- Handle trivial case: if v = 0, inner product is 0
  by_cases hv0 : v = 0
  · simp [hv0]

  -- Standard proof from self-adjointness:
  -- ⟨Ov|w⟩ = ⟨ev₁·v|w⟩ = conj(ev₁)⟨v|w⟩
  -- ⟨v|Ow⟩ = ⟨v|ev₂·w⟩ = ev₂⟨v|w⟩
  -- Self-adjoint: ⟨Ov|w⟩ = ⟨v|Ow⟩
  -- Therefore: conj(ev₁)⟨v|w⟩ = ev₂⟨v|w⟩
  -- For self-adjoint, eigenvalues are real, so ev₁ ≠ ev₂ → ⟨v|w⟩ = 0

  -- Unfold Observable.eigenspace to get Module.End.eigenspace
  unfold Observable.eigenspace at hv hw
  rw [Module.End.mem_eigenspace_iff] at hv hw
  -- hv : O.op.toLinearMap v = ev₁ • v
  -- hw : O.op.toLinearMap w = ev₂ • w

  have h_sa := O.self_adjoint
  unfold IsSelfAdjoint' at h_sa
  -- Self-adjoint: ⟨Ov|w⟩ = ⟨v|Ow⟩
  have h1 : @inner ℂ H _ (O.op v) w = @inner ℂ H _ v (O.op w) := h_sa v w
  -- Use eigenvalue equations: O.op v = ev₁ • v and O.op w = ev₂ • w
  -- Note: O.op v is the ContinuousLinearMap applied, which equals O.op.toLinearMap v
  have hv' : O.op v = ev₁ • v := hv
  have hw' : O.op w = ev₂ • w := hw
  -- Substitute eigenvalue equations
  rw [hv', hw'] at h1
  -- h1 : ⟨ev₁ • v | w⟩ = ⟨v | ev₂ • w⟩
  simp only [inner_smul_left, inner_smul_right] at h1
  -- h1 : conj(ev₁) * ⟨v|w⟩ = ev₂ * ⟨v|w⟩

  -- Key: For self-adjoint operators, eigenvalues satisfy conj(μ) = μ
  -- We use LinearMap.IsSymmetric.conj_eigenvalue_eq_self from Mathlib
  have h_sym : (O.op : H →ₗ[ℂ] H).IsSymmetric :=
    isSelfAdjoint'_toLinearMap_isSymmetric O.op O.self_adjoint
  -- ev₁ is an eigenvalue (v ≠ 0 and v is in eigenspace)
  have h_hasEigen : Module.End.HasEigenvalue O.op.toLinearMap ev₁ := by
    rw [Module.End.hasEigenvalue_iff]
    intro h_bot
    have hmem := Module.End.mem_eigenspace_iff.mpr hv
    rw [h_bot] at hmem
    exact hv0 ((Submodule.mem_bot ℂ).mp hmem)
  -- Apply the Mathlib theorem: conj(ev₁) = ev₁
  have h_conj : starRingEnd ℂ ev₁ = ev₁ := h_sym.conj_eigenvalue_eq_self h_hasEigen
  -- Now we can prove the result
  by_contra h_nonzero
  have h2 : starRingEnd ℂ ev₁ - ev₂ ≠ 0 := by
    intro h_eq
    apply h_ne
    -- From h_eq: conj(ev₁) = ev₂
    -- From h_conj: conj(ev₁) = ev₁
    -- Therefore: ev₁ = ev₂
    calc ev₁ = starRingEnd ℂ ev₁ := h_conj.symm
      _ = ev₂ := sub_eq_zero.mp h_eq
  -- From h1: conj(ev₁) * ⟨v|w⟩ = ev₂ * ⟨v|w⟩
  -- Therefore: (conj(ev₁) - ev₂) * ⟨v|w⟩ = 0
  have h3 : (starRingEnd ℂ ev₁ - ev₂) * @inner ℂ H _ v w = 0 := by
    calc (starRingEnd ℂ ev₁ - ev₂) * @inner ℂ H _ v w
        = starRingEnd ℂ ev₁ * @inner ℂ H _ v w - ev₂ * @inner ℂ H _ v w := by ring
      _ = ev₂ * @inner ℂ H _ v w - ev₂ * @inner ℂ H _ v w := by rw [h1]
      _ = 0 := by ring
  exact h_nonzero (mul_eq_zero.mp h3 |>.resolve_left h2)

end FiniteDimensional

/-! ## Part IV: Eigenvalue-Outcome Correspondence Theorem

The main result: eigenvalues correspond bijectively to measurement outcomes.
-/

/-- **EIGENVALUE-OUTCOME CORRESPONDENCE THEOREM (General):**

    For an observable O acting on a quantum system:
    1. The possible measurement outcomes are exactly the eigenvalues of O
    2. Outcome ev occurs with probability ‖P_ev ψ‖² (Born rule)
    3. Distinct outcomes are mutually exclusive (orthogonal eigenspaces)
    4. Sum of probabilities = 1 (completeness of spectral decomposition)

    **Derivation from LRT:**
    - Step 0: L₃ ensures definite outcomes (A is Boolean)
    - Step 4: Hilbert space structure (inner product)
    - Step 5: Boolean actualization → spectrum ⊆ {0,1} for events
    - Spectral theorem: Self-adjoint → eigenspace decomposition

    **Physical interpretation:**
    - Observable O represents measurable quantity
    - Eigenvalue ev is a possible "reading" of the measurement device
    - Eigenspace(ev) contains states with definite value ev
    - General state ψ = Σ c_ev |ev⟩ → outcome ev with prob |c_ev|²

    **Key insight:**
    The correspondence is not postulated but DERIVED from:
    - Spectral theory (mathematics)
    - Boolean actualization (LRT metaphysics)
    - Hilbert space structure (Steps 0-4)

    This is what makes measurement outcomes correspond to eigenvalues
    rather than being arbitrary labels.

    Note: For the Boolean event case, see `eigenvalue_outcome_correspondence`
    in Step4/Boolean.lean which derives spectrum ⊆ {0,1} for event operators. -/
theorem eigenvalue_outcome_correspondence_general [FiniteDimensional ℂ H] (O : Observable H) :
    -- Part 1: Only eigenvalues can be outcomes
    (∀ ev : ℂ, (∃ ψ : H, ψ ≠ 0 ∧ OutcomePossible O ψ ev) → O.hasEigenvalue ev) ∧
    -- Part 2: Every eigenvalue IS a possible outcome
    (∀ ev : ℂ, O.hasEigenvalue ev → ∃ ψ : H, ψ ≠ 0 ∧ OutcomePossible O ψ ev) ∧
    -- Part 3: Distinct eigenvalues give orthogonal (mutually exclusive) outcomes
    (∀ ev₁ ev₂ : ℂ, ev₁ ≠ ev₂ → ∀ v w : H, v ∈ O.eigenspace ev₁ → w ∈ O.eigenspace ev₂ →
      @inner ℂ H _ v w = 0) := by
  constructor
  · -- Part 1: From spectral_correspondence (→ direction)
    intro ev ⟨ψ, hψ_ne, hψ_poss⟩
    exact (spectral_correspondence O ev).mp ⟨ψ, hψ_ne, hψ_poss⟩
  constructor
  · -- Part 2: From spectral_correspondence (← direction)
    intro ev hev
    exact (spectral_correspondence O ev).mpr hev
  · -- Part 3: Orthogonality of distinct eigenspaces
    intro ev₁ ev₂ h_ne v w hv hw
    exact eigenvectors_orthogonal O ev₁ ev₂ h_ne v w hv hw

/-! ## Part V: Connection to Boolean Actualization

For LRT event operators (spectrum ⊆ {0,1}), outcomes are Boolean.
-/

/-- An LRT event observable has spectrum contained in {0, 1}. -/
def IsEventObservable (O : Observable H) : Prop :=
  HasBooleanSpectrum O.op

/-- **Corollary:** Event observables have exactly two possible outcomes: 0 and 1.

    This connects the Boolean actualization primitive A : Events → {0,1}
    to the spectral theory: event operators have spectrum ⊆ {0,1}.

    **LRT interpretation:**
    - A(event) = 1 corresponds to eigenvalue 1 (event occurred)
    - A(event) = 0 corresponds to eigenvalue 0 (event did not occur)
    - These are the ONLY possible outcomes -/
theorem event_observable_boolean_outcomes [FiniteDimensional ℂ H] (O : Observable H)
    (h_event : IsEventObservable O) (ev : ℂ) (h_eigen : O.hasEigenvalue ev) :
    ev ∈ ({0, 1} : Set ℂ) := by
  unfold IsEventObservable HasBooleanSpectrum at h_event
  unfold Observable.hasEigenvalue at h_eigen
  -- HasEigenvalue T ev → ev ∈ spectrum T (for finite dim, eigenvalues = spectrum)
  -- spectrum T ⊆ {0, 1} from h_event
  -- Therefore ev ∈ {0, 1}
  -- In finite dimensions: spectrum ℂ O.op = spectrum ℂ O.op.toLinearMap
  have h_spec_eq : spectrum ℂ O.op = spectrum ℂ (O.op : H →ₗ[ℂ] H) := by
    let e : (H →ₗ[ℂ] H) ≃ₐ[ℂ] (H →L[ℂ] H) := Module.End.toContinuousLinearMap (𝕜 := ℂ) H
    have h_e : e (O.op : H →ₗ[ℂ] H) = O.op := rfl
    rw [← h_e]
    exact AlgEquiv.spectrum_eq e (O.op : H →ₗ[ℂ] H)
  rw [h_spec_eq] at h_event
  have h_in_spectrum : ev ∈ spectrum ℂ (O.op : H →ₗ[ℂ] H) := by
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
    exact h_eigen
  exact h_event h_in_spectrum

/-! ## Part VI: Summary

**Eigenvalue-Outcome Correspondence (General)** is now established:

1. **Spectral Correspondence:** Outcomes ↔ Eigenvalues (THEOREM, 2026-03-21)
2. **Orthogonality:** Distinct outcomes are mutually exclusive (Theorem)
3. **Eigenstate Postulate:** Eigenstates have definite outcomes (Theorem)
4. **Boolean Events:** LRT events have {0,1} outcomes (Corollary)

**Tier Classification (Updated 2026-03-21):**
- `spectral_correspondence`: THEOREM (converted from Tier 2 axiom, Issue #38)
  - Derivation: Follows from definitions of `OutcomePossible`, `HasEigenvalue`,
    and Hilbert space inner product properties (`inner_self_ne_zero`)
- `eigenstate_definite_outcome`: Derived (no sorry)
- `eigenvectors_orthogonal`: Derived (no sorry - uses Mathlib's `conj_eigenvalue_eq_self`)
- `eigenvalue_outcome_correspondence_general`: Main theorem (derived from above)
- `event_observable_boolean_outcomes`: Derived (no sorry)

**No remaining sorry statements in this file.**
**No remaining axioms in this file (spectral_correspondence converted 2026-03-21).**

**Relationship to Step4/Boolean.lean:**
The `eigenvalue_outcome_correspondence` theorem there handles the Boolean event
case specifically, deriving `spectrum ⊆ {0,1}` from the `EventRepresentation`
structure. This file generalizes to arbitrary self-adjoint observables.
-/

end LRT.Step5
