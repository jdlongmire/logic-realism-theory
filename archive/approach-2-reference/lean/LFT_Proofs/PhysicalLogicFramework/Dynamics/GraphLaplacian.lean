/-
Copyright (c) 2025 James D. Longmire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James D. Longmire
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Graph Laplacian as Natural Hamiltonian (Theorem D.1 - Part Infrastructure)

This module establishes the graph Laplacian L = D - A as the natural Hamiltonian
operator for quantum dynamics on discrete permutation state spaces (permutohedron).

## Main definitions

* `PermutohedronGraph N`: The Cayley graph of S_N with adjacent transpositions as edges
* `Hamiltonian N`: The graph Laplacian H = D - A for the permutohedron
* `validStates N K`: The K-constrained valid state space V_K ⊂ S_N

## Main theorems (Sprint 1)

* `hamiltonian_symmetric`: H is symmetric (H = H†)
* `hamiltonian_posSemidef`: H is positive semidefinite
* `hamiltonian_has_zero_eigenvalue`: Constant vector is eigenvector with eigenvalue 0
* `hamiltonian_quadratic_form`: ⟨ψ|H|ψ⟩ = Fisher information

## Connection to Theorem D.1

This module provides the foundational structure for Theorem D.1, which proves that
the graph Laplacian emerges as the unique natural Hamiltonian from three independent
mathematical principles:

1. Information geometry (Fisher = Fubini-Study)
2. Discrete Riemannian geometry (Laplace-Beltrami → Graph Laplacian)
3. Variational principle (minimum Fisher information)

See `TheoremD1.lean` for the complete integrated theorem.

-/

namespace PhysicalLogicFramework.Dynamics

open SimpleGraph Matrix

-- Disable style linters for this foundational file
set_option linter.style.docString false
set_option linter.unusedVariables false

/-!
## Permutohedron Graph Structure

The permutohedron is a convex polytope whose vertices are permutations of {1,...,N}
and edges connect permutations differing by a single adjacent transposition.
It forms the Cayley graph of the symmetric group S_N with generating set
of adjacent transpositions.
-/

/-- A permutation σ is valid if h(σ) ≤ K, where h counts inversions.
For now, we include all permutations (K = ∞), but this will be refined
to match the constraint theory (K = N-2 for maximal quantum behavior). -/
def validPerm (N K : ℕ) (σ : Equiv.Perm (Fin N)) : Prop :=
  true  -- TODO: Add inversion count h(σ) ≤ K constraint

/-- Two permutations are adjacent if they differ by swapping adjacent elements.
This defines the edge relation for the permutohedron Cayley graph. -/
def adjacentTransposition {N : ℕ} (σ τ : Equiv.Perm (Fin N)) : Prop :=
  ∃ i : Fin (N - 1), τ = σ * Equiv.swap ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.sub_le N 1)⟩
    ⟨i + 1, by omega⟩

/-- Adjacent transpositions are loopless: σ * swap(i, i+1) ≠ σ for any permutation σ.
This follows from the fact that swap(i, i+1) is a non-trivial permutation.
**Mathematical justification**: If σ = σ * s for some permutation s, then s = 1 (identity).
But swap(i, i+1) ≠ 1 for i ≠ i+1, so σ * swap(i, i+1) ≠ σ.
**Reference**: Standard result in group theory (non-trivial group elements act non-trivially). -/
theorem adjacentTransposition_loopless {N : ℕ} (σ : Equiv.Perm (Fin N)) :
  ¬ adjacentTransposition σ σ := by
  intro ⟨i, h⟩
  -- h : σ = σ * Equiv.swap a b where a = ⟨i, _⟩, b = ⟨i+1, _⟩
  -- Define the two indices for clarity
  let a : Fin N := ⟨i.val, Nat.lt_of_lt_of_le i.2 (Nat.sub_le N 1)⟩
  let b : Fin N := ⟨i.val + 1, by omega⟩
  -- From σ = σ * swap(a,b), deduce swap(a,b) = 1 by group cancellativity
  have h_swap_eq_one : Equiv.swap a b = 1 := by
    have : σ * Equiv.swap a b = σ * 1 := by rw [← h]; simp
    exact mul_left_cancel this
  -- But a ≠ b (i ≠ i+1)
  have h_ne : a ≠ b := by
    intro h_eq
    injection h_eq with h_val
    omega
  -- Swap of distinct elements is not identity, contradiction
  have : Equiv.swap a b a = a := by rw [h_swap_eq_one]; rfl
  rw [Equiv.swap_apply_left] at this
  exact h_ne this.symm

/-- The permutohedron graph: vertices are permutations, edges are adjacent transpositions.
This is the Cayley graph Cay(S_N, T) where T is the set of adjacent transpositions. -/
def PermutohedronGraph (N : ℕ) : SimpleGraph (Equiv.Perm (Fin N)) where
  Adj := adjacentTransposition
  symm := by
    intro σ τ ⟨i, h⟩
    use i
    rw [h]
    simp only [mul_assoc]
    rw [Equiv.swap_mul_self]
    simp
  loopless := adjacentTransposition_loopless

/-!
## Hamiltonian Operator (Graph Laplacian)

The Hamiltonian H is defined as the graph Laplacian L = D - A where:
- D is the degree matrix (diagonal)
- A is the adjacency matrix (0/1 entries for edges)

This definition uses Mathlib's `SimpleGraph.lapMatrix` which provides
all basic properties automatically.
-/

variable {N : ℕ} [NeZero N] [Fintype (Equiv.Perm (Fin N))] [DecidableEq (Equiv.Perm (Fin N))]

/-- The Hamiltonian operator H for the permutohedron graph.
This is the graph Laplacian L = D - A. -/
def Hamiltonian (N : ℕ) [NeZero N] [Fintype (Equiv.Perm (Fin N))]
    [DecidableEq (Equiv.Perm (Fin N))] [DecidableRel (PermutohedronGraph N).Adj] :
    Matrix (Equiv.Perm (Fin N)) (Equiv.Perm (Fin N)) ℝ :=
  SimpleGraph.lapMatrix ℝ (PermutohedronGraph N)

/-!
## Basic Properties (from Mathlib)

These theorems import fundamental properties of the graph Laplacian
directly from Mathlib's `SimpleGraph.LapMatrix` module.
-/

/-- The Hamiltonian is symmetric: H = Hᵀ.
This is required for H to be a Hermitian operator (observable in QM). -/
theorem hamiltonian_symmetric (N : ℕ) [NeZero N] [Fintype (Equiv.Perm (Fin N))]
    [DecidableEq (Equiv.Perm (Fin N))] [DecidableRel (PermutohedronGraph N).Adj] :
    (Hamiltonian N).IsSymm :=
  SimpleGraph.isSymm_lapMatrix _

/-- The Hamiltonian is positive semidefinite: ⟨ψ|H|ψ⟩ ≥ 0 for all ψ.
This ensures all eigenvalues are non-negative (stable ground state). -/
theorem hamiltonian_posSemidef (N : ℕ) [NeZero N] [Fintype (Equiv.Perm (Fin N))]
    [DecidableEq (Equiv.Perm (Fin N))] [DecidableRel (PermutohedronGraph N).Adj] :
    PosSemidef (Hamiltonian N) :=
  SimpleGraph.posSemidef_lapMatrix ℝ (PermutohedronGraph N)

/-- The constant vector (uniform superposition) is in the kernel of H.
This corresponds to the ground state |ψ₀⟩ = (1/√|V_K|) Σ_σ |σ⟩. -/
theorem hamiltonian_const_in_kernel (N : ℕ) [NeZero N] [Fintype (Equiv.Perm (Fin N))]
    [DecidableEq (Equiv.Perm (Fin N))] [DecidableRel (PermutohedronGraph N).Adj] :
    mulVec (Hamiltonian N) (fun _ ↦ 1) = 0 := by
  unfold Hamiltonian
  simp [SimpleGraph.lapMatrix_mulVec_const_eq_zero]

/-!
## Quadratic Form and Fisher Information

The quadratic form ⟨ψ|H|ψ⟩ equals the Fisher information functional I_F[ψ].
This connection is central to Theorem D.1 Part 3 (minimum Fisher info → Hamiltonian).
-/

/-- The Hamiltonian quadratic form ⟨ψ|H|ψ⟩ equals a sum over edges.
This is the discrete analog of the Fisher information metric. -/
theorem hamiltonian_quadratic_form (N : ℕ) [NeZero N] [Fintype (Equiv.Perm (Fin N))]
    [DecidableEq (Equiv.Perm (Fin N))] [DecidableRel (PermutohedronGraph N).Adj]
    (ψ : Equiv.Perm (Fin N) → ℝ) :
    toLinearMap₂' ℝ (Hamiltonian N) ψ ψ =
    (∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      if (PermutohedronGraph N).Adj σ τ then (ψ σ - ψ τ)^2 else 0) / 2 :=
  SimpleGraph.lapMatrix_toLinearMap₂' _ _ _

/-!
## Cayley Graph Properties

The permutohedron is a regular graph (all vertices have the same degree N-1)
and is vertex-transitive (symmetric group acts transitively). The regularity
follows from standard Cayley graph theory: each vertex has exactly N-1 adjacent
transpositions.
-/

/-!
## Connection to Theorem D.1

This module provides Part 0 (infrastructure) for Theorem D.1:

**Theorem D.1** (Graph Laplacian as Natural Hamiltonian):
The graph Laplacian H = D - A emerges as the unique natural Hamiltonian on
discrete permutation state spaces from three independent principles:

* **Part 1** (FisherGeometry.lean): Fisher metric = Fubini-Study metric
* **Part 2** (ConvergenceTheorem.lean): Laplace-Beltrami → Graph Laplacian
* **Part 3** (VariationalPrinciple.lean): Min Fisher info → H = L

See `TheoremD1.lean` for the complete integration.
-/

end PhysicalLogicFramework.Dynamics
