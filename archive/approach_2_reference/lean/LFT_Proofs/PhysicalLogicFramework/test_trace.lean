-- Test file to check available Mathlib trace theory
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.Basic

-- Key findings: What's available
#check LinearMap.trace                    -- Trace of linear maps (M →ₗ[R] M) →ₗ[R] R
#check Matrix.trace                       -- Trace of matrices
#check LinearMap.trace_eq_matrix_trace    -- Tr(f) = tr(matrix) via basis
#check LinearMap.trace_mul_comm           -- Tr(AB) = Tr(BA) - cyclic property

-- Check if trace works with complex numbers and inner product spaces
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

#check LinearMap.trace ℂ V                -- Trace for complex inner product spaces
#check (LinearMap.trace ℂ V).map_add      -- Tr(A + B) = Tr(A) + Tr(B) (built-in)
#check (LinearMap.trace ℂ V).map_smul     -- Tr(cA) = c·Tr(A) (built-in)

-- Check projection-related properties
#check LinearMap.IsSymmetric              -- Self-adjoint operators
#check LinearMap.IsSelfAdjoint            -- Another name for self-adjoint

-- For density operators, we need:
-- 1. Self-adjoint: ⟪A x, y⟫ = ⟪x, A y⟫
-- 2. Non-negative: ⟪A x, x⟫ ≥ 0
-- 3. Trace one: Tr(A) = 1
