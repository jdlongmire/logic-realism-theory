# Lean 4 Typeclass Inference Issue - NonUnitaryEvolution.lean

Need expert guidance on resolving typeclass inference errors in Lean 4 module.

## Context
Formalizing quantum measurement theory in Lean 4. Module addresses peer review concern about Stone's theorem (requires unitarity) vs non-unitary measurement. Theory document complete - now need Lean formalization to compile.

## Progress So Far
- Successfully imported Matrix from Mathlib.Data.Matrix.Basic
- All Matrix operations work (conjTranspose, mulVec, mul, one)
- Real.sqrt and analysis functions compile
- Using dot notation throughout

## Current Issue
Persistent typeclass inference errors with section variables:

```lean
variable {V : Type*} [Fintype V] [DecidableEq V]

structure UnitaryOperator (K : ℕ) where
  matrix : Matrix V V ℂ
  unitary : matrix.conjTranspose * matrix = 1
  preserves_K : ∀ (ψ : QuantumState K) (σ : V),
    σ ∈ StateSpace K → (matrix.mulVec ψ.amplitude) σ ≠ 0 → σ ∈ StateSpace K

axiom measurement_is_projection {K_pre K_post : ℕ}
    (M : MeasurementOperator K_pre K_post) :
  M.matrix * M.matrix = M.matrix
```

## Errors
```
error: typeclass instance problem is stuck, it is often due to metavariables
  Fintype ?m.4
error: typeclass instance problem is stuck, it is often due to metavariables
  HMul (Matrix ?m.25 ?m.25 ℂ) (Matrix ?m.25 ?m.25 ℂ) (Matrix ?m.25 ?m.25 ℂ)
error: typeclass instance problem is stuck, it is often due to metavariables
  DecidableEq ?m.1
```

Errors occur at lines: 87, 102, 106, 111, 114, 145, 154, 171, 174, 178, 185

## What We've Tried
1. Imported Matrix from Mathlib (works!)
2. Used dot notation instead of namespace notation
3. Added `open Matrix` to namespace
4. Section variables still not captured in axiom/structure contexts

## Reference Implementation
approach_2_reference/.../MeasurementMechanism.lean compiles successfully with same Matrix imports and similar structures. Key difference: may have different variable/instance handling.

## Questions
1. **How to ensure section variable instances are captured in axioms?**
   - Do we need explicit instance parameters instead of section variables?
   - Should axioms declare instances explicitly: `axiom foo {V : Type*} [Fintype V] [DecidableEq V] ...`?

2. **Structure field type inference:**
   - Why does `matrix : Matrix V V ℂ` not capture section variable instances?
   - Do structure fields need explicit instance annotations?

3. **Multiplication typeclass:**
   - Why is `HMul (Matrix ?m.25 ?m.25 ℂ)` stuck on metavariables?
   - Is there a missing instance declaration or import?

4. **Alternative approaches:**
   - Should we restructure to avoid section variables?
   - Is there a pattern from Mathlib we should follow?

## Module Details
- File: lean/LogicRealismTheory/Measurement/NonUnitaryEvolution.lean
- Imports: Mathlib.Data.Complex.Basic, Mathlib.Data.Fintype.Basic, Mathlib.Data.Matrix.Basic, Mathlib.Analysis.InnerProductSpace.Basic, Mathlib.Analysis.SpecialFunctions.Sqrt
- Namespace: LogicRealismTheory.Measurement
- Open: Complex Matrix

## Success Criteria
Module compiles with 0 errors (sorrys acceptable for proof obligations).

## Urgency
Module is NOT imported in root (non-blocking), but we want to complete formalization for peer review readiness.

Please provide:
1. Root cause analysis of typeclass inference failures
2. Specific fixes for the error patterns
3. Code examples showing correct approach
4. Any missing imports or instance declarations needed
5. Or a valid workaround if the current approach is fundamentally incompatible with Lean 4
