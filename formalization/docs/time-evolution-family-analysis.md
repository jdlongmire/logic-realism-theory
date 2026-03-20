# Time Evolution Family Axiom Analysis

**File:** `LrtFormalization/Step7_Unitarity.lean`
**Line:** 129
**Date:** 2026-03-20
**Status:** ROOT BLOCKER for 4 related axioms

## 1. Current Axiom Structure

The axiom at line 129:

```lean
axiom time_evolution_family : ℝ → (H →L[ℂ] H)
```

This asserts the existence of a family of continuous linear operators `U(t)` indexed by time `t : ℝ`. This is one of **four interrelated axioms**:

| Axiom | Description | Line |
|-------|-------------|------|
| `time_evolution_family` | Existence of U(t) family | 129 |
| `evolution_preserves_norm` | Probability conservation | 135 |
| `evolution_group_composition` | U(s+t) = U(s) * U(t) | 140 |
| `evolution_identity` | U(0) = I | 146 |

Together, these axioms constitute a **one-parameter unitary group**.

## 2. What Mathlib Has

### 2.1 Exponential in Banach Algebras

Mathlib has comprehensive support for the exponential map:

**Key file:** `Mathlib.Analysis.Normed.Algebra.Exponential`

```lean
-- NormedSpace.exp : 𝔸 → 𝔸
-- For any Banach algebra with Algebra ℚ 𝔸
noncomputable irreducible_def exp (x : 𝔸) : 𝔸 :=
  if h : Nonempty (Algebra ℚ 𝔸) then
    (NormedSpace.expSeries ℚ 𝔸).sum x
  else 1
```

**Key properties available:**
- `exp_zero : exp 0 = 1`
- `exp_add_of_commute : Commute x y → exp (x + y) = exp x * exp y`
- `exp_neg : exp (-x) = (exp x)⁻¹` (for division rings)
- `exp_nsmul : exp (n • x) = exp x ^ n`

### 2.2 Matrix Exponential

**Key file:** `Mathlib.Analysis.Normed.Algebra.MatrixExponential`

```lean
-- For Matrix m m 𝔸 with NormedAlgebra ℚ 𝔸
theorem Matrix.exp_add_of_commute (A B : Matrix m m 𝔸) (h : Commute A B) :
    exp (A + B) = exp A * exp B
```

### 2.3 Exponential with Scalar Multiplication

**Key file:** `Mathlib.Analysis.SpecialFunctions.Exponential`

```lean
-- Derivative of exp(t • x) with respect to t
theorem hasDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t
```

This is crucial: it provides `d/dt exp(tA) = A exp(tA)`.

### 2.4 Self-Adjoint to Unitary Map

**Key file:** `Mathlib.Analysis.CStarAlgebra.Exponential`

```lean
/-- The map from selfadjoint elements to unitary elements via exp(I • a) -/
noncomputable def selfAdjoint.expUnitary (a : selfAdjoint A) : unitary A :=
  ⟨exp ((I • a.val) : A), exp_mem_unitary_of_mem_skewAdjoint ...⟩
```

**Key properties:**
- `selfAdjoint.expUnitary_zero : expUnitary 0 = 1`
- `Commute.expUnitary_add : Commute a b → expUnitary (a + b) = expUnitary a * expUnitary b`

### 2.5 Unitary Path Connectivity

**Key file:** `Mathlib.Analysis.CStarAlgebra.Unitary.Connected`

```lean
/-- Path from 1 to expUnitary x via t ↦ expUnitary (t • x) -/
noncomputable def selfAdjoint.expUnitaryPathToOne (x : selfAdjoint A) :
    Path 1 (expUnitary x) where
  toFun t := expUnitary ((t : ℝ) • x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp
```

### 2.6 Circle Group (Simple One-Parameter Group)

**Key file:** `Mathlib.Analysis.Complex.Circle`

```lean
/-- The map fun t => exp (t * I) from ℝ to the unit circle -/
def Circle.exp : C(ℝ, Circle) where
  toFun t := ⟨(t * I).exp, ...⟩

-- Group homomorphism property
theorem Circle.exp_add (x y : ℝ) : exp (x + y) = exp x * exp y
```

## 3. What Mathlib Does NOT Have

### 3.1 Stone's Theorem on One-Parameter Unitary Groups

Listed in `docs/1000.yaml` as `Q4455030: Stone's theorem on one-parameter unitary groups` — **NOT FORMALIZED**.

Stone's theorem states: For every strongly continuous one-parameter unitary group `U(t)` on a Hilbert space, there exists a unique (possibly unbounded) self-adjoint operator `H` such that `U(t) = exp(-itH)`.

### 3.2 Hille-Yosida Theorem

Listed in `docs/1000.yaml` as `Q974405: Hille–Yosida theorem` — **NOT FORMALIZED**.

This characterizes generators of strongly continuous semigroups.

### 3.3 Strongly Continuous Semigroups (C₀-semigroups)

No dedicated infrastructure for:
- `StronglyContinuousSemigroup` structure
- Generator definitions
- Resolvent operators

### 3.4 Unbounded Self-Adjoint Operators

The Hamiltonian `H` in quantum mechanics is typically unbounded. Mathlib has limited support for unbounded operators in general position.

## 4. Construction Strategy Options

### Option A: Axiomatize Hamiltonian (RECOMMENDED)

The cleanest approach given current Mathlib:

```lean
/-- TIER 2 AXIOM: There exists a bounded self-adjoint operator H (Hamiltonian). -/
axiom hamiltonian : H →L[ℂ] H

/-- The Hamiltonian is self-adjoint. -/
axiom hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian

/-- DEFINITION: Time evolution as exponential of Hamiltonian. -/
noncomputable def time_evolution (t : ℝ) : H →L[ℂ] H :=
  exp ((-t * I) • hamiltonian)
```

**Pros:**
- Uses existing Mathlib `exp` machinery
- `exp_add_of_commute` gives group law automatically
- `exp_zero` gives identity
- Self-adjoint structure gives unitarity

**Cons:**
- Restricts to bounded Hamiltonians (excludes position, momentum operators)
- Need to verify `ContinuousLinearMap` forms appropriate algebra

### Option B: Use C*-Algebra Framework

Use `selfAdjoint.expUnitary`:

```lean
variable {A : Type*} [CStarAlgebra A]

/-- Hamiltonian as selfadjoint element -/
axiom H : selfAdjoint A

/-- Time evolution via exponential map -/
noncomputable def U (t : ℝ) : unitary A :=
  selfAdjoint.expUnitary (t • H)
```

**Pros:**
- Group properties follow from `Commute.expUnitary_add`
- Unitarity is automatic
- Path connectivity gives continuity

**Cons:**
- Works in C*-algebra context, not directly on Hilbert spaces
- Requires casting between `unitary A` and `H →L[ℂ] H`

### Option C: Direct Construction on Inner Product Space

Given `H` self-adjoint on finite-dimensional space:

```lean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
         [CompleteSpace H] [FiniteDimensional ℂ H]

-- Finite-dimensional self-adjoint operator
axiom hamiltonian : H →L[ℂ] H
axiom hamiltonian_selfAdjoint : ∀ x y, ⟨hamiltonian x, y⟩ = ⟨x, hamiltonian y⟩

-- exp exists on finite-dimensional spaces
noncomputable def time_evolution (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ℂ ((-t * I : ℂ) • hamiltonian)
```

**Note:** This requires `FiniteDimensional` which may be too restrictive.

## 5. Verification of Group Properties

With any construction approach, we need to prove:

### 5.1 Identity: `U(0) = I`

Using `exp_zero`:
```lean
theorem evolution_identity : time_evolution 0 = ContinuousLinearMap.id ℂ H := by
  simp [time_evolution, exp_zero]
```

### 5.2 Composition: `U(s + t) = U(s) * U(t)`

Using `exp_add_of_commute`:
```lean
theorem evolution_composition (s t : ℝ) :
    time_evolution (s + t) = time_evolution s * time_evolution t := by
  simp only [time_evolution]
  -- Need: (-(s+t) * I) • H = (-s * I) • H + (-t * I) • H
  -- And: Commute ((-s * I) • H) ((-t * I) • H)
  rw [exp_add_of_commute]
  · ring_nf
  · -- Commute proof: scalar multiples of same operator commute
    exact Commute.smul_left (Commute.smul_right (Commute.refl _) _) _
```

### 5.3 Norm Preservation: `‖U(t)ψ‖ = ‖ψ‖`

This requires proving the exponential of a skew-adjoint operator is unitary.

**Key lemma needed:**
```lean
lemma exp_skewAdjoint_isUnitary (A : H →L[ℂ] H)
    (hA : ∀ x y, ⟨A x, y⟩ = -⟨x, A y⟩) :
    IsUnitary (exp A)
```

This is available in Mathlib as `exp_mem_unitary_of_mem_skewAdjoint`.

## 6. Concrete Next Steps

### Step 1: Add Hamiltonian Axiom

In `Step7_Unitarity.lean`, replace `time_evolution_family` with:

```lean
/-- TIER 2 AXIOM (LRT): The Hamiltonian operator exists and is self-adjoint. -/
axiom hamiltonian : H →L[ℂ] H

/-- TIER 2 AXIOM (LRT): Hamiltonian is self-adjoint. -/
axiom hamiltonian_isSelfAdjoint : IsSelfAdjoint hamiltonian
```

### Step 2: Define Time Evolution

```lean
/-- Time evolution operator U(t) = exp(-itH) -/
noncomputable def time_evolution_family (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ((-t * Complex.I : ℂ) • hamiltonian)
```

### Step 3: Derive Group Properties

Convert axioms to theorems:

```lean
theorem evolution_identity' : time_evolution_family 0 = ContinuousLinearMap.id ℂ H := by
  simp [time_evolution_family]
  sorry -- needs exp_zero for ContinuousLinearMap

theorem evolution_group_composition' (s t : ℝ) :
    time_evolution_family (s + t) = time_evolution_family s * time_evolution_family t := by
  sorry -- needs exp_add_of_commute
```

### Step 4: Required Imports

```lean
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
```

## 7. Blocking Issues

### Issue 1: ContinuousLinearMap is Not a NormedAlgebra

`H →L[ℂ] H` has `NormedRing` structure but needs to verify:
- `Algebra ℚ (H →L[ℂ] H)` or `Algebra ℂ (H →L[ℂ] H)`

**Check:** `Mathlib.Analysis.Normed.Operator.Basic` may have this.

### Issue 2: Unbounded Operators

If we want the full physical theory, we need unbounded operators. This would require:
- Defining dense domains
- Spectral theory for unbounded operators
- Stone's theorem proper

This is significant foundational work not yet in Mathlib.

### Issue 3: Continuity in t

We get analyticity from `exp`, but may need to explicitly show strong continuity.

## 8. Recommendations

### Short Term (Axiom Reduction)

**Replace 4 axioms with 2:**
1. `hamiltonian : H →L[ℂ] H` (existence)
2. `hamiltonian_isSelfAdjoint : IsSelfAdjoint hamiltonian` (self-adjointness)

**Then derive:**
- `time_evolution_family` as definition
- `evolution_identity` as theorem
- `evolution_group_composition` as theorem
- `evolution_preserves_norm` as theorem

**Net reduction:** 4 axioms → 2 axioms

### Medium Term (Further Work)

1. Verify `NormedSpace.exp` works on `H →L[ℂ] H`
2. Prove group law from `exp_add_of_commute`
3. Prove unitarity from `exp_mem_unitary_of_mem_skewAdjoint`

### Long Term (Future Mathlib)

Wait for:
- Stone's theorem formalization
- Strongly continuous semigroup infrastructure
- Unbounded operator theory

## 9. Summary

| Current | Proposed |
|---------|----------|
| `time_evolution_family` (axiom) | `time_evolution_family` (def via exp) |
| `evolution_preserves_norm` (axiom) | Theorem from self-adjoint |
| `evolution_group_composition` (axiom) | Theorem from exp_add |
| `evolution_identity` (axiom) | Theorem from exp_zero |
| — | `hamiltonian` (new axiom) |
| — | `hamiltonian_isSelfAdjoint` (new axiom) |

**Net effect:** More physically transparent axioms (Hamiltonian existence) with standard consequences derived.
