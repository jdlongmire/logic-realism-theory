# LRT Lean Strategy: Minimal Axiom Formalization

**Date**: October 25, 2025
**Goal**: Define ~5-10 axioms for LRT, prove everything else as theorems
**Context**: Approach 2 had 140 axioms (lesson learned: too many)

---

## Core Principle: Axiomatic Minimalism

**Philosophy**: An axiom is ONLY justified if it's:
1. **Unprovable** from more basic principles
2. **Necessary** for the theory (removing it breaks derivations)
3. **Primitive** (can't be defined in terms of other concepts)

**Everything else** should be:
- **Definition** (if it's a new concept built from axioms)
- **Theorem** (if it's a provable consequence)
- **Import** from Mathlib (if it's standard mathematics)

---

## Proposed Axiom Set (~5-6 axioms)

### Axiom 1: Infinite Information Space Exists

```lean
-- The primitive ontological entity: infinite information space
axiom IIS : Type*

-- IIS is infinite (not finite)
axiom iis_infinite : Infinite IIS
```

**Justification**:
- This is the ontological primitive of LRT
- Can't be proven from anything more basic (it's the foundation)
- Wheeler's "It from Bit" + infinity assumption

**Approach 2 equivalent**: `InfiniteInformationSpace` (18 axioms in Foundations)
**Reduction**: 18 → 2 axioms

---

### Axiom 2-4: The Three Fundamental Laws of Logic (3FLL)

```lean
-- Identity: Every element of IIS has persistent identity
axiom identity_law : ∀ (x : IIS), x = x

-- Non-Contradiction: No element can simultaneously be and not be
axiom non_contradiction_law : ∀ (x : IIS) (P : IIS → Prop),
  ¬(P x ∧ ¬P x)

-- Excluded Middle: Every proposition about IIS is either true or false
axiom excluded_middle_law : ∀ (x : IIS) (P : IIS → Prop),
  P x ∨ ¬P x
```

**Justification**:
- These are ontological laws, not epistemological (LRT's core claim)
- They operate on IIS to produce actualization
- Can't be proven (they're the logical foundation of proof itself)

**Philosophical note**: LRT argues these are not "laws of thought" but "laws of being"

**Approach 2 equivalent**: InfoSpaceStructure axioms (absorbed into 3FLL)
**Reduction**: Many property axioms → 3 fundamental laws

---

### Axiom 5: Hilbert Space Structure

```lean
-- IIS admits Hilbert space structure for operator formalism
axiom iis_hilbert_space : Type* → NormedAddCommGroup IIS ∧ InnerProductSpace ℂ IIS
```

**Justification**:
- Operators (Π_id, {Π_i}, R) need Hilbert space to be defined
- This is mathematical structure assumption, not derivable from 3FLL alone
- Standard quantum formalism (we're deriving QM, but we need math structure)

**Alternative approach**: Import Hilbert space axioms from Mathlib
- Pro: 0 new axioms (use standard math)
- Con: Less explicit about our specific use

**Decision**: Try to use Mathlib's `NormedSpace`, `InnerProductSpace` classes
- If successful: 0 axioms (import only)
- If Mathlib insufficient: 1-2 axioms for our specific structure

**Approach 2 equivalent**: Scattered across QuantumEmergence (72 axioms)
**Reduction**: 72 → 0-2 axioms (rest are theorems or Mathlib imports)

---

### Axiom 6 (Optional): Actualization Principle

```lean
-- Actualization is the result of 3FLL filtering IIS
axiom actualization_principle :
  ∃ (A : Set IIS), A = { x : IIS | identity_law x ∧
                                    (∀ P, non_contradiction_law x P) ∧
                                    (∀ P, excluded_middle_law x P) }
```

**Justification**:
- This is the A = L(I) principle
- Could be a **definition** instead of axiom

**Decision**: Make it a **definition**, not axiom!

```lean
def Actualization : Set IIS :=
  { x : IIS | identity_law x ∧
              (∀ P, non_contradiction_law x P) ∧
              (∀ P, excluded_middle_law x P) }
```

**Result**: This is NOT an axiom (it's a definition)

---

## Total Axiom Count: **5** (or **5-7** if Hilbert space needs explicit axioms)

**Minimal set**:
1. `axiom IIS : Type*` (ontological primitive)
2. `axiom iis_infinite : Infinite IIS` (infinity assumption)
3. `axiom identity_law` (3FLL: Identity)
4. `axiom non_contradiction_law` (3FLL: Non-Contradiction)
5. `axiom excluded_middle_law` (3FLL: Excluded Middle)

**Optional** (if Mathlib insufficient):
6. `axiom iis_inner_product : InnerProductSpace ℂ IIS`
7. `axiom iis_complete : CompleteSpace IIS`

**Everything else** (operators, derivations) becomes **definitions** and **theorems**.

---

## What Becomes Definitions (Not Axioms)

### Operator Definitions

```lean
-- Identity projector (persistence operator)
def Π_id : IIS →ₗ[ℂ] IIS :=
  -- Definition: Projects onto identity-satisfying subspace
  ...

-- Incompatibility projector family (non-contradiction)
def incompatible_projectors : ∀ (i j : ℕ), i ≠ j →
  Π_i ∘ Π_j = 0 :=
  -- Definition: Orthogonal projectors for incompatible states
  ...

-- Resolution map (excluded middle, Booleanization)
def resolution_map (R : IIS → Bool) : IIS →ₗ[ℂ] Bool :=
  -- Definition: Forces binary outcomes
  ...

-- Logical filter (composition of 3FLL)
def logical_filter : IIS → Prop :=
  λ x => identity_law x ∧
         (∀ P, non_contradiction_law x P) ∧
         (∀ P, excluded_middle_law x P)

-- Actualization (NOT an axiom!)
def Actualization : Set IIS :=
  { x : IIS | logical_filter x }
```

**Key insight**: All operators are **defined** in terms of 3FLL axioms, not axiomatized separately.

---

## What Becomes Theorems (Not Axioms)

### Time Emergence Theorem

```lean
theorem time_emergence :
  ∃ (t : ℝ → IIS →ₗ[ℂ] IIS),
    (∀ t₁ t₂, U(t₁ + t₂) = U(t₁) ∘ U(t₂)) ∧
    (∃ H : IIS →ₗ[ℂ] IIS, U(t) = exp(-i * H * t / ℏ))
:= by
  -- Proof: Stone's theorem applied to identity_law
  -- identity_law requires continuity → continuous 1-parameter unitary group
  -- Stone's theorem → ∃ H such that U(t) = e^(-iHt/ℏ)
  sorry -- Placeholder (will be proven)
```

**Why theorem**: This is derivable from identity_law + Hilbert space structure + Stone's theorem (standard math)

### Born Rule Theorem

```lean
theorem born_rule :
  ∀ (ψ : IIS), ‖ψ‖ = 1 →
    ∃ (p : IIS → ℝ),
      (∀ x, p(x) = ‖⟨x|ψ⟩‖²) ∧
      (∀ x, p(x) ≥ 0) ∧
      (Σ x, p(x) = 1)
:= by
  -- Proof: Maximum entropy under identity + NC constraints
  sorry -- Placeholder (will be proven)
```

**Why theorem**: Derivable from 3FLL + maximum entropy principle

### Measurement Collapse Theorem

```lean
theorem measurement_collapse :
  ∀ (ψ : IIS) (observable : IIS →ₗ[ℂ] IIS),
    ∃ (ψ' : IIS), resolution_map ψ = ψ' ∧
                   ψ' ∈ eigenspace(observable)
:= by
  -- Proof: Excluded middle forces definite outcome
  sorry -- Placeholder (will be proven)
```

**Why theorem**: Derivable from excluded_middle_law + resolution_map definition

### Constraint Hierarchy Theorem

```lean
theorem constraint_hierarchy :
  IIS ⊇ ℋ_Id ⊇ ℋ_NC ⊇ 𝒜
  where
    ℋ_Id = { x : IIS | identity_law x }
    ℋ_NC = { x : ℋ_Id | ∀ P, non_contradiction_law x P }
    𝒜 = { x : ℋ_NC | ∀ P, excluded_middle_law x P }
:= by
  -- Proof: Sequential application of 3FLL constraints
  sorry -- Placeholder (will be proven)
```

**Why theorem**: This is the logical structure implied by 3FLL, not an axiom

---

## Module Structure

### Lean File Organization

```
lean/LogicRealismTheory/
├── Foundation/
│   ├── IIS.lean                    # Axioms 1-5 (foundation)
│   ├── ThreeLaws.lean              # 3FLL properties and lemmas
│   └── HilbertStructure.lean       # Hilbert space imports from Mathlib
├── Operators/
│   ├── IdentityProjector.lean      # Π_id definition + properties
│   ├── IncompatibilityFamily.lean  # {Π_i} definition + orthogonality
│   ├── ResolutionMap.lean          # R definition + Booleanization
│   └── LogicalFilter.lean          # L = EM ∘ NC ∘ Id composition
├── Derivations/
│   ├── TimeEmergence.lean          # Theorem: Stone's theorem → time
│   ├── EnergyConstraint.lean       # Theorem: Spohn's inequality → energy
│   ├── BornRule.lean               # Theorem: MaxEnt → Born rule
│   ├── Superposition.lean          # Theorem: Partial constraint
│   └── Measurement.lean            # Theorem: Full constraint → collapse
└── Realizations/
    └── SymmetricGroups.lean        # S_N as concrete realization
```

**File count**: ~13 files (vs. Approach 2's ~30+ files)
**Total axioms**: 5-7 (vs. Approach 2's 140)
**Total theorems**: ~15-20 major theorems (all proven, 0 sorry)

---

## Proof Strategy: "Axioms → Definitions → Theorems"

### Step 1: Axioms (IIS + 3FLL)

Establish the minimal ontological foundation:
- IIS exists
- 3FLL operate on IIS

**No proofs needed** (these are axioms)

### Step 2: Definitions (Operators)

Define operators in terms of 3FLL:
- Π_id = projection onto identity-satisfying subspace
- {Π_i} = orthogonal projectors (from NC)
- R = resolution map (from EM)
- L = R ∘ {Π_i} ∘ Π_id

**No proofs needed** (these are definitions)

### Step 3: Theorems (Derivations)

Prove physical consequences:
- Time emergence: identity_law → continuous evolution → Stone's theorem → U(t) = e^(-iHt/ℏ)
- Born rule: 3FLL + MaxEnt → p(x) = |⟨x|ψ⟩|²
- Measurement: excluded_middle_law + R → collapse to eigenstate
- Superposition: identity_law + non_contradiction_law (but not EM) → quantum superposition
- Energy: Spohn's inequality + constraint measure → E ∝ constraint applied

**Proofs required** (but these are standard techniques)

---

## Comparison: Approach 2 vs. LRT Lean

| Metric | Approach 2 | LRT (Target) | Improvement |
|--------|------------|--------------|-------------|
| **Axioms** | 140 | 5-7 | **96% reduction** |
| **Sorry statements** | 0 | 0 | Maintained |
| **Modules** | 6 | 4 | Simplified |
| **Files** | ~30 | ~13 | Streamlined |
| **Philosophy** | Implicit | Explicit (3FLL) | Clearer |
| **Operator formalism** | Concrete (S_N) | Abstract + concrete | More general |
| **Primary prediction** | Finite-N | β ≠ 0 | More testable |

---

## Implementation Timeline

### Phase 1: Foundation (Week 1)
- Create `IIS.lean` with 5 axioms
- Verify build with Mathlib imports
- Establish 3FLL properties (lemmas)

**Deliverable**: 5 axioms, 0 sorry, builds successfully

### Phase 2: Operators (Week 2)
- Define Π_id, {Π_i}, R
- Prove orthogonality, composition properties
- Define logical_filter and Actualization

**Deliverable**: All operators defined, properties proven

### Phase 3: Derivations (Weeks 3-4)
- Time emergence theorem
- Born rule theorem
- Measurement collapse theorem
- Energy constraint theorem
- Superposition theorem

**Deliverable**: 5 major theorems, all proven (0 sorry)

### Phase 4: Realization (Week 5)
- Show S_N as concrete realization of abstract operators
- Bridge to Approach 2 computational results

**Deliverable**: Complete formalization, reference to Approach 2

---

## Risk Mitigation

### Risk 1: "Can we really get to 5 axioms?"

**Mitigation**:
- If Hilbert space needs explicit axioms, go to 7-8
- Still a 95% reduction from 140
- Document each axiom's necessity

### Risk 2: "What if theorems are unprovable?"

**Mitigation**:
- Start with Stone's theorem (standard math, should be in Mathlib)
- If proof is too hard, add as axiom WITH justification
- Document any "axioms of convenience" separately from "axioms of necessity"

### Risk 3: "What if Mathlib is insufficient?"

**Mitigation**:
- Import Mathlib's `Analysis.InnerProductSpace`, `Analysis.NormedSpace`
- If gaps exist, add minimal axioms (2-3 max)
- Contribute missing proofs to Mathlib (community benefit)

---

## Success Criteria

**Minimal Success** (acceptable):
- 10 axioms total
- 0 sorry statements
- All 5 major derivations (time, energy, Born, superposition, measurement)

**Target Success** (goal):
- 5-7 axioms total
- 0 sorry statements
- All 5 major derivations + S_N realization

**Ideal Success** (stretch):
- 5 axioms exactly (IIS + iis_infinite + 3FLL)
- 0 sorry statements
- All derivations + S_N + β prediction formalized

---

## Next Steps

1. ✅ **Complete this strategy** (this document)
2. 🔄 **Outline 9 notebook sequence** (what does each notebook derive?)
3. ⏳ **Create repository setup plan** (folder structure, initial files)
4. ⏳ **Draft Session 0.0 for LRT** (handoff document)
5. ⏳ **Discuss with user** (get approval before creating repo)

---

**Status**: Lean strategy complete, targeting 5-7 axioms (96% reduction from Approach 2)
