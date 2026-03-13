# S9: Lean 4 Formalization Strategy for Step 5 (Eigenvalue Restriction)

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Type:** Formalization Specification (no Lean code; strategy only)
**Addresses:** Step 5 proof obligations; Boolean A → projection operators argument

---

## Abstract

This supplement develops the formalization strategy for Step 5 (eigenvalue restriction) in Lean 4. Step 5 argues that the Boolean character of LRT's action primitive A entails that all event operators on the Hilbert space $\mathcal{H}$ are projection operators — operators with spectrum in $\{0,1\}$ — rather than general POVM elements. The strategy identifies required type signatures, Mathlib spectral theory dependencies, proof obligations, and staging. The target is a machine-verifiable proof that Boolean actualization constrains event operators to be projections. This document is a specification; actual Lean code follows in a separate implementation phase.

---

## 1. The Formalization Target

### 1.1 What Must Be Proven

**Main Theorem (Step 5 — Eigenvalue Restriction):** If the action primitive A is Boolean (outputs in $\{0,1\}$), then every event operator representing an actualization predicate is a projection operator.

**Formal Statement (target):**
```lean
theorem step5_eigenvalue_restriction
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : H →L[ℂ] H)
    (h_self_adjoint : IsSelfAdjoint E)
    (h_event_operator : IsEventOperator E)  -- Encodes Boolean actualization constraint
    : E ^ 2 = E
```

where `IsEventOperator E` formalizes the condition that E represents an actualization predicate with Boolean output.

### 1.2 Dependency Chain

The proof requires formalizing:
1. **L<sub>3</sub> constitutive status** (already in `D0_1_ThreeFundamentalLaws.lean`)
2. **Action primitive A** with Boolean codomain (new: from LRT-MASTER §1.2)
3. **Event operator definition** connecting operator eigenvalues to A's output (new)
4. **Spectral characterization of projections** (Mathlib: standard spectral theory)
5. **Boolean eigenvalue constraint → projection** (the main theorem)

### 1.3 Epistemic Status of Components

| Component | Source | Current Status | Target Status |
|-----------|--------|----------------|---------------|
| L<sub>3</sub> | D0_1 | ESTABLISHED (Lean) | — |
| Boolean A definition | LRT-MASTER §1.2 | ESTABLISHED (prose) | ESTABLISHED (Lean) |
| Event operator type | S3 (prose) | ARGUED (prose) | ESTABLISHED (Lean) |
| Spectral theorem | Mathlib | ESTABLISHED | Import |
| Projection characterization | Mathlib + custom | ESTABLISHED | Prove |
| Step 5 main theorem | S3, LRT-MASTER | ARGUED (prose) | ESTABLISHED (Lean) |

---

## 2. Spectral Theory Dependencies in Mathlib

### 2.1 Required Mathlib Imports

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
```

### 2.2 Key Mathlib Structures and Theorems

| LRT Concept | Mathlib Structure/Theorem | Notes |
|-------------|---------------------------|-------|
| Hilbert space | `InnerProductSpace ℂ H` + `CompleteSpace H` | Standard complex Hilbert space |
| Self-adjoint operator | `IsSelfAdjoint` | From `LinearMap.IsSelfAdjoint` |
| Spectrum of operator | `spectrum ℂ T` | Set of eigenvalues |
| Spectral theorem | Various (see below) | Different forms available |
| Projection | `IsOrthoProjection` or `P^2 = P` | Idempotent + self-adjoint |

### 2.3 Mathlib Spectral Theory Status (as of 2026)

**Available:**
- `spectrum`: The spectrum of a bounded linear operator
- `eigenspace`: Eigenspaces for specific eigenvalues
- `IsStarNormal`: Normal operators (includes self-adjoint)
- Spectral mapping theorems for polynomial functions
- Projection operators and orthogonal complements

**Partially Available:**
- Spectral decomposition for self-adjoint operators (functional calculus approach)
- Continuous functional calculus on C*-algebras

**Gap Analysis:**
The key lemma — "self-adjoint operator with spectrum in $\{0,1\}$ satisfies $P^2 = P$" — may require custom proof assembling Mathlib components.

### 2.4 Spectral Theorem Forms in Mathlib

Mathlib offers several approaches to spectral theory:

1. **Algebraic approach:** `spectrum ℂ T` gives eigenvalues; functional calculus extends to continuous functions.

2. **Projection-valued measure approach:** Not fully developed in Mathlib as of 2026; would need axiomatization.

3. **Direct idempotent characterization:** For finite-dimensional spaces, can prove directly that eigenvalues in $\{0,1\}$ implies $P^2 = P$.

**Recommended approach:** Use the algebraic characterization combined with polynomial functional calculus. The polynomial $p(\lambda) = \lambda^2 - \lambda$ vanishes on $\{0,1\}$, so $p(T) = T^2 - T = 0$ for any operator with spectrum in $\{0,1\}$.

---

## 3. Type Signatures (Specification)

### 3.1 Core Types

```lean
/-- The Boolean codomain of the action primitive A -/
abbrev BooleanOutcome : Type := Bool
-- or equivalently: Fin 2

/-- A's output is Boolean: for any event E and configuration c,
    A(E,c) ∈ {0,1} -/
def A_boolean (A : Event → Config → ℕ) : Prop :=
  ∀ E c, A E c = 0 ∨ A E c = 1
```

```lean
/-- An event operator on Hilbert space H -/
structure EventOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  op : H →L[ℂ] H
  is_self_adjoint : IsSelfAdjoint op
```

```lean
/-- An event operator represents an actualization predicate:
    its eigenvalues correspond to A's Boolean outputs -/
def IsActualizationOperator
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : EventOperator H) : Prop :=
  spectrum ℂ E.op ⊆ {0, 1}
```

### 3.2 The Projection Characterization

```lean
/-- A bounded self-adjoint operator is a projection iff it is idempotent -/
def IsProjection
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint P ∧ P ^ 2 = P
```

```lean
/-- Orthogonal projection (stronger: onto a closed subspace) -/
def IsOrthoProjection
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : H →L[ℂ] H) : Prop :=
  ∃ K : Submodule ℂ H, IsComplete K ∧ P = orthogonalProjection K
```

### 3.3 Connection Types

```lean
/-- The actualization interpretation: measurement outcome = eigenvalue -/
structure ActualizationInterpretation
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : EventOperator H) where
  eigenvalue_outcome :
    ∀ λ ∈ spectrum ℂ E.op, λ = 0 ∨ λ = 1
  -- Outcome λ = 1 means "event is actual"
  -- Outcome λ = 0 means "event is not actual"
```

---

## 4. Proof Obligations

### 4.1 Main Theorem

**Target:**
```lean
theorem step5_eigenvalue_restriction
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : EventOperator H)
    (h_actualization : IsActualizationOperator H E) :
    IsProjection H E.op
```

**Proof sketch (formalization target):**

1. `h_actualization` gives: `spectrum ℂ E.op ⊆ {0, 1}`
2. The polynomial $p(\lambda) = \lambda^2 - \lambda = \lambda(\lambda - 1)$ vanishes on $\{0, 1\}$
3. By the spectral mapping theorem: if $f$ vanishes on $\sigma(T)$, then $f(T) = 0$
4. Therefore $E.op^2 - E.op = 0$, i.e., $E.op^2 = E.op$
5. Combined with `E.is_self_adjoint`, this gives `IsProjection H E.op`

### 4.2 Supporting Lemmas

**Lemma 4.2.1 (Polynomial Spectral Mapping):**
```lean
lemma polynomial_vanishes_on_spectrum
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H)
    (p : Polynomial ℂ)
    (h_vanishes : ∀ λ ∈ spectrum ℂ T, p.eval λ = 0) :
    p.aeval T = 0
```

*Proof obligation:* This is the polynomial functional calculus. May be available in Mathlib under `Polynomial.aeval_eq_zero_of_forall_mem_spectrum_eq_zero` or similar.

**Lemma 4.2.2 (Spectrum Subset Implies Polynomial Vanishing):**
```lean
lemma spectrum_01_implies_idempotent
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H)
    (h_spectrum : spectrum ℂ T ⊆ {0, 1}) :
    T ^ 2 = T
```

*Proof obligation:* Apply Lemma 4.2.1 to $p(\lambda) = \lambda^2 - \lambda$.

**Lemma 4.2.3 (Self-Adjoint + Idempotent = Orthogonal Projection):**
```lean
lemma self_adjoint_idempotent_is_orthogonal_projection
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : H →L[ℂ] H)
    (h_sa : IsSelfAdjoint P)
    (h_idem : P ^ 2 = P) :
    IsOrthoProjection H P
```

*Proof obligation:* Construct the subspace $K = \text{range}(P)$ and show $P = \text{orthogonalProjection } K$.

### 4.3 Dependency Graph

```
D0_1 (L₃)
    ↓
Boolean A definition (new)
    ↓
EventOperator type (new)
    ↓
IsActualizationOperator definition (new)
    ↓
Lemma: polynomial_vanishes_on_spectrum (Mathlib / prove)
    ↓
Lemma: spectrum_01_implies_idempotent (prove)
    ↓
Lemma: self_adjoint_idempotent_is_orthogonal_projection (prove)
    ↓
step5_eigenvalue_restriction (main theorem)
    ↓
IsProjection / IsOrthoProjection
```

---

## 5. The Actualization Interpretation Bridge

### 5.1 The Conceptual Gap

The mathematical argument (spectrum $\subseteq \{0,1\}$ $\Rightarrow$ projection) is straightforward. The formalization challenge is **grounding** the spectrum constraint in LRT's Boolean actualization primitive.

**The bridge argument (from S3):**
1. A is Boolean: $A : D \to \{0,1\}$ where $D = L_3(I_\infty)$
2. Events are propositions about configurations; A assigns actuality status
3. Measurement outcomes correspond to A's actualization values (Premise 4 in S3)
4. Measurement outcomes are eigenvalues of event operators (spectral theorem)
5. Therefore eigenvalues $\in \{0,1\}$

### 5.2 Formalization of the Bridge

**Option A: Axiomatize the correspondence**

```lean
/-- TIER 2 AXIOM (actualization interpretation):
    The eigenvalue obtained by measuring E on state ψ equals
    the actualization value A(E, ψ). -/
axiom actualization_eigenvalue_correspondence
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : EventOperator H)
    (ψ : H)
    (λ : ℂ)
    (h_eigenvalue : ψ ∈ eigenspace E.op λ) :
    λ = 0 ∨ λ = 1
```

*Status:* This axiom encodes the actualization interpretation. It is a physical input (Tier 2/3) connecting operator eigenvalues to LRT's ontology.

**Option B: Derive from measurement structure**

Define a `MeasurementContext` type that explicitly models the physical interaction, and prove that LRT's Boolean A constrains eigenvalues. This is more elaborate but reduces axiom count.

**Recommendation:** Use Option A for initial formalization. The axiom makes the physical input explicit and localizable. It can be refined in future work if a more derived treatment becomes available.

### 5.3 The No-Intermediate-Actualization Lemma

```lean
/-- L₃'s Excluded Middle rules out intermediate actualization values -/
lemma excluded_middle_no_intermediate_actualization
    (A : Event → Config → ℝ)
    (E : Event) (c : Config)
    (h_L3 : SatisfiesL3 c)  -- c is L₃-admissible
    (h_actualization : A E c ∈ Set.Icc 0 1) :  -- A output in [0,1]
    A E c = 0 ∨ A E c = 1
```

*Proof obligation:* This requires formalizing how Excluded Middle (from L<sub>3</sub>) constrains A's output. The prose argument in S3 is:
- For any event E and configuration c, either E is actual or E is not actual (EM)
- "E is actual" corresponds to output 1; "E is not actual" to output 0
- No third option exists
- Therefore A's output is in $\{0,1\}$, not $(0,1)$

---

## 6. Staging Plan

### 6.1 Phase 1: Foundation Extensions

**Files to create:**
- `LogicRealismTheory/Step5/BooleanAction.lean`
- `LogicRealismTheory/Step5/EventOperator.lean`

**Content:**
- `BooleanOutcome` type
- `A_boolean` predicate
- `EventOperator` structure
- `IsActualizationOperator` definition
- Basic lemmas about Boolean outputs

**Estimated effort:** 1-2 days

### 6.2 Phase 2: Spectral Theory Lemmas

**Files to create:**
- `LogicRealismTheory/Step5/SpectralLemmas.lean`

**Content:**
- Import Mathlib spectral theory
- `polynomial_vanishes_on_spectrum` (if not in Mathlib)
- `spectrum_01_implies_idempotent`
- `self_adjoint_idempotent_is_orthogonal_projection`

**Estimated effort:** 2-4 days (depends on Mathlib coverage)

### 6.3 Phase 3: Actualization Bridge

**Files to create:**
- `LogicRealismTheory/Step5/ActualizationInterpretation.lean`

**Content:**
- `ActualizationInterpretation` structure
- `actualization_eigenvalue_correspondence` axiom (Tier 2)
- Connection to L<sub>3</sub> via `excluded_middle_no_intermediate_actualization`

**Estimated effort:** 1-2 days

### 6.4 Phase 4: Main Theorem

**Files to create:**
- `LogicRealismTheory/Step5/EigenvalueRestriction.lean`

**Content:**
- `step5_eigenvalue_restriction` theorem
- Integration with Step 4 (Hilbert space) and Step 6 (Gleason)

**Estimated effort:** 1-2 days

### 6.5 Total Estimated Effort

| Phase | Days | Critical? |
|-------|------|-----------|
| Phase 1 | 1-2 | Foundation |
| Phase 2 | 2-4 | **Critical** (Mathlib gap) |
| Phase 3 | 1-2 | Bridge |
| Phase 4 | 1-2 | Integration |
| **Total** | **5-10** | — |

---

## 7. Critical Challenges

### 7.1 Mathlib Spectral Theory Gap

**Challenge:** The polynomial functional calculus result needed may not be directly available in Mathlib for general bounded operators on Hilbert spaces.

**Mitigation options:**
1. **Finite-dimensional restriction:** For finite-dimensional H, the spectral theorem is simpler and more completely formalized.
2. **Direct eigenvalue argument:** Instead of functional calculus, prove directly that for any eigenvector $v$ with eigenvalue $\lambda$, we have $P^2 v = \lambda^2 v = \lambda v = P v$ (since $\lambda^2 = \lambda$ for $\lambda \in \{0,1\}$).
3. **Axiomatize spectral mapping:** Add a Tier 2 axiom for the polynomial spectral mapping theorem.

**Recommendation:** Start with option 2 (direct eigenvalue argument) as it avoids functional calculus machinery.

### 7.2 Infinite-Dimensional Subtleties

**Challenge:** In infinite dimensions, operators may have continuous spectrum, and the spectral theorem involves projection-valued measures rather than eigenvalue sums.

**Analysis:** For LRT's Step 5, the relevant operators are event operators with Boolean actualization structure. The claim is that their spectrum (point + continuous) is contained in $\{0,1\}$. For bounded self-adjoint operators, this is equivalent to being a projection.

**Mitigation:** State the theorem for bounded operators with spectrum in $\{0,1\}$, which is well-defined. The physical input (actualization interpretation) constrains the spectrum; the mathematics shows this implies projection.

### 7.3 The Actualization Interpretation as Axiom

**Challenge:** The correspondence "eigenvalues = actualization values" is a physical interpretation, not a mathematical theorem. Making it an axiom adds to the tier count.

**Analysis:** This is unavoidable — the connection between operator formalism and LRT's ontology requires a bridge principle. The axiom is analogous to the Born rule's eigenvalue interpretation in standard QM.

**Classification:** Tier 2 (physical principle widely accepted in QM foundations). It is the LRT-specific grounding of the standard eigenvalue-eigenstate link.

---

## 8. Open Questions

### 8.1 Scope of Formalization

**Q1:** Should we formalize Step 5 for bounded operators only, or include unbounded self-adjoint operators?

**Recommendation:** Start bounded. Unbounded operators (position, momentum, Hamiltonians) use the spectral theorem for unbounded operators, which is more complex. The core eigenvalue restriction argument applies equally, but formalization is harder. Extension to unbounded operators is a follow-up.

### 8.2 POVM Treatment

**Q2:** Should the formalization include the Naimark dilation theorem showing POVMs arise from PVMs on extended spaces?

**Recommendation:** Defer. Naimark dilation is Tier 2 mathematics but not required for Step 5's core claim. It supports the interpretive point that POVMs are derived, not fundamental — but this is already argued in S3 at the prose level.

### 8.3 Connection to Gleason

**Q3:** How tightly should Step 5 formalization link to Step 6 (Gleason's theorem)?

**Recommendation:** Keep them modular. Step 5 establishes PVM structure; Step 6 takes PVMs as input and produces the Born rule. The formalization should reflect this: `step5_eigenvalue_restriction` produces `IsProjection`, which `step6_gleason` consumes.

---

## 9. Connection to Other Steps

### 9.1 Upstream Dependencies

| Dependency | File | Status |
|------------|------|--------|
| L<sub>3</sub> (classical logic) | `D0_1_ThreeFundamentalLaws.lean` | Complete |
| I<sub>∞</sub>, Infinite | `D0_2_InformationSpace.lean` | Complete |
| Complex Hilbert space (Step 4) | External / Mathlib | Available |

### 9.2 Downstream Consumers

| Consumer | Depends On | Notes |
|----------|------------|-------|
| Step 6 (Gleason) | PVM structure | Import `IsProjection` from Step 5 |
| Step 7 (Born rule) | Steps 5 + 6 | Transitive |

### 9.3 Parallel Work

S9 (this strategy) can proceed in parallel with:
- S8 (Step 3 formalization — local tomography)
- S10 (if targeting dynamics, Steps 8-13)

Step 5 formalization is independent of Step 3 formalization; both are prerequisites for Step 6.

---

## 10. Summary

### 10.1 Formalization Deliverables

| File | Content | Priority |
|------|---------|----------|
| `Step5/BooleanAction.lean` | Boolean A definition, basic lemmas | P1 |
| `Step5/EventOperator.lean` | EventOperator type, IsActualizationOperator | P1 |
| `Step5/SpectralLemmas.lean` | Mathlib imports, spectral lemmas | P1 (critical) |
| `Step5/ActualizationInterpretation.lean` | Bridge axiom, L<sub>3</sub> connection | P2 |
| `Step5/EigenvalueRestriction.lean` | Main theorem | P3 |

### 10.2 Success Criteria

1. **Compilation:** All files compile without `sorry` (except Tier 2 axioms)
2. **Theorem proven:** `step5_eigenvalue_restriction` proven from definitions + Tier 2 axiom
3. **Mathlib integration:** Spectral theory properly imported; no reinvention
4. **Tier compliance:** One new Tier 2 axiom maximum (actualization interpretation)
5. **Documentation:** Each file has header matching STANDARD_FILE_HEADER.md

### 10.3 Risks and Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Mathlib spectral gap | Medium | Medium | Direct eigenvalue argument (avoid functional calculus) |
| Unbounded operator complications | Low | Low | Restrict to bounded; note extension |
| Actualization axiom objection | Low | Medium | Clear Tier 2 classification with citation |

---

## 11. Next Steps

1. **Audit Mathlib spectral theory** for `spectrum_01_implies_idempotent` equivalents
2. **Create `Step5/BooleanAction.lean`** with Boolean A type
3. **Prototype the direct eigenvalue argument** for spectrum $\subseteq \{0,1\}$ → idempotent
4. **Draft actualization axiom** with proper tier labeling
5. **Assemble main theorem** once lemmas are in place

---

## References

Busch, P. (2003). Quantum states and generalized observables: A simple proof of Gleason's theorem. *Physical Review Letters*, 91(12), 120403.

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885-893.

Mathlib Community. (2026). *Mathlib: The Lean Mathematical Library*. https://github.com/leanprover-community/mathlib4

Naimark, M. A. (1943). Positive definite operator functions on a commutative group. *Izvestiya Rossiiskoi Akademii Nauk. Seriya Matematicheskaya*, 7(5), 237-244.

Reed, M., and Simon, B. (1980). *Methods of Modern Mathematical Physics I: Functional Analysis*. Academic Press.

---

*Supplement S9 | Logic Realism Theory Project | 2026-03-13*
