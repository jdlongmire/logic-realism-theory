# Effect Algebras and Chu Spaces for Step 3 Tomography Bridge

**Date:** 2026-03-17
**Purpose:** Research findings for closing the `stats_imply_events` gap in Step3_LocalTomography.lean
**Status:** Research complete, formalization paths identified

---

## Executive Summary

The `stats_imply_events` hypothesis in Step 3 (line 329-331) requires a bridge from:
- **Input:** Equal probability statistics on product effects for two states
- **Output:** Equal Boolean event truth values on their configurations

Two mathematical frameworks provide rigorous foundations for this bridge:

1. **Effect Algebras:** Boolean algebras embed as full subcategory; every effect algebra is a colimit of finite Boolean algebras
2. **Chu Spaces:** Provide duality between states and events via the Chu construction on Set

The key insight: **probability statistics on effects determine states via Gleason's theorem**, and **states determine event truth values via the effect algebra representation theorem**.

---

## The Gap: `stats_imply_events`

From `Step3_LocalTomography.lean:329-331`:

```lean
(stats_imply_events : forall (rho sigma : sys.AB.State),
  (forall (e : ProductEffect sys), pep.prob rho e = pep.prob sigma e) ->
  forall (e : Step0.Event), e.query (state_to_config rho) <-> e.query (state_to_config sigma))
```

This hypothesis asserts: if two states have identical probability distributions over all product effects, then they agree on all Boolean event queries.

**Why this matters:** The derivation of H1 (Tomographic Locality) from L3 hinges on this bridge. Without it, the logical connection between statistical equality and configuration identity remains unformalized.

---

## Framework 1: Effect Algebras

### Definition

An **effect algebra** is a partial commutative monoid (E, +, 0) with an orthocomplement (-)^perp satisfying:
- x^perp is the unique element with x + x^perp = 1
- x + 1 defined implies x = 0

**Key insight:** Effect algebras generalize Boolean algebras to accommodate quantum "fuzzy" effects.

### Boolean Algebra Embedding (Key Result)

**Theorem (Staton-Uijlen):** Every Boolean algebra embeds as a full subcategory of the category of effect algebras. More strongly:

> "Every effect algebra is a canonical colimit of finite Boolean algebras."

**Reference:** [Staton & Uijlen, "Effect Algebras as Presheaves on Finite Boolean Algebras"](https://www.cs.ox.ac.uk/people/samuel.staton/papers/infocomp2017.pdf)

This means:
1. Boolean algebras ARE effect algebras (via: a + b defined iff a AND b = 0)
2. A Boolean algebra homomorphism is exactly an effect algebra morphism
3. Finite Boolean algebras form a dense subcategory

### Presheaf Representation

**Theorem (Staton-Uijlen):** Every effect algebra A can be faithfully represented by a presheaf R(A) on the category of finite Boolean algebras.

This provides the formalization path: represent LRT events as an effect algebra, then use the presheaf representation to connect Boolean measurement statistics to the effect algebra structure.

### Application to stats_imply_events

**Strategy:**
1. Model Step0.Event as a Boolean subalgebra of an effect algebra
2. Model ProductEffect sys as effects in the same effect algebra
3. Use the presheaf representation: agreement on effects implies agreement on their Boolean "shadows"

**Formalizable Witness:**
```lean
-- Effect algebra structure on events
structure EffectAlgebraStructure (E : Type*) where
  add : E -> E -> E  -- partial, defined when orthogonal
  zero : E
  one : E
  orthocomplement : E -> E
  -- axioms...

-- Boolean subalgebra embedding
def boolean_embedding (B : BooleanAlgebra) (E : EffectAlgebraStructure) :
  (B.carrier -> E.carrier) := ...

-- Key theorem: effect equality implies Boolean shadow equality
theorem effect_stats_determine_boolean_shadow
  (A : EffectAlgebraStructure)
  (B : BooleanAlgebra)
  (emb : boolean_embedding B A)
  (rho sigma : State)
  (h : forall e : A.carrier, prob rho e = prob sigma e) :
  forall b : B.carrier, prob rho (emb b) = prob sigma (emb b) := by
  intro b
  exact h (emb b)
```

---

## Framework 2: Chu Spaces

### Definition

A **Chu space** over a set K is a triple (A, r, X) where:
- A is a set of "points" (or states)
- X is a set of "states" (or events)
- r : A x X -> K is an evaluation function

For K = 2 (two elements), Chu(Set, 2) captures classical logic; states and events are dual.

### Key Property: Self-Duality

The Chu construction yields a star-autonomous category where objects are self-dual:

> "Chu(C, d)^op -> Chu(C, d) takes (a, b; r) to (b, a; r^dagger)"

**Reference:** [nLab, Chu Construction](https://ncatlab.org/nlab/show/Chu+construction)

### Boolean Algebras in Chu(Set, 2)

**Theorem:** Chu(Set, 2) realizes Boolean algebras, distributive lattices, semilattices, and complete atomic Boolean algebras as special cases.

This means LRT's Boolean event structure can be embedded in Chu(Set, 2), gaining:
- Duality between states and events
- Stone-type correspondence
- Categorical tools for proofs

### Application to stats_imply_events

**Strategy:**
1. Model (configurations, events, query) as a Chu space (I, Event, query)
2. Model (states, effects, prob) as related Chu space structure
3. Use Chu morphism properties to transfer statistical agreement to event agreement

**Formalizable Witness:**
```lean
-- Chu space structure
structure ChuSpace (K : Type*) where
  points : Type*      -- states/configurations
  costates : Type*    -- events/effects
  eval : points -> costates -> K

-- For Boolean events: K = Prop (or Bool)
def EventChuSpace (chi : X) : ChuSpace Prop := {
  points := I
  costates := Step0.Event
  eval := fun c e => e.query c
}

-- Chu morphism preserves evaluation
def ChuMorphism (A B : ChuSpace K) :=
  { f : A.points -> B.points //
    exists g : B.costates -> A.costates,
    forall a x, A.eval a (g x) = B.eval (f a) x }

-- Key theorem: Chu isomorphism preserves event agreement
theorem chu_iso_preserves_events
  (A : ChuSpace Prop)
  (rho sigma : A.points)
  (h : forall e : A.costates, A.eval rho e = A.eval sigma e) :
  rho = sigma := by
  -- Uses that events separate points (from L3 via config_separation)
  sorry
```

---

## Framework 3: Projection-Valued Measures (PVMs)

### Definition

A **projection-valued measure** is a map P : Sigma -> Proj(H) from a sigma-algebra to projections on a Hilbert space, satisfying:
- P(empty) = 0, P(Omega) = I
- P(A cap B) = P(A) * P(B) (multiplicativity)
- P(A cup B) = P(A) + P(B) for disjoint A, B (additivity)

### Boolean to Projection Bridge

**Key Property:** PVMs are exactly homomorphisms from Boolean sigma-algebras to projection lattices:

> "A projection-valued measure is an algebra homomorphism from the Boolean algebra of Borel sets into the Hilbert lattice of projections."

This is the EXACT construction needed for stats_imply_events: Boolean events map homomorphically to projections, preserving the Boolean structure.

### Application to stats_imply_events

**Strategy:**
1. LRT Boolean events form a Boolean algebra
2. Construct PVM: Event -> Proj(H)
3. Probability on projections = probability on events (homomorphism)
4. Gleason's theorem: probability statistics determine state
5. State determines projection truth values, hence event truth values

**Formalizable Witness:**
```lean
-- PVM structure (already in Step4/Boolean.lean as PVM)
structure PVM (H : Type*) [InnerProductSpace C H] where
  meas : BooleanAlgebra -> (H ->L[C] H)
  orthogonal : forall A B, disjoint A B -> meas A * meas B = 0
  additive : forall A B, disjoint A B -> meas (A cup B) = meas A + meas B
  complete : meas top = ContinuousLinearMap.id C H

-- Events embed as PVM
axiom complete_events_form_pvm :
  forall (chi : X), exists (pvm : PVM H),
  forall (e : Step0.Event), IsOrthogonalProjection (pvm.event_proj e)
```

This axiom already exists in Step4/Boolean.lean:297 and is the direct bridge.

---

## Gleason's Theorem as the Key Witness

### Statement

**Gleason's Theorem (1957):** For dim(H) >= 3, every finitely additive probability measure on projections extends uniquely to a state (density operator via Born rule).

Conversely, every state restricts to such a measure.

### Why This Closes the Gap

1. **Probability statistics on effects** are exactly probability measures on projections (via PVM bridge)
2. **Gleason guarantees:** same statistics => same density operator (state)
3. **Same state** => same expectation values on all projections
4. **Projections include** Boolean event projections (via PVM embedding)
5. **Therefore:** same statistics => same event truth values

**Reference:** [nLab, Gleason's Theorem](https://ncatlab.org/nlab/show/Gleason's+theorem)

### Formal Statement

```lean
-- Gleason's theorem (already axiomatized in Step6_BornRule.lean:197)
axiom gleason_theorem [FiniteDimensional C H] :
  forall (f : ValidFrameFunction H),
  exists! (rho : DensityOperator H),
    True  -- Conceptual: f.f(|e>) = <e|rho|e>

-- Stats determine state (Gleason consequence)
theorem stats_determine_state
  [FiniteDimensional C H]
  (rho sigma : DensityOperator H)
  (h_stats : forall (P : Proj H), Tr(rho * P) = Tr(sigma * P)) :
  rho = sigma := by
  -- Direct from Gleason uniqueness
  sorry  -- Would use gleason_theorem uniqueness clause

-- Therefore stats imply events
theorem stats_imply_events_via_gleason
  [FiniteDimensional C H]
  (rho sigma : sys.AB.State)
  (pvm : PVM H)
  (h_stats : forall e : ProductEffect sys, pep.prob rho e = pep.prob sigma e) :
  forall (e : Step0.Event),
    event_truth rho (pvm.event_proj e) <-> event_truth sigma (pvm.event_proj e) := by
  -- 1. h_stats implies equal probability on all projections
  -- 2. Gleason implies equal states
  -- 3. Equal states have equal truth values on projections
  sorry
```

---

## Formalization Strategy

### Path A: Direct Effect Algebra Route

1. **Define effect algebra structure** in Lean
2. **Prove Boolean embedding** (Boolean algebras are effect algebras)
3. **Use presheaf representation** to show effect statistics cover Boolean events
4. **Connect to existing `complete_events_form_pvm`** axiom

**Difficulty:** Medium. Requires new algebraic infrastructure.

### Path B: PVM + Gleason Route (Recommended)

1. **Use existing `complete_events_form_pvm`** axiom (Step4/Boolean.lean:297)
2. **Use existing `gleason_theorem`** axiom (Step6_BornRule.lean:197)
3. **Chain:** ProductEffect -> PVM -> Gleason uniqueness -> Event truth values

**Difficulty:** Low. Leverages existing axioms.

**Implementation:**
```lean
-- In Step3_LocalTomography.lean, add:

/-- stats_imply_events follows from PVM embedding + Gleason uniqueness -/
theorem stats_imply_events_from_gleason
  (chi : X)
  (sys : BipartiteSystem)
  (pep : ProductEffectProb sys)
  (pvm : PVM H)  -- from complete_events_form_pvm
  (gleason : ValidFrameFunction H -> exists! rho, ...)  -- from gleason_theorem
  : stats_imply_events_type chi sys pep := by
  intro rho sigma h_same_stats
  -- 1. Convert effect statistics to projection statistics
  -- 2. Apply Gleason uniqueness
  -- 3. Same state implies same event truth values
  sorry  -- Would fill in with Gleason + PVM lemmas
```

### Path C: Chu Space Route

1. **Define Chu space structure** in Lean (state-event duality)
2. **Prove Stone-type embedding** for Boolean events
3. **Use duality** to transfer statistical agreement to event agreement

**Difficulty:** High. Requires categorical infrastructure.

---

## Summary: Formalizable Witnesses

| Witness | Foundation | Existing Axioms Used | New Infrastructure |
|---------|------------|---------------------|-------------------|
| **PVM Bridge** | PVMs are Boolean -> Projection homomorphisms | `complete_events_form_pvm` | None |
| **Gleason Uniqueness** | Statistics determine state uniquely | `gleason_theorem` | State -> Truth value lemma |
| **Effect Presheaf** | Effect algebras as colimits of Boolean algebras | None | Effect algebra structure |
| **Chu Duality** | States and events are dual | None | Chu space structure |

**Recommended Path:** B (PVM + Gleason)
**Reason:** Minimal new infrastructure, leverages existing axioms, mathematically strongest argument

---

## References

### Effect Algebras
- [Foulis & Bennett (1994)](https://www.sciencedirect.com/science/article/abs/pii/0034487779900569) - Original definition
- [Staton & Uijlen (2017)](https://www.cs.ox.ac.uk/people/samuel.staton/papers/infocomp2017.pdf) - Presheaf representation
- [nLab: Effect Algebra](https://ncatlab.org/nlab/show/effect+algebra) - Categorical overview
- [arXiv:2406.13775](https://arxiv.org/html/2406.13775) - Finite effect algebras

### Chu Spaces
- [nLab: Chu Construction](https://ncatlab.org/nlab/show/Chu+construction) - Formal definition
- [Pratt (1994)](http://boole.stanford.edu/pub/ph94.pdf) - Quantum aspects of Chu spaces
- [Chu Guide](http://chu.stanford.edu/guide.html) - Overview

### Projection-Valued Measures
- [Jordan Bell (2014)](https://jordanbell.info/LaTeX/mathematics/pvm/pvm.pdf) - Technical reference
- [Colorado Notes, Ch. 9](https://spot.colorado.edu/~baggett/funcchap9.pdf) - Definition and spectral theorem

### Gleason's Theorem
- [nLab: Gleason's Theorem](https://ncatlab.org/nlab/show/Gleason's+theorem) - Statement and significance
- [Gleason (1957)](https://www.jstor.org/stable/24900629) - Original paper
- [arXiv:2603.07745](https://arxiv.org/html/2603.07745v1) - Bloch-space perspective

### Quantum Reconstruction
- [Hardy (2001)](https://arxiv.org/abs/quant-ph/0101012) - Five axioms
- [Hardy (2011)](https://arxiv.org/abs/1104.2066) - Reformulating quantum theory
- [Masanes & Muller (2011)](https://arxiv.org/abs/1004.1483) - Derivation from physical requirements

---

*Generated by research agent on 2026-03-17*
