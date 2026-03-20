# Medium-Priority Axiom Triage

**Date:** 2026-03-17
**Agent:** Axiom audit agent
**Purpose:** Detailed analysis of 12 medium-priority axioms to determine implementation status

---

## Summary

| # | Axiom | Status | Verdict |
|---|-------|--------|---------|
| 1 | `config_separation` | REAL AXIOM | Needs derivation from Event structure |
| 2 | `complete_events_form_pvm` | REAL AXIOM | Returns existential, needs PVM construction |
| 3 | `event_operator_has_bool_spectrum` | PLACEHOLDER | Has `h_event : True` |
| 4 | `boolean_implies_purification` | PLACEHOLDER | `PurificationHolds' : Prop := True` |
| 5 | `evolution_preserves_distinguishability` | PLACEHOLDER | Has `h_evolution : True` |
| 6 | `evolution_bijective` | PLACEHOLDER | Has `h_evolution : True` |
| 7 | `evolution_preserves_norm` | PLACEHOLDER | Has `h_evolution : True` |
| 8 | `time_evolution_group` | REAL AXIOM | Returns `UnitaryGroup` structure |
| 9 | `stationary_phase_principle` | PLACEHOLDER | Body is `True` |
| 10 | `noether_theorem` | REAL AXIOM | Returns existential for conserved quantity |
| 11 | `schrodinger_from_stone` | REAL AXIOM | Returns `SchrodingerEquation` structure |
| 12 | `time_arrow` | REAL AXIOM | Returns `TimeArrow` structure |

**Totals:**
- REAL AXIOMS: 7 (substantive content)
- PLACEHOLDERS: 5 (condition or body is `True`)

---

## Detailed Analysis

### 1. `config_separation` (Step0_Primitives.lean:273)

**Declaration:**
```lean
axiom config_separation :
  ∀ (c₁ c₂ : Configuration), c₁ ≠ c₂ →
    ∃ (e : Event), e.query c₁ ∧ ¬e.query c₂
```

**Status:** REAL AXIOM — non-trivial statement about Event structure.

**Analysis:** This is the key axiom bridging I∞'s distinguishability to the Event algebra. It states that distinct configurations can be separated by some event query. The documentation says it's derivable from "I being formally specifiable" — a philosophical claim that formal specification implies event-based separation.

**Reduction path:** Needs explicit Event algebra construction showing that for any two configs, there exists a separating event. Could potentially derive from Stone representation theorem if Event forms a Boolean algebra.

---

### 2. `complete_events_form_pvm` (Step4/Boolean.lean:297)

**Declaration:**
```lean
axiom complete_events_form_pvm (χ : X) (outcomes : Type*) (events : outcomes → Event)
    (h_exclusive : ∀ i j, i ≠ j → ∀ c, ¬(events i).query c ∨ ¬(events j).query c)
    (h_exhaustive : ∀ c, ∃ i, (events i).query c) :
    ∃ (H : Type*) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H),
      ∃ (pvm : PVM H), True
```

**Status:** REAL AXIOM — constructs Hilbert space and PVM.

**Analysis:** Given an exclusive/exhaustive family of events, this asserts existence of a Hilbert space with a corresponding PVM. The statement is substantive but the body (`True`) doesn't require the PVM to actually correspond to the events.

**Reduction path:** Needs proper Stone representation: Boolean algebra → projection lattice isomorphism. The `True` body is weak; should strengthen to require PVM correspondence.

---

### 3. `event_operator_has_bool_spectrum` (Step5/EigenvalueRestriction.lean:289)

**Declaration:**
```lean
axiom event_operator_has_bool_spectrum
    (E : H →L[ℂ] H)
    (h_event : True) -- Placeholder for "E represents an LRT event"
    : HasBooleanSpectrum E
```

**Status:** PLACEHOLDER — condition `h_event : True` is trivial.

**Analysis:** The condition "E represents an LRT event" is just `True`. This means ANY operator is declared to have Boolean spectrum, which is false. This is a placeholder awaiting proper EventRepresentation structure.

**Reduction path:** Needs `EventRepresentation` witness connecting E to actual events. The theorem `eigenvalue_outcome_correspondence` in Step4/Boolean.lean provides the conceptual derivation but lacks the infrastructure.

---

### 4. `boolean_implies_purification` (Step4/Purification.lean:200)

**Declaration:**
```lean
axiom boolean_implies_purification :
  (∀ (E : H →L[ℂ] H), IsSelfAdjoint' E → HasBooleanSpectrum E) →
  PurificationHolds'
```

**Status:** PLACEHOLDER — `PurificationHolds' : Prop := True`.

**Analysis:** The conclusion `PurificationHolds'` is defined as `True`, making this axiom trivially true given any premise. This is OPN-005 core, awaiting proper purification infrastructure.

**Reduction path:** Needs real purification definition with tensor products, partial trace, Schmidt decomposition. The documentation outlines the argument: Boolean → no-hiding → encoding → purification.

---

### 5. `evolution_preserves_distinguishability` (Step7_Unitarity.lean:123)

**Declaration:**
```lean
axiom evolution_preserves_distinguishability
    (U : H →L[ℂ] H)
    (h_evolution : True) -- Placeholder for "U represents time evolution"
    (ψ φ : H)
    (h_orth : @inner ℂ H _ ψ φ = 0) :
    @inner ℂ H _ (U ψ) (U φ) = 0
```

**Status:** PLACEHOLDER — condition `h_evolution : True` is trivial.

**Analysis:** Claims any operator preserves orthogonality given `h_evolution : True`. This is false for general operators. The intended meaning is that TIME EVOLUTION operators preserve orthogonality (from L₃), but the placeholder condition doesn't enforce this.

**Reduction path:** Should require U to come from the time evolution group, or require U to be unitary. With proper infrastructure, this follows from `IsUnitary U → PreservesInner U`.

---

### 6. `evolution_bijective` (Step7_Unitarity.lean:133)

**Declaration:**
```lean
axiom evolution_bijective
    (U : H →L[ℂ] H)
    (h_evolution : True) :
    Function.Bijective U
```

**Status:** PLACEHOLDER — condition `h_evolution : True` is trivial.

**Analysis:** Same issue as above. Claims any operator is bijective. Should require U to be a time evolution operator.

**Reduction path:** Follows from unitarity: IsUnitary U → Bijective U.

---

### 7. `evolution_preserves_norm` (Step7_Unitarity.lean:141)

**Declaration:**
```lean
axiom evolution_preserves_norm
    (U : H →L[ℂ] H)
    (h_evolution : True) :
    PreservesNorm U
```

**Status:** PLACEHOLDER — condition `h_evolution : True` is trivial.

**Analysis:** Same pattern. Should follow from unitarity.

**Reduction path:** IsUnitary U → PreservesNorm U.

---

### 8. `time_evolution_group` (Step7_Unitarity.lean:174)

**Declaration:**
```lean
axiom time_evolution_group : UnitaryGroup (H := H)
```

**Status:** REAL AXIOM — returns full `UnitaryGroup` structure.

**Analysis:** This is a genuine existence claim: there exists a one-parameter unitary group representing time evolution. The structure requires:
- U : ℝ → (H →L[ℂ] H)
- ∀ t, IsUnitary (U t)
- Group property: U(s+t) = U(s) * U(t)
- Identity: U(0) = I

**Reduction path:** Could be derived from continuity + Stone's theorem, but currently axiomatized. May remain as physics input (time translation symmetry).

---

### 9. `stationary_phase_principle` (Step9_EnergyAction.lean:220)

**Declaration:**
```lean
axiom stationary_phase_principle :
    ∀ S : Action (H := H), True  -- Classical paths extremize action
```

**Status:** PLACEHOLDER — body is `True`.

**Analysis:** The statement is trivially true (∀ S, True). The intended content (classical limit selects δS=0 paths) is in comments only.

**Reduction path:** Needs proper statement involving path integrals, classical limit, action extremization. This is a deep physics result (asymptotic analysis).

---

### 10. `noether_theorem` (Step9_EnergyAction.lean:261)

**Declaration:**
```lean
axiom noether_theorem (S : Symmetry (H := H)) :
    ∃ Q : H →L[ℂ] H, IsSelfAdjoint' Q
```

**Status:** REAL AXIOM — returns existential for conserved quantity.

**Analysis:** Given a symmetry, asserts existence of a self-adjoint conserved quantity. The statement is weaker than full Noether (doesn't specify the conservation relation), but substantive.

**Reduction path:** Full derivation requires Lagrangian/Hamiltonian mechanics formalization. Currently standard physics input.

---

### 11. `schrodinger_from_stone` (Step10_Schrodinger.lean:155)

**Declaration:**
```lean
axiom schrodinger_from_stone
    (U : UnitaryGroup (H := H))
    (H_op : Hamiltonian (H := H))
    (hbar : ℝ)
    (h_hbar : hbar > 0) :
    SchrodingerEquation (H := H)
```

**Status:** REAL AXIOM — returns `SchrodingerEquation` structure.

**Analysis:** Given a unitary group and Hamiltonian, asserts existence of Schrödinger equation structure. Substantive but `SchrodingerEquation` involves placeholders internally.

**Reduction path:** Follows directly from Stone's theorem + generator differentiation. Needs unbounded operator formalization in Mathlib.

---

### 12. `time_arrow` (Step8_TemporalEmergence.lean:168)

**Declaration:**
```lean
axiom time_arrow : TimeArrow
```

**Status:** REAL AXIOM — returns `TimeArrow` structure.

**Analysis:** `TimeArrow` has:
- direction : Int
- forward_is_actual : direction = 1

The axiom asserts time flows forward (in actualization direction). This is a genuine physical/philosophical claim.

**Reduction path:** Could be derived from actualization ordering + thermodynamics. Currently axiomatized as LRT's temporal commitment.

---

## Recommendations

### Immediate actions (can be done now):

1. **Strengthen placeholder conditions** — Replace `h_event : True` and `h_evolution : True` with proper type witnesses (EventRepresentation, IsUnitary, etc.)

2. **Fix placeholder bodies** — Replace `PurificationHolds' := True` and `stationary_phase_principle` body with real definitions

### Short-term (requires infrastructure):

3. **Derive evolution axioms from unitarity** — Once evolution operators are properly typed, axioms 5-7 follow from IsUnitary

4. **Complete OPN-005** — Need tensor product, partial trace, Schmidt decomposition to prove `boolean_implies_purification`

### Long-term (substantial work):

5. **Stone-based separations** — Derive `config_separation` and `complete_events_form_pvm` from Stone representation

6. **Unbounded operators** — Need Mathlib support for Stone's theorem to derive `schrodinger_from_stone`

---

*Generated by axiom audit agent, 2026-03-17*
