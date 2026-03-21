# Issue #39: Fix `event_operator_has_bool_spectrum` predicate

**Status:** OPEN (BROKEN)
**Priority:** HIGH
**Blocked by:** #38 (spectral_correspondence)
**Blocks:** Born rule chain
**Project:** #51

---

## Current Form

```lean
axiom event_operator_has_bool_spectrum [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (E : H →L[ℂ] H) (h_event : True) : HasBooleanSpectrum E
```

**Location:** `Step5/EigenvalueRestriction.lean:180`

---

## Issue

The predicate `h_event : True` is meaningless. This axiom says "every operator has Boolean spectrum," which is false.

The intent was: "event operators have Boolean spectrum." But there's no `EventOperator` type defined.

---

## Analysis

The derivation exists in Step4b (`phase4_boolean_bridge`):
```
L₃ → sharp events → binary evaluation → eigenvalue correspondence
    → Boolean spectrum → idempotence → projections → PVMs
```

But this chain doesn't connect to the axiom in Step5.

---

## Path to Resolution

1. **Define `EventOperator` type** that wraps operators satisfying event criteria
2. **Wire Step4b to Step5:** The `phase4_boolean_bridge` theorem should provide the predicate
3. **Replace axiom with theorem:** Prove `HasBooleanSpectrum` for properly typed event operators

---

## Proposed Fix

```lean
-- In Step4b or shared definitions:
structure EventOperator (H : Type*) [InnerProductSpace ℂ H] where
  op : H →L[ℂ] H
  represents_sharp_event : RepresentsSharpEvent op

-- In Step5:
theorem event_operator_has_bool_spectrum (E : EventOperator H) :
  HasBooleanSpectrum E.op := by
  -- derive from E.represents_sharp_event + phase4_boolean_bridge
```

---

## Dependencies

- Requires Step4b infrastructure to be properly exported
- Requires #38 (`spectral_correspondence`) for eigenvalue interpretation
- Once fixed, validates #40 (`born_rule_completeness`)
