# Issue #51: PROJECT: Axiom Reduction Campaign (10 REMAINING → ~4)

**Status:** ACTIVE
**Priority:** HIGH
**Created:** 2026-03-21
**Target:** Reduce REMAINING axioms from 10 to ~4

---

## Current State

| Category | Count |
|----------|-------|
| PRIMITIVE | 3 |
| EXTERNAL | 17 |
| REMAINING | 10 |
| **Total** | **30** |

---

## Dependency Structure

```
                    ┌─────────────────────────────────────────────┐
                    │           INDEPENDENT CLUSTERS              │
                    └─────────────────────────────────────────────┘

    ┌──────────────────────┐      ┌──────────────────────────────┐
    │   STEP 5 (Spectral)  │      │      STEP 6 (Born Rule)      │
    │                      │      │                              │
    │  spectral_           │      │  born_rule_completeness (#40)│
    │  correspondence (#38)│      │                              │
    │         │            │      │     (uses partition of unity)│
    │         ▼            │      └──────────────────────────────┘
    │  event_operator_has_ │                    ▲
    │  bool_spectrum (#39) │                    │ (validates)
    │    (BROKEN predicate)│◄───────────────────┘
    └──────────────────────┘

    ┌──────────────────────────────────────────────────────────────────────────┐
    │                        STEP 7+8 (Dynamics) — TIGHTLY COUPLED              │
    │                                                                          │
    │  time_evolution_family (#41) ◄─────── ROOT (existence)                   │
    │         │                                                                │
    │         ├───────► evolution_preserves_norm (#42) ─┐                      │
    │         │                                         │                      │
    │         ├───────► evolution_group_composition (#43)├─► derive from root │
    │         │                                         │                      │
    │         └───────► evolution_identity (#44) ───────┘                      │
    │                                                                          │
    └──────────────────────────────────────────────────────────────────────────┘
                    │
                    ▼
    ┌──────────────────────────────────────────────────────────────────────────┐
    │                     STEP 8 (Temporal) — DEPENDS ON STEP 7                 │
    │                                                                          │
    │  time_embedding (#45) ◄─────── CONSTRUCTIBLE (one-line definition)       │
    │         │                                                                │
    │         └───────► time_embedding_strict_mono (#46) — derivable           │
    │                                                                          │
    │  evolution_matches_actualization (#47) — REDUNDANT with #43              │
    │                                                                          │
    └──────────────────────────────────────────────────────────────────────────┘
```

---

## Reduction Targets by Priority

### Phase 1: Zero-Cost (definitions only) — ELIMINATE 4 AXIOMS

| Issue | Axiom | Status | Action |
|-------|-------|--------|--------|
| #44 | `evolution_identity` | TRIVIAL | Prove via `exp_zero` |
| #45 | `time_embedding` | CONSTRUCTIBLE | Define as `fun e => (e.id : ℝ)` |
| #46 | `time_embedding_strict_mono` | DERIVABLE | Prove from #45 definition |
| #47 | `evolution_matches_actualization` | REDUNDANT | Remove (same as #43) |

**Dependency order:** #45 → #46 (sequential); #44, #47 (independent)

- [ ] #44 evolution_identity
- [ ] #45 time_embedding
- [ ] #46 time_embedding_strict_mono
- [ ] #47 evolution_matches_actualization

### Phase 2: Step 7 Consolidation — NET -2 AXIOMS

| Issue | Axiom | Status | Action |
|-------|-------|--------|--------|
| #41 | `time_evolution_family` | ROOT | Replace with `hamiltonian` + `hamiltonian_isSelfAdjoint` |
| #42 | `evolution_preserves_norm` | DERIVABLE | Derive from Hamiltonian + exp properties |
| #43 | `evolution_group_composition` | DERIVABLE | Derive from exp_add |

**Strategy:** Introduce 2 Hamiltonian axioms, derive 3 evolution axioms as theorems.
**Net:** -1 axiom (4 become 2, but we keep #41 as root assessment)

- [ ] #41 time_evolution_family (assess)
- [ ] #42 evolution_preserves_norm
- [ ] #43 evolution_group_composition

### Phase 3: Spectral/Boolean Cleanup — QUALITY IMPROVEMENT

| Issue | Axiom | Status | Action |
|-------|-------|--------|--------|
| #38 | `spectral_correspondence` | MEDIUM | Clean formulation, assess derivability |
| #39 | `event_operator_has_bool_spectrum` | BROKEN | Fix predicate, wire Step4b chain |
| #40 | `born_rule_completeness` | MEDIUM | Parseval identity from spectral theory |

**Dependency order:** #38 → #39 → #40

- [ ] #38 spectral_correspondence
- [ ] #39 event_operator_has_bool_spectrum
- [ ] #40 born_rule_completeness

---

## Closed (Reclassified to EXTERNAL)

These are established mathematics blocked by Mathlib infrastructure (unbounded operators):

- [x] #48 schrodinger_from_stone → EXT-004
- [x] #49 hamiltonian_generates_unitary → EXT-005
- [x] #50 hamiltonian_generates_group_mul → EXT-006

---

## Expected Final State

| Category | Before | After Phase 1 | After Phase 2 | After Phase 3 |
|----------|--------|---------------|---------------|---------------|
| PRIMITIVE | 3 | 3 | 3 | 3 |
| EXTERNAL | 17 | 17 | 17 | 17 |
| REMAINING | 10 | 6 | ~4 | ~3 |
| **Total** | **30** | **26** | **~24** | **~23** |

---

## Resolution Order

1. **Phase 1** (#44-#47): Do together as single "Step 8 cleanup" commit
2. **Phase 2** (#41-#43): Do together as single "Step 7 consolidation" commit
3. **Phase 3** (#38-#40): Can be done independently after Phases 1-2

---

## Notes

- Phase 1 is purely mechanical: no new mathematics required
- Phase 2 requires introducing Hamiltonian-based approach (well-understood)
- Phase 3 involves conceptual work: proper typing and Step4b wiring
- All changes preserve the derivation chain X → Schrödinger
