# Logic Realism Theory Refactor

**Created**: 2025-12-21
**Status**: Planning
**Goal**: Rebuild LRT from first principles with rigorous verification pipeline

---

## Methodology

Every derivation follows a 2-stage pipeline:

```
Stage 1: Notebook                    Stage 2: Lean 4
─────────────────────────────────    ─────────────────────────────────
First principles reasoning           Formal proof
+ Computational verification

notebooks/                           lean/LogicRealismTheory/Derivations/
  D{tier}.{seq}-{name}.ipynb           D{tier}{seq}_{Name}.lean
```

**Notebook contains both:**
- Markdown cells: First-principles theory reasoning
- Code cells: Computational verification

**Rules:**
1. Each derivation is incremental (builds only on prior verified steps)
2. No Stage 2 (Lean) without Stage 1 (Notebook) complete
3. Circularity checked at every stage

---

## Derivation Chain

### Tier 0: Primitives (Self-Grounding)

| ID | Derivation | Notebook | Lean | Status |
|----|------------|----------|------|--------|
| D0.1 | Three Fundamental Laws (L₃) | [ ] | [ ] | Pending |
| D0.2 | Information Space (I∞) | [ ] | [ ] | Pending |
| D0.3 | Co-Fundamentality (L₃ ⊗ I∞) | [ ] | [ ] | Pending |

### Tier 1: Structural Consequences

| ID | Derivation | Depends On | Notebook | Lean | Status |
|----|------------|------------|----------|------|--------|
| D1.1 | Distinguishability | D0.1, D0.2 | [ ] | [ ] | Pending |
| D1.2 | Minimum Resolution (ℏ) | D1.1 | [ ] | [ ] | Pending |
| D1.3 | State Space Structure | D1.1, D1.2 | [ ] | [ ] | Pending |
| D1.4 | Hilbert Space Emergence | D1.3 | [ ] | [ ] | Pending |

### Tier 2: Dynamics

| ID | Derivation | Depends On | Notebook | Lean | Status |
|----|------------|------------|----------|------|--------|
| D2.1 | Unitarity | D1.4, D0.1 | [ ] | [ ] | Pending |
| D2.2 | Time Evolution | D2.1 | [ ] | [ ] | Pending |
| D2.3 | Schrödinger Equation | D2.2 | [ ] | [ ] | Pending |

### Tier 3: Measurement

| ID | Derivation | Depends On | Notebook | Lean | Status |
|----|------------|------------|----------|------|--------|
| D3.1 | Born Rule | D1.4, D0.1 | [ ] | [ ] | Pending |
| D3.2 | Projection Postulate | D3.1 | [ ] | [ ] | Pending |

### Tier 4: Physical Constants

| ID | Derivation | Depends On | Notebook | Lean | Status |
|----|------------|------------|----------|------|--------|
| D4.1 | Dimensionality (d=3+1) | D1.3 | [ ] | [ ] | Pending |
| D4.2 | Fine Structure (α) | D4.1 | [ ] | [ ] | Pending |

---

## Dependency Graph (DAG)

```
                    ┌─────────────────────────────────────────────────────────┐
                    │                      TIER 0: PRIMITIVES                 │
                    │  D0.1 (L₃)  ────┬────  D0.2 (I∞)  ────┬────  D0.3 (⊗)  │
                    └────────┬────────┴──────────┬──────────┴────────┬────────┘
                             │                   │                   │
                             ▼                   ▼                   ▼
                    ┌─────────────────────────────────────────────────────────┐
                    │                 TIER 1: STRUCTURAL                      │
                    │         D1.1 (Distinguishability)                       │
                    │                    │                                    │
                    │                    ▼                                    │
                    │         D1.2 (Minimum Resolution ℏ)                     │
                    │                    │                                    │
                    │                    ▼                                    │
                    │         D1.3 (State Space) ──────────────┬──────────    │
                    │                    │                     │              │
                    │                    ▼                     │              │
                    │         D1.4 (Hilbert Space)             │              │
                    └────────────────────┬─────────────────────┼──────────────┘
                                         │                     │
              ┌──────────────────────────┼─────────────────────┘
              │                          │
              ▼                          ▼
┌─────────────────────────┐    ┌─────────────────────────┐
│     TIER 2: DYNAMICS    │    │    TIER 4: CONSTANTS    │
│                         │    │                         │
│  D2.1 (Unitarity)       │    │  D4.1 (d=3+1)           │
│         │               │    │         │               │
│         ▼               │    │         ▼               │
│  D2.2 (Time Evolution)  │    │  D4.2 (α=1/137)         │
│         │               │    │                         │
│         ▼               │    └─────────────────────────┘
│  D2.3 (Schrödinger)     │
│                         │
└─────────────────────────┘

              │
              ▼
┌─────────────────────────┐
│   TIER 3: MEASUREMENT   │
│                         │
│  D3.1 (Born Rule)       │
│         │               │
│         ▼               │
│  D3.2 (Projection)      │
│                         │
└─────────────────────────┘
```

**Update Rule:** This graph is updated immediately when any derivation advances stage.

**Rollback Rule:** If any node is invalidated, all downstream nodes must be re-verified.

---

## Notation Standard

| Symbol | Meaning | Usage |
|--------|---------|-------|
| I∞ | Information Space | Infinite distinguishable states |
| L₃ | Three Fundamental Laws | Identity, Non-Contradiction, Excluded Middle |
| A* | Actualization Operator | L₃(I∞) → Physical Reality |
| □ | Necessity Operator | □∃I, □∃L, □(P = L(I)) |

---

## Source Materials

| File | Purpose | Extract |
|------|---------|---------|
| `20251221-logic_realism_theory.md` | Latest draft | Primitive Criteria, Meta-Principles, Gödel Argument |
| `20251221-Claude-LRT-ground-up.md` | Ground-up exploration | Type 1/2 distinction, Co-Fundamentality, Necessity analysis |
| `archive/20251221-theory-consolidation/` | Historical reference | Prior derivation attempts |

---

## Quality Gates

### Stage 1 (Notebook) Gate
- [ ] First principles only (no smuggled assumptions)
- [ ] Explicit dependency chain
- [ ] Circularity check passed
- [ ] No undefined terms
- [ ] Computational verification complete
- [ ] Edge cases tested
- [ ] Clear outputs demonstrating correctness

### Stage 2 (Lean) Gate
- [ ] Compiles without sorry
- [ ] Axiom count matches tier
- [ ] Dependencies match notebook
- [ ] No Tier 2/3 assumptions smuggled into Tier 1 claims

---

## File Naming Convention

```
notebooks/D{tier}.{seq}-{name}.ipynb
lean/LogicRealismTheory/Derivations/D{tier}{seq}_{Name}.lean
```

Examples:
- `notebooks/D0.1-three-fundamental-laws.ipynb`
- `lean/LogicRealismTheory/Derivations/D01_ThreeFundamentalLaws.lean`

---

## Progress Tracking

| Tier | Derivations | Notebook | Lean | Complete |
|------|-------------|----------|------|----------|
| 0 | 3 | 0/3 | 0/3 | 0% |
| 1 | 4 | 0/4 | 0/4 | 0% |
| 2 | 3 | 0/3 | 0/3 | 0% |
| 3 | 2 | 0/2 | 0/2 | 0% |
| 4 | 2 | 0/2 | 0/2 | 0% |
| **Total** | **14** | **0/14** | **0/14** | **0%** |

---

## Notes

*Add notes as work progresses*

---
