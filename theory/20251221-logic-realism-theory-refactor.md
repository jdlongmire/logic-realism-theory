# Logic Realism Theory Refactor

**Created**: 2025-12-21
**Status**: Planning
**Goal**: Rebuild LRT from first principles with rigorous verification pipeline

---

## Methodology

Every derivation follows a 3-stage pipeline:

```
Stage 1: Theory          Stage 2: Notebook        Stage 3: Lean 4
─────────────────────    ─────────────────────    ─────────────────────
First principles         Computational            Formal proof
reasoning                verification

theory/derivations/      notebooks/               lean/LogicRealismTheory/
  *.md                     *.ipynb                  *.lean
```

**Rules:**
1. Each derivation is incremental (builds only on prior verified steps)
2. No step advances to Stage 2 without Stage 1 complete
3. No step advances to Stage 3 without Stage 2 complete
4. Circularity checked at every stage

---

## Derivation Chain

### Tier 0: Primitives (Self-Grounding)

| ID | Derivation | Theory | Notebook | Lean | Status |
|----|------------|--------|----------|------|--------|
| D0.1 | Three Fundamental Laws (L₃) | [ ] | [ ] | [ ] | Pending |
| D0.2 | Information Space (I∞) | [ ] | [ ] | [ ] | Pending |
| D0.3 | Co-Fundamentality (L₃ ⊗ I∞) | [ ] | [ ] | [ ] | Pending |

### Tier 1: Structural Consequences

| ID | Derivation | Depends On | Theory | Notebook | Lean | Status |
|----|------------|------------|--------|----------|------|--------|
| D1.1 | Distinguishability | D0.1, D0.2 | [ ] | [ ] | [ ] | Pending |
| D1.2 | Minimum Resolution (ℏ) | D1.1 | [ ] | [ ] | [ ] | Pending |
| D1.3 | State Space Structure | D1.1, D1.2 | [ ] | [ ] | [ ] | Pending |
| D1.4 | Hilbert Space Emergence | D1.3 | [ ] | [ ] | [ ] | Pending |

### Tier 2: Dynamics

| ID | Derivation | Depends On | Theory | Notebook | Lean | Status |
|----|------------|------------|--------|----------|------|--------|
| D2.1 | Unitarity | D1.4, D0.1 | [ ] | [ ] | [ ] | Pending |
| D2.2 | Time Evolution | D2.1 | [ ] | [ ] | [ ] | Pending |
| D2.3 | Schrödinger Equation | D2.2 | [ ] | [ ] | [ ] | Pending |

### Tier 3: Measurement

| ID | Derivation | Depends On | Theory | Notebook | Lean | Status |
|----|------------|------------|--------|----------|------|--------|
| D3.1 | Born Rule | D1.4, D0.1 | [ ] | [ ] | [ ] | Pending |
| D3.2 | Projection Postulate | D3.1 | [ ] | [ ] | [ ] | Pending |

### Tier 4: Physical Constants

| ID | Derivation | Depends On | Theory | Notebook | Lean | Status |
|----|------------|------------|--------|----------|------|--------|
| D4.1 | Dimensionality (d=3+1) | D1.3 | [ ] | [ ] | [ ] | Pending |
| D4.2 | Fine Structure (α) | D4.1 | [ ] | [ ] | [ ] | Pending |

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

### Stage 1 (Theory) Gate
- [ ] First principles only (no smuggled assumptions)
- [ ] Explicit dependency chain
- [ ] Circularity check passed
- [ ] No undefined terms

### Stage 2 (Notebook) Gate
- [ ] Computational implementation matches theory
- [ ] Numerical verification where applicable
- [ ] Edge cases tested
- [ ] Clear outputs demonstrating correctness

### Stage 3 (Lean) Gate
- [ ] Compiles without sorry
- [ ] Axiom count matches tier
- [ ] Dependencies match theory
- [ ] No Tier 2/3 assumptions smuggled into Tier 1 claims

---

## File Naming Convention

```
theory/derivations/D{tier}.{seq}-{name}.md
notebooks/D{tier}.{seq}-{name}.ipynb
lean/LogicRealismTheory/Derivations/D{tier}{seq}_{Name}.lean
```

Examples:
- `theory/derivations/D0.1-three-fundamental-laws.md`
- `notebooks/D0.1-three-fundamental-laws.ipynb`
- `lean/LogicRealismTheory/Derivations/D01_ThreeFundamentalLaws.lean`

---

## Progress Tracking

| Tier | Derivations | Theory | Notebook | Lean | Complete |
|------|-------------|--------|----------|------|----------|
| 0 | 3 | 0/3 | 0/3 | 0/3 | 0% |
| 1 | 4 | 0/4 | 0/4 | 0/4 | 0% |
| 2 | 3 | 0/3 | 0/3 | 0/3 | 0% |
| 3 | 2 | 0/2 | 0/2 | 0/2 | 0% |
| 4 | 2 | 0/2 | 0/2 | 0/2 | 0% |
| **Total** | **14** | **0/14** | **0/14** | **0/14** | **0%** |

---

## Notes

*Add notes as work progresses*

---
