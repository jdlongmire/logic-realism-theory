# LRT Derivations

**Location:** `theory/derivations/`
**Purpose:** First-principles mathematical derivations for Logic Realism Theory
**Protocol:** See `LRT-Collaboration-Addendum.md` for 3-stage pipeline

---

## Derivation Pipeline

Every derivation follows a 3-stage pipeline:

```
Stage 1: Theory          Stage 2: Notebook        Stage 3: Lean 4
─────────────────────    ─────────────────────    ─────────────────────
theory/derivations/      notebooks/               lean/LogicRealismTheory/
  D{tier}.{seq}-*.md       D{tier}.{seq}-*.ipynb    Derivations/D{tier}{seq}_*.lean
```

**No advancement without prior stage complete.**

---

## Derivation Chain

### Tier 0: Primitives (Self-Grounding)

| ID | Derivation | Status |
|----|------------|--------|
| D0.1 | Three Fundamental Laws (L₃) | Pending |
| D0.2 | Information Space (I∞) | Pending |
| D0.3 | Co-Fundamentality (L₃ ⊗ I∞) | Pending |

### Tier 1: Structural Consequences

| ID | Derivation | Depends On | Status |
|----|------------|------------|--------|
| D1.1 | Distinguishability | D0.1, D0.2 | Pending |
| D1.2 | Minimum Resolution (ℏ) | D1.1 | Pending |
| D1.3 | State Space Structure | D1.1, D1.2 | Pending |
| D1.4 | Hilbert Space Emergence | D1.3 | Pending |

### Tier 2: Dynamics

| ID | Derivation | Depends On | Status |
|----|------------|------------|--------|
| D2.1 | Unitarity | D1.4, D0.1 | Pending |
| D2.2 | Time Evolution | D2.1 | Pending |
| D2.3 | Schrödinger Equation | D2.2 | Pending |

### Tier 3: Measurement

| ID | Derivation | Depends On | Status |
|----|------------|------------|--------|
| D3.1 | Born Rule | D1.4, D0.1 | Pending |
| D3.2 | Projection Postulate | D3.1 | Pending |

### Tier 4: Physical Constants

| ID | Derivation | Depends On | Status |
|----|------------|------------|--------|
| D4.1 | Dimensionality (d=3+1) | D1.3 | Pending |
| D4.2 | Fine Structure (α) | D4.1 | Pending |

---

## File Header (Mandatory)

Every derivation file must begin with:

```markdown
# D{tier}.{seq}: {Title}

**Stage**: Theory | Notebook | Lean
**Status**: Draft | Review | Complete
**Depends On**: [list of D{x}.{y} IDs]
**Assumptions**: [explicit list of what this derivation takes as given]
**Falsification**: [what would disprove this derivation]

---
```

---

## Archive

Previous derivations (pre-refactor) archived at:
- `archive/20251221-pre-refactor/`

These contain valuable content to reference but do not follow current rigor protocols.

---

## Tracking

Full progress tracking: `theory/20251221-logic-realism-theory-refactor.md`

---

**Last updated:** 2025-12-21 (Session 49.0)
