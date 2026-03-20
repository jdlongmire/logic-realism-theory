# LRT Derivation Notebooks

**Location:** `notebooks/`
**Purpose:** Stage 1 of 2-stage derivation pipeline (Notebook → Lean)
**Protocol:** See `LRT-Collaboration-Addendum.md`

---

## Pipeline Role

Each notebook contains:
- **Markdown cells**: First-principles theory reasoning
- **Code cells**: Computational verification

No notebook advances to Lean (Stage 2) without completing all quality gates.

---

## Derivation Chain

### Tier 0: Primitives (Self-Grounding)

| ID | Notebook | Lean | Status |
|----|----------|------|--------|
| D0.1 | `D0.1-three-fundamental-laws.ipynb` | `D0_1_ThreeFundamentalLaws.lean` | Complete |
| D0.2 | `D0.2-information-space.ipynb` | `D0_2_InformationSpace.lean` | Complete |
| D0.3 | `D0.3-co-fundamentality.ipynb` | Pending | Pending |

### Tier 1: Structural Consequences

| ID | Notebook | Depends On | Status |
|----|----------|------------|--------|
| D1.1 | `D1.1-distinguishability.ipynb` | D0.1, D0.2 | Pending |
| D1.2 | `D1.2-minimum-resolution.ipynb` | D1.1 | Pending |
| D1.3 | `D1.3-state-space-structure.ipynb` | D1.1, D1.2 | Pending |
| D1.4 | `D1.4-hilbert-space-emergence.ipynb` | D1.3 | Pending |

### Tier 2-4: See `theory/20251221-logic-realism-theory-refactor.md`

---

## Notebook Header (Mandatory)

Every notebook must begin with a markdown cell:

```markdown
# D{tier}.{seq}: {Title}

**Stage**: Notebook | Lean
**Status**: Draft | Review | Complete
**Depends On**: [list of D{x}.{y} IDs]
**Assumptions**: [explicit list]
**Falsification**: [what would disprove this]
```

---

## Quality Gates (Stage 1)

Before advancing to Lean:
- [ ] First principles only (no smuggled assumptions)
- [ ] Explicit dependency chain
- [ ] Circularity check passed
- [ ] No undefined terms
- [ ] Computational verification complete
- [ ] Edge cases tested
- [ ] Clear outputs demonstrating correctness

---

## Archive

Previous notebooks (pre-refactor) archived at:
- `archive/20251221-pre-refactor/`

Contains valuable reference material but does not follow current protocols.

---

## Installation

```bash
pip install -r requirements.txt
```

---

## Tracking

Full progress: `theory/20251221-logic-realism-theory-refactor.md`

---

**Last updated:** 2025-12-21 (Session 49.0)
