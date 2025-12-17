# LRT Derivations

**Location:** `theory/derivations/`
**Purpose:** First-principles mathematical derivations for Logic Realism Theory

---

## Foundational Principle

### All Axioms Are Downstream of 3FLL

The Three Fundamental Laws of Logic (3FLL) are constitutive of coherent reality:

- **Identity (L₁):** ∀A: A = A
- **Non-Contradiction (L₂):** ∀A: ¬(A ∧ ¬A)
- **Excluded Middle (L₃):** ∀A: A ∨ ¬A

**Key insight:** ALL axioms - mathematical, physical, and operational - are downstream derivations from 3FLL. They are theorems of coherent reality, whether or not we explicitly show the derivation chain.

### The Tier System

```
3FLL (primitive, self-grounding)
  ↓
Tier 1: Presuppositions of 3FLL
  - I (Information Space) - what 3FLL requires as domain of discourse
  - I_infinite - no arbitrary bound on distinguishability
  ↓
Tier 2: Theorems of coherent mathematics
  - Stone's theorem, Gleason's theorem, Masanes-Müller reconstruction
  - Valid because coherent mathematics is grounded in 3FLL
  - Accepted for practical use without re-deriving each one
  ↓
Tier 3: Theorems of coherent physics
  - Energy additivity, conservation laws
  - Valid because coherent physics is grounded in 3FLL
```

### What This Means for Derivations

1. **Tier 2/3 inputs are legitimate** - Using established mathematical results is not "importing external assumptions." These results are valid because they're part of coherent mathematics, which derives from 3FLL.

2. **Explicit derivation chains are valuable but not required** - Showing how a result follows from 3FLL strengthens the framework. But using established results without re-deriving them is valid.

3. **"Gaps" are unwritten derivations, not missing axioms** - When something isn't explicitly derived, the derivation exists in principle (because 3FLL grounds all coherent structure). The work is to make it explicit.

---

## Derivation Files

### Variational Framework (Session 13.0)

| File | Content | Status |
|------|---------|--------|
| `Identity_to_K_ID_Derivation.md` | K_ID = 1/β² from Identity constraint | 100% derived |
| `ExcludedMiddle_to_K_EM_Derivation.md` | K_EM = (ln 2)/β from EM constraint | 100% derived |
| `Measurement_to_K_enforcement_Derivation.md` | K_enforcement = 4β² from measurement | 85% derived |
| `Four_Phase_Necessity_Analysis.md` | Why N=4 phases in measurement | Complete |
| `Phase_Weighting_*.md` (3 files) | Phase weighting analysis | Complete |

### Constants Derivations (Session 45.0)

| File | Content | Status |
|------|---------|--------|
| `Issue_012_Alpha_Formula.md` | α⁻¹ = 137.036 from d=3 | Complete (8 ppb) |
| `Issue_012_Dimension_Derivation.md` | Why d=3 spatial dimensions | Complete |
| `Issue_012_Mass_Ratio.md` | Muon/electron mass ratio | Partial (92 ppm) |

### Action Functional (Session 46.0)

| File | Content | Status |
|------|---------|--------|
| `Issue_013_Logical_Action_Functional_v2.md` | S = ∫ L dt from 3FLL | Complete |

**Note:** v2 uses Tier 2 theorems (Masanes-Müller reconstruction) as legitimate inputs.

### Other

| File | Content |
|------|---------|
| `Linearity_Derivation.md` | Linearity of quantum mechanics |
| `1_Paper_Formalization_Section.md` | Formal section for papers |

---

## Format Standards

- **Source of truth:** Markdown files (.md) are canonical
- **Equations:** LaTeX format for readability
- **Structure:** Step-by-step chains with explicit dependencies
- **Non-circularity:** Dependency traces required
- **Tier labeling:** Mark which tier each input comes from

---

## Quality Standards

From `AI-Collaboration-Profile.json`:

1. Every step must be justified (no "it follows that" without reasoning)
2. Circular reasoning actively hunted (dependency traces required)
3. Parameters must not appear in their own derivation chain
4. Honest acknowledgment of assumptions and limitations
5. Tier 2/3 inputs explicitly marked as such

---

## Adding New Derivations

When creating a new derivation:

1. **State the goal clearly** at the top
2. **List inputs by tier:**
   - What comes from 3FLL + parsimony (explicit)
   - What comes from Tier 2 theorems (legitimate)
   - What comes from Tier 3 physics (legitimate)
3. **Show the chain** step by step
4. **Mark the status** honestly
5. **Acknowledge gaps** if any steps are incomplete

---

**Last updated:** 2025-12-16 (Session 46.0)
