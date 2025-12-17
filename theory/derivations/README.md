# LRT Derivations

**Location:** `theory/derivations/`
**Purpose:** First-principles mathematical derivations for Logic Realism Theory

---

## Foundational Principle

### The Logic Realism Thesis

The Three Fundamental Laws of Logic (3FLL) are constitutive of coherent reality:

- **Identity (L₁):** ∀A: A = A
- **Non-Contradiction (L₂):** ∀A: ¬(A ∧ ¬A)
- **Excluded Middle (L₃):** ∀A: A ∨ ¬A

**The Logic Realism Thesis (LRT's core claim):** All axioms of mathematics and physics are downstream of 3FLL - they are theorems of coherent structure, constrained by the requirement that reality be logically coherent.

**Important clarification:** This is a *research conjecture* and *metaphysical thesis*, not an established result of standard logic. In standard accounts, the laws of thought are constraints on reasoning, not sufficient to fix all substantive axioms. LRT's claim is stronger: that 3FLL are *constitutive* of reality, not merely descriptive of valid reasoning.

### The Tier System

```
3FLL (primitive, self-grounding)
  ↓
Tier 1: Structural assumptions for coherent application of 3FLL
  - I (Information Space) - domain of discourse
  - I_infinite - no arbitrary bound on distinguishability
  NOTE: These are substantive extra assumptions, not pure
  consequences of 3FLL. LRT argues they are *required* for
  coherent application, but this is part of the thesis.
  ↓
Tier 2: Established mathematical reconstruction results
  - Stone's theorem, Gleason's theorem, Masanes-Müller reconstruction
  - Each presupposes its own non-logical structural assumptions
  - Accepted for practical use; presuppositions tracked
  ↓
Tier 3: Physical principles
  - Energy additivity, conservation laws
  - Track: empirical regularities vs. symmetry consequences
```

### Tier 2 Presupposition Tracking

When using Tier 2 theorems, note their non-logical assumptions:

| Theorem | Key Presuppositions |
|---------|---------------------|
| Masanes-Müller | Tomographic locality, continuous reversibility, subspace axiom |
| Stone's theorem | Strongly continuous unitary group, Hilbert space structure |
| Gleason's theorem | Hilbert space dim ≥ 3, frame functions |
| Spectral theorem | Self-adjoint operator on Hilbert space |

This tracking shows where features like Hilbert space structure, linearity, or dimensionality first enter the derivation.

### What This Means for Derivations

1. **Tier 2/3 inputs are methodologically legitimate** - Using established reconstruction results without re-proving them is standard practice in foundations work. Track their presuppositions.

2. **The LRT thesis is a guiding principle, not a proven result** - "All axioms downstream of 3FLL" is the theory's core claim. Derivations test and develop this thesis.

3. **Substantive assumptions must be marked** - Tier 1 assumptions and Tier 2 presuppositions are not pure logic. Mark them explicitly to avoid overstating what 3FLL alone delivers.

4. **"Gaps" are research opportunities** - When something isn't explicitly derived, it's an open question whether the derivation exists. The thesis says it should; the work is to show it.

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

### Leaked Assumptions Section (Required)

Each derivation MUST include a "Leaked Assumptions" section flagging any implicit dependencies:

```markdown
## Leaked Assumptions

| Step | Implicit Dependency | Tier | Resolution |
|------|---------------------|------|------------|
| Theorem 7.1 | Hilbert space separability | Tier 2 | Accepted (MM reconstruction) |
| Step 4 | Continuous time parameter | Tier 1? | Needs explicit derivation |
```

**Purpose:** If a derivation step relies on a property (e.g., of Hilbert space) not explicitly in Tier 2 presuppositions, flag it immediately. This maintains deductive integrity and prevents pseudo-derivation.

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
