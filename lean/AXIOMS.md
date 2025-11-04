# LRT Axiom Approach

**Logic Realism Theory Lean Formalization**

---

## The 3-Tier Classification System

All axioms in this formalization are classified into three tiers:

### Tier 1: LRT Specific
**Novel LRT axioms** - Theory-defining postulates

**Count**: 2 axioms
- `I : Type*` - Infinite Information Space exists (Foundation/IIS.lean)
- `I_infinite : Infinite I` - I is infinite (Foundation/IIS.lean)

**Status**: These define what LRT *is*. Analogous to QM's "Hilbert space exists" postulate.

**Rule**: LRT should have only 2-3 Tier 1 axioms total.

---

### Tier 2: Established Math Tools
**Well-known mathematical theorems** - Axiomatized for practical formalization

**Count**: ~16 axioms

**Examples**:
- Stone's Theorem (Stone 1932) - Unitary groups ↔ self-adjoint generators
- Spectral Theorem (von Neumann 1932) - Hermitian operators have real eigenvalues
- Gleason's Theorem (Gleason 1957) - Probability measures on Hilbert space
- Jaynes MaxEnt (Jaynes 1957) - Maximum entropy principle
- Spohn's Inequality (Spohn 1978) - Entropy bounds
- Complex field algebraic properties (standard)

**Status**: These have published proofs in the mathematics literature. We axiomatize them following standard practice in formal quantum foundations (Hardy 2001, Chiribella et al. 2011).

**Why Axiomatized**: Full formalization would require extensive work without adding physical insight to LRT. Standard approach for foundations research.

**Revisit Policy**: As Mathlib matures, replace these with imports when available.

**NOT Counted As**: Novel LRT axioms (these are mathematical infrastructure)

---

### Tier 3: Universal Physics Assumptions
**Domain-standard physical principles** - Accepted across all physics

**Count**: 1 axiom
- Energy additivity for independent systems (Derivations/Energy.lean)

**Status**: Fundamental physical principle used in statistical mechanics, thermodynamics, QM, and classical mechanics. Cannot be derived from pure mathematics.

---

## Total Axiom Count

**Current**:
- Tier 1 (LRT Specific): 2 axioms
- Tier 2 (Established Math Tools): ~16 axioms
- Tier 3 (Universal Physics): 1 axiom
- **Total**: ~19 axioms

**Target**: Keep Tier 1 at 2-3 axioms, prove ~30-35 LRT-specific theorems from these foundations using Tier 2 tools.

---

## What LRT Proves (Not Axiomatized)

From these ~19 axioms, LRT proves:
- **Born Rule**: From MaxEnt (Tier 2) + Non-Contradiction (proven from 3FLL, 0 axioms)
- **Hilbert Space Structure**: From distinguishability geometry
- **Time Evolution**: From Identity constraint (Tier 1) + Stone's theorem (Tier 2)
- **Measurement Collapse**: From Excluded Middle (proven from 3FLL) + K-transition
- **Energy**: From entropy reduction
- **3FLL**: Identity, Non-Contradiction, Excluded Middle proven from Lean's classical logic (0 LRT axioms)
- **A = L(I)**: Actualization theorems proven (0 LRT axioms)

---

## Comparison to Other Theories

| Framework | Foundational Axioms | Math Infrastructure | Total |
|-----------|---------------------|---------------------|-------|
| **QM (Dirac)** | 4-5 postulates | ~10 | ~15 |
| **Hardy (2001)** | 5 operational axioms | ~10 | ~15 |
| **Chiribella et al. (2011)** | 6 principles | ~8 | ~14 |
| **LRT (this work)** | 2-3 (Tier 1) | ~16 (Tier 2) + 1 (Tier 3) | ~19 |

**Key Difference**: LRT derives Born rule and Hilbert space structure (QM postulates them). LRT postulates I and I_infinite (pre-physical ontology). LRT uses similar mathematical infrastructure as other theories.

---

## Honest Paper Framing

**What to say**:
> "LRT has 2 foundational axioms (I, I_infinite) defining the infinite information space, plus ~16 established mathematical results (Stone's theorem, spectral theorem, Gleason's theorem, MaxEnt, etc.) axiomatized for practical formalization, plus 1 standard physical assumption (energy additivity). From these, LRT proves ~30-35 theorems including Born rule, Hilbert space structure, time evolution, and measurement collapse."

**What NOT to say**:
- ❌ "LRT has only 2 axioms" (ignores Tier 2 infrastructure)
- ❌ "Everything proven from scratch" (uses established results as building blocks)

---

## Implementation

### Every Axiom Gets Tier Label

```lean
axiom I : Type*                              -- TIER 1: LRT SPECIFIC
axiom stones_theorem : ...                   -- TIER 2: ESTABLISHED MATH TOOLS
axiom energy_additivity : ...                -- TIER 3: UNIVERSAL PHYSICS ASSUMPTIONS
```

### Every File Header Includes Tier Count

```lean
**Axiom Count by Tier**:
- Tier 1 (LRT Specific): X axioms
- Tier 2 (Established Math Tools): Y axioms
- Tier 3 (Universal Physics): Z axioms
- **Total**: N axioms
```

See `STANDARD_FILE_HEADER.md` for complete format.

---

## References

**For complete system documentation**: See `AXIOM_CLASSIFICATION_SYSTEM.md`

**For quick reference**: See `TIER_LABELING_QUICK_START.md`

**For proof strategy**: See `PROOF_REFACTOR_STRATEGY.md`

**Exemplar**: `Foundation/IIS.lean` (proper Tier 1 axioms with full documentation)

---

**Last Updated**: 2025-11-04
**Status**: Active axiom classification framework
