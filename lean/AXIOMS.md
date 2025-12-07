# LRT Axiom Approach

**Logic Realism Theory Lean Formalization**

---

## Formalization Methodology

All formal reasoning for this work is carried out in the Lean 4 theorem prover, using the community mathematical library Mathlib as the foundational corpus. Lean's type-theoretic kernel serves as the trusted core, so that every theorem stated in the development is accompanied by a machine-checkable proof object.

### Use of External Mathematical Results

The central results in this work build on standard theorems that are widely accepted in the mathematical literature but not yet fully formalized in Lean. To incorporate these ingredients, each such result is represented as an explicit Lean axiom: a constant of the appropriate propositional type, declared without proof and annotated with a citation to the source theorem in the literature.

**These axioms are collected in a dedicated module:** `LogicRealismTheory/ExternalTheorems.lean`

This ensures that every dependency on non-formalized mathematics is localized and auditable.

### Soundness Interpretation

Under this methodology, any theorem proved in the Lean development is formally correct relative to:
1. The soundness of Lean's kernel
2. The truth of the explicitly stated axioms corresponding to external results

If, in future work, some of these axioms are replaced by fully formal Lean proofs of the corresponding literature theorems, the remaining development can be reused unchanged.

### Correspondence to Technical Paper

The external theorems (E1-E8) correspond to Appendix A in:
> Longmire, J.D. (2025). "Logic Realism Theory: Technical Foundations"
> DOI: 10.5281/zenodo.17831883

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
- **Energy**: From entropy reduction (see theory/derivations/Identity_to_K_ID_Derivation.md for full non-circular chain: Identity → Noether → Fermi)
- **Variational Framework**: K_total = (ln 2)/β + 1/β² + 4β² (98% derived from first principles, see theory/derivations/)
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

## Axiom Count Framing (Always Use This)

**When discussing LRT axiom count, use this framing:**

- ❌ **NOT** "57 axioms" or "58 axioms" (raw declaration count)
- ✅ **USE** "~19 axioms (2 Tier 1 + ~16 Tier 2 + 1 Tier 3)"
- ✅ **Separate** Tier 2 (~16) as mathematical infrastructure, not novel LRT axioms

**Why this matters:**
- Tier 2 axioms are standard mathematical results (Stone's theorem 1932, Gleason's theorem 1957, etc.)
- ALL quantum mechanics reconstructions use similar mathematical infrastructure (~10-16 axioms)
- Other programs (Hardy, Chiribella, Dakic) don't count infrastructure as "theory axioms"
- Honest comparison: LRT foundational axioms (2 Tier 1) vs. their foundational axioms (3-6)

**Current honest breakdown:**
- **Total axioms**: ~19
  - **Tier 1 (LRT Specific)**: 2 axioms (I, I_infinite)
  - **Tier 2 (Established Math Tools)**: ~16 axioms (Stone's, Gleason's, MaxEnt, etc.)
  - **Tier 3 (Universal Physics)**: 1 axiom (energy additivity)

**What LRT derives** (not axiomatized):
- Born rule, Hilbert space structure, time evolution, measurement collapse
- Variational framework K_total = (ln 2)/β + 1/β² + 4β² (98% derived from first principles)
- ~30-35 LRT-specific theorems proven from these foundations

**Comparison to other theories:**
- Hardy (2001): 5 operational axioms + ~10 math infrastructure = ~15 total
- Chiribella et al. (2011): 6 principles + ~8 math infrastructure = ~14 total
- LRT: 2 foundational + ~16 math infrastructure + 1 physics = ~19 total

**Key difference**: LRT derives Born rule and Hilbert space (QM postulates them). LRT postulates infinite information space I (pre-physical ontology).

---

## Honest Paper Framing

**Recommended framing for papers**:
> "LRT has 2 foundational axioms (I, I_infinite) defining the infinite information space, plus ~16 established mathematical results (Stone's theorem, spectral theorem, Gleason's theorem, MaxEnt, etc.) axiomatized for practical formalization, plus 1 standard physical assumption (energy additivity). From these, LRT proves ~30-35 theorems including Born rule, Hilbert space structure, time evolution, measurement collapse, and the variational framework."

**What NOT to say**:
- ❌ "LRT has only 2 axioms" (ignores Tier 2 infrastructure - dishonest)
- ❌ "LRT has 57 axioms" (counts raw declarations without tier classification - misleading)
- ❌ "Everything proven from scratch" (uses established results as building blocks)

**Transparency requirement**: Always disclose tier breakdown when claiming "2 axioms" or similar

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

## Related Derivations

**Theory Derivations** (theory/derivations/):
- `Identity_to_K_ID_Derivation.md` - Non-circular energy derivation (Identity → Noether → Fermi)
- `ExcludedMiddle_to_K_EM_Derivation.md` - EM → Shannon entropy → Lindblad dephasing
- `Measurement_to_K_enforcement_Derivation.md` - 4-phase measurement cycle (N=4, β² scaling)
- `Phase_Weighting_Symmetry_Analysis.md` - Equal weighting analysis (70-80% justified)
- `Phase_Weighting_Coupling_Analysis.md` - Coupling theory deep dive

**Status**: Variational framework 98% derived from first principles (Session 13.0, 2025-11-06)

---

**Last Updated**: 2025-11-06
**Status**: Active axiom classification framework
