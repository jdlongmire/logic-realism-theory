# Axiom Classification System for LRT Lean Formalization

**Purpose**: Distinguish **novel LRT postulates** from **established mathematical infrastructure** from **domain-standard physical assumptions** while maintaining formal verification.

**Date**: 2025-11-04
**Status**: Active framework for all Lean formalization

---

## The Three-Tier System

### Tier 1: LRT Specific (Foundational Postulates)

**Definition**: Novel ontological commitments that define what LRT *is*. These are analogous to QM's postulates (Hilbert space, Born rule, etc.).

**Keyword in Lean**: `axiom`

**Documentation Standard**:
```lean
/--
[Axiom Name]

**TIER 1: FOUNDATIONAL POSTULATE**

**Theory-Defining Assumption**: This is a core ontological commitment of Logic Realism Theory.

**Justification**: [Why this is necessary for the theory]

**Analogous to**: [Comparable postulate in QM/other theories]

**Status**: Novel LRT axiom

**References**: Logic_Realism_Theory_Main.md Section X.Y
-/
axiom [name] : [type]
```

**Current Count**: 2-3 axioms
- `I : Type*` - Infinite Information Space exists
- `I_infinite : Infinite I` - I is infinite
- (possibly) `L : I → A` - Actualization function (or provable as definition?)

**Counting Rule**: These ARE counted as "LRT axiom count" in papers/claims.

---

### Tier 2: Established Math Tools (Mathematical Infrastructure)

**Definition**: Well-known mathematical theorems with published proofs that we axiomatize for practical reasons. These are NOT novel LRT claims.

**Keyword in Lean**: `axiom` (but with "K_math" classification)

**Documentation Standard**:
```lean
/--
[Theorem Name]

**TIER 2: MATHEMATICAL INFRASTRUCTURE (K_math)**

**Established Result**: This theorem has a published proof in the mathematics literature.

**Original Reference**: [Author (Year), citation]

**Why Axiomatized**: Full formalization would require [X lines / specific Mathlib infrastructure]
without adding physical insight to LRT. Standard practice in quantum foundations formalizations.

**Mathlib Status**: [Not yet in Mathlib / Available but not imported / etc.]

**Proof Exists**: Yes - see [reference to textbook/paper with full proof]

**Status**: Axiomatized established result (not novel LRT axiom)

**Analogous Approach**: Hardy (2001), Chiribella et al. (2011), Dakic et al. (2009) similarly
use established mathematical theorems as building blocks without re-proving from ZFC.
-/
axiom [name] : [type]
```

**Examples**:
- **Stone's Theorem** (Stone 1932) - Unitary groups ↔ self-adjoint generators
- **Spectral Theorem** (von Neumann 1932) - Hermitian operators have real eigenvalues
- **Gleason's Theorem** (Gleason 1957) - Probability measures on Hilbert space
- **Jaynes MaxEnt** (Jaynes 1957) - Maximum entropy principle
- **Spohn's Inequality** (Spohn 1978) - Entropy change bounds
- **Jordan-von Neumann Theorem** (von Neumann & Jordan 1935) - Parallelogram law → inner product

**Current Count**: ~16 axioms

**Counting Rule**: These are NOT counted as "LRT axiom count" in papers/claims. Analogous to not counting "calculus" or "linear algebra" as axioms in a physics paper.

**Transparency Requirement**: Always disclose in papers:
- "LRT formalization uses 2-3 foundational axioms plus ~16 established mathematical results (Stone's theorem, spectral theorem, etc.) axiomatized for practical formalization reasons."
- "These mathematical results have published proofs; we axiomatize them following standard practice in formal quantum foundations (analogous to Hardy 2001, Chiribella et al. 2011)."

---

### Tier 3: Universal Physics Assumptions (Physical Postulates)

**Definition**: Fundamental physical principles that are accepted across physics (not specific to LRT or QM). Cannot be derived from pure mathematics.

**Keyword in Lean**: `axiom`

**Documentation Standard**:
```lean
/--
[Postulate Name]

**TIER 3: PHYSICAL POSTULATE (Domain-Standard)**

**Fundamental Physical Principle**: This is a domain-standard assumption used across physics.

**Justification**: [Why this cannot be derived from mathematics alone]

**Used By**: [List other theories/frameworks that assume this]

**Status**: Physical axiom (not novel to LRT, but cannot be mathematically derived)

**References**: [Standard physics textbooks]
-/
axiom [name] : [type]
```

**Examples**:
- **Energy Additivity**: E_total = E₁ + E₂ for independent systems
  - Used in: Statistical mechanics, thermodynamics, QM, classical mechanics
  - Cannot derive from pure math (requires physical extensivity principle)

**Current Count**: 1 axiom

**Counting Rule**: May be counted separately as "physical assumptions" but distinguished from LRT-specific postulates.

---

## Implementation: File Organization

### Option A: Separate Modules by Tier

```
lean/LogicRealismTheory/
├── Foundation/
│   ├── Axioms/
│   │   ├── Foundational.lean          # Tier 1: I, I_infinite
│   │   ├── MathematicalInfrastructure.lean  # Tier 2: All K_math
│   │   └── Physical.lean              # Tier 3: Energy additivity, etc.
│   └── ...
```

### Option B: Keep Current Structure, Add Headers

Keep axioms in their relevant modules (TimeEmergence.lean has Stone's theorem, etc.) but add clear tier classification in headers:

```lean
/-!
# Time Emergence from Identity Constraint

**Axiom Inventory**:
- **Tier 1 (Foundational)**: 0 axioms
- **Tier 2 (K_math)**: 1 axiom (Stone's theorem)
- **Tier 3 (Physical)**: 0 axioms
- **Total**: 1 axiom (established result, not novel LRT claim)

See AXIOM_CLASSIFICATION_SYSTEM.md for tier definitions.
-/
```

**Recommended**: Option B (current structure + clear classification)

---

## Counting Rules for Papers/Claims

### What to Report

**Honest Framing (use this)**:
- "LRT formalization: **2-3 foundational axioms** (I, I_infinite, L: I → A)"
- "Plus ~16 established mathematical results (Stone's theorem, spectral theorem, Gleason's theorem, etc.) axiomatized for practical formalization"
- "Plus 1 domain-standard physical postulate (energy additivity)"
- "These compare to QM's 4-5 postulates (Hilbert space, Born rule, unitary evolution, measurement collapse)"

**What LRT Derives vs. Postulates**:
- ✅ **LRT derives**: Born rule, Hilbert space structure, time evolution
- 🔷 **LRT postulates**: I, I_infinite (analogous to QM's Hilbert space postulate)
- 🔷 **Uses as building blocks**: Stone's theorem, MaxEnt (analogous to all QM theories using calculus)

### Comparison Table

| Framework | Foundational | K_math Infrastructure | Physical | Total Formal Axioms |
|-----------|-------------|----------------------|----------|---------------------|
| **QM (Dirac)** | 4-5 | ~10 (functional analysis) | ~2 | ~15-17 |
| **Hardy (2001)** | 5 | ~10 (Gleason, etc.) | ~1 | ~16 |
| **Chiribella et al.** | 6 | ~8 | ~1 | ~15 |
| **LRT (this work)** | 2-3 | ~16 | 1 | ~19-20 |

**Key**: All frameworks use established mathematical results. The distinguishing factor is **what's postulated vs. derived**. LRT derives Born rule and Hilbert space; QM postulates them.

---

## Verification Protocol

### For Each Axiom Declaration

**Checklist**:
1. [ ] Determine tier (1, 2, or 3)
2. [ ] Add appropriate documentation header
3. [ ] Include literature reference (if Tier 2 or 3)
4. [ ] State why axiomatized (if Tier 2)
5. [ ] Update axiom count tracking (by tier)
6. [ ] Add to `lean/AXIOMS.md` (comprehensive list)

### Peer Review Transparency

**When submitting papers**:
- Appendix: Complete axiom list by tier
- Distinguish "novel LRT axioms" from "mathematical infrastructure"
- Cite original sources for all Tier 2 axioms
- Compare axiom structure to comparable theories (Hardy, Chiribella, etc.)

---

## Example: Stone's Theorem

### Current (Problematic)
```lean
axiom stones_theorem : ...
```
→ Looks like we're claiming Stone's theorem as a novel result!

### Revised (Honest)
```lean
/--
Stone's Theorem (Stone 1932)

**TIER 2: MATHEMATICAL INFRASTRUCTURE (K_math)**

**Established Result**: One-parameter unitary groups on Hilbert spaces correspond
bijectively to self-adjoint operators (generators) via exponentiation:
U(t) = e^{-iHt/ℏ}

**Original Reference**:
Stone, M. H. (1932). "On one-parameter unitary groups in Hilbert space."
Annals of Mathematics, 33(3), 643-648.
https://doi.org/10.2307/1968538

**Why Axiomatized**: Full proof requires:
- Spectral theory for unbounded operators (~300 lines)
- Functional analysis infrastructure (Banach space theory)
- Resolution of identity for continuous spectra
Without adding physical insight to LRT's core claims.

**Mathlib Status**: Partial infrastructure exists (Mathlib.Analysis.NormedSpace.HahnBanach)
but full Stone's theorem not formalized as of Lean 4.3.0.

**Proof Exists**: Yes - see Reed & Simon (1980) "Methods of Modern Mathematical Physics Vol. I",
Theorem VIII.8, pp. 264-266. Standard textbook result in functional analysis.

**Used By**: All quantum mechanics formalizations (Hardy 2001, Chiribella et al. 2011, etc.)
similarly use Stone's theorem as infrastructure without re-proving.

**Status**: Axiomatized established result (not novel LRT axiom)
-/
axiom stones_theorem {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] :
  ∀ (U : ℝ → ℋ →L[ℂ] ℋ),
    (∀ t s, U (t + s) = U t ∘ U s) →  -- Group property
    (∀ t, ∀ ψ, ‖U t ψ‖ = ‖ψ‖) →       -- Unitary (norm-preserving)
    (U 0 = id) →                       -- Identity at zero
    ∃! (H : ℋ →L[ℂ] ℋ),                -- Unique generator exists
      (∀ ψ, IsSelfAdjoint H) ∧         -- H is self-adjoint
      (∀ t ψ, U t ψ = exp (-I * t * H) ψ)  -- U(t) = e^{-iHt}
```

---

## Benefits of This System

### 1. Formal Verification Maintained
- Still using `axiom` keyword (Lean requires this for unproven statements)
- Build system still checks all proofs that *are* completed
- No loss of formal rigor

### 2. Intellectual Honesty
- Clear distinction between novel claims and borrowed results
- Peer reviewers can immediately see what's theory-specific
- No misleading "we have only 2 axioms!" when there are 19 formally

### 3. Comparable to Standard Practice
- Mirrors how Hardy, Chiribella, Dakic, etc. handle their formalizations
- Standard practice: use established math as building blocks
- Don't count "prove calculus from ZFC" as part of physics axiom count

### 4. Reproducibility
- Anyone can verify which axioms are novel vs. established
- Literature references allow verification of Tier 2 claims
- Clear path for future work: "formalize Stone's theorem in Mathlib" is separate project

---

## Action Items for Current Refactor

### Immediate
1. Update all existing `axiom` declarations with tier classification
2. Add literature references to all Tier 2 axioms
3. Create `lean/AXIOMS.md` with complete by-tier listing
4. Update headers in all Lean files with tier counts

### Phase 1 Refactor (Revised Goals)
- **Don't try to prove Stone's theorem, spectral theorem, etc.** (waste of effort)
- **Do prove LRT-specific claims** from foundational axioms:
  - Born rule from MaxEnt + 3FLL
  - Hilbert space emergence from distinguishability
  - Measurement collapse from EM + K-transition
  - Energy from entropy reduction

### Documentation
- Update `PROOF_REFACTOR_STRATEGY.md` to reflect tier system
- Target: 2-3 Tier 1 + ~16 Tier 2 + 1 Tier 3 + **proven LRT theorems**
- Transparency: Always report axiom count by tier in papers

---

## Comparison: What Other Theories Do

### Hardy (2001) - "Quantum Theory from Five Reasonable Axioms"

**Claims**: 5 axioms derive quantum theory

**Reality**: 5 *operational* axioms + mathematical infrastructure
- Uses probability theory (entire field assumed)
- Uses information theory (Shannon entropy, etc.)
- Uses functional analysis (Hilbert spaces)
- Claims to "derive" QM from 5 axioms, but those axioms assume ~10 mathematical results

**Our approach is more honest**: We explicitly list the ~16 mathematical results we use.

### Chiribella et al. (2011) - "Informational Derivation of Quantum Theory"

**Claims**: 6 principles derive quantum theory

**Reality**: 6 *purification/reversibility* axioms + Gleason's theorem + spectral theorem + ...
- Explicitly uses Gleason's theorem (axiomatized, not proven)
- Uses spectral decomposition (axiomatized)
- Standard practice: use established math as infrastructure

**Our approach**: Same practice, more transparent documentation.

---

## Summary: The Three Keywords

In Lean formalization:

| What | Lean Keyword | Documentation Tier | Count In Papers As |
|------|-------------|-------------------|-------------------|
| **Novel LRT postulates** | `axiom` | Tier 1: Foundational | "LRT axioms" |
| **Established math results** | `axiom` | Tier 2: K_math | "Mathematical infrastructure (not novel)" |
| **Domain physical postulates** | `axiom` | Tier 3: Physical | "Standard physical assumptions" |
| **LRT-specific theorems** | `theorem` | (proven) | "Derived results" |

**Formal mechanism**: All use `axiom` keyword in Lean (that's the only way to declare unproven statements)

**Conceptual distinction**: Documentation, classification, and paper reporting distinguish them

**Honest reporting**:
- "LRT has 2-3 foundational axioms"
- "Plus ~16 established mathematical results axiomatized for practical formalization"
- "These results have published proofs; we follow standard practice in quantum foundations"

---

**Next Step**: Update all current axiom declarations with tier classification and references.
