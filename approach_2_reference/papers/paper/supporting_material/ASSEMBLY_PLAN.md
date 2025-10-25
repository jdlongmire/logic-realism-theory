# Final Paper Assembly Plan

**Target**: 8,500 words total (currently ~8,791 words in draft + ~2,979 trimmed = ~11,770 before cuts)

**Strategy**: Integrate 5 trimmed sections into Born_Rule_Paper_DRAFT.md while trimming existing content to reach target.

---

## Integration Points

### 1. Section 2.2 - Logical Operators (REPLACE)
**Action**: Replace existing Section 2.2 (179-223, ~400 words) with Section_2.2_TRIMMED.md (674 words)
- **Current**: Basic description of logical operators
- **New**: Theorem 2.2.1 (Natural Representation), 5 independent criteria, worked example
- **Net change**: +274 words
- **Justification**: Addresses peer review Priority 1 - logic→permutation mapping

### 2. Section 2.6 - Alternative Metrics (INSERT NEW)
**Action**: Insert Section_2.6_TRIMMED.md (424 words) as new subsection after 2.5
- **Current**: None
- **New**: Comparison table, robustness test, uniqueness demonstration
- **Net change**: +424 words
- **Justification**: Demonstrates framework robustness and uniqueness

### 3. Section 3.4 + 3.5 - Quantum Structure (REPLACE & EXTEND)
**Action**: Replace existing 3.4 (514-580, ~600 words) with Section_3.4_3.5_COMBINED_TRIMMED.md (366 words)
- **Current**: "Comparison to Standard Quantum Mechanics"
- **New**: "3.4 Hilbert Space Emergence" + "3.5 Superposition and Interference"
- **Net change**: -234 words
- **Justification**: Addresses peer review Priority 3 - quantum structure derivation

### 4. Section 4.5 - K(N) Triple Proof (INSERT NEW)
**Action**: Insert Section_4.5_K_N_TRIMMED.md (1,064 words) as new subsection after 4.4
- **Current**: None (currently K(N) is empirical parameter only)
- **New**: Triple proof (Mahonian + Coxeter + MaxEnt)
- **Net change**: +1,064 words
- **Justification**: **MAJOR CONTRIBUTION** - Addresses peer review Priority 2 (K derivation)

### 5. Section 6.3.1 - Lorentz Toy Model (INSERT NEW)
**Action**: Insert Section_6.3.1_TRIMMED.md (451 words) as new subsection under 6.3
- **Current**: Generic "Limitations and Open Problems" (1000-1042, ~400 words)
- **New**: Specific Lorentz invariance analysis with 2T connection
- **Net change**: +51 words (if we keep existing 6.3 intro and add 6.3.1 as sub-subsection)
- **Justification**: Addresses peer review Priority 4 - Lorentz hand-waving

---

## Word Count Budget

### Current State
- Base draft: 8,791 words
- Section 2.2 replacement: +274 words
- Section 2.6 insert: +424 words
- Section 3.4+3.5 replacement: -234 words
- Section 4.5 insert: +1,064 words
- Section 6.3.1 insert: +451 words
- **Subtotal**: 10,770 words

### Required Cuts: ~2,270 words

**Trimming Strategy**:

1. **Section 1 (Introduction)**: Currently ~2,400 words → Trim to ~1,800 words (-600)
   - Reduce 1.2 (logical compliance) by 30%
   - Trim 1.3 (main results) - move detailed tables to Section 4
   - Condense 1.4 (paper structure)

2. **Section 2 (Mathematical Framework)**: After replacements ~2,200 → Trim to ~1,900 (-300)
   - Condense 2.1 (information space)
   - Trim 2.3 (inversion count) - now covered in 2.2
   - Reduce 2.4 (empirical threshold) - now covered in 4.5
   - Condense 2.5 (geometric structure)

3. **Section 3 (Born Rule Derivation)**: After replacements ~1,600 → Keep at ~1,400 (-200)
   - Trim 3.1 and 3.2 (MaxEnt proofs already tight)
   - Remove redundancy with new 3.4+3.5

4. **Section 4 (Computational Validation)**: Currently ~2,400 → Trim to ~1,700 (-700)
   - Keep 4.5 (triple proof) fully
   - Reduce 4.1-4.4: condense methodology, trim detailed N=9 analysis
   - Move some tables to supplementary

5. **Section 5 (Lean 4)**: Currently ~1,800 → Trim to ~1,200 (-600)
   - This can be heavily condensed or moved to supplementary
   - Keep only key theorem statements

6. **Section 6 (Discussion)**: After 6.3.1 insert ~2,400 → Trim to ~2,000 (-400)
   - Reduce 6.1, 6.2, 6.4, 6.5, 6.6
   - Keep 6.3.1 (Lorentz) fully

7. **Section 7 (Conclusion)**: ~600 → Trim to ~500 (-100)

**Total Cuts**: 600 + 300 + 200 + 700 + 600 + 400 + 100 = 2,900 words

**Final Target**: 10,770 - 2,900 = 7,870 words (slightly under 8,500, leaving room for polish)

---

## Execution Steps

1. ✅ Read Born_Rule_Paper_DRAFT.md structure
2. ✅ Create assembly plan (this document)
3. Create PAPER_FINAL_v1.md with all integrations
4. Systematic trimming pass (7 sections)
5. Verify word count ≈ 8,500
6. Final polish and consistency check
7. Update references and figure captions

**Estimated Time**: 2-3 hours

---

## Figure Updates

Current figures (already exist):
- Figure 1-3: From previous work
- Figure 4a, 4b, 4c: Section 4.5 triple proof (just generated)
- Figure 4: Triple convergence diagram (just generated)

**Note**: May need to renumber figures to accommodate new Section 4.5 figures.
