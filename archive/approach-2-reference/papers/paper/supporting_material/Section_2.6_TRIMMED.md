# Section 2.6: Alternative Metrics - Robustness Analysis (TRIMMED)

**Word Count Target**: 400 words (trimmed from 2,200)

---

We examine four alternative distance measures on permutations, demonstrating that **only inversion count** satisfies the five criteria from Section 2.2.

## Comparison Table

| Metric | Definition | Logical? | Statistical? | Computational? | Informational? | Algebraic? |
|--------|------------|----------|--------------|----------------|----------------|------------|
| **Inversion count** h | # pairs (i<j) with σ(i)>σ(j) | ✓ EM violations | ✓ Kendall tau | ✓ Bubble sort | ✓ MDL | ✓ Coxeter word length |
| **Hamming distance** d_H | |{i : σ(i)≠i}| | ✗ No | ✗ No | ✗ No | ✗ No | ✗ No |
| **Cayley distance** d_C | Min # arbitrary transpositions | ✗ No | ✗ No | ✗ Not adjacent | ✗ No | ✗ Not adjacent |
| **Ulam distance** d_U | N - LIS(σ) | ✗ Indirect | ✗ No | ✗ Complex | ✗ No | ✗ No |

LIS(σ) = length of longest increasing subsequence

## Why Alternatives Fail

**Hamming distance**: Counts position mismatches, not pairwise ordering violations. Example: σ=(2,1,3,4) has d_H=2 but h=1 (only one pair misordered). No logical interpretation.

**Cayley distance**: Uses arbitrary transpositions (any pair swap), breaking locality. Not related to Coxeter generators (which are adjacent only). Cycle-based, not relational.

**Ulam distance**: Indirect measure (what's missing vs. what's wrong). Computationally complex. No pairwise violation interpretation.

## Robustness Test: K=N-2 Specificity

**Question**: Would K=N-2 hold for alternative metrics?

**Test** (N=4): For each metric d, compute V_2^d = {σ : d(σ,id) ≤ 2}

| Metric | |V_2| | Symmetric split? | K=N-2 properties? |
|--------|------|------------------|-------------------|
| Inversion | 9 | ✓ Yes | ✓ Yes |
| Hamming | 7 | ✗ No | ✗ No |
| Cayley | 14 | ✗ No | ✗ No |

**Result**: K=N-2 is **specific to inversion count**. Alternative metrics exhibit neither:
- Mahonian symmetry split (Section 4.5.1) ✗
- Braid relation connection (Section 4.5.2) ✗
- MaxEnt selection (Section 4.5.3) ✗

## Conclusion

Inversion count is the **unique metric** where:
1. Logical: Counts EM violations directly
2. Statistical: Equals Kendall tau (standard)
3. Computational: Equals bubble sort cost
4. Informational: Proportional to description length
5. Algebraic: Equals Coxeter word length
6. **K=N-2 derivation holds** (Section 4.5 triple proof)

Alternative metrics fail criterion (1)-(5) and break the K=N-2 mathematical structure. This confirms the framework is **tightly constrained** by mathematical necessity, not arbitrary choice—a strength, demonstrating robustness.

---

**Full alternative analysis**: See supplementary material for detailed examination, experimental verification, and sensitivity analysis.
