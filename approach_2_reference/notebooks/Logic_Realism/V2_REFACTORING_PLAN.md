# V2 Refactoring Plan - Production-Ready Scholarly Notebooks

**Status**: Ready for implementation pending approval
**Created**: October 8, 2025
**Estimated Effort**: 2-3 hours for Notebooks 00-02

---

## Key Changes from V1 → V2

### 1. Self-Contained Code (No External Dependencies)

**V1 Approach**:
```python
# Cell 1: Import utilities
from logic_realism_utils import generate_permutations, inversion_count, ...
```

**V2 Approach**:
```python
# Cell 1: All imports and helper function definitions
import numpy as np
import matplotlib.pyplot as plt
import networkx as nx
from itertools import permutations

def generate_permutations(N):
    """Generate all permutations of {1, 2, ..., N}."""
    return list(permutations(range(1, N + 1)))

def inversion_count(sigma):
    """Compute inversion count h(σ)."""
    count = 0
    for i in range(len(sigma)):
        for j in range(i + 1, len(sigma)):
            if sigma[i] > sigma[j]:
                count += 1
    return count

# ... all other helper functions inlined here ...
```

**Impact**: Each notebook becomes 100-200 lines longer, but is fully portable.

---

### 2. Complete Mathematical Derivations

**V1 Approach**:
```markdown
## Mathematical Background

The inversion count h(σ) measures disorder. See Logic Realism paper Section 3.2.
```

**V2 Approach**:
```markdown
## Mathematical Derivation

### Definition: Inversion Count

For a permutation σ ∈ S_N, the **inversion count** is:

$$h(\sigma) = |\{(i,j) : 1 \leq i < j \leq N, \sigma(i) > \sigma(j)\}|$$

**Theorem**: The inversion count has the following properties:

1. **Bounds**: $0 \leq h(\sigma) \leq \frac{N(N-1)}{2}$ for all $\sigma \in S_N$

   *Proof*: The minimum occurs for the identity permutation $\text{id} = (1,2,\ldots,N)$ where no pairs are inverted, giving $h(\text{id}) = 0$. The maximum occurs for the reversal $\omega = (N, N-1, \ldots, 1)$ where all $\binom{N}{2} = \frac{N(N-1)}{2}$ pairs are inverted. □

2. **Adjacent Transpositions**: If $\sigma' = \sigma \cdot \tau_i$ where $\tau_i = (i, i+1)$, then $|h(\sigma') - h(\sigma)| = 1$

   *Proof*: An adjacent transposition swaps two neighboring elements. This either creates or removes exactly one inversion between positions $i$ and $i+1$, changing $h$ by ±1. □

... [complete derivation continues] ...
```

**Impact**: Each notebook gains 500-1500 words of LaTeX mathematics.

---

### 3. Validation Triangle Structure

**V1 Approach**: Mixed presentation of math, code, and validation

**V2 Approach**: Clear three-pillar structure

```markdown
# Notebook Structure

## 1. Mathematical Proof
[Complete derivation in LaTeX]

## 2. Computational Validation
[Python implementation + assertions]

## 3. Formal Verification Link
This result is formally verified in a machine-checked proof with zero `sorry` axioms:
- **File**: `lean/LFT_Proofs/PhysicalLogicFramework/Foundations/Permutations.lean`
- **Lines**: 1-250
- **Status**: ✓ Proven (0 sorrys)
```

---

### 4. Standardized Header Cell

**New Cell 1 in Every Notebook**:

```markdown
# Logic Realism Computational Validation
## Notebook XX: [Title]

---

**Copyright Notice**
© 2025 James D. Longmire. All rights reserved.

**License**
This work is released under the [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0).

You may reproduce, distribute, and create derivative works from this notebook, provided that:
1. You retain this copyright notice and license
2. You provide attribution to the original author
3. You indicate if modifications were made

**How to Cite**
If you use this notebook in your research, please cite:

```bibtex
@software{longmire2025_logic_realism_notebooks,
  author = {Longmire, James D.},
  title = {Logic Realism Computational Validation Notebooks},
  year = {2025},
  publisher = {GitHub},
  url = {https://github.com/jdlongmire/physical-logic-framework},
  note = {Notebook XX: [Title]}
}
```

**Papers Supported**:
- *Logic Realism Foundational Paper* (8,281 words)
- *Logic Field Theory I: Quantum Probability* (Technical)

**Formal Verification**:
- Lean 4 proof: `[path to .lean file]`
- Status: ✓ Proven (0 sorrys)

---
```

---

## V2 Notebook Template Structure

Each notebook will follow this exact structure:

```
┌─────────────────────────────────────────────────────────┐
│ CELL 1: Header (Markdown)                               │
│ - Copyright & License                                   │
│ - Citation                                              │
│ - Paper references                                      │
│ - Lean proof reference                                  │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ CELL 2: Introduction (Markdown)                         │
│ - Purpose of notebook                                   │
│ - Key theorem being validated                           │
│ - Outline of validation approach                        │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ CELL 3: Mathematical Derivation (Markdown)              │
│ - Complete LaTeX proof                                  │
│ - Step-by-step derivation                               │
│ - All lemmas and theorems proven                        │
│ - No references to external documents required          │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ CELL 4: Setup & Helper Functions (Code)                 │
│ - All library imports                                   │
│ - All helper functions (inlined, no external .py)       │
│ - Configuration (matplotlib settings, paths, etc.)      │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ CELLS 5-N: Computational Implementation (Code+Markdown) │
│ - Main computational work                               │
│ - Figure generation                                     │
│ - Table generation                                      │
│ - Intermediate results                                  │
│ - Commentary cells explaining each step                 │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ CELL N+1: Validation Summary (Code)                     │
│ - Assert statements for all key results                 │
│ - Programmatic verification of numerical accuracy       │
│ - Print success message if all checks pass              │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ CELL N+2: Conclusion & Formal Verification (Markdown)   │
│ - Summary of findings                                   │
│ - Confirmation that computation validates proof         │
│ - Explicit link to Lean proof file                      │
│ - References                                            │
└─────────────────────────────────────────────────────────┘
```

---

## Refactoring Checklist for Each Notebook

### Notebook 00: Permutations and Inversions

**Current State**: V1 with `logic_realism_utils` imports

**V2 Modifications**:
- [ ] Add header cell (copyright, license, citation)
- [ ] Add introduction cell (purpose, theorem, outline)
- [ ] Add complete mathematical derivation cell:
  - Definition of inversion count
  - Proof of bounds (0 to N(N-1)/2)
  - Proof of adjacent transposition property
  - Mahonian distribution definition and symmetry
  - Permutohedron geometry
- [ ] Inline all helper functions:
  - `generate_permutations(N)`
  - `inversion_count(sigma)`
  - `mahonian_distribution(N)`
  - `permutohedron_embedding(sigma)`
  - `build_cayley_graph(N)`
  - `project_to_2d(vertices)`
  - `is_adjacent_transposition(sigma1, sigma2)`
- [ ] Add validation summary cell with assertions:
  - `assert len(generate_permutations(3)) == 6`
  - `assert inversion_count((1,2,3)) == 0`
  - `assert inversion_count((3,2,1)) == 3`
  - `assert sum(mahonian_distribution(3).values()) == 6`
  - Print "✓ All validation checks passed"
- [ ] Add conclusion cell with Lean proof reference:
  - `lean/.../Foundations/Permutations.lean`

**Estimated Effort**: 45-60 minutes

---

### Notebook 01: Logical Operators

**Current State**: V1 with `logic_realism_utils` imports

**V2 Modifications**:
- [ ] Add header cell (copyright, license, citation)
- [ ] Add introduction cell (purpose, Theorem on logical operators, outline)
- [ ] Add complete mathematical derivation cell:
  - Definition of logical operators (ID, NC, EM)
  - Composition L = EM ∘ NC ∘ ID
  - Definition of V_K = {σ : h(σ) ≤ K}
  - Proof of nested structure: V_0 ⊂ V_1 ⊂ ... ⊂ V_{max}
  - Proof that identity ∈ V_K for all K ≥ 0
- [ ] Inline all helper functions (same as Notebook 00, plus):
  - `compute_V_K(N, K)`
  - `logical_operator_L(sigma, K)`
  - `operator_ID(sigma)`
  - `operator_NC(sigma, K)`
  - `operator_EM(sigma, K)`
- [ ] Add validation summary cell with assertions:
  - `assert (1,2,3) in compute_V_K(3, 0)`  # Identity in V_0
  - `assert len(compute_V_K(3, 1)) == 3`  # V_1 has 3 elements
  - `assert all(h(s) <= K for s in V_K)`  # All states valid
  - Print "✓ All validation checks passed"
- [ ] Add conclusion cell with Lean proof reference:
  - `lean/.../Foundations/LogicalOperators.lean` (if exists)

**Estimated Effort**: 45-60 minutes

---

### Notebook 02: Constraint Threshold K(N) = N-2

**Current State**: V1 with `logic_realism_utils` imports

**V2 Modifications**:
- [ ] Add header cell (copyright, license, citation)
- [ ] Add introduction cell (purpose, Theorem K(N) = N-2, outline)
- [ ] Add complete mathematical derivation cell (THREE PROOFS):
  1. **Mahonian Statistics Proof**:
     - Definition of Mahonian distribution M_N(h)
     - Proof of symmetry: M_N(h) = M_N(N(N-1)/2 - h)
     - Peak at h = K(N) = N-2 (maximum of distribution)
  2. **Coxeter Braid Relations Proof**:
     - Generators τ_i = (i, i+1) for i = 1, ..., N-1
     - Braid relations: τ_i τ_{i+1} τ_i = τ_{i+1} τ_i τ_{i+1}
     - Count of independent braid relations = N-2
  3. **Maximum Entropy Proof**:
     - Information-theoretic optimization
     - Lagrange multiplier derivation
     - K = N-2 maximizes entropy subject to constraints
- [ ] Inline all helper functions (same as Notebook 00/01, plus):
  - `K_from_mahonian(N)`
  - `K_from_coxeter(N)`
  - `K_from_maxent(N)`
  - `verify_K_N_formula(N)`
- [ ] Add validation summary cell with assertions:
  - `assert K_from_mahonian(3) == 1`
  - `assert K_from_coxeter(3) == 1`
  - `assert K_from_maxent(3) == 1`
  - `assert len(compute_V_K(3, 1)) == OEIS_A001892[3]`  # OEIS match
  - `assert all(verify_K_N_formula(N)['all_agree'] for N in range(3, 8))`
  - Print "✓ All validation checks passed (3 independent proofs agree)"
- [ ] Add conclusion cell with Lean proof reference:
  - `lean/.../Foundations/ConstraintThreshold.lean (0 sorrys, ~400 lines)`

**Estimated Effort**: 60-90 minutes

---

## Implementation Order

1. **Refactor Notebook 00** → Test → Commit
2. **Refactor Notebook 01** → Test → Commit
3. **Refactor Notebook 02** → Test → Commit
4. **Update README.md** with V2 installation instructions
5. **Final commit**: "V2 refactoring complete - all notebooks self-contained"

---

## Testing Protocol

After each notebook refactoring:

1. **Restart kernel** and **run all cells**
2. **Verify all assertions pass** in validation summary
3. **Check all figures generated** and saved to `outputs/`
4. **Verify no import errors** (no `logic_realism_utils` imports)
5. **Commit** to git with detailed message

---

## README.md Updates Required

### New Installation Section

```markdown
## Installation

### Quick Start (Minimal Dependencies)

```bash
cd notebooks/Logic_Realism/
pip install -r requirements.txt
```

### Exact Reproducibility

For perfect environment reproduction:

```bash
pip install -r requirements.lock.txt
```

This installs the exact package versions used during notebook development.

## Running Notebooks

Each notebook is fully self-contained and can be run independently:

```bash
jupyter notebook 00_Permutations_and_Inversions.ipynb
```

**Important**: Always use "Restart Kernel & Run All" to ensure reproducibility.
```

---

## Expected Deliverables

After V2 refactoring is complete:

- [ ] 3 refactored notebooks (00-02) meeting all V2 requirements
- [ ] `requirements.txt` (minimal dependencies)
- [ ] `requirements.lock.txt` (exact environment)
- [ ] Updated `README.md` with installation instructions
- [ ] 4 git commits (1 per notebook + 1 for README)
- [ ] All notebooks tested and validated
- [ ] All outputs generated and saved

**Total Time**: 2.5-3.5 hours

---

## Benefits of V2 Approach

1. **Perfect Portability**: Send a single `.ipynb` file to reviewer
2. **Peer Review Ready**: Complete proofs embedded in notebook
3. **Validation Triangle**: Math → Code → Lean (all three explicit)
4. **Reproducibility**: Exact dependencies locked
5. **Citation**: Clear authorship and licensing
6. **Scholarly**: Publication-quality mathematical exposition

---

## Approval Required

This is a significant refactoring effort. Please approve before proceeding:

- [ ] **Approve V2 strategy** as outlined above
- [ ] **Confirm** elimination of `logic_realism_utils.py` dependency
- [ ] **Confirm** addition of complete mathematical derivations
- [ ] **Confirm** copyright/license/citation headers

---

**Created**: 2025-10-08
**Author**: Claude (Session 5.0)
**Status**: Awaiting approval
