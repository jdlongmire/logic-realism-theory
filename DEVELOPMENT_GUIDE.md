# Development Guide

**Purpose**: Reference material for development workflows, architecture, and troubleshooting.

**For operational protocols**, see `CLAUDE.md`.

---

## Architecture

### Core Components

1. **Publications** (`paper/`): Canonical scholarly papers and supplementary materials
   - **Main Paper**: `It_from_Logic_Scholarly_Paper.md` (peer-review ready)
   - **Figures**: Publication-ready visualizations (figure1-6)
   - **Supplementary**: Foundational framework, first-principles derivation, Gödel argument
   - This is the primary reference for the theoretical framework

2. **Jupyter Notebooks** (`notebooks/approach_1/`): Computational validation and exploration
   - **Foundation Layer** (00-02): Core thesis, information space, and logical operator implementation
   - **Worked Examples** (03-05): Complete analyses for N=3,4 with geometric visualizations
   - **Spacetime Emergence** (06-09): Scaling analysis, time emergence, and strain dynamics
   - **Quantum Derivations** (10-13): Quantum mechanics derivation from geometric principles
   - **Extensions** (14, 20-22): Gravity proof-of-concept, predictions, and comparative analysis

3. **Lean 4 Proofs** (`lean/LFT_Proofs/`): Formal mathematical verification
   - Configured with Mathlib for advanced mathematical libraries
   - Project name: `PhysicalLogicFramework`
   - Modules: Foundations, LogicField, QuantumEmergence

4. **Multi-LLM System** (`multi_LLM_model/`): AI consultation framework
   - Public distribution package for multi-model expert consultation
   - Used in development for Lean 4 proof assistance
   - Parallel queries to Grok-3, GPT-4, Gemini-2.0

5. **Analysis Scripts** (`scripts/`): Computational utilities
   - Constraint analysis and validation tools
   - Data processing scripts

6. **Archive** (`archive/`): Historical development artifacts
   - Previous paper versions (v1-v5)
   - AI conversation logs and development notes
   - Session artifacts

### Key Mathematical Concepts

- **Information Space**: Directed graphs on N elements
- **Logical Operator L**: Composition of Identity, Non-Contradiction, and Excluded Middle
- **Permutohedron**: The N-1 dimensional geometric realization of the symmetric group S_N
- **L-Flow**: Monotonic descent process that generates the arrow of time

---

## Development Commands

### Python/Jupyter Environment

```bash
# Install Python dependencies
pip install -r notebooks/LFT_requirements.txt

# Launch Jupyter notebook environment
jupyter notebook

# Navigate to notebooks/ directory and run foundation notebooks first (00-02)
```

### Core Dependencies
- `numpy>=1.20.0` - Numerical computation
- `matplotlib>=3.4.0` - Plotting and visualization
- `networkx>=2.6.0` - Graph algorithms
- `pandas>=1.3.0` - Data manipulation
- `scipy>=1.7.0` - Scientific computing
- `jupyter>=1.0.0` - Notebook environment

### Lean 4 Formal Proofs

```bash
# Build Lean project (requires Lean 4 and Lake)
cd lean
lake build

# Check specific proof files
lake exe cache get  # Download mathlib cache
lean --make LFT_Proofs/
```

**Note**: Lean/Lake may not be available in all environments. The repository can be used without Lean for computational work.

---

## GitHub Issue Management

### Accessing Issues Programmatically

When `gh` CLI is not available, use the WebFetch tool to access GitHub issues:

**Method 1: List all issues**
```
WebFetch(url: "https://github.com/jdlongmire/logic-realism-theory/issues",
         prompt: "List all open issues with their titles, numbers, and descriptions.")
```

**Result**: Summary of all issues with titles, numbers, labels, dates
**Limitation**: Descriptions may be truncated or missing in summary view

**Method 2: Get full issue details**
```
WebFetch(url: "https://github.com/jdlongmire/logic-realism-theory/issues/[N]",
         prompt: "Extract the full issue title, description/body, labels, and any comments.")
```

**Result**: Complete issue body, all comments, full context
**Use when**: Need detailed description or comments for a specific issue

### Example Workflow

```bash
# Step 1: Try gh CLI first (may not be installed)
gh issue list --repo jdlongmire/logic-realism-theory --limit 10

# Step 2: If gh not available, use WebFetch to get issue list
# (See Method 1 above)

# Step 3: For each issue of interest, fetch full details
# (See Method 2 above, replace [N] with issue number)
```

### When to Use Each Method

**Use summary view (Method 1) when**:
- Getting overview of all open issues
- Checking issue counts and labels
- Quick triage of what needs attention

**Use individual fetch (Method 2) when**:
- Issue description appears empty in summary
- Need to see comments or discussion
- Writing response or making updates
- Detailed review required

### Current Issues (as of Oct 30, 2025)

**Repository**: https://github.com/jdlongmire/logic-realism-theory/issues

**Active Issues**:
- **#5**: Add Null hypothesis (H₀: T2/T1 ≈ 1.0 vs H₁: T2/T1 ≈ 0.81)
- **#4**: Paper v3 review (hierarchical emergence, QM comparison, axiom transparency)
- **#3**: Prediction paths - additions (10+ testable predictions, 2025-2035 timeline)
- **#2**: don't forget Lagrangian and Hamiltonian (empty description - needs filling)
- **#1**: Lean dependencies into structured .olean provenance tree (tamper-evident system)

**Note**: Issue summaries may not show full descriptions. Always fetch individual issues for complete context.

---

## Computational Parameters

### Safe Operating Ranges
- **N (elements)**: 3-6 for exact computation, 3-8 for sampling methods
- **K (micro-constraints)**: 1-200 for finite-K quantum effects
- **trials**: 1000-10000 for statistical convergence

### Memory Requirements
- N≤4: Any modern laptop
- N=5: ~1GB RAM
- N=6: ~4GB RAM
- Full analysis: ~30 minutes runtime

---

## Common Workflows

### 1. Quick Validation
Run notebooks 03 (N=3 example) and 04 (N=4 geometry) to verify core constructions work correctly.

### 2. Full Reproduction
Execute notebooks in order: Foundation (00-02) → Examples (03-05) → Choose specialization track (quantum 10-13, spacetime 06-09, or predictions 20-22).

### 3. New Research
Start with Foundation notebooks to understand the framework, then modify parameters in existing notebooks or create new analyses.

---

## File Organization

### Repository Structure
```
physical_logic_framework/
├── paper/                   # Canonical publications
│   ├── It_from_Logic_Scholarly_Paper.md/pdf
│   ├── figures/            # Publication figures
│   ├── supplementary/      # Supporting documents
│   └── potential_extensions/ # Speculative future research
├── notebooks/              # Computational validation
│   └── approach_1/         # Complete theory (00-22)
├── lean/                   # Formal proofs
│   └── LFT_Proofs/PhysicalLogicFramework/
├── multi_LLM/              # AI consultation (public)
│   ├── consultation/       # Team consultation results
│   └── enhanced_llm_bridge.py  # Multi-LLM system
├── sprints/                # Sprint planning and tracking
│   ├── sprint_6/           # Current sprint (Born Rule)
│   └── SPRINT_PLAN_ENHANCED_TEAM_INTEGRATION.md
├── scripts/                # Analysis utilities
├── Session_Log/            # Session tracking (X.Y format)
└── archive/                # Historical versions
```

### Notebook Outputs
Notebooks generate files in `notebooks/approach_1/outputs/`:
- `N*_permutohedron_*.png` - Geometric visualizations
- `N*_edge_distortions.csv` - Embedding quality metrics
- `finiteK_*.png` - Quantum finite-size effects
- `*_summary.json` - Numerical results

### Publication Figures
Canonical figures are in `paper/figures/`:
- 6 publication-ready PNG files (figure1-6)
- `figure_data.json` - Source data
- `figure_specifications.md` - Technical specs

---

## Key Verification Tests

```python
# Core construction (notebook 03)
N = 3
assert factorial(N) == 6  # S_3 has 6 elements
assert N*(N-1)*factorial(N)//2 == 6  # Adjacent edges

# Dimensionality (notebook 04)
N = 4
assert N - 1 == 3  # Spatial dimensions

# Reproducibility - always set seeds
import numpy as np, random
np.random.seed(42); random.seed(42)
```

---

## Troubleshooting

- **Memory errors for N>6**: Use sampling methods or reduce trial counts
- **Missing outputs directory**: Notebooks create this automatically with `os.makedirs('./outputs', exist_ok=True)`
- **NetworkX version issues**: Ensure v2.6+ for `nx.all_topological_sorts()`
- **Slow linear extensions**: Add `limit=1000` parameter to enumeration functions

---

## Migration Notes

### If you find files in wrong locations:
1. Identify canonical location from CLAUDE.md folder structure protocol
2. Move file to correct location
3. Update all references (Lean comments, README files, etc.)
4. Add deprecation notice if renaming folder

**Example (Sprint 8)**:
- Created notebooks in `approach_1` → Should be in `Logic_Realism`
- Solution: Migrate to `Logic_Realism/`, deprecate `approach_1/`

---

## Research Context

This repository implements active theoretical research in fundamental physics. All results are mathematical/computational demonstrations of the LFT framework. The core thesis is that physical laws (quantum mechanics, spacetime geometry, gravity) can be derived rather than postulated, emerging from logical consistency requirements on an information space.
