# Theory Folder

This folder contains all theoretical documents for Logic Realism Theory (LRT), organized by document type and purpose.

---

## Folder Structure

```
theory/
├── papers/          # Main canonical papers
├── frameworks/      # Core theoretical frameworks
├── derivations/     # First-principles mathematical derivations (Session 13.0)
├── analysis/        # Technical analyses & problem solving
├── predictions/     # Experimental predictions & test designs
├── drafts/          # Work in progress sections & revisions
├── references/      # Bibliography & citations
├── supplementary/   # Supplementary materials (MToE papers)
└── figures/         # Figures (currently empty)
```

**Note**: Audit files are stored in the root-level `audit/` folder (not in theory/).

---

## 📄 papers/ - Main Canonical Papers

**Purpose**: Primary scholarly papers representing the canonical statements of LRT.

### Active Papers

- **`Logic-realism-theory-v3.md`** (1,986 lines) 📋 **HISTORICAL WORKING PAPER**
  - Clean slate rewrite with standard physics paper structure (Session 4.0+)
  - Complete 10-section manuscript
  - Includes variational optimization framework
  - **Status**: Historical version (superseded by root Logic_Realism_Theory_Main.md)

- **`Logic_Realism_Theory_Branch-2.md`** (390 lines) 📚 **ALTERNATIVE FRAMING**
  - Alternative philosophical approach
  - Focuses on energy as "work of instantiation" (Landauer)
  - Emphasizes quantum measurement problem resolution
  - Simpler presentation, more accessible
  - **Status**: Complementary framing reference

### Historical Reference & Snapshots

- **`Logic-realism-theory-foundational.md`** (1,401 lines)
  - Original foundational paper
  - Source material for content extraction
  - Contains existing derivations, philosophical arguments, experimental protocols
  - **Status**: Historical reference

- **`Logic_Realism_Theory_Main_2025-11-05_Session10.md`** (2,608 lines)
  - Session 10 snapshot of main paper
  - Captures state before Session 13.0 variational framework derivation
  - **Status**: Historical snapshot

---

## 🧩 frameworks/ - Core Theoretical Frameworks

**Purpose**: Formal mathematical and philosophical frameworks underlying LRT.

- **`LRT_Hierarchical_Emergence_Framework.md`** (430 lines) ⚠️ **CRITICAL REFERENCE**
  - Formal mathematical framework for hierarchical emergence
  - Rigorous definitions of information space structure
  - Constraint operator hierarchy (L_0 → L_1 → L_2 → ...)
  - Emergence dynamics differential equations
  - Entropy reduction formalism
  - Proto-mathematical primitive specifications
  - **When to use**: Formalizing claims about emergence, defining operators mathematically, addressing "hand-wavy" critiques

- **`LRT_Philosophical_Foundations.md`** (1,635 lines)
  - Deep philosophical grounding of LRT
  - Logic as prescriptive vs descriptive
  - Ontological status of information space
  - Response to philosophical objections

- **`LRT_Explanatory_Power.md`** (1,249 lines)
  - Comprehensive analysis of LRT's explanatory scope
  - Comparison to competing frameworks
  - Testable predictions catalog

---

## 🔬 derivations/ - First-Principles Mathematical Derivations

**Purpose**: Rigorous mathematical derivations from LRT axioms to physical predictions.

**Session 13.0 Achievement** (2025-11-06): Variational framework 98% derived from first principles (~3,700 lines)

- **`Identity_to_K_ID_Derivation.md`** (381 lines) ✅ **100% DERIVED**
  - Non-circular chain: Identity → Noether theorem → Energy conservation → Fermi's Golden Rule
  - Result: K_ID = 1/β²
  - Expert validated, ready for Lean formalization

- **`ExcludedMiddle_to_K_EM_Derivation.md`** (401 lines) ✅ **100% DERIVED**
  - Chain: Excluded Middle → Shannon entropy (ln 2) → Lindblad dephasing (1/β)
  - Result: K_EM = (ln 2)/β
  - Expert validated, ready for Lean formalization

- **`Measurement_to_K_enforcement_Derivation.md`** (592 lines) ✅ **95% DERIVED**
  - N=4 phases derivation (3FLL + irreversibility)
  - β² scaling rigorously proven
  - Result: K_enforcement = 4β²
  - Expert validated, ready for Lean formalization

- **`Four_Phase_Necessity_Analysis.md`** (520 lines)
  - Detailed analysis of why N=4 phases are necessary
  - Physical mechanisms for each phase

- **`Phase_Weighting_Symmetry_Analysis.md`** (662 lines)
  - Analysis of equal weighting assumption (wᵢ=1)
  - 3FLL symmetry, MaxEnt, Landauer's principle examination
  - Finding: 70-80% theoretically justified

- **`Phase_Weighting_Coupling_Analysis.md`** (887 lines)
  - Deep dive into coupling theory for phase weights
  - Multi-LLM expert consultation on derivability
  - Consensus: NOT 100% derivable (honest 98% with caveat)

- **`Phase_Weighting_Variational_Analysis.md`** (676 lines)
  - Variational optimization β = 3/4 derivation
  - Comprehensive multi-phase analysis

**Status**: Complete mathematical derivations providing ~10-15 theorems for future Lean formalization

---

## 🔬 analysis/ - Technical Analyses & Problem Solving

**Purpose**: Deep technical investigations of specific derivation challenges and open problems.

**NOTE**: Many issues identified in these analyses have been resolved by Session 13.0 derivations (see derivations/ folder above).

- **`Energy_Circularity_Analysis.md`** (344 lines)
  - Identifies circularity in energy derivation via Spohn's inequality
  - Problem: Spohn presupposes energy, temperature
  - **Status**: ✅ RESOLVED in Session 13.0 (Identity_to_K_ID_Derivation.md provides non-circular chain)

- **`Eta_Parameter_Analysis.md`** (383 lines)
  - Analysis of η (Excluded Middle coupling strength) parameter
  - Derivation approaches: Fisher information, constraint threshold dynamics
  - **Status**: ✅ RESOLVED in Session 13.0 (98% derived via variational framework)
  - See: derivations/ folder for complete derivation chain

- **`K_Threshold_Gap_Analysis.md`** (525 lines)
  - Analysis of K-threshold dynamics (constraint count transitions)
  - Quantum (fixed K) vs non-unitary (measurement, K → K-ΔK) regimes
  - Gap identification and resolution strategies
  - **Status**: Partially addressed by Session 13.0 K_enforcement derivation

- **`K_Threshold_Approach2_Mining.md`** (448 lines)
  - Mining insights from earlier framework development
  - Permutation-based K-threshold formalism
  - Integration with current LRT framework
  - **Status**: Historical reference (approach_2 not used in current LRT)

- **`Non_Unitary_Resolution.md`** (491 lines)
  - Resolving non-unitary evolution in LRT framework
  - Measurement as K-transition mechanism
  - Consistency with quantum mechanics
  - **Status**: Partially addressed by Session 13.0 Measurement_to_K_enforcement derivation

---

## 🧪 predictions/ - Experimental Predictions & Test Designs

**Purpose**: Testable experimental predictions, protocols, and validation reports.

**Latest Status** (Session 12.4): TOP 4 TIER 1 PATHS computationally validated ✅

**Contains**: Multiple folders and tracking documents (see `predictions/README.md` for details)

**Key Documents**:
- **`Prediction_Paths_Master.md`** - Comprehensive tracking of all prediction paths
- **`PREDICTION_PATHS_RANKED.md`** - Ranked list of prediction paths
- **`TOP_4_VV_REPORT.md`** - Validation report for top 4 paths

**Active Prediction Folders** (Session 10-12):
- **Path_1_AC_Stark_Theta/** - AC Stark θ-dependence (HIGH conf, 9σ, 6-12 mo)
- **Path_2_Bell_State_Asymmetry/** - ΔT2/T1 Bell states (HIGH conf, 12σ, FASTEST 1-2 mo)
- **Path_3_Ramsey_Theta_Scan/** - γ(θ) dephasing scan (HIGH conf, 5σ, 6-12 mo)
- **Path_4_Zeno_Crossover_Shift/** - Zeno γ* shift (MEDIUM conf, 1σ, 6-12 mo)

**Historical/Paused Folders**:
- **Path_5_T2-T1/** - Original T2/T1 decoherence asymmetry (Rank 5)
- **Bell_Ceiling-FALSIFIED/** - Bell ceiling prediction (❌ falsified Session 10, see LESSONS_LEARNED_BELL_CEILING.md)
- **QC_Limits/** - Quantum computing limits (⏸️ paused for refinement)
- **Computational_Validation/** - QuTiP simulation work
- **Archive/** - Historical documents

**Status**: TOP 4 paths fully developed (~10,000 lines), computationally validated, ready for experimental testing

---

## ✏️ drafts/ - Work in Progress

**Purpose**: Sections being developed, revision plans, and working analyses.

**Paper Sections**:
- **`section8_draft.md`** (170 lines) - Comparative Analysis
- **`section9_draft.md`** (227 lines) - Objections & Future Work
- **`section10_draft.md`** (132 lines) - Conclusion
- **`FOUNDATIONAL_PAPER_REVISION_PLAN.md`** (496 lines) - Overall revision strategy

**Working Analyses**:
- **`V3_Branch2_Synthesis_Analysis.md`** (386 lines) - Analysis of v3 and Branch-2 papers for synthesis

**Status**: Draft material and working documents

---

## 📚 references/ - Bibliography & Citations

**Purpose**: Citations, bibliography, and reference management.

- **`references.md`** (84 lines) - Markdown reference list
- **`LRT_References.bib`** - BibTeX bibliography

---

## Root-Level Files

**Remaining in `theory/` root**:

- **`Logic_Realism_Theory_Foundational.md`** (106 lines) - Short foundational overview (different from papers/ version)
- **`README.md`** (this file) - Theory folder navigation

**Note**: The **canonical** main paper is in the **root directory** as `Logic_Realism_Theory_Main.md` (not in theory/). The theory/papers/ folder contains historical versions and snapshots.

---

## Navigation Guide

### For Theoretical Work

**If you need:**
- **Current main paper** → `Logic_Realism_Theory_Main.md` (root directory)
- **Variational framework derivations** → `derivations/` folder (Session 13.0 work)
- **Rigorous mathematical formalism** → `frameworks/LRT_Hierarchical_Emergence_Framework.md`
- **Philosophical grounding** → `frameworks/LRT_Philosophical_Foundations.md`
- **Historical paper versions** → `papers/Logic-realism-theory-v3.md` or `papers/Logic-realism-theory-foundational.md`

### For Problem Solving

**If you're working on:**
- **Variational framework derivations** → `derivations/` folder (Session 13.0 - COMPLETE)
- **Energy derivation issues** → RESOLVED: See `derivations/Identity_to_K_ID_Derivation.md`
- **η parameter derivation** → RESOLVED: See `derivations/` folder (98% derived)
- **K-threshold dynamics** → `analysis/K_Threshold_Gap_Analysis.md` (partially addressed by Session 13.0)
- **Measurement/non-unitary** → `analysis/Non_Unitary_Resolution.md` (partially addressed by Session 13.0)

### For Experimental Design

**If you need:**
- **Latest predictions** → `predictions/Prediction_Paths_Master.md` (TOP 4 TIER 1 paths)
- **Individual path protocols** → `predictions/Path_X_*/` folders
- **Bell ceiling lessons** → `predictions/Bell_Ceiling-FALSIFIED/LESSONS_LEARNED_BELL_CEILING.md`

---

## Key Cross-References

**CLAUDE.md** references:
- `theory/frameworks/LRT_Hierarchical_Emergence_Framework.md` as CRITICAL REFERENCE for emergence formalisms
- **Main paper**: `Logic_Realism_Theory_Main.md` (root directory) - Current canonical paper

**Related project areas**:
- **Lean proofs**: `lean/LogicRealismTheory/` - Formal verification (~2,400 lines, ~19 axioms)
- **Notebooks**: `notebooks/` - Computational validation (TOP 4 paths validated)
- **Sprints**: `sprints/` - Development tracking
- **Session logs**: `Session_Log/` - Development history

**Latest Work** (Session 13.0):
- `theory/derivations/` - Variational framework 98% derived (~3,700 lines)

---

## Folder Maintenance

**When adding new documents**:
1. **Papers**: Only add if it's a complete paper manuscript (not sections or drafts)
2. **Frameworks**: Add if it provides reusable formal infrastructure
3. **Derivations**: Add rigorous mathematical derivations from LRT axioms
4. **Analysis**: Add if it's a deep technical investigation of a specific problem (check if resolved by derivations/)
5. **Predictions**: Add to existing predictions/ folder with proper path numbering
6. **Drafts**: Add if it's work-in-progress for a paper section

**When in doubt**: Place in `drafts/` and reorganize later when purpose clarifies.

**Maintenance Notes**:
- As Session 13.0 derivations have resolved many analysis/ issues, consider updating their status sections with resolution notes
- **Audit files should go in root-level `audit/` folder** (not in theory/ subfolders)

---

**Last Updated**: 2025-11-06 (Session 14.0)
**Current Focus**: Repository organization and paper updates following Session 13.0 variational framework derivation
