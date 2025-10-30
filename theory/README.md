# Theory Folder

This folder contains all theoretical documents for Logic Realism Theory (LRT), organized by document type and purpose.

---

## Folder Structure

```
theory/
├── papers/          # Main canonical papers
├── frameworks/      # Core theoretical frameworks
├── analysis/        # Technical analyses & problem solving
├── predictions/     # Experimental predictions & test designs
├── drafts/          # Work in progress sections & revisions
└── references/      # Bibliography & citations
```

---

## 📄 papers/ - Main Canonical Papers

**Purpose**: Primary scholarly papers representing the canonical statements of LRT.

### Active Papers

- **`Logic-realism-theory-v3.md`** (1,986 lines) ⚠️ **PRIMARY WORKING PAPER**
  - Clean slate rewrite with standard physics paper structure
  - Complete 10-section manuscript
  - Includes η ≈ 0.23 (T2/T1 ≈ 0.81) hypothesis from variational optimization
  - Formal verification documentation (~2,400 lines Lean 4)
  - Target: Peer-review ready manuscript
  - **Status**: Work in progress (Session 4.0+, updated Sprint 8 with variational derivation)

- **`Logic_Realism_Theory_Branch-2.md`** (390 lines) 🔄 **TO SYNTHESIZE WITH V3**
  - Alternative philosophical approach
  - Focuses on energy as "work of instantiation" (Landauer)
  - Emphasizes quantum measurement problem resolution
  - Simpler presentation, more accessible
  - **Status**: To be synthesized with v3

### Historical Reference

- **`Logic-realism-theory-foundational.md`** (1,401 lines)
  - Original foundational paper (replaced by v3)
  - Source material for content extraction during rewrites
  - Contains existing derivations, philosophical arguments, experimental protocols
  - **Status**: Historical reference only, being replaced by v3

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

## 🔬 analysis/ - Technical Analyses & Problem Solving

**Purpose**: Deep technical investigations of specific derivation challenges and open problems.

- **`Energy_Circularity_Analysis.md`** (344 lines)
  - Identifies circularity in energy derivation via Spohn's inequality
  - Problem: Spohn presupposes energy, temperature
  - Status: Problem identified, solutions in development (Sprint 5)

- **`Eta_Parameter_Analysis.md`** (383 lines)
  - Analysis of η (Excluded Middle coupling strength) parameter
  - Derivation approaches: Fisher information, constraint threshold dynamics
  - **Status**: Resolved in Sprint 7 via variational optimization (β = 3/4 → η ≈ 0.23)
  - See: Notebook 07_Variational_Beta_Derivation.ipynb for implementation

- **`K_Threshold_Gap_Analysis.md`** (525 lines)
  - Analysis of K-threshold dynamics (constraint count transitions)
  - Quantum (fixed K) vs non-unitary (measurement, K → K-ΔK) regimes
  - Gap identification and resolution strategies

- **`K_Threshold_Approach2_Mining.md`** (448 lines)
  - Mining insights from earlier framework development
  - Permutation-based K-threshold formalism
  - Integration with current LRT framework

- **`Non_Unitary_Resolution.md`** (491 lines)
  - Resolving non-unitary evolution in LRT framework
  - Measurement as K-transition mechanism
  - Consistency with quantum mechanics

---

## 🧪 predictions/ - Experimental Predictions & Test Designs

**Purpose**: Testable experimental predictions, protocols, and validation reports.

**Contains**: 17 documents (see `predictions/README.md` for details)

**Key documents**:
- `Prediction_Paths_Master.md` - Overall prediction strategy
- `Quantitative_Predictions_Derivation.md` - First-principles derivations
- `T1_vs_T2_Protocol.md` - Primary decoherence asymmetry test
- `Hardware_Test_Report.md` - IBM Q hardware validation
- `Phase_2_Validation_Report.md`, `Phase_3_Results_Report.md` - Simulation validation

---

## ✏️ drafts/ - Work in Progress

**Purpose**: Sections being developed for v3 paper and revision plans.

- **`section8_draft.md`** (170 lines) - Comparative Analysis (for v3)
- **`section9_draft.md`** (227 lines) - Objections & Future Work (for v3)
- **`section10_draft.md`** (132 lines) - Conclusion (for v3)
- **`FOUNDATIONAL_PAPER_REVISION_PLAN.md`** (496 lines) - Overall revision strategy

**Status**: Draft material to be integrated into v3 as sections mature

---

## 📚 references/ - Bibliography & Citations

**Purpose**: Citations, bibliography, and reference management.

- **`references.md`** (84 lines) - Markdown reference list
- **`LRT_References.bib`** - BibTeX bibliography

---

## Navigation Guide

### For Theoretical Work

**If you need:**
- **Primary working paper** → `papers/Logic-realism-theory-v3.md`
- **Rigorous mathematical formalism** → `frameworks/LRT_Hierarchical_Emergence_Framework.md`
- **Philosophical grounding** → `frameworks/LRT_Philosophical_Foundations.md`
- **Content from old paper** → `papers/Logic-realism-theory-foundational.md`

### For Problem Solving

**If you're working on:**
- **Energy derivation issues** → `analysis/Energy_Circularity_Analysis.md`
- **η parameter derivation** → `analysis/Eta_Parameter_Analysis.md`
- **K-threshold dynamics** → `analysis/K_Threshold_Gap_Analysis.md` or `K_Threshold_Approach2_Mining.md`
- **Measurement/non-unitary** → `analysis/Non_Unitary_Resolution.md`

### For Experimental Design

**If you need:**
- **Test protocols** → `predictions/` folder
- **Simulation validation** → `predictions/Phase_2_Validation_Report.md`, `Phase_3_Results_Report.md`
- **Hardware testing** → `predictions/Hardware_Test_Report.md`

---

## Key Cross-References

**CLAUDE.md** references:
- `theory/LRT_Hierarchical_Emergence_Framework.md` as CRITICAL REFERENCE for emergence formalisms
- `theory/Logic-realism-theory-foundational.md` as source material (being replaced)
- `theory/Logic-realism-theory-v3.md` as primary working paper (Session 4.0+)

**Related project areas**:
- **Lean proofs**: `lean/LogicRealismTheory/` - Formal verification (~2,400 lines)
- **Notebooks**: `notebooks/` - Computational validation
- **Sprints**: `sprints/` - Development tracking

---

## Synthesis Task (Next Priority)

**v3 + Branch-2 Synthesis**:
- Branch-2 offers complementary framing (energy as work of instantiation, simpler measurement resolution)
- v3 offers complete formal structure with predictions
- **Goal**: Integrate Branch-2's accessible framing into v3 where appropriate
- **Approach**: Extract key insights from Branch-2 (Landauer connection, measurement clarity) and enhance v3 sections

See synthesis analysis document (to be created) for detailed integration plan.

---

## Folder Maintenance

**When adding new documents**:
1. **Papers**: Only add if it's a complete paper manuscript (not sections or drafts)
2. **Frameworks**: Add if it provides reusable formal infrastructure
3. **Analysis**: Add if it's a deep technical investigation of a specific problem
4. **Predictions**: Add to existing predictions/ folder
5. **Drafts**: Add if it's work-in-progress for a paper section

**When in doubt**: Place in `drafts/` and reorganize later when purpose clarifies.
