# All-Work Survey: Overlooked Nuggets and Ideas

**Date**: 2025-12-02 (Session 36.0)
**Purpose**: Comprehensive survey of past and archived work to identify useful nuggets or ideas that may have been missed
**Scope**: theory/, lean/, notebooks/, approach_2_reference/, archive/

---

## Executive Summary

This survey examined ~392 files across 5 major folders to identify overlooked ideas, abandoned approaches, and resurrection candidates. Key findings:

- **23 high-priority nuggets** identified for potential resurrection
- **3 critical blockers** in Lean formalization (fixable)
- **2 documents incorrectly archived** (should be active)
- **Multiple proof strategies** from earlier work transferable to current framework

---

## Part 1: High-Value Resurrection Candidates

### Priority 1: IMMEDIATE ACTION (Move to Active Work)

| Item | Source | Why Important | Action |
|------|--------|---------------|--------|
| **COMPUTATIONAL_VALIDATION_SPRINT.md** | archive/ | Complete sprint plan for Session 14.0, 5 scripts specified, not superseded | Move to sprints/ |
| **LRT_Current_Comparison_Scorecard.md** | archive/ | Living strategic document, LRT vs 8 theories scoring | Move to theory/ or root |
| **Phase 4 Measurement Mechanism** | derivations/ | Critical gap: mechanism unknown, changes K_enforcement predictions | Prioritize research |

### Priority 2: SHORT-TERM (1-2 Weeks)

| Item | Source | Why Important | Action |
|------|--------|---------------|--------|
| **Time Emergence Universe Fix** | lean/TimeEmergence.lean | 1 sorry, fixable in 20-30 min via axiom refactor | Implement fix |
| **Measurement Structure Import** | approach_2_reference/ | 302 lines of 0-sorry measurement formalization | Port to current lean/ |
| **Born Rule Theorem** | approach_2_reference/ | ~50 lines formal Born rule, non-circular | Port to current lean/ |
| **Energy Derivation Proofs** | lean/Energy.lean | 5 sorry statements, 2-3 hours to complete | Complete proofs |
| **Multi-LLM Quantitative Scoring** | archive/AI_Enabled_*.md | 0-1 scale system documented but not operationalized | Implement as tool |

### Priority 3: MEDIUM-TERM (2-4 Weeks)

| Item | Source | Why Important | Action |
|------|--------|---------------|--------|
| **Consciousness Framework** | theory/archive/LRT_Metaphysical_Architecture.md | Dual-access architecture to 3FLL+IIS, not in papers | Extract for philosophy paper |
| **Fractal Decoherence Mechanism** | theory/frameworks/LRT_Hierarchical_Emergence_Framework.md | Same constraint pattern at every level | Integrate into main paper |
| **Landauer Floor Prediction** | theory/drafts/V3_Branch2_Synthesis_Analysis.md | Alternative falsification route, "collapse calorimetry" | Add to predictions section |
| **State-Dependent K Mapping** | Multiple sources | How does |psi> map to K value? | Research needed |
| **Parallelogram Law Derivation** | theory/derivations/Linearity_Derivation.md | ~85% rigorous, needs strengthening | Complete derivation |

---

## Part 2: Critical Technical Gaps

### Lean Formalization Blockers

| Blocker | File | Severity | Fix Effort | Impact |
|---------|------|----------|------------|--------|
| Universe polymorphism | TimeEmergence.lean:338 | HIGH | 30 min | Unlocks time emergence theorem |
| Existential axioms | Multiple files | MEDIUM | 2-3 hours | Clean proofs |
| Stubs as theorems | DynamicsFromSymmetry.lean | HIGH | 3-4 hours | Honest status |

**Overall Lean Status**:
- Structure: ~85% complete
- Proofs: ~15% complete
- 55 sorry statements across 7 files
- 2 Tier 1 axioms, ~16 Tier 2, 1 Tier 3 (~19 total)

### Derivation Gaps

| Gap | Status | Impact | Resolution Path |
|-----|--------|--------|-----------------|
| **Phase 4 Stabilization** | UNKNOWN | Critical: changes predictions | Formalize 4 candidate mechanisms |
| **Equal Phase Weighting** | ~30% derived | 15% model uncertainty | Symmetry + parsimony arguments |
| **Beta Parameter Origin** | Phenomenological | Final 5% gap | Derive from bath properties |
| **Local Tomography** | Cannot derive | Irreducible axiom | Accept as physical input |

---

## Part 3: Folder-by-Folder Findings

### theory/ (121 files)

**Archive Nuggets**:
- LRT_Metaphysical_Architecture.md: Consciousness framework (dual-access to 3FLL + IIS)
- Temporal emergence from Non-Contradiction constraint
- Parsimony as inference-to-best-explanation (5-step argument)
- Information-action connection: S ~ hbar*K (conjectural)

**Framework Insights Not in Papers**:
- Fractal decoherence mechanism (same pattern at every level)
- Meta-decoherence (Layer 2->3 transition)
- Potentialism reconciliation (eternalism + presentism synthesis)

**Derivation Status**:
- K_ID = 1/beta^2: 95% derived
- K_EM = (ln 2)/beta: 95% derived
- K_enforcement = 4*beta^2: 85% derived (Phase 4 weak)
- N = 4 phases: 95% derived (multiple independent justifications)
- Linearity: 85% derived (parallelogram law needs work)

**Predictions**:
- 4 Tier 1 paths validated and ready (AC Stark, Bell asymmetry, Ramsey, Zeno)
- 1 falsified (Bell ceiling - good lesson)
- QC_Limits paused but concept viable

**Open Issues**:
- ISSUE 005 (Variational Framework): OPEN, needs decision
- ISSUE 006 (Bit as Fundamental): OPEN, underdeveloped in papers

### lean/ (28 files)

**Orphaned Files** (not imported):
- GeometricStructure.lean (220 lines)
- EMRelaxation.lean (297 lines)
- VectorSpaceStructure.lean (352 lines)

**Completed Modules** (0 axioms, 0 sorry):
- Actualization.lean: A = L(I) proven
- RussellParadox.lean: Paradox resolution
- ConstraintThreshold.lean: StateSpace monotonicity

**High-Impact Quick Wins**:
1. Fix TimeEmergence.lean (30 min): Refactor stones_theorem axiom
2. Complete NonUnitaryEvolution.lean (1.5-2 hrs): 6 sorry, straightforward
3. Complete Energy.lean (2-3 hrs): 5 sorry, uses Tier 2 axioms

### notebooks/ (31 files)

**Completed & Validated**:
- 4 executed root notebooks (01-04)
- 8 Logic_Realism/ QuTiP notebooks
- 2 analysis modules (ramsey_theta, zeno_crossover)

**Incomplete**:
- 05_Distinguishability_Emergence.ipynb (structure only)
- 08_Complex_Field_Necessity.ipynb (minimal)
- 09_Layer3_Quantum_Structure.ipynb (skeleton)

**Key Computational Results**:
- beta* = 3/4 (variational optimization)
- eta ~ 0.232 (excluded-middle coupling)
- T2/T1 ~ 0.81 prediction
- Ramsey theta-scan: 13.7% effect at 90 degrees
- Zeno crossover: 15.9% shift at 90 degrees

**Hardware Testing** (quantum_simulations/):
- Phase 1-2 complete, Phase 3 ready
- Duration-matching fix available (corrected_simulation.py)
- IBM Quantum integration ready

### approach_2_reference/ (202 files)

**Transferable Proofs** (0 sorry):
- MeasurementMechanism.lean: 302 lines
- Born rule from measurement: ~50 lines
- K=0 classical emergence: ~20 lines
- ConstraintAccumulation.lean: 821 lines

**Key Insights**:
- Triple proof convergence: K(N)=N-2 proven three independent ways
- Zero-sorry production code template
- 140 -> 5 axiom reduction lessons

**What NOT to Transfer**:
- Permutohedron geometry (discrete-specific)
- Mahonian symmetry proofs (combinatorial)
- Full S_N validation (already done)

### archive/ (Root)

**Incorrectly Archived** (should be active):
- COMPUTATIONAL_VALIDATION_SPRINT.md: Active sprint plan
- LRT_Current_Comparison_Scorecard.md: Living strategy document

**Valuable Templates**:
- Multi-LLM quantitative scoring (0-1 scale)
- Program Auditor automation (grep verification)
- Pre-commit tone checklist
- Beta phenomenological caveat framework

---

## Part 4: Abandoned Ideas Worth Reconsidering

### From Branch-2 Synthesis (V3_Branch2_Synthesis_Analysis.md)

| Idea | Current Status | Value |
|------|----------------|-------|
| Energy as "work of instantiation" | Not integrated | Intuitive framing |
| Landauer floor prediction | Not in papers | Alternative falsifier |
| "Collapse calorimetry" experiment | Not developed | Novel test |
| Time as sequential A-states | Partial | Clearer than Fisher approach |

### From Earlier Frameworks

| Idea | Source | Why Abandoned | Reconsider? |
|------|--------|---------------|-------------|
| 4-paper structure | theory/archive/ | Unwieldy | NO - 3 papers better |
| Phenomenological eta | Multiple | Wanted first-principles | RESOLVED via variational |
| QC Limits predictions | predictions/QC_Limits/ | Off by 15 orders | YES - with refinement |

---

## Part 5: Action Items

### Immediate (This Session)

1. [ ] Move COMPUTATIONAL_VALIDATION_SPRINT.md to sprints/
2. [ ] Move LRT_Current_Comparison_Scorecard.md to theory/
3. [ ] Document this survey findings in session log

### Short-Term (Next 1-2 Sessions)

1. [ ] Fix TimeEmergence.lean universe polymorphism (30 min)
2. [ ] Import measurement structure from approach_2 (1-2 hrs)
3. [ ] Complete NonUnitaryEvolution.lean proofs (1.5-2 hrs)
4. [ ] Execute Path3_T1_vs_T2_QuTiP_Validation.ipynb (15 min)
5. [ ] Decide on ISSUE 005 (Variational Framework): archive or develop?

### Medium-Term (Next 2-4 Sessions)

1. [ ] Complete Energy.lean derivation proofs
2. [ ] Strengthen Linearity_Derivation.md parallelogram argument
3. [ ] Research Phase 4 stabilization mechanism
4. [ ] Extract consciousness framework for philosophy paper
5. [ ] Integrate fractal decoherence into main paper

### Research Questions Identified

1. **Phase 4 mechanism**: What physical process? (Zeno? Information spreading? Heat flow?)
2. **State-dependent K**: How does |psi> map to K value for qubits?
3. **Beta origin**: Can beta be derived from bath properties + IIS structure?
4. **K(d) generalization**: How does K(N)=N-2 extend to continuous Hilbert spaces?

---

## Part 6: Summary Statistics

| Category | Files Surveyed | Key Nuggets | Action Items |
|----------|---------------|-------------|--------------|
| theory/ | 121 | 12 | 8 |
| lean/ | 28 | 5 | 6 |
| notebooks/ | 31 | 4 | 4 |
| approach_2_reference/ | 202 | 4 | 3 |
| archive/ | 10 | 6 | 3 |
| **Total** | **392** | **31** | **24** |

---

## Appendix: File Locations for Key Nuggets

### Consciousness Framework
- `theory/archive/LRT_Metaphysical_Architecture.md` Section 5

### Fractal Decoherence
- `theory/frameworks/LRT_Hierarchical_Emergence_Framework.md`

### Measurement Formalization
- `approach_2_reference/lean/LogicField/QuantumEmergence/MeasurementMechanism.lean`

### Constraint Accumulation
- `approach_2_reference/lean/LogicField/ConstraintAccumulation.lean` (821 lines, 0 sorry)

### Validation Sprint
- `archive/COMPUTATIONAL_VALIDATION_SPRINT.md` (should be in sprints/)

### Comparison Scorecard
- `archive/LRT_Current_Comparison_Scorecard.md` (should be active)

### Branch-2 Ideas
- `theory/drafts/V3_Branch2_Synthesis_Analysis.md`

---

*Survey completed Session 36.0. Total time: ~3 hours across 6 sprints.*
