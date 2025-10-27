# Logic Realism Theory - Computational Notebooks

**Copyright © 2025 James D. (JD) Longmire**
**License**: Apache License 2.0

This folder contains the computational validation suite for Logic Realism Theory (LRT).

---

## Active Notebooks

### Path 3: T1 vs T2 QuTiP Validation (Primary)

**[`Path3_T1_vs_T2_QuTiP_Validation.ipynb`](Path3_T1_vs_T2_QuTiP_Validation.ipynb)** - QuTiP simulation validation of Path 3 protocol
- **Purpose**: Validate experimental protocol for detecting T2/T1 ≈ 0.7-0.9 (superposition decoherence)
- **Status**: Complete (Session 3.6)
- **Key Results**:
  - LRT effect (T2/T1 = 0.8) detectable at >4σ significance
  - 40,000 shots per point provides 97% statistical power
  - Fitting accuracy ~1-2% matches error budget predictions
- **Protocol**: [`../theory/predictions/T1_vs_T2_Protocol.md`](../theory/predictions/T1_vs_T2_Protocol.md)
- **Error Budget**: [`../theory/predictions/T1_vs_T2_Error_Budget.md`](../theory/predictions/T1_vs_T2_Error_Budget.md)

---

## Planned Notebooks (9 Total - In Development)

### Foundation (01-02)
- **01_IIS_and_3FLL.ipynb** - Infinite Information Space and Three Fundamental Laws
- **02_Operator_Formalism.ipynb** - Π_id, {Π_i}, R operators

### Derivations (03-07)
- **03_Time_Emergence.ipynb** - Time from Stone's theorem
- **04_Energy_Constraint.ipynb** - Energy from Spohn's inequality
- **05_Born_Rule.ipynb** - Born rule from maximum entropy
- **06_Quantum_Superposition.ipynb** - Partial constraint → superposition
- **07_Measurement_Problem.ipynb** - Full constraint → classical state

### Predictions & Bridge (08-09)
- **08_Beta_Prediction.ipynb** - β ≠ 0 in quantum error correction
- **09_SN_Realization.ipynb** - Bridge to Approach 2 (S_N hierarchy)

**Note**: These notebooks (01-09) are planned for future development. Current focus is on Path 3 experimental protocol validation.

---

## Reference: Approach 2 Archive

**Approach 2** (Physical Logic Framework): 25 notebooks, ~80,000 words
- Comprehensive computational exploration
- All notebooks archived in [`../approach_2_reference/notebooks/`](../approach_2_reference/notebooks/)

**Logic Realism Theory** (this folder): Focused on core derivations and experimental validation
- References Approach 2 for computational validation
- Professional scholarly tone throughout
- Current focus: Path 3 T1 vs T2 protocol

---

## Copyright Format (3 Lines)

All notebooks must use this exact format:

```markdown
**Copyright © 2025 James D. (JD) Longmire**
**License**: Apache License 2.0
**Citation**: Longmire, J.D. (2025). *Logic Realism Theory: Deriving Quantum Mechanics from Logical Consistency*. Logic Realism Theory Repository.
```

---

## Professional Tone Guidelines

**DO**:
- Present correct approach directly
- Use scholarly, professional language
- Explain reasoning clearly
- Reference Approach 2 results where applicable

**DO NOT**:
- Include thinking commentary ("Wait, that doesn't seem right...")
- Include self-corrections ("Let me recalculate...", "Actually, this is wrong...")
- Use stream-of-consciousness style

---

## Installation

```bash
pip install -r requirements.txt
```

**Key Dependencies**:
- `qutip` - Quantum Toolbox in Python (for Path 3 simulation)
- `numpy`, `matplotlib`, `scipy` - Numerical computation and visualization
- `jupyter` - Notebook environment

---

## Usage

```bash
jupyter notebook
```

Navigate to desired notebook and execute cells sequentially.

**Recommended Start**: `Path3_T1_vs_T2_QuTiP_Validation.ipynb` (primary experimental validation)

---

## Outputs

Generated figures and data are saved to `outputs/` (gitignored except .gitkeep).

**Path 3 Simulation Outputs**:
- `Path3_QuTiP_Validation_Summary.png` - 4-panel validation summary
- Various intermediate plots (T1 decay, T2 Ramsey, power analysis)

---

## Latest Work

**Session 3.6** (October 27, 2025):
- Created [`Path3_T1_vs_T2_QuTiP_Validation.ipynb`](Path3_T1_vs_T2_QuTiP_Validation.ipynb)
- Validated Path 3 protocol with realistic noise models
- Confirmed >95% statistical power with 40,000 shots
- See [`../Session_Log/Session_3.6.md`](../Session_Log/Session_3.6.md) for details

---

## Related Documentation

- **Theory**: [`../theory/Logic-realism-theory-foundational.md`](../theory/Logic-realism-theory-foundational.md)
- **Protocols**: [`../theory/predictions/`](../theory/predictions/)
- **Session History**: [`../Session_Log/`](../Session_Log/)
- **Approach 2 Archive**: [`../approach_2_reference/notebooks/`](../approach_2_reference/notebooks/)
