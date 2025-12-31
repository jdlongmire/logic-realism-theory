# Logic Realism Theory (LRT)

**Determinate Identity as Ontological Constraint on Physical Reality**

---

## Author

**James D. (JD) Longmire**
- Email: jdlongmire@outlook.com
- ORCID: [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)

**License**: Apache 2.0

---

## Core Paper

**[Logic Realism and the Born Rule: Determinate Identity as Ontological Constraint on Physical Reality](theory/20251231_Logic_Realism_Theory__working_paper.md)**

The central document of this repository. It derives the Born rule and complex Hilbert space from the classical laws of logic (L₃) understood as ontological constraints on physical instantiation.

### Key Results

| Result | Status | Location |
|--------|--------|----------|
| **Born rule derived** | Complete | §4, Appendix A |
| **Complex Hilbert space forced** | Complete | Appendix B (via Masanes-Müller) |
| **Bell correlations reinterpreted** | Complete | §4.5, Appendix C |
| **Local tomography forced** | Complete | Appendix D.5 |
| **Vehicle trilemma for rivals** | Complete | §4.6 |

### Derivation Chain (Revised)

The derivation requires **L₃ alone**—no empirical supplementation, no bridging principles.

```
L₃ (Determinate Identity, Non-Contradiction, Excluded Middle)
    ↓ [Theorem D.1: global holism ruled out]
    ↓ [Section 2.3: parts ground wholes]
Local Self-Sufficiency — theorem from L₁
    ↓ [Theorem B.7: CDP as theorem]
Local Tomography — consequence
    ↓ [Theorem B.9: grounds Masanes-Müller axioms]
Complex Hilbert Space — unique arena
    ↓ [Vehicle-weight invariance from L₁]
Born Rule — unique measure (Gleason/Busch)
```

**Key revision**: CDP and M₁ are now consequences of L₁, not separate inputs. The chain is as tight as the mathematics permits.

### Falsification Criteria (§6.1)

The framework makes severe negative predictions:

1. **No persistent macroscopic superposition** after identity engagement
2. **No macro-branch interference** between distinct outcome histories
3. **No numerical identity through singularity** (information ≠ identity)
4. **No sub-Planck individuation**
5. **No instantiated actual infinity**

If any are overturned, the hard core is refuted. The theory is willing to die.

---

## Core Thesis

The Three Fundamental Logical Laws (L₃)—Determinate Identity, Non-Contradiction, Excluded Middle—are not merely rules of reasoning but **ontological constraints constitutive of physical reality**.

Physical reality is not a neutral arena onto which logic is later imposed. It is constituted such that only configurations satisfying L₃ can be instantiated at all. A configuration without determinate identity is not a borderline entity; it is nothing.

**Vehicle/Content Distinction**: A quantum state is a physical vehicle (determinate configuration) representing admissible outcome-histories (content). The Born measure characterizes the vehicle's objective disposition toward outcomes. Determinate Identity constrains this measure to be basis-independent, forcing the Born rule via Gleason's theorem.

---

## Methodology

**Lakatosian Structure**: Hard core (L₃ as ontological constraint, strict trans-temporal identity) + protective belt (metric details, decoherence mechanisms). The programme is progressive: it unifies disparate phenomena under a single constraint while exposing itself to severe risk.

**Popperian Nerve**: The falsification criteria (§6.1) are not hedged. Each strikes directly at the hard core.

---

## Repository Structure

```
theory/
├── 20251231_Logic_Realism_Theory__working_paper.md  # CORE PAPER
├── 20251230-LRT-Refactor.md         # Refactor reasoning (CDP elimination)
├── LRT_Extended/                    # Development versions (v5-v8)
├── supplementary/                   # Working papers
└── archive/                         # Historical papers

lean/                                # Lean 4 formalization
├── LogicRealismTheory/
│   └── Derivations/
│       ├── D0_1_ThreeFundamentalLaws.lean  ✓
│       └── D0_2_InformationSpace.lean      ✓

notebooks/                           # Derivation notebooks (Stage 1)
├── D0.1-three-fundamental-laws.ipynb  ✓
├── D0.2-information-space.ipynb       ✓
└── D0.3-co-fundamentality.ipynb       Pending

Session_Log/                         # Development history (50+ sessions)
```

---

## Appendix Structure (Core Paper)

| Appendix | Content | Status |
|----------|---------|--------|
| **A** | Formal proof: Determinate Identity → Born rule via Gleason | Complete |
| **B** | Complex Hilbert space forced via L₃ + Masanes-Müller | Complete |
| **C** | Bell non-locality as global identity constraint | Complete |
| **D** | Formal derivation chain (D.1–D.7) | Complete |
| **E** | QFT Extension (Programmatic) | Research direction |
| **F** | GR Extension (Programmatic) | Research direction |
| **G** | Cosmological Implications (Programmatic) | Research direction |

### Appendix D Theorems (Revised)

- **D.1**: Intrinsic identity forced; global holism ruled out
- **D.2**: Macroscopic self-sufficiency as consequence of L₁
- **D.3**: Tightened derivation chain (L₃ alone)
- **D.4**: Vehicle-weight invariance → Born rule
- **D.5**: Local tomography forced (reductio)
- **D.6**: Incompleteness and pre-mathematical priority of L₃
- **D.7**: Summary

### Programmatic Appendices (E–G)

- **E**: QFT — Fock space, vacuum uniqueness, renormalization as L₃-admissibility
- **F**: GR — Time as logical sequencing, Lorentzian signature, CTC exclusion
- **G**: Cosmology — Ontological expansion, flexible determinism, Λ > 0 conjecture

---

## Published Pre-Prints (Historical)

Papers published on Zenodo (December 2025):

| Paper | DOI |
|-------|-----|
| [It from Bit, Bit from Fit](https://doi.org/10.5281/zenodo.17831819) | 10.5281/zenodo.17831819 |
| [Technical Foundations](https://doi.org/10.5281/zenodo.17831883) | 10.5281/zenodo.17831883 |
| [Philosophical Foundations](https://doi.org/10.5281/zenodo.17831912) | 10.5281/zenodo.17831912 |

These represent earlier formulations. The core paper supersedes them for the Born rule derivation.

---

## Citation

```bibtex
@misc{longmire2025lrt_born,
  author = {Longmire, James D.},
  title = {Logic Realism and the Born Rule: Determinate Identity as Ontological Constraint on Physical Reality},
  year = {2025},
  note = {Working paper},
  url = {https://github.com/jdlongmire/logic-realism-theory}
}
```

---

## Disclaimer

Logic Realism Theory is a proposed theoretical framework. All claims require scrutiny. The framework is explicitly falsifiable (§6.1). Scientific judgments remain the author's responsibility.

*Human-curated, AI-enabled.*
