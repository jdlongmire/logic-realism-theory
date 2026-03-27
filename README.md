# Logic Realism Theory (LRT)

**Physical Foundations from Logical Constraints**

---

## Core Thesis

Three primitives are jointly necessary and sufficient for the constitution of reality:

| Primitive | Role |
|-----------|------|
| **L₃** | Prescriptive logical constraint (identity, non-contradiction, excluded middle) |
| **I∞** | Total informational possibility space |
| **A** | Actualization — marks configurations as obtaining |

These primitives form a co-constitutive unity:

$$\chi \equiv [L_3 : I_\infty : A]$$

Their interaction yields the **Bridge Identity**:

$$A_\Omega = L_3(I_\infty)$$

Actuality coincides with the logically admissible informational configurations of the total possibility space.

**Reconstruction Chain:**
```
χ → A_Ω → Determinate Identity → Local Tomography → ℂℋ → PVM → Born Rule → UNS → t → Schrödinger
```

---

## Repository Structure

```
logic-realism-theory/
├── theory/                 # Active theory documents (001-003, 400, 500)
├── formalization/          # Lean 4 formalization (Steps 0-10)
├── docs/                   # Consolidated documentation
│   ├── formalization/      # Lean research and axiom audits
│   ├── traceability/       # Claim tracking reports
│   ├── papers/             # Technical papers
│   └── articles/           # Expository content
├── traceability/           # Claim-control infrastructure
├── archive/                # All deprecated/historical content
└── scripts/                # Build and utility scripts
```

---

## Formalization Status (2026-03-27)

| Metric | Value |
|--------|-------|
| **Build** | ✅ SUCCESS |
| **Total Axioms** | 19 |
| **PRIMITIVE** | 3 (I∞, I_infinite, bridge_principle) |
| **EXTERNAL** | 16 (established math: Gleason, Stone, Hardy, CDP, No-Hiding, etc.) |
| **REMAINING** | 0 |
| **Sorries** | 3 (technical, not conceptual) |

See [docs/formalization/axiom-status.md](docs/formalization/axiom-status.md) for current axiom classification.

---

## Key Documents

### Theory

| Document | Description |
|----------|-------------|
| [001-LRT-TAB-PHILOSOPHY.md](theory/001-LRT-TAB-PHILOSOPHY.md) | Transcendental Argument for Being: metaphysical groundwork |
| [002-LRT-CORE-PHYSICS.md](theory/002-LRT-CORE-PHYSICS.md) | Canonical unified source: complete 14-step derivation (Steps 0-14) |

### Formalization

| Document | Description |
|----------|-------------|
| [400-LRT-FORMALIZATION.md](theory/400-LRT-FORMALIZATION.md) | Complete formalization reference (static) |
| [500-LRT-FORMALIZATION-STATUS.md](theory/500-LRT-FORMALIZATION-STATUS.md) | Current formalization status (living doc) |

### Published (Zenodo)

| Paper | DOI |
|-------|-----|
| [Position Paper](theory/20260109_Logic_Realism_Theory_Position_Paper.md) | [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18202130.svg)](https://doi.org/10.5281/zenodo.18202130) |
| [Philosophical Foundations](theory/20260109_Logic_Realism_Theory_Philosophical_Foundations.md) | [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.14581992.svg)](https://doi.org/10.5281/zenodo.14581992) |
| [It From Bit, Bit From Fit](theory/20260109_It_From_Bit_Bit_From_Fit.md) | [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17831883.svg)](https://doi.org/10.5281/zenodo.17831883) |

---

## Building the Formalization

```bash
cd formalization
./scripts/build.sh    # Fetches Mathlib cache, then builds (~2 min)
```

Or manually:
```bash
source ~/.elan/env && lake exe cache get && lake build
```

---

## Author

**James (JD) Longmire**
ORCID: [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)
Contact: jdlongmire@outlook.com

---

## Citation

```bibtex
@misc{longmire2026lrt,
  author = {Longmire, James},
  title = {Logic Realism Theory: Physical Foundations from Logical Constraints},
  year = {2026},
  publisher = {Zenodo},
  doi = {10.5281/zenodo.18202130}
}
```

---

## License

[![CC BY 4.0](https://licensebuttons.net/l/by/4.0/88x31.png)](https://creativecommons.org/licenses/by/4.0/)

This work is licensed under [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/).

---

*Human-Curated, AI-Enabled (HCAE)*

**Last Updated**: 2026-03-27
