# Session 37.0 - DOI Updates, Reference Validation, PDF Regeneration

**Date**: 2025-12-05
**Focus**: Zenodo v2 DOI updates, reference validation, PDF regeneration
**Status**: COMPLETE

---

## Session Summary

Updated all papers with new v2 Zenodo DOIs, ran reference validation protocol, fixed missing DOIs in Philosophy paper, regenerated all PDFs with Cambria font (Unicode fix), and created Reddit introduction post.

---

## Work Completed

### 1. File Renaming
- Renamed Saturated Entanglement files with `LRT_` prefix:
  - `theory/LRT_Saturated_Entanglement_Interface_Criterion.md`
  - `theory/001_pdfs/LRT_Saturated_Entanglement_Interface_Criterion.pdf`

### 2. Zenodo DOI Updates (v2)

All papers now have v2 DOIs:

| Paper | DOI |
|-------|-----|
| Main | 10.5281/zenodo.17831819 |
| Technical | 10.5281/zenodo.17831883 |
| Philosophy | 10.5281/zenodo.17831912 |
| QFT Extension | 10.5281/zenodo.17831926 |
| Saturated Entanglement | 10.5281/zenodo.17831946 |

- Updated `theory/Zenodo_submission.md` with all new DOIs
- Updated cross-references in all papers to point to v2 DOIs

### 3. Reference Validation Protocol

Ran validation against all 5 theory root papers:
- **Total citations:** 75 unique across all papers
- **DOIs verified:** 27 via Crossref API (tier-1)
- **Without DOIs:** 48 (books, pre-DOI papers) - appropriately lack DOIs
- **Corrections needed:** 3 missing DOIs in Philosophy paper

**Fixed in Philosophy paper:**
- French & Ladyman 2003: `10.1023/A:1024156116636`
- Ladyman 1998: `10.1016/S0039-3681(98)80129-5`
- Maudlin 1995: `10.1007/BF00763473`

**Final status:** All 5 papers PASS reference validation

### 4. PDF Regeneration (v2.10)

All papers updated to v2.10 and PDFs regenerated with Cambria font (fixes Unicode math symbols):

| Paper | Size |
|-------|------|
| Main-v2 | 4.7 MB |
| Technical-v2 | 162 KB |
| Philosophy-v2 | 103 KB |
| QFT Extension-v2 | 174 KB |
| Saturated Entanglement | 78 KB |

### 5. Keywords Development

Created unified keyword set for all papers:
```
quantum foundations; logic realism; Born rule; measurement problem;
reconstruction theorems; complex Hilbert space; falsifiability;
distinguishability; structural realism; decoherence; Three Fundamental Laws of Logic
```

### 6. Reddit Post

Created `theory/reddit_post.md` with introduction to LRT and recommended reading order:
1. Main Paper - https://zenodo.org/records/17831819
2. Philosophy Paper - https://zenodo.org/records/17831912
3. Technical Paper - https://zenodo.org/records/17831883
4. QFT Extension - https://zenodo.org/records/17831926
5. Interface Criterion - https://zenodo.org/records/17831946

---

## Commits This Session

| Commit | Description |
|--------|-------------|
| `0194487` | Add LRT_ prefix to Saturated Entanglement files |
| `6dfc260` | Update Zenodo submission file for v2 papers |
| `11ce183` | Regenerate Main v2 PDF with interface hypothesis |
| `f84c7a0` | Regenerate Main v2 PDF with Cambria font (Unicode fix) |
| `edeedf8` | Regenerate all v2 PDFs with Cambria font |
| `a56f87e` | Update Main DOI cross-references to v2 |
| `896cabe` | Update all DOIs to v2 versions |
| `bccb5ba` | Add 3 missing DOIs to Philosophy paper |
| `ced43cb` | Update all papers to v2.10, regenerate all PDFs |

---

## Final Paper Status

| Paper | Version | DOI | Status |
|-------|---------|-----|--------|
| Main | v2.10 | 10.5281/zenodo.17831819 | Published |
| Technical | v2.10 | 10.5281/zenodo.17831883 | Published |
| Philosophy | v2.10 | 10.5281/zenodo.17831912 | Published |
| QFT Extension | v2.10 | 10.5281/zenodo.17831926 | Published |
| Saturated Entanglement | v2.10 | 10.5281/zenodo.17831946 | Published |

---

## Interaction Count: 16

