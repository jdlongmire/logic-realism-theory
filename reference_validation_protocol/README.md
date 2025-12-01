# Reference Validation Protocol

**Version**: 0.2.3
**Purpose**: Systematic verification of bibliographic citations with full audit trail

---

## Overview

This protocol ensures citation accuracy through **two-phase verification** with explicit source hierarchy. It was developed after external review identified citation errors that single-phase validation missed.

**Key Insight**: A paper *existing* does not mean citation details are *correct*. Phase 1 confirms existence; Phase 2 verifies bibliographic accuracy.

---

## Source Hierarchy

| Tier | Sources | Use For |
|------|---------|---------|
| **Tier 1** | DOI resolution, Crossref API, Publisher pages | Bibliographic details (REQUIRED for VERIFIED status) |
| **Tier 2** | PubMed, JSTOR, Library catalogs, Google Scholar (pre-DOI only) | Cross-validation, pre-DOI papers |
| **Tier 3** | arXiv, Web search, Google Scholar | Discovery only, NEVER for bibliographic details |

---

## Verification Workflow

### Step 1: Discovery
- Search for paper by title/authors using tier_3 sources
- Goal: Find the paper and obtain its DOI

### Step 2: DOI Verification
- Run `verify_citation.py` with discovered DOI
- Goal: Get authoritative bibliographic data from Crossref (tier_1)

```bash
python reference_validation_protocol/verify_citation.py <DOI>
```

### Step 2b: Fallback for Pre-DOI Papers
- **Trigger**: Crossref returns no results OR paper is pre-1990
- Use Google Scholar as tier_2 verification source
- Require 2+ independent sources agreeing on bibliographic details
- Result status: `VERIFIED_VIA_SECONDARY`

### Step 3: Comparison
- Compare provided citation against script output
- Goal: Identify discrepancies in journal, volume, year, pages

```bash
python reference_validation_protocol/verify_citation.py --compare "<citation>" <DOI>
```

### Step 4: Page Verification
- Explicitly verify page numbers match
- Catches wrong-paper-same-author errors
- Check: start page, end page, article number vs page confusion

### Step 5: Correction
- If discrepancies found, use script output as corrected citation

```bash
python reference_validation_protocol/verify_citation.py --json <DOI>
```

---

## Red Flags (Automatic Triggers)

| Flag | Meaning |
|------|---------|
| `ARXIV_USED_FOR_JOURNAL` | arXiv used to verify journal name (invalid) |
| `YEAR_MISMATCH_PREPRINT_VS_PUBLICATION` | arXiv date differs from publication date |
| `NO_DOI_FOUND` | Paper has no discoverable DOI |
| `TIER_3_ONLY_VERIFICATION` | Only discovery sources used |
| `PAGE_MISMATCH` | Page numbers don't match authoritative source |
| `WRONG_PAPER_SAME_AUTHORS` | Citing different paper by same authors |

---

## Verification Statuses

| Status | Meaning |
|--------|---------|
| `VERIFIED` | Phase 1 + Phase 2 complete with tier_1 source |
| `VERIFIED_VIA_SECONDARY` | Pre-DOI paper verified via Step 2b |
| `CORRECTED` | Error found and fixed |
| `UNVERIFIED` | Could not verify with authoritative source |
| `WRONG` | Bibliographic details incorrect |

---

## Tools

### verify_citation.py

Queries Crossref API (tier_1 source) for authoritative bibliographic data.

**Usage:**
```bash
# Basic lookup
python reference_validation_protocol/verify_citation.py 10.1103/PhysRevLett.102.020505

# Compare citation against DOI
python reference_validation_protocol/verify_citation.py --compare "McKague QIC 9, 2009" 10.1103/PhysRevLett.102.020505

# JSON output for protocol compliance
python reference_validation_protocol/verify_citation.py --json <DOI>

# Batch mode
python reference_validation_protocol/verify_citation.py --file dois.txt
```

**Output fields**: doi, title, authors, journal, volume, issue, pages, article_number, year, publisher

---

## Folder Structure

```
reference_validation_protocol/
├── README.md                           # This file
├── reference_validation_protocol.json  # Full protocol schema
├── verify_citation.py                  # Crossref API verification script
└── validation_results/
    └── citation_validation_report.md   # Validation reports
```

---

## Lessons Learned (Post-Mortem)

1. **Existence ≠ Accuracy**: A paper existing does not mean citation details are correct
2. **arXiv is not a journal**: arXiv confirms a paper was written, not where it was published
3. **DOI is ground truth**: When available, DOI resolution provides authoritative bibliographic data
4. **Web search confirms titles, not venues**: Search engines find papers but don't verify journal/volume/pages
5. **Page numbers catch errors**: Page mismatches often indicate citing the WRONG paper

---

*Protocol developed 2025-11-30, updated to v0.2.3 2025-12-01*
