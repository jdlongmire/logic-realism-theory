# Zenodo Pre-print Submission Guide

**Author**: James D. Longmire
**ORCID**: 0009-0009-1383-7698
**Contact**: jdlongmire@outlook.com

---

## DOI Reservation Strategy

Zenodo assigns DOIs when drafts are created, not when published. This solves the cross-reference chicken-egg problem.

### Workflow

```
1. Create DRAFT for each paper → Reserved DOI assigned
2. Note all reserved DOIs
3. Update cross-references in all papers with actual DOIs
4. Re-upload final PDFs to drafts
5. Publish all simultaneously
```

---

## Papers and Reserved DOIs

| Paper | File | Reserved DOI | Status |
|-------|------|--------------|--------|
| Main | Logic_Realism_Theory_Main.md | TBD | Draft pending |
| Technical | Logic_Realism_Theory_Technical.md | TBD | Draft pending |
| Philosophy | Logic_Realism_Theory_Philosophy.md | TBD | Draft pending |
| QFT Extension | Logic_Realism_Theory_QFT_Gravity_Extension.md | TBD | Draft pending |

**Update this table as DOIs are reserved.**

---

## Release Phases

### Phase 1: Core Package (simultaneous)
- Main
- Technical
- Philosophy

### Phase 2: Extension (2-4 weeks after Phase 1)
- QFT Extension

---

## Metadata Template

Use this for each Zenodo upload:

### Common Fields (all papers)

| Field | Value |
|-------|-------|
| **Upload type** | Publication |
| **Publication type** | Preprint |
| **Authors** | Longmire, James D. (ORCID: 0009-0009-1383-7698) |
| **License** | Creative Commons Attribution 4.0 International (CC-BY-4.0) |
| **Access** | Open Access |
| **Language** | English |

### Paper-Specific Metadata

#### Main Paper

| Field | Value |
|-------|-------|
| **Title** | It from Bit, Bit from Fit: Logic Realism Theory |
| **Description** | Logic Realism Theory (LRT) proposes that the Three Fundamental Laws of Logic—Identity, Non-Contradiction, and Excluded Middle—are ontological constraints constitutive of physical reality, not merely rules of reasoning. This paper derives the core structures of quantum mechanics (complex Hilbert space, Born rule, unitary dynamics) from these logical constraints via the Continuous Bit Principle. |
| **Keywords** | quantum foundations; logic realism; Born rule; measurement problem; quantum interpretation; Gleason's theorem; information physics |
| **Subjects** | Physics > Quantum Physics |
| **Related identifiers** | (Add DOIs for Technical, Philosophy papers once reserved) |

#### Technical Paper

| Field | Value |
|-------|-------|
| **Title** | Logic Realism Theory: Technical Foundations |
| **Description** | Rigorous mathematical foundations for Logic Realism Theory, including formal definitions, theorem statements, and detailed proofs. Provides the technical backing for claims made in the main paper. |
| **Keywords** | quantum foundations; mathematical physics; Hilbert space; operator theory; Gleason's theorem; quantum logic |
| **Subjects** | Physics > Mathematical Physics |
| **Related identifiers** | (Add DOIs for Main, Philosophy papers once reserved) |

#### Philosophy Paper

| Field | Value |
|-------|-------|
| **Title** | Logic Realism Theory: Philosophical Foundations |
| **Description** | Philosophical analysis of Logic Realism Theory's ontological claims. Examines the status of logical laws as constitutive constraints, addresses objections from conventionalism and pluralism, and situates LRT within the landscape of quantum interpretations. |
| **Keywords** | philosophy of physics; quantum foundations; logical realism; ontology; philosophy of logic; measurement problem |
| **Subjects** | Physics > History and Philosophy of Physics |
| **Related identifiers** | (Add DOIs for Main, Technical papers once reserved) |

#### QFT Extension Paper

| Field | Value |
|-------|-------|
| **Title** | Logic Realism Theory: Extension to Quantum Field Theory |
| **Description** | Extends Logic Realism Theory to relativistic quantum field theory through a tiered derivation structure. Derives Fock space, spin-statistics connection, and CCR/CAR algebras from logical constraints plus explicit physical inputs (Lorentz invariance, locality, microcausality). Distinguishes rigorously between derivations, interpretations, and conjectures. |
| **Keywords** | quantum field theory; quantum foundations; spin-statistics; Fock space; logical constraints; relativistic quantum mechanics |
| **Subjects** | Physics > Quantum Physics; Physics > Mathematical Physics |
| **Related identifiers** | (Add DOIs for Main, Technical, Philosophy papers once reserved) |

---

## Cross-Reference Format

Once DOIs are reserved, add to each paper's References section:

```markdown
## Related Papers in This Series

Longmire, J. D. "It from Bit, Bit from Fit: Logic Realism Theory." Zenodo, 2025. DOI: 10.5281/zenodo.XXXXXX1

Longmire, J. D. "Logic Realism Theory: Technical Foundations." Zenodo, 2025. DOI: 10.5281/zenodo.XXXXXX2

Longmire, J. D. "Logic Realism Theory: Philosophical Foundations." Zenodo, 2025. DOI: 10.5281/zenodo.XXXXXX3

Longmire, J. D. "Logic Realism Theory: Extension to Quantum Field Theory." Zenodo, 2025. DOI: 10.5281/zenodo.XXXXXX4
```

---

## Pre-Submission Checklist

### Format Conversion
- [ ] Convert Main.md → Main.pdf (LaTeX intermediate)
- [ ] Convert Technical.md → Technical.pdf
- [ ] Convert Philosophy.md → Philosophy.pdf
- [ ] Convert QFT_Extension.md → QFT_Extension.pdf

### Quality Checks
- [ ] All citations verified (v0.3.0 protocol: 64/64 passed)
- [ ] Cross-references between papers consistent
- [ ] No broken internal links
- [ ] Figures/equations render correctly in PDF
- [ ] Author name and ORCID correct

### Zenodo Draft Creation
- [ ] Create Main draft → Note DOI: ____________
- [ ] Create Technical draft → Note DOI: ____________
- [ ] Create Philosophy draft → Note DOI: ____________
- [ ] Create QFT Extension draft → Note DOI: ____________

### Final Steps
- [ ] Update all PDFs with cross-reference DOIs
- [ ] Re-upload final PDFs to drafts
- [ ] Final review of metadata
- [ ] Publish Phase 1 (Main, Technical, Philosophy)
- [ ] Wait for feedback (2-4 weeks)
- [ ] Publish Phase 2 (QFT Extension)

---

## Post-Publication

### Versioning
- Minor corrections → New version (v1.0.1)
- Significant updates → New version (v1.1.0)
- Zenodo preserves all versions with same concept DOI

### Promotion
- [ ] Update GitHub README with DOI badges
- [ ] Share on relevant forums/communities
- [ ] Submit to arXiv if endorsement available

### Tracking
- Zenodo provides view/download statistics
- Track citations via DOI

---

## arXiv Consideration

| Platform | Pros | Cons |
|----------|------|------|
| Zenodo | No endorsement needed, immediate | Less physics visibility |
| arXiv | High visibility, physics standard | Requires endorsement |

**Strategy**: Upload to Zenodo first (guaranteed). Pursue arXiv endorsement in parallel. If arXiv accepts, cross-link both.

**arXiv categories**:
- quant-ph (primary)
- physics.hist-ph (secondary, for Philosophy paper)

---

## Notes

- Zenodo is operated by CERN, permanent and free
- DOIs are persistent identifiers, never change
- CC-BY-4.0 allows reuse with attribution
- GitHub repo can be linked as supplementary material

---

*Last updated: 2025-12-01*
