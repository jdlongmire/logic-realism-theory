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
| Main | Logic_Realism_Theory_Main.md | 10.5281/zenodo.17778402 | Draft created |
| Technical | Logic_Realism_Theory_Technical.md | 10.5281/zenodo.17778707 | Draft created |
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
| **Title** | It from Bit, Bit from Fit: Foundational Physics Logically Remastered |
| **Description** | Every physical measurement ever conducted has yielded exactly one outcome: self-identical, non-contradictory, determinate. This paper argues that the Three Fundamental Laws of Logic (Identity, Non-Contradiction, and Excluded Middle) are not cognitive conventions but ontological constraints constitutive of physical distinguishability. From this thesis, quantum mechanics emerges as the unique stable structure at the interface between non-Boolean possibility and Boolean actuality. The framework derives rather than postulates: complex Hilbert space structure follows from interface constraints combined with the physical requirement of compositional consistency (local tomography); the Born rule follows from Gleason's theorem; unitary dynamics follows from information preservation requirements. One structural prediction, that quantum mechanics requires complex amplitudes, has been experimentally confirmed (Renou et al., 2021). The framework specifies twelve explicit conditions that would falsify it. Logic Realism Theory provides unified explanation for seventeen quantum phenomena that other interpretations treat as independent postulates, while maintaining realism, locality, and parsimony. |
| **Keywords** | quantum foundations; logic realism; Born rule; measurement problem; entanglement; falsifiability |
| **Subjects** | Physics > Quantum Physics |
| **Related identifiers** | (Add DOIs for Technical, Philosophy papers once reserved) |

#### Technical Paper

| Field | Value |
|-------|-------|
| **Title** | Logic Realism Theory: Technical Foundations |
| **Description** | This companion paper provides the rigorous mathematical constructions underlying Logic Realism Theory. We prove three key results: (1) the Hardy kernel construction derives inner product structure directly from the distinguishability metric D without presupposing Hilbert space or the Born rule; (2) LRT axioms imply all five Masanes-Müller axioms, including MM5 (entanglement connectivity) via the Lee-Selby theorem applied to CBP-enforced purification uniqueness; (3) complex quantum mechanics is the unique theory satisfying LRT axioms. The derivation chain from logical constraints (3FLL) to quantum mechanics is complete—no conditional hedges or irreducible gaps remain. |
| **Keywords** | quantum foundations; mathematical physics; Hilbert space; reconstruction theorems; Masanes-Müller; distinguishability |
| **Subjects** | Physics > Mathematical Physics |
| **Related identifiers** | (Add DOIs for Main, Philosophy papers once reserved) |

#### Philosophy Paper

| Field | Value |
|-------|-------|
| **Title** | Logic Realism Theory: Philosophical Foundations |
| **Description** | Logic Realism Theory (LRT) proposes that the Three Fundamental Laws of Logic (3FLL)—Identity, Non-Contradiction, and Excluded Middle—are not merely rules of reasoning but ontological constraints constitutive of physical distinguishability. The core evidence is an asymmetry: we can conceive of 3FLL violations, yet physical reality never produces them. This asymmetry indicates that 3FLL constrain reality, not merely cognition. This paper develops the philosophical foundations of this claim. We argue that: (1) 3FLL have a dual character, functioning both epistemically and ontologically; (2) quantum mechanics emerges as the unique "interface" structure mediating between non-Boolean possibility and Boolean actuality; (3) this framework resolves longstanding interpretive puzzles while maintaining scientific realism. The result is a form of structural realism grounded in logical necessity rather than contingent physical law. |
| **Keywords** | philosophy of physics; quantum foundations; logical realism; ontology; structural realism; measurement problem |
| **Subjects** | Physics > History and Philosophy of Physics |
| **Related identifiers** | (Add DOIs for Main, Technical papers once reserved) |

#### QFT Extension Paper

| Field | Value |
|-------|-------|
| **Title** | LRT Constraints on QFT: Deriving Fock Structure and Interpreting Renormalization from Logical Foundations |
| **Description** | Logic Realism Theory (LRT) derives non-relativistic quantum mechanics from the claim that the Three Fundamental Laws of Logic are ontological constraints constitutive of physical distinguishability. This paper extends LRT to quantum field theory through a tiered derivation structure with explicit physical inputs at each level. We establish three principal results: (1) Fock space structure is derived from LRT axioms plus Lorentz invariance and locality; (2) the spin-statistics connection follows from Lorentz invariance and microcausality via the standard Pauli argument; (3) the uniqueness of complex QFT is established. The paper distinguishes derivations from interpretations. Cluster decomposition, vacuum uniqueness, and the spectral gap are physical inputs (Tier 4), not consequences of logical constraints. Renormalization is interpreted as 3FLL-restoration at UV scales, but this does not derive renormalization group equations. Four predictions and six strong falsifiers are identified. |
| **Keywords** | quantum field theory; logic realism; Fock space; spin-statistics; falsifiability; reconstruction theorems |
| **Subjects** | Physics > Quantum Physics; Physics > Mathematical Physics |
| **Related identifiers** | (Add DOIs for Main, Technical, Philosophy papers once reserved) |

---

## Cross-Reference Format

Once DOIs are reserved, add to each paper's References section:

```markdown
## Related Papers in This Series

Longmire, J. D. "It from Bit, Bit from Fit: Foundational Physics Logically Remastered." Zenodo, 2025. DOI: 10.5281/zenodo.17778402

Longmire, J. D. "Logic Realism Theory: Technical Foundations." Zenodo, 2025. DOI: 10.5281/zenodo.17778707

Longmire, J. D. "Logic Realism Theory: Philosophical Foundations." Zenodo, 2025. DOI: 10.5281/zenodo.XXXXXX3

Longmire, J. D. "LRT Constraints on QFT: Deriving Fock Structure and Interpreting Renormalization from Logical Foundations." Zenodo, 2025. DOI: 10.5281/zenodo.XXXXXX4
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
- [x] Create Main draft → DOI: 10.5281/zenodo.17778402
- [x] Create Technical draft → DOI: 10.5281/zenodo.17778707
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
