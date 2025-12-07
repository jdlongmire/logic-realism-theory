# Phase 3: Content Access Verification

**Version**: 0.3.0  
**Status**: Standalone extension to reference_validation_protocol v0.3.0  
**Purpose**: Prove source content was accessed, not just metadata verified  
**Relationship to core protocol**: Optional extension. Phases 1-2 (existence + bibliographic verification) are required; Phase 3 adds content access verification for higher assurance.

**Changelog**: 
- v0.1.0: Initial draft after empirical access testing
- v0.2.0: Added secondary access strategies, triangulation requirements, worked example
- v0.3.0: Added reference replacement strategies with decision tree

---

## Rationale

Phases 1-2 verify that a citation is bibliographically accurate. They do not verify that the validator actually read the source. This creates a gap: claims about what a source says can be fabricated even when the citation details are correct.

Phase 3 addresses this by requiring evidence of content access where possible, and honest flagging where access is limited.

---

## Access Status Hierarchy

| Status | Meaning | Evidence Required |
|--------|---------|-------------------|
| `FULL_ACCESS` | Complete text retrieved and examined | Structural details + distinctive content |
| `PARTIAL_ACCESS` | Abstract, preview, or excerpts only | Abstract first sentence + section count if visible |
| `PREPRINT_ACCESS` | arXiv/preprint version accessed (may differ from published) | Preprint structural details; flag version differences |
| `SECONDARY_ACCESS` | Content known only through quotations in other sources | Cite the secondary source; flag as indirect |
| `METADATA_ONLY` | Bibliographic data verified, content not accessible | Crossref/DOI data only |
| `UNVERIFIABLE` | Cannot confirm content access | Explicit acknowledgment |

---

## Evidence Requirements by Access Level

### FULL_ACCESS

Required evidence (provide at least 3):

1. **Opening line**: First sentence of abstract or introduction (paraphrased to avoid copyright)
2. **Structure**: Section count, figure count, theorem/lemma count
3. **Distinctive terminology**: Technical terms introduced or prominently used
4. **Methodology note**: Brief description of approach (empirical, theoretical, review, etc.)
5. **Key claim**: Central thesis or finding in own words

Example:
```json
{
  "access_status": "FULL_ACCESS",
  "evidence": {
    "opening_line_paraphrase": "Paper opens by noting that quantizing general relativity raises questions about QM interpretation",
    "structure": "6 sections, no figures, key equations in sections 4-5",
    "distinctive_terminology": ["relative state", "Process 1", "Process 2", "external observation formulation"],
    "methodology": "Theoretical reformulation; no experiments",
    "key_claim": "Wave mechanics without collapse (Process 2 only) provides complete description"
  },
  "access_url": "http://www.weylmann.com/relative_state.pdf",
  "accessed_at": "2025-12-07T10:30:00Z"
}
```

### PARTIAL_ACCESS

Required evidence:

1. **Abstract first sentence** (paraphrased)
2. **What is visible**: Abstract only / first page / preview pages
3. **What is not accessible**: Full methods, full results, etc.

Example:
```json
{
  "access_status": "PARTIAL_ACCESS",
  "evidence": {
    "abstract_paraphrase": "Investigates whether complex numbers are necessary in quantum formalism",
    "visible_content": "Abstract + author affiliations + references",
    "not_accessible": "Full methods, supplementary materials"
  },
  "access_limitation": "Paywalled; only abstract visible without institutional access",
  "accessed_at": "2025-12-07T10:30:00Z"
}
```

### PREPRINT_ACCESS

Required evidence:

1. All FULL_ACCESS evidence, applied to preprint
2. **Version flag**: arXiv version number (v1, v2, etc.)
3. **Publication delta**: Note if preprint predates publication (content may differ)

Example:
```json
{
  "access_status": "PREPRINT_ACCESS",
  "evidence": {
    "opening_line_paraphrase": "...",
    "structure": "...",
    "distinctive_terminology": ["..."]
  },
  "preprint_id": "arXiv:2101.10873v2",
  "preprint_date": "2021-12-27",
  "publication_date": "2021-12-15",
  "version_note": "Preprint v2 posted after publication; likely matches published version",
  "warning": "Content may differ from published version"
}
```

### SECONDARY_ACCESS

Required evidence:

1. **Secondary source**: Where the quotation or description appears
2. **What is known**: Specific claims from the secondary source
3. **What is not known**: Everything not explicitly quoted

Example:
```json
{
  "access_status": "SECONDARY_ACCESS",
  "evidence": {
    "secondary_source": "Wikipedia article on Gleason's theorem",
    "known_content": "Introduces 'frame function' concept; proves measures on closed subspaces determined by density operators for dim > 2",
    "not_verified": "Proof structure, lemmas, acknowledgments"
  },
  "warning": "Content known only indirectly; claims about source should be qualified"
}
```

### METADATA_ONLY

Required evidence:

1. **Bibliographic source**: Crossref, DOI resolution, publisher page
2. **What is verified**: Title, authors, journal, volume, pages, year
3. **What is not verified**: Any claims about content

Example:
```json
{
  "access_status": "METADATA_ONLY",
  "evidence": {
    "bibliographic_source": "Crossref API",
    "verified_fields": ["title", "authors", "journal", "volume", "pages", "year", "doi"],
    "not_verified": ["content", "methodology", "claims", "terminology"]
  },
  "access_blocked_by": "robots.txt / paywall / no digital version",
  "warning": "Cannot verify any claims about what this source says"
}
```

---

## Access Strategies by Source Type

### Journal Articles (Post-2000)

**Try in order:**

1. Check for open-access PDF via DOI
2. Check PMC/PubMed Central (NIH-funded often available)
3. Check arXiv for preprint version
4. Check author institutional page for preprint
5. If all fail: METADATA_ONLY

### Journal Articles (Pre-2000)

**Try in order:**

1. Check JSTOR (often has older articles)
2. Check publisher archive
3. Check Internet Archive
4. Check Google Scholar for PDF links
5. If all fail: METADATA_ONLY or SECONDARY_ACCESS via citations

### Books

**Try in order:**

1. Check Google Books preview
2. Check Internet Archive / Open Library
3. Check publisher "Look Inside" feature
4. If chapter: check if chapter has separate DOI
5. If all fail: METADATA_ONLY

### Book Chapters

**Try in order:**

1. Check if chapter has DOI (verify via Crossref)
2. Check containing volume's table of contents
3. Check Google Books for chapter preview
4. Check author's institutional page
5. If all fail: METADATA_ONLY with volume verification

### Conference Proceedings

**Try in order:**

1. Check ACM DL / IEEE Xplore (often open after embargo)
2. Check DBLP for links
3. Check arXiv for preprint
4. Check author page
5. If all fail: METADATA_ONLY

---

## Red Flags for Phase 3

| Flag | Meaning | Action |
|------|---------|--------|
| `CONTENT_CLAIM_WITHOUT_ACCESS` | Making claims about source content without FULL_ACCESS or PREPRINT_ACCESS | Retract claim or qualify heavily |
| `PREPRINT_PUBLICATION_MISMATCH` | Preprint accessed but publication details cited | Note version accessed vs. version cited |
| `SECONDARY_SOURCE_ONLY` | Know source only through others' descriptions | Cannot make independent claims about content |
| `PAYWALL_BLOCKED` | Cannot access due to paywall | Explicitly flag; do not fabricate content |
| `DISTINCTIVE_CONTENT_MISSING` | Claimed to access but cannot provide structural evidence | Suspect hallucination; re-verify |

---

## Integration with Phases 1-2

Phase 3 runs after Phase 2 (bibliographic verification) succeeds.

**Workflow:**

```
Phase 1: Existence Check
    ↓ FOUND
Phase 2: Bibliographic Verification (Crossref/DOI)
    ↓ VERIFIED or VERIFIED_VIA_SECONDARY
Phase 3: Content Access Verification
    ↓ Access status assigned
Final Status: Combine all phases
```

**Combined Status Examples:**

| Phase 1 | Phase 2 | Phase 3 | Final Status |
|---------|---------|---------|--------------|
| FOUND | VERIFIED | FULL_ACCESS | VERIFIED_WITH_CONTENT |
| FOUND | VERIFIED | PREPRINT_ACCESS | VERIFIED_PREPRINT_CONTENT |
| FOUND | VERIFIED | METADATA_ONLY | VERIFIED_NO_CONTENT_ACCESS |
| FOUND | VERIFIED_VIA_SECONDARY | SECONDARY_ACCESS | VERIFIED_INDIRECT |

---

## Secondary Access Strategies

When primary source access fails, attempt secondary routes before accepting METADATA_ONLY status.

### Strategy 1: Reprints and Anthologies

Many foundational papers are reprinted in collections:

| Original | Common Reprint Location |
|----------|------------------------|
| Everett 1957 | Wheeler & Zurek, "Quantum Theory and Measurement" (1983) |
| Bell 1964 | Bell, "Speakable and Unspeakable in QM" (1987) |
| EPR 1935 | Wheeler & Zurek (1983) |
| Gleason 1957 | Hooker, "Logico-Algebraic Approach to QM" (1975) |
| Kochen-Specker 1967 | Various QM foundations anthologies |

**Action**: Search for "[paper title] reprinted in" or check known anthology tables of contents.

**Status if successful**: FULL_ACCESS (note reprint source)

### Strategy 2: Author Self-Archives

Authors often post copies on:

- Personal academic websites
- Institutional repositories (e.g., arXiv, university DSpace)
- ResearchGate / Academia.edu (often full PDFs)
- ORCID-linked repositories

**Action**: Search "[author name] [paper title] PDF" or check author's publication page.

**Status if successful**: FULL_ACCESS or PREPRINT_ACCESS (depending on version)

### Strategy 3: Review Papers

Review articles in the field often:

- Quote key passages from foundational works
- Summarize methodology and findings
- Provide context for claims

**Useful reviews by field**:

| Field | Review Sources |
|-------|---------------|
| QM Foundations | Schlosshauer's decoherence reviews; SEP entries |
| Quantum Information | Nielsen & Chuang textbook; RMP review articles |
| Philosophy of Physics | PhilPapers; Routledge Companion volumes |

**Action**: Search for review papers citing the target; extract quoted content.

**Status if successful**: SECONDARY_ACCESS (cite the review; note indirect access)

### Strategy 4: Textbook Coverage

Standard textbooks often reproduce:

- Key theorems with proofs (Gleason, Bell inequalities)
- Foundational arguments (measurement problem discussions)
- Historical derivations

**Action**: Check if claim can be verified against textbook treatment.

**Status if successful**: SECONDARY_ACCESS (textbook provides independent verification of content)

### Strategy 5: Science Journalism

For recent papers (post-2010), quality science journalism often provides:

- Author quotes
- Key findings summaries
- Context and significance

**Reliable sources**: Quanta Magazine, Nature News, Physics Today, APS Physics

**Action**: Search "[paper title] [author] Quanta" or similar.

**Status if successful**: PARTIAL_ACCESS (journalistic summary; not full content)

### Strategy 6: Citation Context Mining

Papers that cite the target often quote it:

- Use Semantic Scholar's "citations" feature
- Check Google Scholar "cited by"
- Look for papers with extensive literature reviews

**Action**: Find 2-3 papers that cite the target; extract their quotations/descriptions.

**Status if successful**: SECONDARY_ACCESS (triangulated from multiple citing sources)

### Strategy 7: Legal Open Access Routes

Before accepting paywall block:

1. **Unpaywall** (browser extension / API) - finds legal OA versions
2. **CORE** (core.ac.uk) - aggregates institutional repositories
3. **BASE** (base-search.net) - academic search engine
4. **PubMed Central** - NIH-funded papers often deposited
5. **Europe PMC** - European equivalent
6. **DOAJ** - Directory of Open Access Journals

**Action**: Check these before declaring METADATA_ONLY.

### Strategy 8: Library Access Simulation

Some content accessible via:

- Internet Archive's "Borrow" feature (books)
- HathiTrust (limited preview or full for public domain)
- Google Books preview (often includes key pages)
- Publisher "sample chapter" PDFs

**Action**: Check these for partial content access.

**Status if successful**: PARTIAL_ACCESS (note pages/sections accessed)

---

## Secondary Access Decision Tree

```
Primary access failed
         │
         ▼
┌─────────────────────────────┐
│ Is paper pre-1990?          │
└─────────────────────────────┘
         │
    YES  │  NO
         │
         ▼
┌─────────────────────────────┐
│ Check anthologies/reprints  │──YES──▶ FULL_ACCESS (reprint)
│ (Strategy 1)                │
└─────────────────────────────┘
         │ NO
         ▼
┌─────────────────────────────┐
│ Check author self-archive   │──YES──▶ FULL_ACCESS or PREPRINT_ACCESS
│ (Strategy 2)                │
└─────────────────────────────┘
         │ NO
         ▼
┌─────────────────────────────┐
│ Check OA routes             │──YES──▶ FULL_ACCESS
│ (Strategy 7)                │
└─────────────────────────────┘
         │ NO
         ▼
┌─────────────────────────────┐
│ Check Google Books/IA       │──YES──▶ PARTIAL_ACCESS
│ (Strategy 8)                │
└─────────────────────────────┘
         │ NO
         ▼
┌─────────────────────────────┐
│ Find review papers citing   │──YES──▶ SECONDARY_ACCESS
│ (Strategies 3, 4, 6)        │
└─────────────────────────────┘
         │ NO
         ▼
┌─────────────────────────────┐
│ Check science journalism    │──YES──▶ PARTIAL_ACCESS (journalistic)
│ (Strategy 5)                │
└─────────────────────────────┘
         │ NO
         ▼
      METADATA_ONLY
```

---

## Secondary Access Documentation

When using secondary access, document:

```json
{
  "access_status": "SECONDARY_ACCESS",
  "primary_source_blocked": "Paywall (Springer)",
  "secondary_sources_used": [
    {
      "source": "Schlosshauer 2007, Decoherence and the QM-to-Classical Transition",
      "type": "textbook",
      "content_extracted": "Quotes Gleason's theorem statement; summarizes proof strategy",
      "pages": "45-48"
    },
    {
      "source": "Pitowsky 1998, J Math Phys",
      "type": "citing_paper",
      "content_extracted": "Reproduces frame function definition from Gleason",
      "doi": "10.1063/1.532334"
    }
  ],
  "confidence_in_content_claims": "MEDIUM - triangulated from 2 secondary sources",
  "claims_not_verifiable": "Gleason's acknowledgments, exact proof structure, lemma attributions"
}
```

---

## Triangulation Requirements

SECONDARY_ACCESS claims require corroboration:

| Claim Type | Minimum Sources | Rationale |
|------------|-----------------|-----------|
| Paper's central thesis | 2 independent | Core claim should be consistently reported |
| Specific quotation | 1 (if quoted directly) | Direct quotes are verifiable |
| Methodology description | 2 independent | Summaries can drift |
| Numerical results | 2 independent | Transcription errors common |
| Author's intent/interpretation | 3+ or decline | Highly subject to interpretation |

**Triangulation failure modes to watch:**

1. **Citation mutation**: Claim gets distorted as it passes through citing papers
2. **Selective quotation**: Secondary source quotes out of context
3. **Paraphrase drift**: Each retelling shifts meaning slightly
4. **Authority cascade**: Everyone cites the same secondary source, creating false consensus

**When triangulation fails**: If secondary sources disagree on content, flag as UNVERIFIABLE for that specific claim. Do not pick the version you prefer.

---

## Upgraded Access Status Definitions

Revising the hierarchy to account for secondary access quality:

| Status | Meaning | Content Claims Permitted |
|--------|---------|-------------------------|
| `FULL_ACCESS` | Primary source retrieved | All claims, with evidence |
| `FULL_ACCESS_REPRINT` | Reprint/anthology accessed | All claims (note reprint source) |
| `PREPRINT_ACCESS` | arXiv/preprint accessed | All claims (note version delta risk) |
| `PARTIAL_ACCESS` | Abstract + preview pages | Claims about visible content only |
| `SECONDARY_ACCESS_STRONG` | 3+ independent secondary sources agree | Central thesis and major claims |
| `SECONDARY_ACCESS_WEAK` | 1-2 secondary sources | Only directly quoted content |
| `METADATA_ONLY` | Bibliographic data only | No content claims permitted |
| `UNVERIFIABLE` | Cannot access or triangulate | No content claims; flag for author verification |

---

---

## Worked Example: Gleason 1957

Demonstrating secondary access workflow for a paywalled foundational paper.

### Initial Attempt

**Citation**: Gleason, A.M. (1957). "Measures on the Closed Subspaces of a Hilbert Space." J. Math. Mech. 6(6): 885-893.

**Phase 2 result**: VERIFIED via Crossref (DOI: 10.1512/iumj.1957.6.56050)

**Primary access attempt**: FAILED (robots.txt blocks IUMJ full text)

### Secondary Access Workflow

**Strategy 1 (Reprints)**: 
- Found: Reprinted in Hooker (ed.), "The Logico-Algebraic Approach to Quantum Mechanics" (1975), Springer
- Result: Google Books preview available but incomplete

**Strategy 2 (Author self-archive)**:
- Gleason deceased (2008); no personal website
- No institutional repository copy found

**Strategy 6 (Citation context)**:
- Pitowsky 1998 (J. Math. Phys.): Defines "frame function" citing Gleason directly
- Cooke, Keane & Moran 1985: "Elementary proof" paper quotes Gleason's theorem statement
- Wikipedia "Gleason's theorem": Extensive coverage with theorem statement

**Strategy 3 (Review papers)**:
- Dvurečenskij 1992 book "Gleason's Theorem and Its Applications": Comprehensive coverage
- Multiple SEP entries discuss theorem

### Triangulated Content

| Content Element | Source 1 | Source 2 | Source 3 | Status |
|-----------------|----------|----------|----------|--------|
| Theorem statement | Wikipedia | Pitowsky 1998 | Cooke et al. 1985 | CONFIRMED |
| "Frame function" definition | Pitowsky 1998 | arXiv 2001.06738 | Wikipedia | CONFIRMED |
| dim > 2 requirement | All three | - | - | CONFIRMED |
| Palais lemma attribution | Wikipedia only | - | - | UNVERIFIED (single source) |
| Proof structure | Varies by source | - | - | UNVERIFIED (descriptions differ) |

### Final Phase 3 Record

```json
{
  "citation": "Gleason 1957",
  "phase_2_status": "VERIFIED",
  "phase_3_status": "SECONDARY_ACCESS_STRONG",
  "primary_access_blocked": "robots.txt / paywall",
  "secondary_sources": [
    {
      "source": "Wikipedia: Gleason's theorem",
      "type": "encyclopedia",
      "accessed": "2025-12-07",
      "content": "Theorem statement, frame function definition, historical context"
    },
    {
      "source": "Pitowsky 1998, J. Math. Phys. 39:218",
      "type": "citing_paper",
      "doi": "10.1063/1.532334",
      "content": "Frame function definition, theorem application"
    },
    {
      "source": "Cooke, Keane & Moran 1985, Math. Proc. Camb. Phil. Soc. 98:117",
      "type": "citing_paper", 
      "content": "Theorem statement, alternative proof"
    }
  ],
  "verified_content": [
    "Central theorem: measures on closed subspaces of Hilbert space (dim ≥ 3) correspond to density operators via trace formula",
    "Frame function concept: assigns weights to unit vectors summing to constant over orthonormal bases",
    "Dimension restriction: theorem fails for dim = 2"
  ],
  "unverified_content": [
    "Exact proof structure",
    "Palais lemma attribution (single source)",
    "Acknowledgments"
  ],
  "content_claims_permitted": "Central theorem and frame function definition - triangulated",
  "content_claims_not_permitted": "Proof details, attribution details - not triangulated"
}
```

---

## Strategy 9: Reference Replacement

When a source cannot be verified or accessed through any route, consider whether an alternative source can support the same claim.

### When Replacement is Appropriate

| Scenario | Replacement Appropriate? | Rationale |
|----------|-------------------------|-----------|
| Citing for a general claim that many sources make | YES | The claim matters, not the specific source |
| Citing for a specific result/theorem | MAYBE | If another paper proves the same result |
| Citing the original/foundational source | USUALLY NO | Historical priority matters |
| Citing for a direct quotation | NO | Cannot quote a source you haven't read |
| Citing for author's unique interpretation | NO | Interpretation is source-specific |
| Citing a review when primary is inaccessible | YES | Reviews exist to synthesize |

### Replacement Hierarchy

When seeking replacement sources, prefer in order:

1. **More recent paper by same author(s)** restating the result
2. **Review article** that synthesizes the claim with citations
3. **Textbook** that presents the result as established
4. **Independent replication** that confirms the finding
5. **Paper that explicitly builds on** the inaccessible source

### Replacement Documentation

When replacing a reference, document:

```json
{
  "original_citation": "Smith 1987, J. Obscure Physics 12:45-67",
  "original_claim": "First demonstration that X implies Y",
  "verification_status": "UNVERIFIABLE - no digital copy, not in any repository",
  "replacement_citation": "Jones 2015, Reviews of Modern Physics 87:1234",
  "replacement_doi": "10.1103/RevModPhys.87.1234",
  "replacement_verification": "FULL_ACCESS",
  "replacement_rationale": "Jones 2015 reviews the X-implies-Y result with full derivation, citing Smith 1987 as original source",
  "what_is_preserved": "The claim that X implies Y",
  "what_is_lost": "Priority attribution to Smith; original proof approach",
  "recommendation": "Cite as 'Jones 2015, reviewing Smith 1987' or footnote the inaccessibility"
}
```

### Replacement Patterns by Claim Type

**Empirical results:**
- Original experiment inaccessible → cite replication or meta-analysis
- Example: Can't access Aspect 1982 → cite Aspect's later reviews, or subsequent Bell tests

**Theorems/Proofs:**
- Original proof inaccessible → cite textbook presentation or alternative proof
- Example: Can't access Gleason 1957 → cite Cooke-Keane-Moran 1985 elementary proof, note it's an alternative proof of the same theorem

**Conceptual claims:**
- Original formulation inaccessible → cite review or subsequent development
- Example: Can't access Everett 1957 → problematic (foundational), but could cite Barrett's SEP entry with caveat

**Definitions:**
- Original definition inaccessible → cite any authoritative source using same definition
- Example: Standard QM definitions → cite Peres or Nielsen & Chuang textbooks

### When NOT to Replace

**Preserve original citations when:**

1. **Historical priority matters**: "Everett first proposed..." requires citing Everett
2. **Specific phrasing matters**: If you're discussing how an author framed something
3. **Intellectual lineage matters**: Showing who influenced whom
4. **Controversy exists**: Different sources may present different versions
5. **The source IS the subject**: Papers about Gleason's theorem should cite Gleason

**In these cases, options are:**

- Cite original + note inaccessibility in footnote
- Cite original + accessible secondary source together
- Cite original + flag for author's personal verification
- Acknowledge you're citing based on secondary accounts

### Replacement Red Flags

| Flag | Meaning | Action |
|------|---------|--------|
| `CLAIM_DRIFT` | Replacement source makes subtly different claim | Do not replace; claims must match |
| `PRIORITY_LOSS` | Replacement obscures who originated the idea | Add footnote preserving priority |
| `CONTEXT_LOSS` | Original context matters but is lost in replacement | Consider dual citation |
| `CIRCULAR_REPLACEMENT` | Replacement source's only source is the inaccessible original | Not a true replacement |
| `QUALITY_DOWNGRADE` | Replacing peer-reviewed with non-peer-reviewed | Acceptable only if claim is uncontroversial |

### Worked Example: Stueckelberg 1960

**Original citation**: Stueckelberg, E.C.G. (1960). "Quantum theory in real Hilbert space." Helv. Phys. Acta 33: 727-752.

**Claim being supported**: Real-valued quantum mechanics can reproduce single-particle predictions.

**Verification attempt**: 
- Phase 2: VERIFIED_VIA_SECONDARY (pre-DOI, found in UNIGE archive)
- Phase 3: PARTIAL_ACCESS (archive has metadata, no full text)

**Replacement analysis**:

| Candidate | Accessible? | Same Claim? | Priority Preserved? |
|-----------|-------------|-------------|---------------------|
| McKague et al. 2009 (PRL) | YES (DOI) | Extends result to multipartite | Cites Stueckelberg |
| Aleksandrova et al. 2013 (PRA) | YES (DOI) | Develops real QM further | Cites Stueckelberg |
| Wootters 2012 (Found. Phys.) | YES (DOI) | Reviews real vs complex QM | Cites Stueckelberg |
| Renou et al. 2021 (Nature) | YES (DOI) | Cites Stueckelberg for historical context | YES |

**Recommendation**: 
- For the historical claim "Stueckelberg showed...": Keep original, add "(as reviewed in Renou et al. 2021)"
- For the technical claim about real QM sufficiency: Could cite McKague 2009 which extends the result
- Do not silently replace: Stueckelberg has historical priority

**Final citation options**:

Option A (preserve priority):
> Stueckelberg (1960) demonstrated that real-valued quantum theory reproduces single-particle predictions; this was later extended to multipartite systems by McKague et al. (2009).

Option B (accessible primary):
> Real-valued quantum theory can reproduce single-particle predictions (McKague et al. 2009, extending Stueckelberg 1960).

Option C (review as primary):
> The sufficiency of real numbers for single-particle quantum mechanics was established by Stueckelberg (1960; see Renou et al. 2021 for review).

---

## Reference Replacement Decision Tree

```
Source verification failed (UNVERIFIABLE or METADATA_ONLY)
                    │
                    ▼
┌────────────────────────────────────────┐
│ Is this a foundational/priority cite?  │
└────────────────────────────────────────┘
                    │
           YES      │      NO
            │       │       │
            ▼       │       ▼
┌──────────────────┐│┌─────────────────────────────┐
│ Keep original    │││ Is claim made by multiple   │
│ Add accessible   │││ accessible sources?         │
│ secondary source │││                             │
└──────────────────┘│└─────────────────────────────┘
                    │          │
                    │     YES  │  NO
                    │          │
                    │          ▼
                    │  ┌───────────────────────────┐
                    │  │ Replace with accessible   │
                    │  │ source making same claim  │
                    │  │ Document replacement      │
                    │  └───────────────────────────┘
                    │          │
                    │          │  NO REPLACEMENT FOUND
                    │          ▼
                    │  ┌───────────────────────────┐
                    │  │ Flag for author to:       │
                    │  │ - Verify personally       │
                    │  │ - Obtain via ILL          │
                    │  │ - Acknowledge limitation  │
                    │  └───────────────────────────┘
                    │
                    ▼
         AUTHOR DECISION REQUIRED
```

---

## Honest Limitations

This protocol cannot overcome:

1. **Paywalls**: Without institutional access, many sources remain METADATA_ONLY
2. **Books**: Most book content is not freely accessible online
3. **Pre-digital sources**: Papers from before ~1990 often have no digital version
4. **Copyright restrictions**: Even when accessible, extensive quotation is prohibited

**What this protocol does:**

- Forces explicit acknowledgment of access limitations
- Prevents false claims of content verification
- Distinguishes "citation is correct" from "I read the source"
- Creates audit trail for what was and was not accessed

**What this protocol does not do:**

- Guarantee content access for all sources
- Replace reading the actual source (for the human author)
- Verify correctness of claims made about sources

---

## Recommendations for Authors

1. **Prioritize open-access sources** where equivalent quality exists
2. **Include arXiv IDs** for physics papers (enables preprint access verification)
3. **Verify critical claims yourself** for sources flagged METADATA_ONLY
4. **Maintain access notes** documenting which sources you personally read
5. **Flag sources you haven't read** - citing secondary citations should be explicit

---

## Schema Extension

Add to `verification_result` in reference_validation_protocol.json:

```json
"phase_3_content_access": {
  "type": "object",
  "required": ["access_status", "evidence"],
  "properties": {
    "access_status": {
      "type": "string",
      "enum": ["FULL_ACCESS", "PARTIAL_ACCESS", "PREPRINT_ACCESS", "SECONDARY_ACCESS", "METADATA_ONLY", "UNVERIFIABLE"]
    },
    "evidence": {
      "type": "object",
      "properties": {
        "opening_line_paraphrase": {"type": "string"},
        "structure": {"type": "string"},
        "distinctive_terminology": {"type": "array", "items": {"type": "string"}},
        "methodology": {"type": "string"},
        "key_claim": {"type": "string"},
        "abstract_paraphrase": {"type": "string"},
        "visible_content": {"type": "string"},
        "not_accessible": {"type": "string"}
      }
    },
    "access_url": {"type": "string", "format": "uri"},
    "preprint_id": {"type": "string"},
    "version_note": {"type": "string"},
    "access_blocked_by": {"type": "string"},
    "warning": {"type": "string"},
    "accessed_at": {"type": "string", "format": "date-time"}
  }
}
```

---

---

## Complete Phase 3 Workflow Summary

```
┌─────────────────────────────────────────────────────────────────┐
│                    PHASE 3 CONTENT ACCESS                       │
│                    (after Phase 2 succeeds)                     │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│ STEP 1: Attempt Primary Access                                  │
│ - DOI resolution to full text                                   │
│ - Publisher open access                                         │
│ - arXiv/preprint                                                │
└─────────────────────────────────────────────────────────────────┘
                              │
                 SUCCESS      │      FAILED
                    │         │         │
                    ▼         │         ▼
            ┌───────────┐     │  ┌─────────────────────────────────┐
            │FULL_ACCESS│     │  │ STEP 2: Secondary Access        │
            │    or     │     │  │ - Reprints/anthologies          │
            │ PREPRINT_ │     │  │ - Author self-archive           │
            │  ACCESS   │     │  │ - OA routes (Unpaywall, PMC)    │
            └───────────┘     │  │ - Google Books/IA preview       │
                              │  │ - Review papers                 │
                              │  │ - Citation context mining       │
                              │  └─────────────────────────────────┘
                              │              │
                              │   SUCCESS    │    FAILED
                              │      │       │       │
                              │      ▼       │       ▼
                              │ ┌─────────┐  │  ┌─────────────────────┐
                              │ │PARTIAL_ │  │  │ STEP 3: Triangulate │
                              │ │ ACCESS  │  │  │ - Find 2-3 sources  │
                              │ │   or    │  │  │   that cite target  │
                              │ │SECONDARY│  │  │ - Extract quotes    │
                              │ │ ACCESS  │  │  │ - Compare accounts  │
                              │ └─────────┘  │  └─────────────────────┘
                              │              │          │
                              │              │ SUCCESS  │  FAILED
                              │              │    │     │     │
                              │              │    ▼     │     ▼
                              │              │┌───────┐ │ ┌─────────────────┐
                              │              ││SECOND-│ │ │ STEP 4: Replace │
                              │              ││ARY_   │ │ │ - Find alt.     │
                              │              ││ACCESS │ │ │   source for    │
                              │              ││_STRONG│ │ │   same claim    │
                              │              │└───────┘ │ │ - Document swap │
                              │              │          │ └─────────────────┘
                              │              │          │         │
                              │              │          │SUCCESS  │ FAILED
                              │              │          │   │     │    │
                              │              │          │   ▼     │    ▼
                              │              │          │┌──────┐ │┌────────┐
                              │              │          ││REPLAC│ ││METADATA│
                              │              │          ││-ED   │ ││_ONLY  │
                              │              │          │└──────┘ │└────────┘
                              │              │          │         │
                              └──────────────┴──────────┴─────────┘
                                             │
                                             ▼
┌─────────────────────────────────────────────────────────────────┐
│ STEP 5: Document & Flag                                         │
│ - Record access status                                          │
│ - List evidence provided                                        │
│ - Flag what claims are/aren't permitted                         │
│ - Flag for author attention if METADATA_ONLY                    │
└─────────────────────────────────────────────────────────────────┘
```

### Quick Reference: What Content Claims Are Permitted

| Access Status | Central Thesis | Specific Claims | Direct Quotes | Proof Details |
|---------------|----------------|-----------------|---------------|---------------|
| FULL_ACCESS | ✓ | ✓ | ✓ | ✓ |
| FULL_ACCESS_REPRINT | ✓ | ✓ | ✓ | ✓ (note reprint) |
| PREPRINT_ACCESS | ✓ | ✓ (flag version) | ✓ (flag version) | ✓ (flag version) |
| PARTIAL_ACCESS | ✓ (if in abstract) | Only visible content | Only visible content | ✗ |
| SECONDARY_ACCESS_STRONG | ✓ | If triangulated | If directly quoted in secondary | ✗ |
| SECONDARY_ACCESS_WEAK | Only if quoted | ✗ | If quoted | ✗ |
| REPLACED | Per replacement source | Per replacement source | ✗ from original | ✗ from original |
| METADATA_ONLY | ✗ | ✗ | ✗ | ✗ |
| UNVERIFIABLE | ✗ | ✗ | ✗ | ✗ |

---

*v0.1.0 - 2025-12-07: Initial draft after empirical access testing*  
*v0.2.0 - 2025-12-07: Added secondary access strategies, triangulation requirements, Gleason worked example*  
*v0.3.0 - 2025-12-07: Added reference replacement strategies, Stueckelberg worked example, decision tree*
