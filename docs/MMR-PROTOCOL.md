# LRT Multi-Model Review Protocol (MMR)

**Version:** 1.0  
**Status:** Active  
**Maintained by:** JD Longmire + Perplexity Computer  
**Supplements:** `LRT-Collaboration-Addendum.md`

---

## Purpose

Replaces ad hoc multi-LLM consultation with a structured, repeatable, traceable review process. Every MMR run produces a GitHub Issue with model verdicts, consensus score, and binding action items.

---

## When MMR Is Triggered

| Trigger | Condition | Required? |
|---------|-----------|-----------|
| **Theory → Lean gate** | Before any ARGUED-status claim advances to Lean formalization | Mandatory |
| **Publication draft gate** | Before TAB or MASTER sections are marked submission-ready | Mandatory |
| **New open problem** | When a new issue is opened for a theoretical claim or derivation gap | Mandatory |
| **On-demand** | Explicit request from JD for any claim, section, or derivation | On request |

MMR is **blocking** at mandatory triggers. No stage transition without a passing MMR.

---

## Model Panel and Roles

Each MMR run assigns fixed critical roles to fixed models. Roles do not rotate.

| Model | Role | Critical Posture |
|-------|------|-----------------|
| **Claude Opus 4.6** | Philosophical Coherence Reviewer | Hunt circularity; challenge necessity claims; probe the transcendental arguments; demand explicit grounding at every step |
| **GPT-5.4** | Formal/Mathematical Rigor Reviewer | Identify derivation gaps; check theorem applicability conditions; flag black-box imports; verify logical entailment chain |
| **Gemini 3.1 Pro** | Literature & Competing Frameworks Reviewer | Compare against Hardy/CDP/Masanes-Müller/Bohmian/MWI; identify precedents; surface papers that challenge or support the claim |
| **Claude Sonnet 4.6** | Synthesis & Consensus Scorer | Aggregate verdicts; identify consensus vs. dissent; assign quality score; generate binding action items |

---

## Scoring Rubric

Each model scores the target on five dimensions (0.0–1.0 each):

| Dimension | What Is Assessed |
|-----------|-----------------|
| **Logical Validity** | Does the argument form hold? Are inferences licensed? |
| **Derivation Completeness** | Are all steps explicit? No unexplained jumps? |
| **Circularity** | Is the claim free of circular dependencies? |
| **Epistemic Honesty** | Are epistemic statuses (ESTABLISHED/ARGUED/OPEN) accurate? |
| **Falsifiability** | Is there a stated condition under which the claim fails? |

**Consensus Score** = mean of all model scores across all dimensions.

**Threshold:** Score ≥ 0.70 → claim passes at current epistemic status.  
Score < 0.70 → claim is demoted (ARGUED→OPEN, ESTABLISHED→ARGUED) pending remediation.

---

## Output Format

Each MMR run produces a GitHub Issue with this exact structure:

```
Title: [MMR] {Claim ID} — {Claim Name} — {trigger type}

## Target
- Claim: {claim ID from claims.yaml}
- Trigger: {Theory→Lean | Publication | Open Problem | On-demand}
- Section: {document and section reference}

## Verdict Summary
| Model | L.Valid | Deriv. | Circular | Epistemic | Falsif. | Score |
|-------|---------|--------|----------|-----------|---------|-------|
| Opus 4.6 | x.x | x.x | x.x | x.x | x.x | x.x |
| GPT-5.4 | x.x | x.x | x.x | x.x | x.x | x.x |
| Gemini 3.1 | x.x | x.x | x.x | x.x | x.x | x.x |
| **Consensus** | | | | | | **x.x** |

**Result:** PASS / FAIL  
**Epistemic Status:** CONFIRMED {status} / DEMOTED to {status}

## Consensus Findings
{Points all models agreed on}

## Dissenting Views
{Points where models disagreed, with model attribution}

## Model Reviews

### Opus 4.6 — Philosophical Coherence
{Full review}

### GPT-5.4 — Formal/Mathematical Rigor
{Full review}

### Gemini 3.1 Pro — Literature & Competing Frameworks
{Full review}

## Action Items
- [ ] {Specific remediation task} — assigned to {Theory/Lean/Publication}
- [ ] {Specific remediation task}

## Labels
multi-model-review, {theory|formalization|publication}, {pass|fail}
```

---

## Process

1. **Initiator** (JD or Perplexity Computer) opens a request specifying: claim ID, trigger type, target text
2. **Perplexity Computer** extracts the target text from the repo and constructs the review prompt for each model
3. **Three subagents** are launched in parallel, one per reviewer model, each with:
   - The target claim/section verbatim
   - Their assigned critical role
   - The scoring rubric
   - Full LRT context (primitives, derivation chain, epistemic status system)
4. **Synthesis** subagent collects all three verdicts, computes consensus score, generates action items
5. **GitHub Issue** created with full output, labeled, and linked to the source issue/milestone
6. **Stage transition** proceeds if PASS; blocked if FAIL pending action item resolution

---

## Remediation

When MMR returns FAIL:

1. Action items from the review are converted to child issues
2. JD addresses each item (theory revision, Lean fix, or explicit scope limitation)
3. MMR re-runs on the revised claim
4. Re-run issue links back to the original MMR issue
5. Stage transition unblocked only after PASS on re-run

---

## Traceability

Every MMR issue is:
- Tagged `multi-model-review`
- Linked to the source claim in `claims.yaml` via issue reference
- Added to the LRT Research Program project board
- Referenced in the relevant milestone

The `claims.yaml` entry for each claim includes a `mmr` field:

```yaml
QM-001:
  name: "Tomographic Locality (H1)"
  status: DERIVED
  mmr:
    - issue: 54
      date: "2026-03-23"
      result: PASS
      score: 0.78
      trigger: "Theory→Lean"
```

---

## Quality History

| Date | Claim | Score | Result | Issue |
|------|-------|-------|--------|-------|
| — | — | — | — | — |

*Populated as reviews are conducted.*

---

**HCAE — Human-Curated, AI-Enabled**
