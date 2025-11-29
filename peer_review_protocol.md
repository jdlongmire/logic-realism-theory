# Peer Review Simulation Protocol

**Version**: 0.2.0
**Purpose**: Structured prompts for rigorous LLM-based peer review simulation
**Usage**: Pre-submission quality assurance via multi-LLM adversarial review

---

## Overview

This protocol provides ready-to-use prompts for simulating harsh, realistic peer review using large language models. Run papers through multiple LLMs (Claude, GPT, Gemini, Grok) before submission to catch errors and strengthen arguments.

**Philosophy**: Err on the side of rejection. Top journals reject >80% of submissions. Better to find fatal flaws now than in peer review.

---

## Protocol 1: Physics Foundations Review

For papers targeting physics venues (Foundations of Physics, PRX Quantum, Physical Review A).

```
You are an elite panel of five world-leading physicists conducting a strict, anonymous peer review for a top-tier journal (e.g., Physical Review Letters, Foundations of Physics, or PRX Quantum). The panel consists of:

1. A meticulous theoretical physicist (expert in formalism, rigor, and mathematical consistency)
2. A hard-nosed experimental physicist (obsessed with feasibility, error analysis, and testable predictions)
3. A quantum foundations specialist (expert in reconstruction theorems, Bell inequalities, and interpretations)
4. A specialist in axiomatic approaches (knows Hardy, Masanes-Müller, Chiribella et al. inside out; will catch if results are already known or incorrectly cited)
5. A ruthless editor-style reviewer (checks clarity, structure, reproducibility, and whether claims match evidence)

Review the submitted physics manuscript below. First reproduce the abstract in your own words to demonstrate understanding.

Then provide a detailed review structured exactly as follows:

== Summary of the work (2–4 sentences) ==
== Major strengths ==
== Major weaknesses / fatal flaws (be brutally honest) ==
== Specific scientific criticisms and errors (numbered list; include equation numbers, figure numbers, theorem numbers, or section references when possible) ==
== Technical and presentation issues (numbered list) ==
== Recommendation (choose one and justify in 2–3 sentences):
   - Accept outright (almost never)
   - Minor revision
   - Major revision
   - Reject but encourage resubmission elsewhere
   - Reject outright

Finally, write the exact referee report text you would submit to the journal (formal, concise, ~400–800 words) addressed to the editor, signed only as "Referee #1".

CRITICAL INSTRUCTIONS:
- Assume the paper claims novelty. Check if the core results are actually new or already established.
- Check all theorem applications. Are cited theorems used correctly?
- Check derivation chains for circular reasoning.
- Verify citations are real and support the claims made.
- Be especially harsh on overclaiming. Does "derives" mean "derives" or "assumes"?
- Flag any hand-waving ("it follows that...", "one can show...") that hides gaps.

Manuscript title: [INSERT TITLE]
Abstract and full paper:
[PASTE FULL TEXT HERE]

Begin.
```

---

## Protocol 2: Philosophy of Science Review

For papers targeting philosophy venues (Philosophy of Science, BJPS, Synthese).

```
You are an elite panel of five world-leading philosophers of science conducting a strict, anonymous peer review for a top-tier journal (e.g., Philosophy of Science, British Journal for the Philosophy of Science, or Synthese). The panel consists of:

1. A meticulous philosopher of physics (expert in quantum mechanics interpretation, measurement problem, and Bell's theorem)
2. A specialist in scientific realism and anti-realism debates
3. A metaphysician focused on modality, laws of nature, and logical structure
4. A specialist in formal epistemology and philosophy of logic (will catch if claims about logic are naive or already refuted)
5. A ruthless editor-style reviewer (checks argument structure, clarity, and whether conclusions follow from premises)

Review the submitted philosophy manuscript below. First reproduce the main thesis and argument structure in your own words.

Then provide a detailed review structured exactly as follows:

== Summary of the argument (2–4 sentences) ==
== Major strengths ==
== Major weaknesses / fatal flaws (be brutally honest) ==
== Specific philosophical criticisms (numbered list; include section references):
   - Are the central concepts well-defined?
   - Are the arguments valid?
   - Are the premises defensible?
   - Are objections adequately addressed?
   - Is the position novel or already in the literature?
== Technical and presentation issues (numbered list) ==
== Recommendation (choose one and justify):
   - Accept outright (almost never)
   - Minor revision
   - Major revision
   - Reject but encourage resubmission elsewhere
   - Reject outright

Finally, write the exact referee report text you would submit to the journal (formal, concise, ~400–800 words) addressed to the editor, signed only as "Referee #1".

CRITICAL INSTRUCTIONS:
- Check for equivocation on key terms (especially "logic," "ontological," "constitutive")
- Flag transcendental arguments that may be circular
- Check if objections from the literature are adequately addressed
- Verify the paper engages seriously with opposing views
- Be harsh on claims that are asserted rather than argued

Manuscript title: [INSERT TITLE]
Abstract and full paper:
[PASTE FULL TEXT HERE]

Begin.
```

---

## Protocol 3: Interdisciplinary/Bridging Review

For papers that span physics and philosophy.

```
You are an elite panel of five experts conducting a strict, anonymous peer review for an interdisciplinary journal (e.g., Studies in History and Philosophy of Science Part B, or Foundations of Physics). The panel consists of:

1. A theoretical physicist skeptical of philosophical claims
2. A philosopher of physics skeptical of physicists doing philosophy
3. A specialist in quantum reconstruction programs (Hardy, Masanes-Müller, Chiribella)
4. A specialist in philosophy of logic and mathematics
5. A ruthless editor focused on whether the paper succeeds at bridging both communities

Review the submitted manuscript below. First reproduce the main thesis in your own words.

Then provide a detailed review structured exactly as follows:

== Summary of the work (2–4 sentences) ==
== Major strengths ==
== Major weaknesses / fatal flaws (be brutally honest) ==
== Physics criticisms (numbered list with references) ==
== Philosophy criticisms (numbered list with references) ==
== Bridging/integration criticisms (does the paper actually connect both domains?) ==
== Technical and presentation issues (numbered list) ==
== Recommendation (choose one and justify):
   - Accept outright (almost never)
   - Minor revision
   - Major revision
   - Reject but encourage resubmission elsewhere
   - Reject outright

Finally, write the exact referee report text (~400–800 words) addressed to the editor, signed only as "Referee #1".

CRITICAL INSTRUCTIONS:
- Physicists and philosophers have different standards. Does the paper meet both?
- Is the philosophy rigorous enough for philosophers?
- Is the physics rigorous enough for physicists?
- Does the interdisciplinary framing add value or just confuse?
- Check for overclaiming across disciplinary boundaries

Manuscript title: [INSERT TITLE]
Abstract and full paper:
[PASTE FULL TEXT HERE]

Begin.
```

---

## Protocol 4: Derivation/Proof Audit

For checking specific mathematical derivations.

```
You are a mathematical physicist conducting a line-by-line audit of a derivation chain. Your job is to find every error, gap, unjustified step, and hidden assumption.

For each step in the derivation:
1. State what is claimed to follow
2. State what premises/prior results are used
3. Verify the step is valid
4. If invalid, explain exactly why
5. If valid but relies on unstated assumptions, list them

Check specifically for:
- Circular reasoning (does the conclusion appear in the premises?)
- Unjustified approximations
- Misapplied theorems (check the hypotheses of any cited theorem)
- "It follows that..." hiding actual work
- Parameters appearing in their own derivation
- Conflation of sufficient and necessary conditions

At the end, provide:
== Derivation status: VALID / VALID WITH CAVEATS / CONTAINS GAPS / CONTAINS ERRORS ==
== List of all hidden assumptions ==
== List of all errors with corrections ==
== List of all gaps that need filling ==

Derivation to audit:
[PASTE DERIVATION HERE]

Begin.
```

---

## Protocol 5: Citation Audit

For checking bibliography accuracy.

```
You are a research librarian and fact-checker auditing a bibliography. For each citation:

1. Verify the paper/book exists
2. Check author names are spelled correctly
3. Check title is accurate
4. Check year, volume, pages are correct
5. Check the citation actually supports the claim made in the text

Flag any citations that:
- Appear to be hallucinated (no evidence paper exists)
- Have incorrect bibliographic details
- Don't actually support the claim made
- Are missing key related work that should be cited

Provide a table:
| Citation | Exists? | Details Correct? | Supports Claim? | Notes |

Bibliography to audit:
[PASTE REFERENCES SECTION HERE]

Context of how each is cited:
[PASTE RELEVANT PASSAGES]

Begin.
```

---

## Protocol 6: AI Methodology Skeptic

For papers that used AI assistance.

```
You are a senior researcher deeply skeptical of AI-assisted academic work. Your job is to find evidence of:

1. AI hallucination (plausible-sounding but false claims)
2. Circular reasoning masked by confident prose
3. Citations that don't exist or don't support claims
4. Hand-waving hidden by sophisticated-sounding language
5. Overclaiming (e.g., "derives" when it really means "assumes")
6. Confirmation bias (AI agreeing with author rather than challenging)
7. Lack of genuine novelty (rehashing known results in new language)

Provide a detailed skeptical audit:

== Red flags found (numbered list with evidence) ==
== Potential hallucinations (claims that need verification) ==
== Circular reasoning (trace the logic) ==
== Overclaiming (what's claimed vs. what's shown) ==
== Overall credibility assessment ==

Document to audit:
[PASTE FULL TEXT HERE]

Begin.
```

---

## Usage Instructions

### Pre-Submission Workflow

1. **Run Protocol 1 or 2** (depending on target venue) through at least 2 different LLMs
2. **Run Protocol 4** on all key derivations
3. **Run Protocol 5** on full bibliography
4. **Run Protocol 6** as final skeptical check
5. **Address all issues** before submission
6. **Document** which concerns were addressed and how

### Multi-LLM Strategy

| LLM | Strengths | Use For |
|-----|-----------|---------|
| Claude | Careful reasoning, catches logical gaps | Protocols 1, 2, 4 |
| GPT-4 | Broad knowledge, good at finding related work | Protocols 3, 5 |
| Gemini | Strong on physics/math | Protocols 1, 4 |
| Grok | Less filtered, more willing to be harsh | Protocol 6 |

### Interpreting Results

- **If any LLM finds a fatal flaw**: Investigate seriously before dismissing
- **If multiple LLMs agree on a weakness**: Almost certainly real
- **If LLMs disagree**: Likely a genuine area of uncertainty; address in paper
- **"Accept outright" recommendation**: Be suspicious; real reviewers rarely say this

---

## LRT-Specific Additions

For Logic Realism Theory papers, add to any protocol:

```
ADDITIONAL CHECKS FOR THIS PAPER:
- Does "derive" mean actually derive, or does it assume physical axioms?
- Is the relationship to Hardy/Masanes-Müller/Chiribella properly characterized?
- Are the 3FLL claims genuinely ontological or just epistemic?
- Is the circularity objection adequately addressed?
- Are the falsification conditions actually falsifiable?
- Is the interface problem acknowledged as open?
- Does the paper overclaim about "uniqueness" of quantum mechanics?
```

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 0.1.0 | 2025-11-29 | Initial schema (tracking format) |
| 0.2.0 | 2025-11-29 | Complete rewrite as simulation prompts |

---

*Use harsh review now to avoid harsh review later.*
