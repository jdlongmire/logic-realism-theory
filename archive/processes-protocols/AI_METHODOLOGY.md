# AI-Assisted Theory Development Methodology

**Author**: James (JD) Longmire
**Status**: Active methodology
**Purpose**: Document workflow for AI-assisted theoretical physics research

---

## Overview

This methodology combines AI assistance with human reasoning, formal verification, and community validation. AI systems assist with formalization and exploration; humans govern all decisions.

**Core Principle**: AI proposes, human disposes. Defense-in-depth verification catches different error types.

**Critical Starting Point**: Begin with a human-originated theoretical insight. AI assists with formalization, not theory generation.

---

## Development Stack

| Tool | Purpose |
|------|---------|
| Claude Code | Primary AI partner |
| Multi-LLM Bridge | Consultation (GPT, Gemini, Grok, Perplexity) |
| Lean 4 | Formal proof verification |
| Python/Jupyter | Computational validation |
| Git/GitHub | Version control |

---

## 10-Phase Process

```
Phase 1: Initial Development (Claude Code)
    ↓
Phase 2: Multi-LLM Adversarial Review
    ↓
Phase 3: Human Review and Decision
    ↓
Phase 4: Iteration Until Verified
    ↓
Phase 5: Repository Documentation
    ↓
Phase 6: SME Pre-Review (Community)
    ↓
Phase 7: Formal Verification (Lean 4)
    ↓
Phase 8: Final Polish
    ↓
Phase 9: Peer Review Submission
    ↓
Phase 10: Experimental Validation
```

**Any phase can return to Phase 1 if issues found.**

---

## Phase Details

### Phase 1: Initial Development

**Human provides**: Core insight, framework, key claims, domain context

**AI provides**: Mathematical exploration, code implementation, documentation, consistency checking

**Profile requirements**:
- Mandatory circularity checking
- Explicit justification for every step
- Citation discipline
- Escalation protocol for hard problems

### Phase 2: Multi-LLM Review

**Task**: Adversarial error detection (NOT confirmation)

AI systems actively search for:
- Circular dependencies
- Invalid citations
- Unjustified logical jumps
- Internal contradictions
- Misapplied theorems

**Quality threshold**: >= 0.70 consensus

### Phase 3: Human Review

**Primary question**: Does this track to truth?

**Checks**:
- Dependencies clean (no circular reasoning)?
- Citations accurate?
- Derivations actually follow from premises?
- Gaps acknowledged vs hidden?

### Phase 4: Iteration

Cycle through Phases 1-3 until:
1. No circularity detected
2. All claims verifiable
3. Internal consistency confirmed
4. Human confirms "tracks to truth"

### Phase 5: Documentation

- Upload papers to `theory/`
- Update tracking documents
- Commit to version control

### Phase 6: SME Pre-Review

**Venues**: Reddit (r/hypotheticalphysics), ArXiv, forums

**Purpose**: Find errors before formal peer review

**Request format**: Specific, falsifiable claims for verification

### Phase 7: Formal Verification

Lean 4 proofs for core derivations:
- Zero `sorry` statements on critical theorems
- Computer-verified logical correctness
- Available for community inspection

### Phase 8-10: Polish, Submit, Validate

- Final formatting for journal
- Peer review submission
- Track experimental predictions

---

## Human vs AI Contributions

| Human | AI | Collaborative |
|-------|-----|---------------|
| Strategic direction | Systematic exploration | Derivation development |
| Physical intuition | Infrastructure code | Problem decomposition |
| Final judgment | Documentation | Protocol refinement |
| Peer review response | Consistency checking | Error detection |

---

## Robustness Guarantees

### Against Hallucination
- Multi-LLM adversarial review
- Mandatory circularity checking
- Citation discipline
- Human verification
- Lean 4 proofs

### Against Confirmation Bias
- "Find errors" not "validate claims"
- Iteration expectation (finding issues = improvement)
- External validation (community, peer review)

### Against Logical Gaps
- Explicit justification requirement
- Proof structure review
- Lean 4 formalization

---

## Key Patterns

1. **Protocol-Driven Quality**: Explicit verification improves outcomes
2. **Infrastructure-First**: Complete structures before proofs
3. **Outcome-Focused**: Track results, not activity
4. **Explicit Terminology**: Define "complete," "verified," "proven" precisely

---

## Session Documentation

Every session documented with:
- What was attempted
- What succeeded/failed
- Decisions and rationale
- Lessons learned

All work committed to GitHub with complete history.

---

*Human-curated, AI-enabled.*
