# CLAUDE.md

Essential guidance for Claude Code in this repository.

---

## Section 1: Critical Artifacts

**Read these FIRST for context and operating mode.**

### Core Operating Mode
- **`AI-Collaboration-Profile.json`** - General stance: skeptical, rigorous, helpful. OVERRIDES DEFAULTS.
- **`LRT-Collaboration-Addendum.md`** - LRT-specific: circularity checking, verification, quality standards.

### Theory Sources
- **`theory/2025-12-16_logic_realism_theory_foundation.md`** - Core unified framework
- **`theory/Comparison_Scorecard.md`** - LRT vs other approaches

### Lean Status (lean/)
- **`lean/AI_ROLE.md`** - AI operating mode for Lean development (read first for Lean work)
- **`lean/AXIOMS.md`** - Axiom count: 2 Tier 1 + ~16 Tier 2 + 1 Tier 3 = ~19
- **`lean/LogicRealismTheory.lean`** - Root import file (build status)
- **`lean/BEST_PRACTICES.md`** - Lean 4 development lessons

### Processes & Protocols (processes-protocols/)
- **`AI_METHODOLOGY.md`** - 10-phase development workflow
- **`SANITY_CHECK_PROTOCOL.md`** - **MANDATORY** verification checklist
- **`DEVELOPMENT_GUIDE.md`** - Architecture, commands, workflows

### Session Context
- **`Session_Log/Session_X.Y.md`** - Read LATEST (highest X.Y) for context
- **`sprints/README.md`** - If active sprint exists

### Derivations
- **`notebooks/D{tier}.{seq}-*.ipynb`** - Derivation notebooks (theory + computation)
- **`lean/LogicRealismTheory/Derivations/`** - Formal proofs
- **`theory/20251221-logic-realism-theory-refactor.md`** - Derivation chain tracking (14 derivations, 5 tiers)
- **MANDATORY**: Follow 2-stage pipeline (Notebook → Lean) per `LRT-Collaboration-Addendum.md`

---

## Section 2: Critical Protocols

### Session Startup
1. Read `AI-Collaboration-Profile.json` + `LRT-Collaboration-Addendum.md`
2. Read latest `Session_Log/Session_X.Y.md`
3. Skim relevant guides based on task

### Session Logging
- Create `Session_X.0.md` at start, update progressively
- Update READMEs at end of major sessions
- Push commits to GitHub

### Rolling Activity Log
Maintain `.claude/activity.log` as a rolling 500-line log of current work.

**Format** (one line per entry):
```
[YYYY-MM-DD HH:MM] ACTION: description
```

**Actions to log:**
- `SESSION_START` / `SESSION_END` - Session boundaries
- `TASK` - Major task started (e.g., "LaTeX standardization sweep")
- `EDIT` - Significant file changes (e.g., "Updated Position Paper §4.3")
- `COMMIT` - Git commits with hash
- `NOTE` - Important context for recovery

**Trim after each update** (keep last 500 lines):
```bash
tail -500 .claude/activity.log > .claude/activity.log.tmp && mv .claude/activity.log.tmp .claude/activity.log
```

**Purpose:** Enables recovery from unexpected terminations by preserving recent work context without accumulating unbounded history.

### Git Commits
- Commit incrementally during work
- Always include Claude Code attribution
- Push at milestones and session end

### Research Philosophy
- Default to problem-solving, not weakening claims
- Core thesis (A = L(I)) non-negotiable unless proven impossible
- Exhaust solutions before escalating

---

## Section 3: LRT Core Thesis

**The Three Fundamental Laws of Logic (3FLL) are constitutive of coherent reality:**
- Identity: ∀A: A = A
- Non-Contradiction: ∀A: ¬(A ∧ ¬A)
- Excluded Middle: ∀A: A ∨ ¬A

**Derivation hierarchy:**
```
3FLL → I + I_infinite → Distinguishability → Phase space → Physics
```

**Tier System:**
- Tier 1: Structural assumptions (I, I_infinite) - LRT-specific
- Tier 2: Established math (Stone, Gleason, Masanes-Müller) - standard tools
- Tier 3: Physical principles (conservation, additivity) - empirical

*For full tier documentation, see `lean/AXIOMS.md`*

---

## Section 4: Key Protocols (References)

### Sanity Check (MANDATORY)
Run `processes-protocols/SANITY_CHECK_PROTOCOL.md` after every track completion.

**Stop words** - don't use without verification:
- "Verified", "Proven", "Complete", "Formalized"

**Safe terms**:
- "Structured", "Builds successfully", "Axiom structure in place"

### Lean Verification
Before claiming "formalized/verified/proven":
```bash
grep -r "sorry" file.lean      # Any found → NOT formalized
grep "theorem.*True" file.lean  # Trivial → NOT real proof
```

*Full protocol in `LRT-Collaboration-Addendum.md`*

### archive/approach_2_reference/
- NEVER reference in public-facing code/docs
- Zero dependencies from LogicRealismTheory/

---

## Section 5: Quick Reference

**Author**: James D. (JD) Longmire (ORCID: 0009-0009-1383-7698)
**Email**: jdlongmire@outlook.com

**Status**: See `lean/AXIOMS.md` (axiom count) and `lean/LogicRealismTheory.lean` (build)

**Detailed docs**: See Critical Artifacts above - this file is intentionally lean.
