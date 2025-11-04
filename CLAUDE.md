# CLAUDE.md

This file provides essential guidance for Claude Code working in this repository.

---

## 🎯 Section 1: Critical Artifacts

**These documents contain all framing information, context, and reference material. Read these FIRST.**

### Core Operating Mode
- **`AI-Collaboration-Profile.json`** - Your core role: hypercritical physicist/mathematician. THIS OVERRIDES ALL OTHER PROTOCOLS.

### Theory Sources of Truth (ROOT folder)
- **`Logic_Realism_Theory_Main.md`** (2,456 lines) - Complete theory paper: formalism, derivations, predictions
- **`Logic_Realism_Theory_AI_Experiment.md`** (602 lines) - Methodology, honest status assessment

### Lean Formalization Status (lean/ folder)
- **`lean/PROOF_REFACTOR_STRATEGY.md`** - **⚠️ ACTIVE** Complete proof refactor: 88 → 30-35 axioms, 5-phase bottom-up program from 2 foundation axioms
- **`lean/LRT_Comprehensive_Lean_Plan.md`** - Option C roadmap: 57 → 35-38 axioms (Sprints 13-15)
- **`lean/Ongoing_Axiom_Count_Classification.md`** - Complete 58 axiom inventory, classifications, **⚠️ AXIOM COUNT FRAMING**
- **`lean/LogicRealismTheory.lean`** - Root import file showing all modules

### Development Guides
- **`DEVELOPMENT_GUIDE.md`** - Architecture, commands, workflows, approach_2 protocol
- **`LEAN_BEST_PRACTICES.md`** - Lean 4 proof development lessons
- **`SANITY_CHECK_PROTOCOL.md`** - **⚠️ MANDATORY** track completion verification checklist

### Session Context
- **`Session_Log/Session_X.Y.md`** - Read LATEST session file (highest X.Y) for complete context
- **`sprints/README.md`** + **`sprints/sprint_X/SPRINT_X_TRACKING.md`** - If active sprint exists

### Theory Frameworks
- **`theory/frameworks/LRT_Hierarchical_Emergence_Framework.md`** - Formal mathematical framework for emergence

---

## ⚙️ Section 2: Critical Protocols

**Essential procedures. Keep these in mind, but detailed instructions live in the artifacts above.**

### Session Startup (Priority Order)
1. Read `AI-Collaboration-Profile.json` (your operating mode)
2. Read latest `Session_Log/Session_X.Y.md` (complete context - tells you what's needed)
3. Based on session context, skim relevant guides:
   - `DEVELOPMENT_GUIDE.md` or `LEAN_BEST_PRACTICES.md` (architecture/Lean work)
   - `lean/LRT_Comprehensive_Lean_Plan.md` (axiom/formalization work)
   - `sprints/README.md` + active sprint tracking (if sprint active)

### Session Logging
- Create `Session_X.0.md` at session start
- **Update progressively** during work (rename to X.1, X.2, etc.)
- **DO NOT wait for user to ask** - update after each major task
- **End of major session**: Update READMEs with current status:
  - Root `README.md`
  - `lean/README.md`
  - `notebooks/README.md` (if relevant)
  - `Session_Log/README.md` (session summary)
  - `sprints/README.md` (if sprint active)
- Final session log update before ending
- Push all commits to GitHub

### Sprint Documentation
- Sprint folders contain **ONLY tracking documents** (no deliverables)
- All outputs go to canonical locations (notebooks/, lean/, multi_LLM/consultation/)
- Update sprint tracking daily

### Git Commits
- Make incremental commits naturally during work (don't wait for permission)
- Push to GitHub at major milestones and end of session
- Follow git safety protocol (see DEVELOPMENT_GUIDE.md)
- Always include Claude Code attribution

### Research Philosophy
- **Default to collaborative problem-solving**, not weakening claims
- Core thesis (A = L(I)) is non-negotiable unless proven logically impossible
- Exhaust solutions before escalating to user

### Program Auditor
- Run before ANY claims about completion status
- Stop using "complete" without verification
- Cross-validate Lean ↔ computational ↔ theory claims

### Sanity Check Protocol ⚠️ MANDATORY
- **Run after EVERY track completion** before claiming success
- See **`SANITY_CHECK_PROTOCOL.md`** for full checklist
- 6 quick checks: Build, Proofs, Imports, Axiom count, Deliverable reality, Professional tone
- Prevents overclaiming: Distinguishes docs vs structure vs proofs
- Ensures professionalism: No celebration language, emojis, or superlatives before peer review
- Stop words: "Verified", "Proven", "Complete", "Formalized" (without verification)
- **When in doubt**: Run the check, report results to user BEFORE claiming completion

### Repository Structure
- Everything has ONE canonical location (see DEVELOPMENT_GUIDE.md for full structure)
- Never create alternative folders without updating CLAUDE.md

### approach_2_reference/ Protocol
- **NEVER reference** "approach_2" in public-facing code or documentation
- Use generic terminology: "established framework", "permutation-based framework"
- Zero dependencies on approach_2_reference in LogicRealismTheory/

### Lean Formalization Verification Protocol ⚠️ CRITICAL

**NEVER claim work is "formalized," "verified," or "proven in Lean" without running these checks:**

#### Status Verification Checklist

Before claiming ANY of these terms, you MUST verify:

**❌ FORBIDDEN TERMS** (unless ALL checks pass):
- "formalized in Lean"
- "verified in Lean"
- "proven in Lean"
- "formally verified"
- "Lean proof complete"
- "derivation verified"

**✅ SAFE TERMS** (for work in progress):
- "structured in Lean"
- "axiomatized in Lean"
- "type-checked in Lean"
- "builds successfully"
- "formal structure defined"
- "proof sketch documented"

#### Mandatory Verification Steps

**Before claiming "formalized/verified/proven":**

1. **Check for sorry statements**:
   ```bash
   grep -r "sorry" lean/LogicRealismTheory/path/to/file.lean
   ```
   - If ANY `sorry` found → NOT formalized, it's a STUB
   - Status: "Structured with proof obligations remaining"

2. **Check for trivial True proofs**:
   ```bash
   grep -A2 "theorem.*True :=" lean/LogicRealismTheory/path/to/file.lean
   ```
   - If theorem proves `True` with `trivial` → NOT the real theorem
   - Status: "Conceptual structure, formal proof needed"

3. **Verify theorem statements match claims**:
   - Does the theorem statement actually say what we claim?
   - Example: `theorem unitarity_from_3FLL : True` does NOT prove unitarity
   - Real theorem would be: `theorem unitarity_from_3FLL : ∀ U, U†U = I`

4. **Count actual axioms vs theorems**:
   ```bash
   grep "^axiom " file.lean | wc -l
   grep "^theorem" file.lean | wc -l
   # Theorems with 'sorry' or proving 'True' count as axioms!
   ```

#### Honest Status Reporting

**What "BUILD SUCCESS" actually means**:
- ✅ Lean syntax is valid
- ✅ Type checking passes
- ✅ No compilation errors
- ✅ Imports resolve correctly
- ❌ **DOES NOT MEAN** proofs are complete
- ❌ **DOES NOT MEAN** theorems are proven
- ❌ **DOES NOT MEAN** formal verification

**Correct phrasing examples**:

❌ **WRONG**: "Track 3 complete - Schrödinger equation formalized and verified in Lean"
✅ **RIGHT**: "Track 3 complete - Schrödinger equation derivation structured in Lean with axioms documented. Formal proofs: 0/3 complete (all use placeholders)."

❌ **WRONG**: "Born rule proven from 3FLL in Lean"
✅ **RIGHT**: "Born rule derivation chain documented. Lean structure: 4 axioms + 3 theorems with sorry placeholders. Informal arguments in markdown."

❌ **WRONG**: "100% formalized, 0 sorries"
✅ **RIGHT**: "Axiom structure complete, builds successfully. Formal proofs: pending (3 sorry statements)."

#### Axiom Counting Rules

**If a theorem uses `sorry` or proves `True` trivially**:
- It MUST be counted as an effective axiom
- Axiom count includes: `axiom` declarations + unproven `theorem` declarations
- Be transparent: "X axioms declared, Y theorems with proof obligations"

#### Session Documentation Rules

**When documenting Lean work, you MUST**:
1. Distinguish "structure" from "proof"
2. Report sorry count explicitly
3. Report trivial True theorem count explicitly
4. Never say "verified" unless proofs are complete
5. Use accurate language: "axiomatized," not "proven"

**Session log template**:
```markdown
## Lean Status

**File**: Module.lean (X lines)
**Build Status**: ✅ Compiles (X jobs)
**Structure**:
- X axiom declarations
- Y theorem declarations (Z with sorry, W with trivial True proofs)
- Actual formal proofs complete: N/Y

**Honest Assessment**:
- Axiom structure documented ✅
- Type signatures defined ✅
- Formal verification: ⏸️ Pending (Y proof obligations)
```

#### Why This Matters

**Credibility risk**: Claiming "formal verification" when only axioms + placeholders exist:
- Undermines trust in all claims
- Misrepresents state of formalization
- Creates vulnerability in peer review
- Conflates "builds" with "proves"

**Philosophy**: Honest documentation of limitations is strength, not weakness. Better to say "structured with proof obligations" than claim false verification.

---

## 📋 Quick Reference

**Author**: James D. (JD) Longmire (ORCID: 0009-0009-1383-7698)

**Current Status**: See `lean/LogicRealismTheory.lean` (build status comments) and `lean/Ongoing_Axiom_Count_Classification.md`

**For detailed information on ANY topic, see the Critical Artifacts section above.**

---

**This CLAUDE.md is intentionally lean. All detailed framing, context, and instructions live in the artifacts listed in Section 1.**
