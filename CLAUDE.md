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
- **`lean/LRT_Comprehensive_Lean_Plan.md`** - Option C roadmap: 57 → 35-38 axioms (Sprints 13-15)
- **`lean/Ongoing_Axiom_Count_Classification.md`** - Complete 58 axiom inventory, classifications, **⚠️ AXIOM COUNT FRAMING**
- **`lean/LogicRealismTheory.lean`** - Root import file showing all modules

### Development Guides
- **`DEVELOPMENT_GUIDE.md`** - Architecture, commands, workflows, approach_2 protocol
- **`LEAN_BEST_PRACTICES.md`** - Lean 4 proof development lessons

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
2. Skim `DEVELOPMENT_GUIDE.md` and `LEAN_BEST_PRACTICES.md` (if relevant)
3. Skim `lean/LRT_Comprehensive_Lean_Plan.md` (if Lean work expected)
4. Read latest `Session_Log/Session_X.Y.md` (complete context)
5. Check `sprints/README.md` for active sprints

### Session Logging
- Create `Session_X.0.md` at session start
- **Update progressively** during work (rename to X.1, X.2, etc.)
- **DO NOT wait for user to ask** - update after each major task
- Final update before ending session
- Push commits to GitHub at major milestones

### Sprint Documentation
- Sprint folders contain **ONLY tracking documents** (no deliverables)
- All outputs go to canonical locations (notebooks/, lean/, multi_LLM/consultation/)
- Update sprint tracking daily

### Git Commits
- Only create commits when user requests
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

### Repository Structure
- Everything has ONE canonical location (see DEVELOPMENT_GUIDE.md for full structure)
- Never create alternative folders without updating CLAUDE.md

### approach_2_reference/ Protocol
- **NEVER reference** "approach_2" in public-facing code or documentation
- Use generic terminology: "established framework", "permutation-based framework"
- Zero dependencies on approach_2_reference in LogicRealismTheory/

---

## 📋 Quick Reference

**Author**: James D. (JD) Longmire (ORCID: 0009-0009-1383-7698)

**Current Status** (2025-11-03):
- Lean: 20 active files, 5,288 lines, 4 sorrys, 57 declarations (30-34 theory + 16 infrastructure)
- Target: 35-38 declarations (7-11 theory + 16 infrastructure) via Sprints 13-15
- Build: ✓ All files compile

**For detailed information on ANY topic, see the Critical Artifacts section above.**

---

**This CLAUDE.md is intentionally lean. All detailed framing, context, and instructions live in the artifacts listed in Section 1.**
