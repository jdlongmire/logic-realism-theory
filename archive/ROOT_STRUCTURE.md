# Repository Root Structure

**Purpose**: Document the organization and purpose of all root-level files and directories.

**Last Updated**: 2025-01-04 (Session 9.1)

---

## Root-Level Files

### Core Documentation (Methodology & Operations)

| File | Purpose | Audience | Update Frequency |
|------|---------|----------|------------------|
| **README.md** | Project overview, quick start, status summary | All users | After major milestones |
| **CLAUDE.md** | Operating instructions for Claude Code (AI collaboration) | Claude Code | As protocols evolve |
| **AI-Collaboration-Profile.json** | Critical review standards, rigor enforcement | Claude Code | Rare (foundational) |
| **DEVELOPMENT_GUIDE.md** | Architecture, workflows, repository structure | Developers | As architecture changes |
| **LEAN_BEST_PRACTICES.md** | Lean 4 proof development lessons learned | Lean developers | After major sprints |
| **SANITY_CHECK_PROTOCOL.md** | Verification protocol (6 checks) before completion claims | All contributors | As verification evolves |
| **LICENSE** | Apache 2.0 license | Legal/users | Stable |

**Placement Rationale**: Core documentation stays at root for maximum visibility and accessibility.

---

### Theory Documents (Primary Research Outputs)

| File | Purpose | Status | Audience |
|------|---------|--------|----------|
| **Logic_Realism_Theory_Main.md** | Complete theory paper (2,456 lines) - formalism, derivations, predictions | Living document | Physicists, peer reviewers |
| **Logic_Realism_Theory_AI_Experiment.md** | Methodology document - AI collaboration patterns, lessons learned | Active | Methodologists, AI researchers |
| **LRT_Current_Comparison_Scorecard.md** | Objective comparison LRT vs 7 other foundational theories | Living document | Physicists, evaluators |

**Placement Rationale**: Primary theory documents remain at root for visibility. These are the "papers" of the project - should be immediately accessible.

**Note**: Additional theory documents are in `theory/` subdirectory for specialized content.

---

## Root-Level Directories

### Core Directories

| Directory | Purpose | Contents | Canonical Location |
|-----------|---------|----------|-------------------|
| **lean/** | Lean 4 formalization | All .lean files, Mathlib deps, build configs | Yes - all Lean code here |
| **notebooks/** | Computational validation | Jupyter notebooks (01-13), simulations | Yes - all notebooks here |
| **theory/** | Detailed theory documents | Frameworks, derivations, supporting docs | Yes - theory elaborations |
| **Session_Log/** | Session-by-session logs | Session_X.Y.md files, session READMEs | Yes - ALL session docs here |
| **sprints/** | Sprint tracking | Sprint plans, tracking docs, deliverables refs | Yes - ALL sprint docs here |
| **multi_LLM/** | Multi-LLM consultations | Reviews, consensus analyses | Yes - all LLM team work here |

**Principle**: ONE canonical location per content type. No alternatives or duplicates.

---

### Supporting Directories

| Directory | Purpose | Update Frequency |
|-----------|---------|------------------|
| **scripts/** | Automation scripts | As needed (validation, conversion, etc.) |
| **docs/** | Additional documentation | As needed (guidelines, references) |
| **archive/** | Deprecated/superseded files | When files become obsolete |
| **audit/** | Historical audit documents | When audits performed |
| **.claude/** | Claude Code configuration | Rare (settings, preferences) |
| **.github/** | GitHub configuration | Rare (workflows, templates) |
| **approach_2_reference/** | Reference implementation (not used in LRT) | Stable (reference only) |

---

## File Disposition Rules

### ✅ Files That SHOULD Be at Root

**Core Documentation**:
- AI-Collaboration-Profile.json
- CLAUDE.md
- DEVELOPMENT_GUIDE.md
- LEAN_BEST_PRACTICES.md
- LICENSE
- README.md
- SANITY_CHECK_PROTOCOL.md

**Theory Documents** (primary papers):
- Logic_Realism_Theory_Main.md
- Logic_Realism_Theory_AI_Experiment.md
- LRT_Current_Comparison_Scorecard.md

**Total**: 10 files (7 docs + 3 theory)

---

### ❌ Files That Should NOT Be at Root

**Session Documents** → Move to `Session_Log/`:
- Session_X.Y_*.md files (unless they are major standalone documents)
- Session analysis or correction files
- Example: ~~Session_9.1_SYSTEMATIC_REVIEW_CORRECTIONS.md~~ → `Session_Log/`

**Sprint Documents** → Move to `sprints/sprint_X/`:
- Sprint_X_*.md files
- Sprint tracking, analysis, or correction files
- Example: ~~SPRINT_11_LEAN_STATUS_CORRECTION.md~~ → `sprints/sprint_11/`

**Theory Elaborations** → Move to `theory/`:
- Detailed derivation documents
- Framework specifications
- Supporting theory documents

**Notebooks** → Move to `notebooks/`:
- .ipynb files
- Computational validation

**Lean Files** → Move to `lean/`:
- .lean files
- Lean-specific documentation

---

## Maintenance Protocol

### When Adding New Files to Root

**Ask**:
1. Is this a **core methodology document** everyone needs to see?
   - Yes → Can stay at root
   - No → Move to appropriate subdirectory

2. Is this a **primary theory paper** for peer review?
   - Yes → Can stay at root
   - No → Move to `theory/` subdirectory

3. Is this a **session or sprint document**?
   - Yes → Move to `Session_Log/` or `sprints/sprint_X/`
   - No → Evaluate against #1-2

### Periodic Review (Quarterly)

**Check**:
- Are any root files obsolete? → Move to `archive/`
- Are any session/sprint files at root? → Move to correct directory
- Are any theory elaborations at root? → Move to `theory/`
- Is ROOT_STRUCTURE.md current? → Update if needed

**Last Review**: 2025-01-04 (Session 9.1)
**Next Review**: 2025-04-04 (or after Sprint 15)

---

## Repository Statistics (as of 2025-01-04)

**Root-Level Organization**:
- Core docs: 7 files
- Theory papers: 3 files
- Directories: 14
- **Total root files**: 10 (well-organized)

**Full Repository**:
- Lean files: 26 modules (~8,000 lines)
- Session logs: 50+ sessions documented
- Sprints: 12 completed, 4 planned
- Notebooks: 13 computational validations
- Theory docs: 15+ framework/derivation documents

---

## Historical Changes

### Session 9.1 (2025-01-04) - Root Organization
- **Moved**: `Session_9.1_SYSTEMATIC_REVIEW_CORRECTIONS.md` → `Session_Log/`
- **Moved**: `SPRINT_11_LEAN_STATUS_CORRECTION.md` → `sprints/sprint_11/`
- **Created**: `ROOT_STRUCTURE.md` (this file)
- **Created**: `LRT_Current_Comparison_Scorecard.md` (new theory document)
- **Result**: Root now has exactly 10 files (7 docs + 3 theory)

### Previous
- Root accumulated session/sprint files over time
- No clear disposition rules documented
- Occasional confusion about file locations

---

## Quick Reference: Where Does It Go?

| File Type | Canonical Location | Example |
|-----------|-------------------|---------|
| Session log | `Session_Log/` | `Session_9.1.md` |
| Session correction/analysis | `Session_Log/` | `Session_9.1_SYSTEMATIC_REVIEW_CORRECTIONS.md` |
| Sprint plan/tracking | `sprints/sprint_X/` | `SPRINT_12_TRACKING.md` |
| Sprint analysis/correction | `sprints/sprint_X/` | `SPRINT_11_LEAN_STATUS_CORRECTION.md` |
| Lean module | `lean/LogicRealismTheory/` | `Energy.lean` |
| Notebook | `notebooks/` | `01_Intro.ipynb` |
| Theory framework | `theory/frameworks/` | `LRT_Hierarchical_Emergence_Framework.md` |
| Theory derivation | `theory/derivations/` | `Born_Rule_Derivation.md` |
| Multi-LLM review | `multi_LLM/consultation/` | `Sprint_11_Track_2_Review.md` |
| Core methodology doc | **Root** | `SANITY_CHECK_PROTOCOL.md` |
| Primary theory paper | **Root** | `Logic_Realism_Theory_Main.md` |

---

**Principle**: One canonical location per content type. No duplicates, no ambiguity.

**When in doubt**: If it's not a core methodology document or primary theory paper, it probably belongs in a subdirectory.

---

**Maintained By**: Repository structure protocols
**Questions**: See DEVELOPMENT_GUIDE.md for full architecture details
