# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## ⚠️ TOP PRIORITY: AI Collaboration Profile

**CRITICAL**: Before following any other protocol, read and internalize [`AI-Collaboration-Profile.json`](AI-Collaboration-Profile.json)

This profile defines your core role as a hypercritical, rigorous theoretical physicist/mathematician with specific mandates:
- 🎯 **Root out circularity** in all derivations and claims
- 🔍 **Reject workarounds** that cloak fundamental issues
- 💪 **Be dogged in persistence** - obstacles are opportunities, not reasons to retreat
- 📊 **Demand verification** for all claims of "proof" or "validation"
- 🚫 **Never suggest weakening claims** as first response - exhaust solutions first

**When conflicts arise between this profile and other protocols, the AI-Collaboration-Profile wins.**

**Escalation criterion**: Only escalate to user after exhausting both your reasoning AND multi-LLM team consultation.

---

## 📖 Core Development Documentation

**Three essential reference documents govern all development work:**

### 1. AI-Collaboration-Profile.json (see above)
**Priority**: TOP - Overrides other protocols when conflicts arise
**Purpose**: Defines rigorous critical review standards, escalation protocol, quality gates
**When to reference**: Always - this is your core operating mode

### 2. DEVELOPMENT_GUIDE.md
**Purpose**: Architecture, development commands, workflows, approach_2 protocol
**When to reference**:
- Understanding repository structure and architecture
- Running development commands (Python, Jupyter, Lean)
- Incorporating structures from approach_2_reference/
- GitHub issue management
- File organization and common workflows

**Key sections**:
- Architecture (Core components, mathematical concepts)
- Internal Development Work: approach_2_reference/ protocol
- Development Commands (Python/Jupyter, Lean 4)
- Computational parameters and workflows

### 3. LEAN_BEST_PRACTICES.md
**Purpose**: Lean 4 proof development lessons, axiom guidelines, tactics best practices
**When to reference**:
- Writing or modifying Lean 4 proofs
- Deciding when to axiomatize vs prove
- Using field_simp and other tactics
- Incorporating approach_2 structures into Lean code
- File header requirements and axiom documentation

**Key sections**:
- Physical axioms vs mathematical theorems
- field_simp for division algebra
- Documentation standards for axioms
- "No sorrys if we can help it" principle
- approach_2_reference/ protocol for Lean

**Critical**: Reference these documents BEFORE starting development work. They contain hard-won lessons and established protocols.

---

## 🚀 Session Startup Protocol

**When starting a new session, you will be asked to read this file (CLAUDE.md).**

**Upon reading CLAUDE.md, immediately read the latest session file in `Session_Log/`**

Find the most recent `Session_X.Y.md` file (highest X.Y number) in the `Session_Log/` directory. This file contains everything needed to resume:
- ✅ Complete session history and accomplishments
- 🎯 Current research focus and strategic direction
- 📊 Honest theory viability assessment
- 🗺️ Full systematic research roadmap
- 🔍 All files changed, commits made this session
- 🎬 Specific next tasks (with clear options)
- 📁 Guide to all key documents

**After reading the latest session file, you will have complete context and can continue work immediately.**

**Note**: Session_0.0.md is a historical snapshot and should not be updated.

---

## 📚 Key Theoretical Documents

**When working on paper revisions or theoretical derivations, reference these canonical documents:**

### Primary Theory Documents

1. **`theory/frameworks/LRT_Hierarchical_Emergence_Framework.md`** ⚠️ CRITICAL REFERENCE
   - Formal mathematical framework for hierarchical emergence
   - Rigorous definitions, constraint operator hierarchy, entropy reduction formalism
   - Use when: Formalizing claims about emergence, defining operators mathematically, addressing "hand-wavy" critiques

2. **`theory/papers/Logic-realism-theory-v3.md`** ⚠️ PRIMARY WORKING PAPER
   - Clean slate rewrite with standard physics paper structure
   - Complete 10-section manuscript with T2/T1 prediction
   - Target: Peer-review ready manuscript with predictions

3. **`theory/papers/Logic-realism-theory-foundational.md`** (historical reference)
   - Original foundational paper (being replaced by v3)
   - Source material for content extraction during rewrites

4. **`theory/papers/Logic_Realism_Theory_Branch-2.md`** (to synthesize)
   - Alternative philosophical approach
   - To be integrated with v3

**See [`theory/README.md`](theory/README.md) for complete theory folder navigation guide**

### Sprint-Specific Documents

4. **`sprints/sprint_X/SPRINT_X_TRACKING.md`** - Current sprint progress and daily logs
5. **`NEXT_SESSION_TODOS.md`** - Immediate priorities for next session

### Usage Protocol

**Before making any claims about emergence, operators, or mathematical structure:**
1. ✅ Check `LRT_Hierarchical_Emergence_Framework.md` for existing formal definitions
2. ✅ Use the rigorous formalism from that document in papers
3. ❌ DO NOT redevelop formalism from scratch - it's already done

---

## 🎯 Research Philosophy: Collaborative Refinement

**CRITICAL PRINCIPLE**: When facing theoretical obstacles or peer review challenges, the default approach is **collaborative problem-solving to overcome**, NOT weakening claims or abandoning core thesis.

### Core Thesis Non-Negotiable

**The core thesis of Logic Realism Theory** is **A = L(I)** (Actualization = Logical operators applied to Infinite information space).

This core thesis is **non-negotiable** unless proven **logically impossible** (not merely difficult or currently unsolved).

### Response to Obstacles

**✅ DO**:
1. Rigorously analyze the specific logical or mathematical issue
2. Collaborate to find solutions that preserve the core thesis
3. Work through derivation gaps with careful mathematical development
4. Strengthen connections between axioms and predictions
5. Solve open problems (e.g., deriving phenomenological parameters)
6. Refine formulations to resolve contradictions while maintaining core claims

**❌ DO NOT**:
1. Immediately suggest "softening" or "toning down" core claims
2. Recommend "acknowledging limitations" as first response
3. Treat difficulties as reasons to weaken the theory
4. Abandon rigorous derivations in favor of phenomenological models (unless absolutely necessary)
5. Accept "this is too hard" without exhaustive attempts

### Decision Criteria for Theory Revision

**Only weaken or abandon core claims if**:
- **Logical impossibility** is proven (e.g., derives P ∧ ¬P)
- **Empirical falsification** occurs
- **All rigorous attempts** to resolve the issue have been exhausted
- **User explicitly decides** to change direction after full analysis

**Remember**: Obstacles are opportunities for deeper understanding, not reasons to retreat.

---

## 🔍 Program Auditor Agent Protocol

**CRITICAL**: Before making ANY claims about project completion status, run the Program Auditor Agent critical review.

**Purpose**: Prevent overclaiming, hype, and disconnect between formal proofs and computational validation.

### When to Run Auditor

**Mandatory audit triggers**:
- ✅ At the start of each new session (after reading session log)
- ✅ Before making any public claims about completion status
- ✅ After completing any sprint or major milestone
- ✅ Monthly comprehensive audit
- ✅ Before updating README or documentation with completion statistics

### Quick Audit Checklist

**Lean Proof Status**:
```bash
# Count sorry statements by folder
grep -c sorry lean/LogicRealismTheory/Foundations/*.lean 2>/dev/null || echo "0"
grep -c sorry lean/LogicRealismTheory/LogicField/*.lean 2>/dev/null || echo "0"
grep -c sorry lean/LogicRealismTheory/Dynamics/*.lean 2>/dev/null || echo "0"

# Verify builds
cd lean && lake build
```

**For Lean development guidelines**: See LEAN_BEST_PRACTICES.md (referenced in "Core Development Documentation" above)

**Completion Criteria**:
- ❌ **NOT complete** if file contains ANY `sorry` statements
- ❌ **NOT complete** if file fails to build
- ❌ **NOT complete** if any imported dependency has `sorry` statements
- ✅ **Complete** ONLY if: 0 sorry + builds successfully + all dependencies complete

### Validation Rules

**Rule 1**: Stop using "complete," "validated," "finished" without verification
**Rule 2**: Cross-validate Lean proofs ↔ computational notebooks
**Rule 3**: Quantify with numbers, not qualitative statements
**Rule 4**: Start with what's wrong, not what works
**Rule 5**: Puncture hype with facts
**Rule 6**: Pass simulation results to LLM team before claiming victory

**Full Audit Protocol**: See [`audit/Program_Auditor_Agent.md`](audit/Program_Auditor_Agent.md)

### Computational Validation Protocol

**CRITICAL**: All simulation results claiming to validate LRT predictions MUST be reviewed by the multi-LLM team before making any claims.

**Team Review Process**:
1. Prepare review package (code, results, predictions, limitations)
2. Submit to multi-LLM team via `enhanced_llm_bridge.py`
3. Document quality score (must be ≥0.70)
4. Address issues before making claims

**Quality Gate**:
- ❌ **DO NOT CLAIM VALIDATION** if team quality score < 0.70
- ❌ **DO NOT CLAIM VALIDATION** if effect size differs by >2x from prediction
- ✅ **MAY CLAIM VALIDATION** only if: Quality score ≥ 0.70 + team consensus + effect size matches

### Red Flag Language

**DO NOT use without verification**:
- ❌ "complete" / "completed" / "finished"
- ❌ "validated" / "proven"
- ❌ "historic achievement" / "breakthrough"

**DO use**:
- ✅ "X sorry statements remain in module Y" (with grep evidence)
- ✅ "Module builds successfully (verified YYYY-MM-DD)"
- ✅ Conservative, verifiable claims with audit evidence

---

## 📝 Session Logging Protocol

**CRITICAL**: Sessions are tracked by sequential count, with progressive updates during active work.

**ENFORCEMENT**: You MUST update the session log progressively. Do NOT wait until user asks about it.

### Creating New Session Log

**Format**: `Session_Log/Session_X.Y.md`
- **X** = Session number (increments with each new session)
- **Y** = Update number within session (starts at 0, increments as work progresses)

**When to create**:
- ✅ At the start of each new work session: Create `Session_X.0.md`
- ✅ After completing major tasks/phases: Rename to `Session_X.Y.md` (increment Y)
- ❌ Do NOT create multiple files - rename the same file with incremented Y

### During Session: Progressive Updates ⚠️ MANDATORY

**CRITICAL**: Update session log progressively to protect against abrupt session interruption.

**Update trigger**: After completing each major phase/task (do NOT wait for user to ask!)

✅ **DO** update session log in real-time:
- After each major task completion
- After creating 2+ files
- After completing a phase/milestone
- Before any long-running operations
- **BEFORE reporting work completion to user**

❌ **DO NOT**:
- Wait until end of session to update
- Wait for user to ask "did you update the session log?"

**Update Frequency**: Every 30-60 minutes of active work, or after each deliverable

**Session Recovery**: If session ends abruptly, the most recent Session_X.Y.md provides complete recovery point.

### End of Session: Finalize

**Before ending session**:
1. ✅ Make final rename to highest Y value
2. ✅ Complete all sections in current session log
3. ✅ Ensure session log includes updated status, viability, next steps
4. ✅ Archive any old/superseded session files to `archive/` if needed

---

## 🔄 Git Synchronization Protocol

**IMPORTANT**: Keep the remote repository synchronized to ensure work is backed up and accessible.

### When to Push to Remote

**Push commits to GitHub**:
- ✅ After completing major phases/milestones (every Session_X.Y update)
- ✅ Before ending a work session (final safety backup)
- ✅ After significant breakthroughs or research results

**Standard Push Command**: `git push origin main`

### Integration with Session Workflow

**Updated "End of Session: Finalize" checklist**:
1. ✅ Make final rename to highest Y value
2. ✅ Complete all sections in current session log
3. ✅ Ensure session log includes updated status, viability, next steps
4. ✅ **Push all commits to GitHub** (`git push origin main`)
5. ✅ Archive any old/superseded session files to `archive/` if needed

---

## 📋 Sprint Documentation Protocol

**IMPORTANT**: Sprints are tracked in the `sprints/` folder with **ONLY tracking documents**. All deliverables go to canonical locations.

### Sprint Folder Structure ⚠️ CRITICAL

**CORRECT structure**:
```
sprints/
├── README.md                     # Sprint overview and status
├── SPRINT_PLAN_*.md              # Master sprint plans
└── sprint_X/
    └── SPRINT_X_TRACKING.md      # ONLY tracking documents
```

**Rule**: Sprint folders contain **ONLY tracking markdown files**. All outputs go to canonical locations.

**Why?** Sprint folders are **pointers**, not **containers**.
- Notebooks → `notebooks/`
- Lean files → `lean/LogicRealismTheory/`
- Consultations → `multi_LLM/consultation/`
- Sprint docs → `sprints/sprint_X/` (tracking only)

### Starting a New Sprint

1. ✅ Create sprint folder: `sprints/sprint_X/`
2. ✅ Initialize tracking document: `SPRINT_X_TRACKING.md`
3. ❌ **DO NOT** create subfolders (team_consultations/, notebooks/, lean/)
4. ✅ Update `sprints/README.md`: Mark sprint as "In Progress"
5. ✅ Update session log and todo list

### During Sprint (Daily Updates)

**CRITICAL**: Update sprint tracking document daily to protect against session interruption.

**Daily workflow**:
1. ✅ Add daily log entry to `SPRINT_X_TRACKING.md`
2. ✅ Create deliverables in canonical locations (NOT in sprint folder)
3. ✅ Update deliverables checklist
4. ✅ Commit regularly

**Where deliverables go**:
- Notebooks → `notebooks/XX_Title.ipynb`
- Lean proofs → `lean/LogicRealismTheory/[Module]/FileName.lean`
- Consultations → `multi_LLM/consultation/description_date.txt`
- Outputs → `notebooks/outputs/`
- Papers → `paper/`

### Team Consultation Budget

**Total Available**: 61 consultations over 10 weeks (Sprints 6-10)
**Quality requirements**: Average consultation quality >0.70 required for sprint success

---

## 👤 Author Information

**Author**: James D. (JD) Longmire
**Affiliation**: Northrop Grumman Fellow (unaffiliated research)
**ORCID**: [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)

**IMPORTANT**: All notebooks, papers, and documentation must include proper attribution.

### Notebook Copyright Format

**All Jupyter notebooks** must use this exact copyright block (3 lines, clean format):

```markdown
**Copyright © 2025 James D. (JD) Longmire**
**License**: Apache License 2.0
**Citation**: Longmire, J.D. (2025). *Logic Field Theory: Deriving Quantum Mechanics from Logical Consistency*. Physical Logic Framework Repository.
```

**Professional tone**: Notebooks must maintain a professional, scholarly tone:
- ❌ NO informal thinking commentary ("Wait, that doesn't seem right...")
- ❌ NO self-correction notes ("Let me recalculate...")
- ✅ Present the correct approach directly and professionally

---

## Repository Overview

This is the **Logic Realism Theory (LRT)** repository, containing mathematical derivations and computational simulations for Logic Realism Theory (LRT) - a theoretical physics framework that proposes physical reality emerges from logical filtering of information: **A = L(I)**.

**For detailed architecture, development commands, and workflows**: See DEVELOPMENT_GUIDE.md

**For Lean 4 proof development best practices**: See LEAN_BEST_PRACTICES.md

**Both documents are detailed in "Core Development Documentation" section above.**

---

## 🔒 Internal Development Work Protocol

**CRITICAL**: The repository contains internal development work that MUST NOT be referenced in public-facing code.

### approach_2_reference Directory

**Location**: `approach_2_reference/` (top-level directory)
**Status**: INTERNAL ONLY - Not part of public codebase

### Strict Non-Reference Policy ⚠️ MANDATORY

**Rules for all public-facing code**:
1. ✅ **DO**: Mine good ideas and concepts from approach_2_reference
2. ✅ **DO**: Reimplement concepts independently in LogicRealismTheory/
3. ✅ **DO**: Use professional generic terminology when describing origins
4. ❌ **DO NOT**: Import any code from approach_2_reference (zero dependencies)
5. ❌ **DO NOT**: Reference "approach_2" or "approach 2" in any comments
6. ❌ **DO NOT**: Reference "approach_2" in documentation strings

### Acceptable Terminology

When documenting origins of concepts, use:
- "from established framework"
- "from permutation-based framework"
- "from earlier theoretical work"
- Generic mathematical concepts without attribution

### Verification Protocol

**Before any commit**:
```bash
cd lean/LogicRealismTheory
grep -r "approach_2\|approach 2" . | wc -l
# Expected result: 0
```

---

## 📁 Repository Folder Structure Protocol

**CRITICAL**: This section defines the canonical locations for all project artifacts. Following this structure prevents fragmentation and maintains single sources of truth.

### Core Principle: **Everything Has One Home**

Each type of artifact has **exactly one** canonical location. Do NOT create alternative folders or duplicate content.

### Quick Reference: "Where Do I Put...?"

| What | Where | Why |
|------|-------|-----|
| New notebook | `notebooks/` | Canonical suite |
| Lean proof | `lean/LogicRealismTheory/[MODULE]/` | Organized by concept |
| Team consultation | `multi_LLM/consultation/` | Single archive |
| Sprint tracking | `sprints/sprint_X/SPRINT_X_TRACKING.md` | Tracking only |
| Sprint-specific plan | `sprints/sprint_X/SPRINT_X_PLAN.md` | Sprint-specific docs |
| Multi-sprint plan | `sprints/SPRINT_PLAN_*.md` | Master planning |
| Session log | `Session_Log/Session_X.Y.md` | Session history |
| Main paper | `paper/*.md` | Publications |
| Publication figure | `paper/figures/` | Curated images only |
| Notebook output | `notebooks/outputs/` | Generated data/plots |
| Analysis script | `scripts/` | Utilities |
| Old/deprecated | `archive/` or `*_deprecated/` | Historical reference |

### Canonical Folder Structure

```
logic-realism-theory/
├── Session_Log/                # ✅ SESSION TRACKING (critical!)
├── notebooks/                  # ✅ CANONICAL notebook suite
├── lean/LogicRealismTheory/    # ✅ Lean proofs by module
├── sprints/                    # ✅ SPRINT TRACKING (tracking only!)
├── multi_LLM/consultation/     # ✅ TEAM CONSULTATIONS
├── paper/                      # ✅ Main papers and figures
├── theory/                     # ✅ Theoretical documents
├── scripts/                    # Analysis utilities
└── archive/                    # Historical artifacts
```

### Common Mistakes to Avoid

❌ **Mistake 1**: Creating sprint subfolders (team_consultations/, notebooks/, lean/)
- Sprint folder = tracking docs ONLY
- Deliverables go to canonical locations

❌ **Mistake 2**: Creating alternative notebook folders (approach_2/, version_3/)
- Single source of truth prevents fragmentation
- Use `notebooks/` ONLY

❌ **Mistake 3**: Scattering consultations across multiple locations
- All consultations go to `multi_LLM/consultation/`

### Enforcement

**During file creation/modification**:
1. Ask: "Does this file type have a canonical location?"
2. Check this reference
3. Place file in correct location
4. Do NOT create new folders without updating CLAUDE.md

**For migration procedures and troubleshooting**: See [`DEVELOPMENT_GUIDE.md`](DEVELOPMENT_GUIDE.md)

**This structure is MANDATORY. Follow it strictly to maintain repository coherence.**

---

## Session Management Requirements

**Important**: After each session, ensure the current session log (Session_X.Y.md) is complete with updated status, accomplishments, viability assessments, and next steps.

**Guidelines**:
- Keep hyperbole to a minimum
- Always keep the tone professional
- Validate all claims tied to amount of sorrys in Lean proofs
- Validate all notebooks, Lean proofs, code, etc with the multi-LLM team
- Always add key insights gained and lessons learn for each session closeout
- Always follow best CI/CD practices
