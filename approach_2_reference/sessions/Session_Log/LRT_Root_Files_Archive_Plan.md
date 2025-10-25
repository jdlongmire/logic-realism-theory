# LRT Root Files Archive Plan

**Date**: October 25, 2025
**Purpose**: Systematically archive Approach 2 root documentation and preserve essential tools
**Context**: Creating clean LRT repository while preserving valuable Approach 2 artifacts

---

## Strategy

**Archive Approach 2 root docs** → `approach_2_reference/root_docs/`
**Archive ALL Approach 2 papers** → `approach_2_reference/papers/` ⚠️
**Write ONE fresh LRT paper** → `theory/Logic_Realism_Theory.md` (NORTH STAR) ⚠️
**Keep essential tools** → LRT root (multi_LLM/, Program_Auditor_Agent.md)
**Adapt core docs** → LRT root (README.md, CLAUDE.md)

### Key Insight: Papers

**ALL Approach 2 papers go to archive**:
- It_from_Logic_Scholarly_Paper.md
- Logic_Realism_Foundational_Paper.md
- Logic_Realism_Theory_Foundational.md
- figures/, supplementary/, potential_extensions/

**LRT has ONE new paper** (north star):
- `theory/Logic_Realism_Theory.md`
- Written FRESH with LRT framing
- Philosophy first, operator formalism second, S_N as example third
- References Approach 2 computational results (cite, don't duplicate)
- Clean narrative: 5-7 axioms, 9 notebooks, β prediction

---

## Approach 2 Root Files (To Archive)

### Files Found in PLF Root

```
AXIOM_HONESTY_AUDIT.md
DISCUSSIONS_WELCOME.md
FALSIFICATION_CRITERIA.md
FOUNDATIONAL_RATIONALE_v2.md
K_N_LITERATURE_SEARCH_RESULTS.md
LEAN_PROOF_INVENTORY.md
LEAN_REMEDIATION_SPRINT_PLAN.md
LEAN_STATUS_REPORT.md
MISSION_STATEMENT.md
MISSION_STATEMENT_v1.1.md
NEXT_SESSION.md
PLF_CONTRIBUTION_ASSESSMENT.md
PROJECT_OVERVIEW.md
README.md (Approach 2 version)
REPOSITORY_SURVEY_2025_10_09.md
RESEARCH_ROADMAP.md
SCOPE_AND_LIMITATIONS.md
SPRINT_14_3_TYPE_B_ELIMINATION.md
```

### Classification

**Category 1: Approach 2 Strategic Documents** (archive as-is)
- ✅ MISSION_STATEMENT.md (and v1.1) - Approach 2 mission
- ✅ PROJECT_OVERVIEW.md - Approach 2 overview
- ✅ SCOPE_AND_LIMITATIONS.md - Approach 2 scope
- ✅ RESEARCH_ROADMAP.md - Approach 2 roadmap
- ✅ README.md - Approach 2 README (replace with LRT version)

**Category 2: Honesty/Assessment Documents** (archive, valuable lessons)
- ✅ AXIOM_HONESTY_AUDIT.md - Session 14.3+ axiom transparency
- ✅ PLF_CONTRIBUTION_ASSESSMENT.md - Session 14.6 honest assessment
- ✅ K_N_LITERATURE_SEARCH_RESULTS.md - Literature context (A001892)
- ✅ FALSIFICATION_CRITERIA.md - Testability framework
- ✅ FOUNDATIONAL_RATIONALE_v2.md - Philosophical foundation

**Category 3: Technical Status Documents** (archive, historical record)
- ✅ LEAN_PROOF_INVENTORY.md - Axiom/sorry counts
- ✅ LEAN_STATUS_REPORT.md - Lean build status
- ✅ LEAN_REMEDIATION_SPRINT_PLAN.md - Sprint planning
- ✅ SPRINT_14_3_TYPE_B_ELIMINATION.md - Sprint documentation
- ✅ REPOSITORY_SURVEY_2025_10_09.md - Repo structure

**Category 4: Meta Documents** (archive)
- ✅ NEXT_SESSION.md - Approach 2 next steps
- ✅ DISCUSSIONS_WELCOME.md - Community guidelines

**Total**: 20+ root markdown files to archive

---

## Essential Tools (Keep in LRT)

### 1. Program Auditor Agent ⚠️ CRITICAL

**File**: `Program_Auditor_Agent.md`
**Current location**: PLF root
**LRT location**: LRT root (adapted)

**Why keep**:
- Prevents overclaiming (Session 14.3 lesson learned)
- Enforces honesty about axiom counts, sorry statements
- Critical for maintaining integrity

**Adaptations for LRT**:
```markdown
# Program Auditor Agent (LRT)

**Updated for Logic Realism Theory**

## Core Audit Protocol

**Lean verification**:
```bash
# LRT axiom count (target: 5-7)
grep -c "^axiom\|^noncomputable axiom" lean/LogicRealismTheory/Foundation/*.lean

# LRT sorry count (target: 0)
grep -c "sorry" lean/LogicRealismTheory/**/*.lean

# LRT build status
cd lean && lake build
```

**Comparison to Approach 2**:
- Approach 2: 140 axioms, 0 sorry (archived in approach_2_reference/)
- LRT target: 5-7 axioms, 0 sorry

**Red flag language** (same as before):
- ❌ "complete" without verification
- ❌ "X modules with 0 sorry" without grep evidence
- ✅ Use conservative, verifiable claims

**Integration with Session Startup**:
1. Read CLAUDE.md
2. Read latest Session_X.Y.md
3. **Run quick audit** (grep for sorry, verify build)
4. Update understanding with audit results
5. Continue work with honest baseline
```

**Enhancements**:
- Add LRT-specific paths
- Reference Approach 2 as baseline (140 axioms achieved, now improving)
- Update audit commands for LogicRealismTheory structure

---

### 2. Multi-LLM System ⚠️ CRITICAL

**Folder**: `multi_LLM/`
**Current location**: PLF root
**LRT location**: LRT root (same structure)

**Why keep**:
- Team consultation capability (Grok-3, GPT-4, Gemini-2.0)
- Quality scoring and caching
- Sprint consultation protocol (Sprints 6-10 planned with 61 consultations)
- Proven valuable in Approach 2 development

**Structure**:
```
multi_LLM/
├── enhanced_llm_bridge.py          # Main consultation system
├── claude_llm_bridge.py            # Claude integration
├── health_check.py                 # API health monitoring
├── test_enhanced_bridge.py         # System tests
├── api_config.json                 # API credentials (gitignored)
├── api_config_template.json        # Template for setup
├── llm_cache.db                    # Response cache (~50% hit rate)
├── consultation/                   # Results archive
│   └── (populated during sprints)
├── consultation_prompts/           # Prompt templates
└── README.md, README_CLI.md        # Documentation
```

**Adaptations for LRT**:
- Update README.md to reference LRT (not PLF)
- Add LRT-specific consultation templates
- Reference LogicRealismTheory Lean structure in prompts
- Keep consultation budget (61 consultations, ~40-45 actual API calls)

**Integration with LRT**:
- Sprint 6-10 consultations (if user wants sprints)
- Lean proof reviews (for 5-7 axioms strategy)
- Notebook validation (9 notebooks)
- Paper reviews (LRT paper)

---

## LRT Root Structure (Complete)

```
logic-realism-theory/
├── README.md                           # LRT project overview (NEW)
├── LICENSE                             # Apache 2.0 (same)
├── .gitignore                          # Python, Lean, OS files (NEW)
├── CLAUDE.md                           # LRT instructions (adapted from PLF)
├── Program_Auditor_Agent.md            # Audit protocol (adapted from PLF) ⚠️
│
├── multi_LLM/                          # Team consultation system ⚠️
│   ├── enhanced_llm_bridge.py          # COPY from PLF
│   ├── claude_llm_bridge.py            # COPY from PLF
│   ├── health_check.py                 # COPY from PLF
│   ├── test_enhanced_bridge.py         # COPY from PLF
│   ├── test_suite.py                   # COPY from PLF
│   ├── api_config_template.json        # COPY from PLF
│   ├── api_config.json                 # User creates (gitignored)
│   ├── llm_cache.db                    # Starts fresh
│   ├── consultation/                   # Results folder
│   ├── consultation_prompts/           # COPY from PLF
│   ├── README.md                       # Adapted for LRT
│   └── README_CLI.md                   # COPY from PLF
│
├── theory/                             # Papers
├── lean/                               # Formal proofs
├── notebooks/                          # Computational validation
│
├── approach_2_reference/               # Approach 2 archive
│   ├── README_APPROACH_2.md            # Archive overview
│   ├── LESSONS_LEARNED.md              # Explicit lessons
│   ├── root_docs/                      # Root markdown files ⚠️ NEW
│   │   ├── AXIOM_HONESTY_AUDIT.md
│   │   ├── PLF_CONTRIBUTION_ASSESSMENT.md
│   │   ├── K_N_LITERATURE_SEARCH_RESULTS.md
│   │   ├── MISSION_STATEMENT.md
│   │   ├── README.md (Approach 2 version)
│   │   └── (all other root .md files)
│   ├── lean/                           # 140 axioms, 0 sorry
│   ├── notebooks/                      # 25 notebooks
│   ├── papers/                         # Session 14 papers
│   └── sessions/                       # Sessions 1-15 logs
│
├── docs/                               # Extended documentation
├── Session_Log/                        # Session tracking
└── archive/                            # Historical artifacts
```

---

## Updated Setup Procedure

### Phase 2.5: Essential Tools (NEW)

**Step 2.5.1: Adapt Program_Auditor_Agent.md**

Source: `physical_logic_framework/Program_Auditor_Agent.md`

Action:
1. Copy to LRT root
2. Update paths:
   - `lean/LFT_Proofs` → `lean/LogicRealismTheory`
   - Module names: `PhysicalLogicFramework` → `LogicRealismTheory`
3. Update axiom baseline:
   - Add note: "Approach 2 achieved: 140 axioms, 0 sorry (archived)"
   - Target: "LRT target: 5-7 axioms, 0 sorry"
4. Update audit commands for LogicRealismTheory structure
5. Keep all red flag language and integrity protocols

**Step 2.5.2: Copy multi_LLM system**

Source: `physical_logic_framework/multi_LLM/`

Action:
```bash
# Copy entire multi_LLM folder
cp -r physical_logic_framework/multi_LLM logic-realism-theory/

# Update README.md for LRT
# (replace PLF references with LRT)

# Create fresh cache (don't copy old one)
rm logic-realism-theory/multi_LLM/llm_cache.db
touch logic-realism-theory/multi_LLM/llm_cache.db

# User will create api_config.json from template
# (not copied, as it contains credentials)
```

**Step 2.5.3: Update .gitignore**

Add to `.gitignore`:
```
# Multi-LLM
multi_LLM/api_config.json
multi_LLM/llm_cache.db
multi_LLM/__pycache__/
```

---

### Phase 6: Approach 2 Archive (UPDATED)

**Step 6.1: Copy Approach 2 content**
```bash
# Copy Lean proofs
cp -r physical_logic_framework/lean/LFT_Proofs logic-realism-theory/approach_2_reference/lean/

# Copy notebooks
cp -r physical_logic_framework/notebooks/Logic_Realism logic-realism-theory/approach_2_reference/notebooks/

# Copy ALL papers (archive everything, LRT will have ONE new paper)
cp -r physical_logic_framework/paper logic-realism-theory/approach_2_reference/papers/

# Copy session logs
cp -r physical_logic_framework/Session_Log logic-realism-theory/approach_2_reference/sessions/

# Copy root documentation (NEW)
mkdir logic-realism-theory/approach_2_reference/root_docs
cp physical_logic_framework/*.md logic-realism-theory/approach_2_reference/root_docs/
# (exclude LICENSE, CLAUDE.md which are rewritten)
```

**Step 6.2: Create README_APPROACH_2.md**

Add section on root docs and papers:
```markdown
## Archive Contents

- `lean/` - 140 axioms, 0 sorry (complete formalization)
- `notebooks/` - 25 notebooks (extensive validation)
- `papers/` - ALL Approach 2 papers (It_from_Logic, Logic_Realism_Foundational, supplementary)
- `sessions/` - Sessions 1-15 logs (development history)
- `root_docs/` - Root-level documentation (strategy, assessment, status)

**Papers Archived**:
- It_from_Logic_Scholarly_Paper.md - Main Approach 2 paper
- Logic_Realism_Foundational_Paper.md - Philosophical foundation (Session 14.6)
- Logic_Realism_Theory_Foundational.md - Early LRT paper
- figures/ - Publication figures (6 PNG files)
- supplementary/ - Supporting documents
- potential_extensions/ - Speculative research

**Note**: LRT has ONE new paper (theory/Logic_Realism_Theory.md) written fresh as the north star.

**Root Documentation**:
- MISSION_STATEMENT.md - Approach 2 mission and goals
- PLF_CONTRIBUTION_ASSESSMENT.md - Honest research positioning
- AXIOM_HONESTY_AUDIT.md - Session 14.3 transparency
- K_N_LITERATURE_SEARCH_RESULTS.md - Literature context (A001892)
- LEAN_STATUS_REPORT.md - Build status and axiom counts
- (20+ strategic and technical documents)
```

---

## Updated CLAUDE.md (LRT Version)

**Section additions**:

### Essential Tools

**Program Auditor Agent**:
- Run at session start (after reading session log)
- Before making completion claims
- After major milestones
- Verify axiom counts: `grep -c "^axiom" lean/LogicRealismTheory/**/*.lean`
- Verify sorry counts: `grep -c "sorry" lean/LogicRealismTheory/**/*.lean`
- See `Program_Auditor_Agent.md` for full protocol

**Multi-LLM System**:
- Team consultations: Grok-3, GPT-4, Gemini-2.0
- Quality scoring and caching (~50% hit rate)
- Consultation budget: 61 consultations over Sprints 6-10
- See `multi_LLM/README.md` for usage
- Results saved to `multi_LLM/consultation/`

**Approach 2 Archive**:
- Reference computational validation: `approach_2_reference/notebooks/`
- Reference Lean formalization: `approach_2_reference/lean/`
- Reference root docs: `approach_2_reference/root_docs/`
- Cite results, learn from lessons, don't duplicate

---

## Updated File Count

**Total files created** (initial setup):
- Root: 6 (README, CLAUDE, LICENSE, .gitignore, Program_Auditor_Agent, NEXT_SESSION)
- multi_LLM/: ~15 files (system + docs + templates)
- theory/: 4 (main paper, 3 supplementary stubs)
- lean/: 14 (lakefile, toolchain, 1 complete module, 12 stubs)
- notebooks/: 11 (requirements, 9 notebook stubs, 1 .gitkeep)
- approach_2_reference/: 5 (README, LESSONS, root_docs/ with ~20 files, content copied)
- docs/: 6 (stubs)
- Session_Log/: 2 (README, Session_0.0)

**Total**: ~63 files + archived Approach 2 content (~20 root docs + lean + notebooks + papers + sessions)

---

## Verification Checklist (UPDATED)

After setup complete, verify:

- [ ] All folders created according to structure
- [ ] README.md clearly explains LRT
- [ ] CLAUDE.md provides instructions for Claude Code
- [ ] **Program_Auditor_Agent.md adapted for LRT** ⚠️
- [ ] **multi_LLM/ system copied and functional** ⚠️
- [ ] **multi_LLM/api_config_template.json present** ⚠️
- [ ] **multi_LLM/ in .gitignore (api_config.json, cache.db)** ⚠️
- [ ] Lean project initializes (`cd lean && lake build`)
- [ ] Notebooks/ has requirements.txt
- [ ] **approach_2_reference/root_docs/ contains ~20 .md files** ⚠️
- [ ] approach_2_reference/ contains archived PLF content
- [ ] Session_Log/Session_0.0.md documents initial state
- [ ] .gitignore covers Python, Lean, OS, multi_LLM credentials
- [ ] LICENSE is Apache 2.0
- [ ] Git initialized with clean commit history
- [ ] All planning documents referenced in Session_0.0.md

---

## Multi-LLM Setup Instructions (For User)

**After repository creation**:

1. **Copy API credentials**:
   ```bash
   cd logic-realism-theory/multi_LLM
   cp api_config_template.json api_config.json
   # Edit api_config.json with actual API keys
   ```

2. **Test connection**:
   ```bash
   python health_check.py
   # Should show: ✅ All APIs connected
   ```

3. **Run test consultation**:
   ```bash
   python test_enhanced_bridge.py
   # Verify quality scoring works
   ```

4. **Update consultation prompts** (optional):
   ```bash
   # Edit consultation_prompts/ for LRT-specific queries
   ```

**Consultation workflow**:
1. Create prompt file in `consultation_prompts/`
2. Run: `python enhanced_llm_bridge.py <prompt_file>`
3. Results saved to `consultation/` with quality score
4. Cache hits ~50% (saves API costs)

---

## Next Steps

1. ✅ **Complete this plan** (this document)
2. 🔄 **Update LRT_Repository_Setup_Plan.md** (integrate Phase 2.5, update Phase 6)
3. 🔄 **Update Session_16.1.md** (note essential tools kept)
4. ⏳ **Discuss with user** (get approval before creating repo)

---

**Status**: Root files archive plan complete, essential tools preserved
**Key Additions**: Program_Auditor_Agent.md (adapted), multi_LLM/ (full system), approach_2_reference/root_docs/ (archive)
