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
- **`lean/AXIOMS.md`** - **⚠️ ACTIVE** LRT axiom approach summary: 2 Tier 1 + ~16 Tier 2 + 1 Tier 3 = ~19 axioms, **⚠️ AXIOM COUNT FRAMING**, honest paper framing
- **`lean/AXIOM_CLASSIFICATION_SYSTEM.md`** - **⚠️ ACTIVE** Complete 3-tier framework documentation with templates and examples
- **`lean/PROOF_REFACTOR_STRATEGY.md`** - **⚠️ ACTIVE** Revised tier-based strategy: Prove ~30-35 LRT theorems from 2 foundation axioms using ~16 math tools
- **`lean/STANDARD_FILE_HEADER.md`** - **⚠️ ACTIVE** Required header format for all Lean files (exemplar: IIS.lean)
- **`lean/TIER_LABELING_QUICK_START.md`** - Quick reference for tier classification and inline labels
- **`lean/LogicRealismTheory.lean`** - Root import file showing all modules

### Development Guides
- **`DEVELOPMENT_GUIDE.md`** - Architecture, commands, workflows, approach_2 protocol
- **`LEAN_BEST_PRACTICES.md`** - Lean 4 proof development lessons
- **`SANITY_CHECK_PROTOCOL.md`** - **⚠️ MANDATORY** track completion verification checklist

### Session Context
- **`Session_Log/Session_X.Y.md`** - Read LATEST session file (highest X.Y) for complete context
- **`sprints/README.md`** + **`sprints/sprint_X/SPRINT_X_TRACKING.md`** - If active sprint exists

### Theory Frameworks & Derivations
- **`theory/frameworks/LRT_Hierarchical_Emergence_Framework.md`** - Formal mathematical framework for emergence
- **`theory/derivations/`** - First-principles mathematical derivations (Session 13.0, ~3,700 lines)
  - **SOURCE OF TRUTH**: Markdown files (.md) are canonical
  - Convert to LaTeX/PDF as needed for paper submission
  - All derivations are non-circular, multi-LLM validated, rigorous

---

## ⚙️ Section 2: Critical Protocols

**Essential procedures. Keep these in mind, but detailed instructions live in the artifacts above.**

### Session Startup (Priority Order)
1. Read `AI-Collaboration-Profile.json` (your operating mode)
2. Read latest `Session_Log/Session_X.Y.md` (complete context - tells you what's needed)
3. Based on session context, skim relevant guides:
   - `DEVELOPMENT_GUIDE.md` or `LEAN_BEST_PRACTICES.md` (architecture/Lean work)
   - `lean/PROOF_REFACTOR_STRATEGY.md` (axiom/formalization work)
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

### Foundational Principle: The Logic Realism Thesis ⚠️ CRITICAL

**The Three Fundamental Laws of Logic (3FLL) are constitutive of coherent reality:**

- **Identity (L₁):** ∀A: A = A
- **Non-Contradiction (L₂):** ∀A: ¬(A ∧ ¬A)
- **Excluded Middle (L₃):** ∀A: A ∨ ¬A

**The Logic Realism Thesis (LRT's core claim):** All axioms of mathematics and physics are downstream of 3FLL - they are theorems of coherent structure, constrained by the requirement that reality be logically coherent.

**Important clarification:** This is a *research conjecture* and *metaphysical thesis*, not an established result of standard logic. In standard accounts, the laws of thought are constraints on reasoning, not sufficient to fix all substantive axioms. LRT's claim is stronger: that 3FLL are *constitutive* of reality, not merely descriptive of valid reasoning.

The derivation hierarchy:

```
3FLL (primitive, self-grounding)
  ↓ presuppose
I + I_infinite (domain of discourse, no arbitrary bound)
  ↓ enforce
Distinguishability → Parsimony → Minimum resolution (ℏ)
  ↓ structure
Phase space → Action → Dynamics
  ↓ constrain
d=3, α=1/137, mass, V(x), all physics
```

**What this means for derivations:**

1. **Tier 1 axioms are structural assumptions** - `I : Type*` and `I_infinite` are substantive assumptions for coherent application of 3FLL. LRT argues they are *required* for 3FLL to be meaningful, but this is part of the thesis, not a proven consequence.

2. **Tier 2/3 inputs are methodologically legitimate** - Using established reconstruction results (Stone's theorem, Gleason's theorem, Masanes-Müller) without re-proving them is standard practice in foundations work. Track their presuppositions.

3. **The Logic Realism Thesis is a guiding principle, not a proven result** - "All axioms downstream of 3FLL" is the theory's core claim. Derivations test and develop this thesis.

4. **Substantive assumptions must be marked** - Tier 1 assumptions and Tier 2 presuppositions are not pure logic. Mark them explicitly to avoid overstating what 3FLL alone delivers.

5. **"Gaps" are research opportunities** - When something isn't explicitly derived (mass, V(x), etc.), it's an open question whether the derivation exists. The thesis says it should; the work is to show it.

**The Tier System (Lean formalization):**
```
Tier 1: Structural assumptions for 3FLL application (I, I_infinite)
  → Substantive extra assumptions (domain, no arbitrary bound)
  → LRT argues they're required; this is part of the thesis
  NOTE: Track these explicitly in derivations

Tier 2: Established mathematical reconstruction results
  → Stone's theorem, Gleason's theorem, Masanes-Müller
  → Each presupposes its own non-logical structural assumptions
  → Accepted for practical use; presuppositions tracked

Tier 3: Physical principles (energy additivity, conservation)
  → Empirical regularities vs. symmetry consequences
  → Accepted for practical use; status tracked
```

**Tier 2 Presupposition Tracking:**

| Theorem | Key Presuppositions |
|---------|---------------------|
| Masanes-Müller | Tomographic locality, continuous reversibility, subspace axiom |
| Stone's theorem | Strongly continuous unitary group, Hilbert space structure |
| Gleason's theorem | Hilbert space dim ≥ 3, frame functions |

**When working on derivations:**
- Tier 2/3 inputs are methodologically legitimate (standard foundations practice)
- Explicit derivation chains are research goals, not prerequisites
- Mark clearly: what comes from 3FLL vs. what comes from Tier 2/3 assumptions

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

### Lean Formalization Best Practices (Sprint 12 Lessons)

**Proven strategies from Session 9.1 for effective formal verification:**

1. **Mandatory Sanity Check After Every Track**
   - Run SANITY_CHECK_PROTOCOL.md after completing ANY track
   - Prevents overclaiming before it happens
   - Distinguishes "builds successfully" from "formally verified"
   - **NOT optional** - make it habit

2. **Infrastructure First, Then Proofs**
   - Complete structure implementations before attempting proofs
   - Missing infrastructure (DensityOperator fields, EntropyFunctional, etc.) blocks theorem completion
   - Systematic refactoring more productive than piecemeal proof attempts
   - **Lesson**: 14 sorry statements in Session 9.1 were infrastructure-blocked, not proof-difficulty-blocked

3. **Axiom Reformulation (Existentials → Functions)**
   - Avoid existential statements in axioms (`∃ H, ...`)
   - Use functions instead: `axiom stone_generator : EvolutionOperator → Generator`
   - **Reason**: Existentials cause universe polymorphism errors in Lean 4
   - **Evidence**: time_emergence_from_identity blocked by this issue

4. **Test-Driven Proofs (Find Blockers Early)**
   - Attempt proving a theorem early to discover infrastructure gaps
   - Don't assume structures are complete until proof is attempted
   - Document blockers when found (don't hide them)
   - **Benefit**: Exposes systematic problems (axiom formulation), not isolated issues

5. **Outcome Metrics (Not Output Volume)**
   - Track axiom reductions and theorems proven (outcomes)
   - NOT lines of code written or files created (outputs)
   - **Evidence**: Session 9.1 achieved -13 axioms (real progress), not just documentation volume
   - **Warning**: AI can produce impressive documentation volume while avoiding hard technical work

**Sprint 12 Results Using These Practices**:
- ✅ -13 effective axioms (32 → 19)
- ✅ First module with 0 axioms (NonUnitaryEvolution.lean)
- ✅ 10+ theorems with complete proofs (Foundation/)
- ✅ Infrastructure blockers identified and documented
- ✅ Professional tone maintained (sanity check verified)

### Repository Structure
- Everything has ONE canonical location (see DEVELOPMENT_GUIDE.md for full structure)
- Never create alternative folders without updating CLAUDE.md

### Derivation Protocol (Session 13.0+)

**Location**: `theory/derivations/` - All first-principles mathematical derivations

**Source of Truth**: Markdown files (.md) are canonical
- 7 files documenting variational framework derivation (~3,700 lines)
- Identity_to_K_ID_Derivation.md (K_ID = 1/β², 100% derived)
- ExcludedMiddle_to_K_EM_Derivation.md (K_EM = (ln 2)/β, 100% derived)
- Measurement_to_K_enforcement_Derivation.md (K_enforcement = 4β², 95% derived)
- Four_Phase_Necessity_Analysis.md, Phase_Weighting_*.md (3 files)

**Format Standards**:
- Markdown with LaTeX equations for readability and version control
- Step-by-step derivation chains with explicit dependencies
- Non-circularity explicitly checked (trace full dependency graph)
- Multi-LLM expert validation required (quality ≥0.70 threshold)
- Transparent about limitations (e.g., "98% derived with caveat")

**Integration into Papers**:
- Generate LaTeX/PDF from markdown as needed for paper submission
- Can be included as supplementary material
- Can be integrated into main paper body if appropriate
- PDF generation is "compilation" - markdown remains source

**Quality Standards** (inherited from AI-Collaboration-Profile.json):
- Every step must be justified (no "it follows that" without explicit reasoning)
- Circular reasoning actively hunted (dependency traces required)
- Parameters must not appear in their own derivation chain
- Multi-LLM team review before claiming validation
- Honest acknowledgment of assumptions and limitations

**Lean Formalization** (future work):
- theory/derivations/ markdown provides ~10-15 theorems for future Lean work
- Lean formalization deferred until after experimental validation
- When ready: lean/LogicRealismTheory/Derivations/ mirrors theory/derivations/
- See lean/README.md "Future Formalization Targets" section

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

**Current Status**: See `lean/LogicRealismTheory.lean` (build status comments) and `lean/AXIOMS.md` (axiom count framing)

**For detailed information on ANY topic, see the Critical Artifacts section above.**

---

**This CLAUDE.md is intentionally lean. All detailed framing, context, and instructions live in the artifacts listed in Section 1.**
