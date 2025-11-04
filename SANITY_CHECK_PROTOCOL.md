# Sanity Check Protocol

**Purpose**: Verify actual completion vs claimed completion after each track
**Invoke**: After completing any track, sprint deliverable, or major claim
**Created**: 2025-11-04 (Session 9.0 - AI-assistant challenge mitigation)

---

## Quick Checklist

Run through these 6 checks before claiming "complete":

### ☐ 1. Build Verification
```bash
cd lean && lake build
```
- **Pass**: 0 errors (warnings OK)
- **Fail**: Any compilation errors
- **Check**: Did ALL relevant files build, or just some?

### ☐ 2. Proof Verification
For each theorem claimed as "proven":
```bash
# Check theorem body
grep -A 5 "theorem <name>" <file>.lean
```
- **Real proof**: Has actual proof steps (not `trivial`, not `sorry`)
- **Trivial placeholder**: `True := by trivial` (NOT A REAL PROOF)
- **Sorry**: `sorry` (UNPROVEN)
- **Check**: Are theorems proving the actual statements or just `True`?

### ☐ 3. Import Verification
```bash
# Check if file is imported in root
grep -r "import.*<YourFile>" lean/LogicRealismTheory.lean
```
- **Imported**: File is part of build (real)
- **Not imported**: File exists but orphaned (wasted effort)
- **Check**: Is the work actually integrated?

### ☐ 4. Axiom Count Reality
```bash
# Count axioms in file
grep -c "^axiom " lean/LogicRealismTheory/<Module>/<File>.lean
```
- **Document**: How many axioms added vs removed?
- **Classify**: K_math, LRT_foundational, Measurement_dynamics, etc.
- **Check**: Did axiom count go UP when claiming to "prove" things?

### ☐ 5. Deliverable Reality Check
For each claimed deliverable:
- **Documentation only**: Markdown file explaining theory (informal argument)
- **Lean structure**: Type signatures, axioms, imports (scaffolding)
- **Lean proof**: Theorem with non-trivial proof body (actual verification)
- **Check**: Which category does each deliverable actually fall into?

### ☐ 6. Professional Tone Verification
Review all documentation and commit messages for professionalism:
- **No celebration language**: Avoid 🎉, "amazing", "breakthrough", "historic" before peer review
- **No emojis**: Unless explicitly requested by user
- **No superlatives**: "significant", "important", "notable" instead of "groundbreaking", "revolutionary"
- **Measured claims**: "This appears to..." not "This proves..."
- **Honest assessment**: Lead with limitations, not achievements
- **Check**: Would a peer reviewer find this tone appropriate for academic work?

**Red flags**:
- ❌ Excessive enthusiasm (🎉 COMPLETE! AMAZING! BREAKTHROUGH!)
- ❌ Premature celebration (claiming success before verification)
- ❌ Marketing language ("revolutionary", "paradigm shift", "game-changing")
- ❌ Overconfident claims ("definitively proves", "conclusively shows")

**Acceptable tone**:
- ✅ Technical and measured ("results suggest", "appears consistent with")
- ✅ Explicit about limitations ("pending verification", "preliminary results")
- ✅ Professional restraint (state facts, not excitement)
- ✅ Academic standard (like arxiv preprints, not press releases)

---

## Stop Words

Do NOT use these words without passing sanity check:

❌ **"Verified"** - unless theorems have real proofs (not `trivial`, not `sorry`)
❌ **"Proven"** - unless theorem body proves actual statement (not `True`)
❌ **"Complete"** - unless all proof obligations satisfied
❌ **"Formalized"** - unless file imported and builds
❌ **"Derived"** - unless derivation is formal proof (not informal argument)

✅ **Acceptable alternatives**:
- "Documented" (for markdown files)
- "Structured" (for type signatures/axioms)
- "Builds successfully" (for compilation)
- "Informal argument provided" (for theory explanations)
- "Axiom structure in place" (for scaffolding)

---

## Reality Check Questions

Ask these before claiming completion:

1. **If a skeptical peer reviewer read this, would they agree it's "complete"?**
2. **Did I write proofs or did I write documentation about proofs?**
3. **Can I point to specific theorem bodies with non-trivial proof steps?**
4. **Did the axiom count go DOWN (real reduction) or UP (more assumptions)?**
5. **Is this actual object-level work or meta-level process work?**

---

## Specific File Checks

### For Lean Files

**Pass Criteria**:
- ✅ File imported in `LogicRealismTheory.lean`
- ✅ `lake build` succeeds with 0 errors
- ✅ Theorems prove actual statements (not `True`)
- ✅ No unresolved `sorry` statements (or explicitly documented as K_math/axioms)
- ✅ Axiom count change documented in tracking

**Fail Indicators**:
- ❌ File not imported (orphaned)
- ❌ Theorems prove `True` with `trivial`
- ❌ Theorems end with `sorry`
- ❌ Axiom count increased when claiming "proven"
- ❌ Build errors or warnings about unused variables

### For Markdown Documentation

**Pass Criteria**:
- ✅ Clearly labeled as "informal argument" or "conceptual derivation"
- ✅ Does NOT claim "formally verified" or "proven in Lean"
- ✅ References Lean files accurately (doesn't overstate their contents)
- ✅ Honest about what's derived vs what's assumed

**Fail Indicators**:
- ❌ Claims "verified" when only documented
- ❌ Claims "complete" when Lean has `sorry`/`True`
- ❌ Implies formal verification without checking theorem bodies
- ❌ Counts markdown lines as "formalization"

### For Sprint Tracks

**Pass Criteria**:
- ✅ All deliverables pass their respective checks above
- ✅ Tracking document accurately reflects pass/fail status
- ✅ No conflation of "documentation complete" with "proofs complete"
- ✅ Honest percentage: what % is formal proof vs informal argument?

**Fail Indicators**:
- ❌ "100% complete" when theorems have `sorry`
- ❌ "Fully formalized" when proofs are `trivial`
- ❌ Celebration (🎉) before verification
- ❌ Counts files created, not theorems proven

---

## Output Format

After running sanity check, report:

```markdown
## Sanity Check Results - [Track Name]

**Build Status**: ✅/❌ [0 errors] / [N errors]
**Files Imported**: ✅/❌ [N/N files] / [N/M files - M orphaned]
**Proof Status**:
  - Real proofs: N theorems
  - Trivial placeholders: N theorems (proving `True`)
  - Unproven: N theorems (`sorry`)
**Axiom Count**: Start: X, End: Y, Change: +/-Z
**Deliverable Reality**:
  - Documentation: N files
  - Lean structure: N files
  - Lean proofs: N theorems with real proof bodies
**Professional Tone**: ✅/❌ [Measured and appropriate] / [Excessive enthusiasm detected]

**Honest Assessment**: [1-2 sentence summary of what was actually achieved]

**Proceed?**: ✅ YES / ❌ NO - [reason]
```

---

## When to Escalate to User

Invoke this check yourself first. If you get:
- ❌ on ANY of the 5 quick checks
- Discrepancy between claimed and actual completion
- Uncertainty about proof vs placeholder
- Temptation to use stop words without verification

Then STOP and report results to user BEFORE claiming completion.

---

## Protocol Status

**Version**: 1.0
**Created**: 2025-11-04
**Purpose**: Mitigation for AI-assistant overclaiming patterns (Session 8 lessons)
**Usage**: Mandatory after each track, optional during track for mid-point check

---

**This protocol exists because**: Session 8 discovered systematic overclaiming of "BUILD SUCCESS" as "formal verification". This check distinguishes compilation from proof completion.
