# Sanity Check Protocol

**Purpose**: Verify actual completion vs claimed completion after each track
**Invoke**: After completing any track, sprint deliverable, or major claim
**Created**: 2025-11-04 (Session 9.0 - AI-assistant challenge mitigation)
**Reports**: Save all sanity check reports to `01_Sanity_Checks/` folder (see Output Format below)

---

## Quick Checklist

Run through these 9 checks before claiming "complete" (Check #7, #8, & #9 are CRITICAL for predictions/simulations/proofs):

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

### ☐ 7. Experimental Literature Cross-Check ⚠️ CRITICAL FOR PREDICTIONS

**Purpose**: Verify prediction is not already falsified by existing experimental data

**When to apply**: Before investing effort in ANY testable prediction

**Checks**:
1. **Literature search** (spend 30-60 minutes):
   - Search for experiments in relevant parameter regime
   - Focus on high-fidelity platforms (ion traps, photonics, superconducting qubits)
   - Identify 3-5 recent experimental papers (last 5 years)
   - Check for review articles or meta-analyses

2. **Extract experimental values**:
   - What quantities do experiments measure?
   - What values with error bars are reported?
   - What is the zero-noise or high-fidelity limit?
   - Are there any systematic trends across platforms?

3. **Compare to prediction**:
   - Is our prediction within error bars of existing results? (consistent)
   - Is our prediction contradicted by published results? (falsified)
   - Is our prediction untested by existing experiments? (viable)

4. **Decision gate**:
   - ✅ **PROCEED**: Prediction untested OR marginally distinguishable from existing data
   - ⚠️ **CAUTION**: Prediction at edge of experimental limits (requires very high precision)
   - ❌ **STOP**: Prediction contradicted by high-fidelity experiments

**Red flags** (immediately STOP if found):
- ❌ High-fidelity platforms already achieve the regime we're predicting
- ❌ Published results show opposite trend from our prediction
- ❌ Multiple independent experiments contradict our claim
- ❌ Our "novel" prediction matches existing experimental reality

**Example failures** (learn from these):
- **Bell Ceiling (2025-11-05)**: Predicted S ≤ 2.71, but ion traps already achieve S ≈ 2.828
  - Error: Confirmed Tsirelson bound (baseline) but didn't check if experiments reach it
  - Lesson: Checking baseline is correct ≠ checking experiments don't already falsify prediction
  - Cost: ~20 hours wasted on derivation, validation, protocol development

**Workflow**:
```bash
# Example literature search
# Search: "[observable] [system] high fidelity experimental"
# For Bell tests: "CHSH inequality ion trap loophole-free"
# For decoherence: "T2 T1 ratio superconducting qubit fidelity"
# Extract values, compare to prediction BEFORE proceeding
```

**When to skip this check**:
- ❌ NEVER skip for experimental predictions
- ❌ NEVER skip for testable claims about physical observables
- ❌ NEVER skip because "we're confident in the theory"
- ✅ Can skip for purely mathematical derivations (no experimental component)

**This check exists because**: Bell Ceiling prediction (2025-11-05) was developed, validated, and nearly pre-registered despite being contradicted by existing experimental data. Reddit community caught the error that our internal sanity checks missed.

### ☐ 8. Computational Circularity Check ⚠️ CRITICAL FOR SIMULATIONS

**Purpose**: Verify computational validation tests LRT mechanism, not arithmetic

**When to apply**: Before claiming "computational validation" for ANY simulation work

**The Circularity Problem**:
```python
# CIRCULAR (forbidden):
eta = 0.23  # Insert by hand
effect = 1 + eta * sin²(θ)  # Calculate
# → Get 23% effect
# → Claim "validated" ❌

# NON-CIRCULAR (correct):
# 1. Derive η from LRT axioms (variational optimization)
# 2. Apply derived η to specific system
# 3. Verify prediction emerges ✅
```

**Checks**:

1. **Parameter Origin**:
   - ❌ **CIRCULAR**: Parameters inserted to match desired output
   - ✅ **VALID**: Parameters derived from LRT framework, then applied

2. **Independence Test**:
   - Question: "Could this simulation predict a DIFFERENT value?"
   - ❌ **CIRCULAR**: No (we put in what we wanted)
   - ✅ **VALID**: Yes (parameters emerge from optimization/derivation)

3. **Claims vs Reality**:
   - ❌ **OVERCLAIM**: "Computational validation complete" (when phenomen

ological)
   - ✅ **HONEST**: "Analysis pipeline tested" OR "Derived parameters applied"

**Red Flags**:
- ❌ Inserting η = 0.23 by hand → getting 23% back → claiming "validation"
- ❌ Parametrizing the effect → calling it "first-principles"
- ❌ Testing arithmetic → claiming to test physics mechanism
- ❌ "Phenomenological model" presented as "computational validation"

**Pass Criteria**:
- ✅ Parameters DERIVED from LRT axioms/optimization (variational framework)
- ✅ Derivation is INDEPENDENT of the specific prediction being tested
- ✅ OR clearly labeled as "phenomenological exploration" with harsh limitations
- ✅ OR labeled as "analysis pipeline test" (no physics validation claims)

**Example: AC Stark θ-Dependence**:

**❌ CIRCULAR approach** (removed November 2025):
```python
# Phenomenological parametrization
Ω_eff(θ) = Ω₀ · √[1 + η·sin²(θ)]  # η = 0.23 inserted
# This DOES NOT test LRT mechanism
# Just confirms: 0.23 → 23% (arithmetic)
```

**✅ FIRST-PRINCIPLES approach** (correct):
```python
# Part 1: Derive η from LRT variational framework
β_optimal = minimize(K_violations + K_enforcement)  # → β ≈ 0.75
η_derived = (ln2 / β²) - 1  # → η ≈ 0.23

# Part 2: Apply to AC Stark system
α(θ) = α₀(1 + η_derived·sin²(θ))
Δω(θ) ∝ α(θ)  # → 23% enhancement emerges

# Non-circular because:
# - Variational optimization independent of AC Stark physics
# - η emerges from general constraint minimization
# - Then applied to specific system
```

**Documentation Requirements**:

If using derived parameters:
- ✅ Show derivation chain explicitly
- ✅ Emphasize independence from prediction being tested
- ✅ State: "η derived from [method], NOT inserted"

If using phenomenological model:
- ✅ Label clearly: "Phenomenological exploration" or "Analysis pipeline test"
- ✅ Do NOT claim "validation" or "first-principles"
- ✅ State limitations prominently

**This check exists because**: AC Stark simulation (2025-11-05) initially used phenomenological parametrization but claimed "computational validation." User correctly flagged this as circular. Notebook was rebuilt from first principles using variational framework.

### ☐ 9. Comprehensive Circularity Check ⚠️ CRITICAL FOR ALL WORK

**Purpose**: Detect ALL forms of circularity in proofs, derivations, formulas, and code before claiming validity

**When to apply**:
- Before claiming any derivation is complete
- Before claiming any theorem is proven
- When introducing new parameters or constants
- When refactoring proof structures
- For ALL track completions

**The 5 Types of Circularity**:

#### 1. Logical Circularity
**Definition**: Proof assumes (directly or indirectly) what it aims to prove

**Examples**:
- Deriving Born rule using probabilities before probabilities are defined
- Using unitarity to prove unitarity
- Assuming measurement outcomes to derive measurement theory

**Check**:
```bash
# For Lean proofs - trace theorem dependencies
grep -r "theorem <name>" lean/
# Verify conclusion doesn't appear in its own dependency tree
```

**Red flag**: If theorem T uses axiom A, and axiom A depends on result from T

#### 2. Definitional Circularity
**Definition**: Definition depends on terms that require the definition to be meaningful

**Examples**:
- Defining entropy using concepts that require entropy to be defined
- Defining time evolution using time-dependent operators
- Defining measurement using measured quantities

**Check**:
- For each definition, list ALL terms used
- Verify those terms are independently defined without invoking current definition
- Create glossary showing definition order (number sequentially)

**Red flag**: If definition N uses terms from definition M where M > N

#### 3. Computational Circularity (expanded from Check #8)
**Definition**: Code uses computed values as inputs to compute those same values

**Examples**:
- Calculating η using formula that depends on η
- Variational optimization that uses optimal value as initial guess
- Simulation using target distribution to generate target distribution

**Check**:
```python
# Trace data flow in code
# For each function: inputs → intermediate → outputs
# Verify no self-dependency
```

**Red flag**: Variable appearing on both left and right side of assignment without clear iteration logic

#### 4. Parametric Circularity
**Definition**: Parameters derived using relationships that assume those parameter values

**Examples**:
- Deriving ℏ from energy spectrum that was calculated using ℏ
- Fitting model parameters to data generated by that model
- Optimizing constants using objective function that includes those constants

**Check**:
| Parameter | Source | Depends On | Used In | Circular? |
|-----------|--------|------------|---------|-----------|
| η | Variational | β, K_violations | AC Stark | ✅ NO |
| ℏ | Assumed | None | Energy calc | ✅ NO |
| η | Inserted | Target value | Validation | ❌ YES |

**Red flag**: If derived parameter P appears in the derivation that produces P

#### 5. Validation Circularity
**Definition**: Validation uses assumptions or data that presuppose the result being validated

**Examples**:
- Validating quantum predictions using quantum simulator
- Testing emergence of time using time-evolved states
- Checking Born rule with probability-normalized data

**Check**:
- Verify validation is independent
- Use only pre-quantum mechanics results, raw data, or independent frameworks
- Check test data doesn't encode the answer

**Red flag**: If validation assumes what it's testing

---

**Mandatory Verification Procedures**:

**A. Dependency Trace (for Lean/mathematical proofs)**:
```bash
# Create explicit dependency graph
# Axioms → Definitions → Lemmas → Theorems → Results
# MUST be acyclic (DAG - Directed Acyclic Graph)

# For Lean:
grep -r "import" lean/LogicRealismTheory/ | sort | uniq
# Check for circular imports

# For math derivations:
# Number equations sequentially (Eq. 1, 2, 3...)
# Annotate which equations each uses
# Verify no equation uses higher-numbered equations
```

**B. Definition Audit**:
```markdown
# Create sequential glossary
1. Information State (I) - primitive concept
2. Logical Constraint (L) - maps I to A
3. Actuality (A = L(I)) - uses 1,2
4. [Never use term from definition 5+ in definition 3]
```

**C. Parameter Source Check**:
```python
# For ALL parameters/constants, document:
params = {
    'eta': {'source': 'derived', 'method': 'variational', 'depends_on': ['beta', 'K_v']},
    'hbar': {'source': 'assumed', 'method': 'standard_value', 'depends_on': []},
    'beta': {'source': 'optimized', 'method': 'minimize_K', 'depends_on': []}
}
# Verify: derived parameters don't appear in their own derivation chain
```

**D. Computational Flow Audit**:
```python
# For each function, trace:
def compute_eta(beta, K_violations):  # inputs
    # ✅ eta NOT in inputs
    intermediate = ln2 / (beta**2)
    eta_result = intermediate - 1     # output
    return eta_result
    # ✅ PASS: eta computed from independent inputs

def compute_eta_WRONG(eta_guess):     # ❌ CIRCULAR
    eta_result = eta_guess * 1.0      # Using eta to compute eta
    return eta_result
```

**E. Axiom Independence Check**:
```bash
# For each axiom A, attempt to derive A from remaining axioms
# If possible → A not independent → remove
# This prevents: axiom A proves theorem B, but A depends on B (hidden circle)
```

---

**Pass Criteria**:
- ✅ Dependency graph is acyclic (DAG verified)
- ✅ All definitions use only previously defined terms
- ✅ All parameters derived from independent sources
- ✅ Code has no self-referential computations (except explicit convergent iteration)
- ✅ Validation independent of result being validated
- ✅ Axioms are mutually independent

**Fail Indicators**:
- ❌ Any cycle detected in dependency graph (A → B → C → A)
- ❌ Definition uses terms not yet defined
- ❌ Parameter P appears in derivation of P
- ❌ Variable computed from itself
- ❌ Validation assumes the result
- ❌ Axiom provable from other axioms

**Documentation When Circularity Found**:
1. STOP immediately - do not proceed with proof/derivation
2. Identify exact location of circular dependency
3. Trace full circular chain: A → B → C → A
4. Document what was assumed vs. what should be derived
5. Propose alternative that breaks the circle
6. Report to user immediately (do not hide or work around)

**Documentation When Clean**:
```
# In code/proof comments:
# Circularity check: 2025-11-06 - verified acyclic dependency graph
# Dependencies: Axioms [A1, A2] → Definitions [D1, D2] → Theorem T1
# No circular references detected
```

**Example from Repository**:
- **Issue**: η (non-unitarity parameter) used in derivation before being derived (Paths 3-4)
- **Resolution**: Derived η from variational optimization, ensuring η_opt independent
- **Commit**: 7636732 - Fix Paths 3-4 circularity

**For Full Protocol**: See `AI-Collaboration-Profile.json` → `circularity_checking_protocol` (comprehensive)

**This check exists because**: Circularity is the most insidious error in theoretical work. It can hide in subtle dependencies, implicit assumptions, or computational loops. Session 12 discovered parametric circularity in Paths 3-4 that required systematic refactoring.

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

After running sanity check, report results AND save to `01_Sanity_Checks/` folder:

**File Naming Convention**: `YYYY-MM-DD_[TrackName]_SanityCheck.md`

**Examples**:
- `01_Sanity_Checks/2025-11-06_Energy_SanityCheck.md`
- `01_Sanity_Checks/2025-11-06_K_ID_Derivation_SanityCheck.md`
- `01_Sanity_Checks/2025-11-06_Sprint13_Track2_SanityCheck.md`

**Report Template**:

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
**Circularity Check**: ✅/❌ [DAG verified, no circular dependencies] / [Circular dependency detected: A → B → C → A]
  - Logical: ✅/❌
  - Definitional: ✅/❌
  - Computational: ✅/❌
  - Parametric: ✅/❌
  - Validation: ✅/❌

**Honest Assessment**: [1-2 sentence summary of what was actually achieved]

**Proceed?**: ✅ YES / ❌ NO - [reason]
```

---

## When to Escalate to User

Invoke this check yourself first. If you get:
- ❌ on ANY of the 9 quick checks
- Discrepancy between claimed and actual completion
- Uncertainty about proof vs placeholder
- Temptation to use stop words without verification
- Experimental prediction that might be contradicted by existing data (Check #7)
- Any circular dependency detected (Check #9)

Then STOP and report results to user BEFORE claiming completion.

---

## Protocol Status

**Version**: 1.2 (updated 2025-11-06)
**Created**: 2025-11-04
**Purpose**: Mitigation for AI-assistant overclaiming patterns (Session 8 lessons)
**Usage**: Mandatory after each track, optional during track for mid-point check

**Updates**:
- v1.2 (2025-11-06): Added Check #9 (Comprehensive Circularity Check) covering all 5 types of circularity in proofs, derivations, formulas, and code
- v1.1 (2025-11-05): Added Check #7 (Experimental Literature Cross-Check) after Bell Ceiling falsification
- v1.0 (2025-11-04): Initial version (6 checks for Lean formalization work)

---

**This protocol exists because**:
- **Session 8**: Discovered systematic overclaiming of "BUILD SUCCESS" as "formal verification"
- **Session 10 (Bell Ceiling)**: Discovered prediction development without checking existing experimental data
- **Session 12**: Discovered parametric circularity in Paths 3-4 (η parameter)
- **Check #7 added**: Prevent investing effort in predictions already falsified by published experiments
- **Check #9 added**: Detect ALL forms of circularity (logical, definitional, computational, parametric, validation) before claiming validity
