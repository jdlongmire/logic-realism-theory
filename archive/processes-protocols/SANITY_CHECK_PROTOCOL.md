# Sanity Check Protocol

**Purpose**: Verify actual completion vs claimed completion
**Invoke**: After completing any track, sprint, or major claim

---

## Quick Checklist (9 Checks)

Run through before claiming "complete":

### 1. Build Verification
```bash
cd lean && lake build
```
- **Pass**: 0 errors
- **Fail**: Any compilation errors

### 2. Proof Verification
```bash
grep -A 5 "theorem <name>" <file>.lean
```
- **Real proof**: Has actual proof steps
- **Placeholder**: `True := by trivial` (NOT a real proof)
- **Unproven**: `sorry`

### 3. Import Verification
```bash
grep -r "import.*<YourFile>" lean/LogicRealismTheory.lean
```
- **Imported**: Part of build
- **Not imported**: Orphaned (wasted effort)

### 4. Axiom Count
```bash
grep -c "^axiom " lean/LogicRealismTheory/<Module>/<File>.lean
```
- Document axioms added vs removed
- Did count go UP when claiming to "prove" things?

### 5. Deliverable Reality
For each claimed deliverable, classify:
- **Documentation**: Markdown explaining theory
- **Lean structure**: Type signatures, axioms, imports
- **Lean proof**: Theorem with non-trivial proof body

### 6. Professional Tone
- No celebration language before peer review
- No emojis unless requested
- Measured claims ("appears to..." not "proves...")
- Lead with limitations, not achievements

### 7. Experimental Literature Check
Before investing in predictions:
1. Search for experiments in relevant regime (30-60 min)
2. Extract experimental values with error bars
3. Compare to prediction: consistent, falsified, or untested?
4. **STOP** if contradicted by high-fidelity experiments

### 8. Computational Circularity
```python
# CIRCULAR (forbidden):
eta = 0.23  # Insert by hand
effect = 1 + eta * f(x)  # Get 23% back

# NON-CIRCULAR (correct):
eta = derive_from_axioms()  # Independent derivation
effect = apply(eta)  # Then apply
```
- Parameters must be DERIVED, not inserted to match output

### 9. Comprehensive Circularity
Five types to check:

| Type | Definition | Red Flag |
|------|------------|----------|
| Logical | Proof assumes what it proves | Conclusion in dependency tree |
| Definitional | Definition uses terms requiring it | Forward references |
| Computational | Code uses output as input | Self-referential variable |
| Parametric | Parameter in own derivation | P used to derive P |
| Validation | Test assumes result | Circular validation |

**Dependency trace must be acyclic (DAG).**

---

## Stop Words

Do NOT use without passing sanity check:

| Forbidden | Use Instead |
|-----------|-------------|
| "Verified" | "Documented" |
| "Proven" | "Structured" |
| "Complete" | "Builds successfully" |
| "Formalized" | "Axiom structure in place" |
| "Derived" | "Informal argument provided" |

---

## Reality Check Questions

1. Would a skeptical peer reviewer agree it's "complete"?
2. Did I write proofs or documentation about proofs?
3. Can I point to specific theorem bodies with non-trivial steps?
4. Did axiom count go DOWN or UP?
5. Is this object-level work or meta-level process work?

---

## Pass Criteria

### Lean Files
- File imported in `LogicRealismTheory.lean`
- `lake build` succeeds with 0 errors
- Theorems prove actual statements (not `True`)
- No unresolved `sorry` (or explicitly documented)

### Markdown
- Labeled as "informal argument"
- Does NOT claim "formally verified"
- Honest about derived vs assumed

---

## Output Format

```markdown
## Sanity Check: [Track Name]

**Build**: [0 errors / N errors]
**Imports**: [N/N files]
**Proofs**: [N real / N trivial / N sorry]
**Axiom Count**: [Start → End, +/- change]
**Circularity**: [Clean / Issue found]
**Tone**: [Professional / Issues]

**Honest Assessment**: [1-2 sentences]
**Proceed?**: [YES / NO - reason]
```

---

## When to Escalate

If ANY check fails:
- STOP
- Report results to user BEFORE claiming completion
- Do not proceed with overclaiming

---

*This protocol exists because: Session 8 discovered systematic overclaiming. Check #7 added after Bell Ceiling falsification. Check #9 added after Paths 3-4 circularity.*
