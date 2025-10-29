# Audit Folder - Quality Assurance and Honesty Enforcement

This folder contains audit protocols and reports for the Logic Realism Theory (LRT) research program.

---

## Purpose

The audit system serves three critical functions:

1. **Prevent Overclaiming**: Enforce honesty about axioms, sorry statements, and completion status
2. **Quality Assurance**: Verify Lean proofs, computational validation, and cross-system consistency
3. **Transparency**: Document all audits with dated reports for peer review

---

## Core Documents

### 1. Program Auditor Agent Protocol

**File**: [`Program_Auditor_Agent.md`](Program_Auditor_Agent.md)

**Purpose**: Comprehensive audit protocol preventing hype and ensuring verification

**Contents**:
- Mandatory audit triggers (session start, milestones, public claims)
- Quick audit checklist (Lean proof status, build verification)
- Computational validation protocol (multi-LLM review requirements)
- Red flag language (words to avoid without verification)
- Full 5-phase audit procedure

**When to use**:
- ✅ At the start of each new session (after reading session log)
- ✅ Before making any public claims about completion status
- ✅ After completing any sprint or major milestone
- ✅ Monthly comprehensive audit
- ✅ Before updating README or documentation with completion statistics

**Referenced in**: `CLAUDE.md` (Section: Program Auditor Agent Protocol)

---

## Audit Reports (Future)

As audits are performed, dated reports will be added to this folder:

```
audit/
├── README.md                           # This file
├── Program_Auditor_Agent.md           # Core protocol
└── reports/                            # Dated audit reports
    ├── audit_2025_10_29.md            # Example: Monthly audit
    ├── audit_sprint_4_complete.md     # Example: Sprint completion audit
    └── ...
```

**Report naming convention**: `audit_YYYY_MM_DD.md` or `audit_[trigger]_[description].md`

**Report template** (minimal):
```markdown
# Audit Report: [Trigger/Description]

**Date**: YYYY-MM-DD
**Type**: [Session Start / Sprint Complete / Monthly / Pre-Claim]
**Auditor**: Program Auditor Agent (via Claude Code)

## Summary

[Overall assessment]

## Lean Proof Status

- **Sorry count**: [number] (verified via grep)
- **Build status**: [success/failure] ([number] jobs)
- **Axiom count**: [number] (documented in lean/AXIOMS.md)

## Computational Validation

- **Notebooks executed**: [list]
- **Multi-LLM reviews**: [count, avg quality score]
- **Cross-validation status**: [summary]

## Compliance Check

- [ ] No overclaiming language
- [ ] All completion claims verified
- [ ] Multi-LLM review for simulations
- [ ] Axiom inventory up to date
- [ ] README files synchronized

## Issues Found

[None / List of issues]

## Recommendations

[Actions needed]

---

**Audit Status**: ✅ PASS / ⚠️ WARNING / ❌ FAIL
```

---

## Integration with CLAUDE.md

The audit folder is referenced in `CLAUDE.md` under the **Program Auditor Agent Protocol** section.

**Quick reference**:
```markdown
**Full Audit Protocol**: See [`audit/Program_Auditor_Agent.md`](audit/Program_Auditor_Agent.md) for comprehensive audit procedures
```

---

## Audit Triggers (From Program_Auditor_Agent.md)

**Mandatory**:
1. Session start (after reading session log)
2. Before public claims about completion
3. After sprint/milestone completion
4. Monthly (first session of each month)
5. Before README updates with statistics

**Recommended**:
- Before paper submission
- After major Lean proofs complete
- After experimental protocol validation
- When making performance claims (5-10x productivity, etc.)

---

## Validation Commands

### Lean Proofs

```bash
# Count sorry statements (main build)
grep -r "^ *sorry$" lean/LogicRealismTheory/Foundation/*.lean \
                    lean/LogicRealismTheory/Operators/*.lean \
                    lean/LogicRealismTheory/Derivations/*.lean | wc -l
```

**Expected**: 0

```bash
# Count axioms
grep -r "^axiom" lean/LogicRealismTheory/Foundation/*.lean \
                 lean/LogicRealismTheory/Operators/*.lean \
                 lean/LogicRealismTheory/Derivations/*.lean | wc -l
```

**Expected**: 6 (as of 2025-10-29)

```bash
# Verify build
cd lean && lake build LogicRealismTheory
```

**Expected**: 0 errors, 2998 jobs (as of 2025-10-29)

### Computational Validation

```bash
# Check multi-LLM consultation quality
ls -lt multi_LLM/consultation/ | head -10
```

**Expected**: Recent consultations with quality scores documented

```bash
# Verify notebook execution (requires manual run)
cd notebooks
jupyter nbconvert --to notebook --execute Path3_T1_vs_T2_QuTiP_Validation.ipynb
```

**Expected**: No errors

---

## Red Flag Language (Avoid Without Verification)

**Completion claims**:
- ❌ "complete" / "completed" / "finished" (without grep evidence)
- ❌ "validated" / "proven" (without multi-LLM review)
- ❌ "0 sorry statements" (without showing grep results)

**Performance claims**:
- ❌ "5-10x productivity" (without documenting specific examples)
- ❌ "unprecedented transparency" (without comparison)

**Use instead**:
- ✅ "X sorry statements remain (verified YYYY-MM-DD)"
- ✅ "Module builds successfully with Y jobs (verified YYYY-MM-DD)"
- ✅ "Multi-LLM quality score Z (consultation dated YYYY-MM-DD)"

---

## Future Enhancements

**Planned audit features**:
- Automated audit script (bash/python) running all verification commands
- Audit report generation template
- Cross-file consistency checker (axiom counts, sorry counts, README claims)
- Historical audit timeline (track progress over time)
- Audit dashboard (visual summary of current status)

**See**: `audit/Program_Auditor_Agent.md` for full protocol details

---

**Last Updated**: 2025-10-29
**Status**: Audit system operational, Program Auditor Agent protocol active
**Next Audit**: Next session start (as per mandatory triggers)
