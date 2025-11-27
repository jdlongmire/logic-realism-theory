# ISSUE 004: Editorial Remediation Plan

**Created:** 2025-11-27 (Session 21.0)
**Status:** CLOSED (All phases complete)
**Priority:** HIGH (blocks publication)

---

## Source

Editorial review dated 2025-11-27 identified structural inconsistencies in the Master Paper.

---

## Triage: Already Addressed vs. Remaining

### ✅ ALREADY FIXED (Sessions 20-21)

| Issue | Original Problem | Resolution |
|-------|-----------------|------------|
| Abstract-content mismatch | Abstract said 6 Parts, 42 sections | Section 1.3 now says Parts I-IV (1-31), Section 32, Appendix A |
| Section 32 references | Referenced non-existent Section 32 | Section 32 (Conclusion) now exists |
| Section 1.3 structure | Described Part V (32-38), Part VI (39-42) | Updated to reflect actual structure |

### ❌ STILL NEEDS WORK

| Issue | Problem | Priority |
|-------|---------|----------|
| 1. Part IV header | Uses `# Part IV` instead of `## Part IV` | Critical |
| 2. Duplicate Theorem 18.x | Section 19 theorems numbered as 18.x | Critical |
| 3. Definition sequencing | Definition 18.4 appears after 18.5, 18.7 | Critical |
| 4. Conjecture numbering gap | Gap between 21.1 and 21.4 | Moderate |
| 5. Axiom 3(b) clarification | Listed as axiom but marked "DERIVED" | Moderate |
| 6. Abstract revision | Current abstract undersells rigor/falsifiability | Consider |

---

## Phase 1: Critical Fixes

### 1.1 Part IV Header (Line 3023)

**Current:** `# Part IV: Empirical Signatures`
**Required:** `## Part IV: Empirical Signatures`

**Action:** Single edit to change `#` to `##`

---

### 1.2 Section 19 Theorem Renumbering

**Problem:** Theorems in Section 19 (Born Rule) use Section 18 numbering.

**Current → Required:**
| Line | Current | Should Be |
|------|---------|-----------|
| 2089 | Theorem 18.1 (Gleason) | Theorem 19.1 |
| 2128 | Theorem 18.3 (Born Rule from LRT) | Theorem 19.2 |
| 2174 | Theorem 18.5 | Theorem 19.3 |
| 2191 | Theorem 18.6 (Kochen-Specker) | Theorem 19.4 |

**Also update any references to these theorems elsewhere in document.**

---

### 1.3 Definition Sequencing in Section 18-19

**Problem:** Definition 18.4 (Mixed State) appears at line 2172, after Definition 18.5 (line 1964) and 18.7 (line 1981).

**Options:**
- **Option A:** Renumber Definition 18.4 → Definition 19.5 (it's in Section 19 context)
- **Option B:** Move Definition 18.4 content to appear before 18.5

**Recommendation:** Option A - the definition is about mixed states which is Section 19 content.

---

## Phase 2: Moderate Fixes

### 2.1 Conjecture Numbering (Section 22)

**Current state:**
- Conjecture 21.1 (Action-Complexity) - line 2634
- Definition 21.2 (Interface Functor) - line 2656
- Definition 21.3 (Fisher-Rao Metric) - line 2676
- Conjecture 21.4 (Emergent Spacetime) - line 2714

**Issue:** Section 22 contains "21.x" numbering (holdover from before renumbering).

**Required:** All should be 22.x:
- Conjecture 22.1 (Action-Complexity)
- Definition 22.2 (Interface Functor)
- Definition 22.3 (Fisher-Rao Metric)
- Conjecture 22.4 (Emergent Spacetime)

---

### 2.2 Axiom 3(b) Clarification

**Problem:** Axiom 3(b) is listed as an axiom but marked "[DERIVED - see Theorem 17.12]"

**Location:** Line 1665

**Options:**
- **Option A:** Keep current, add clarifying note that Axiom 3 lists *interface constraints*, some derived
- **Option B:** Remove 3(b) from axiom list entirely, reference only via Theorem 17.12

**Recommendation:** Option A - the axiom structure is pedagogically clear as-is; add footnote.

---

## Phase 3: Consider

### 3.1 Abstract Revision

The editorial review proposes a stronger abstract emphasizing:
- Global Constraint Satisfaction mechanism
- Global Parsimony as falsifiability anchor
- Explicit bridge from metaphysics to physics ($S = \hbar C$)

**Current abstract:** Accurate but reads as philosophical interpretation.

**Proposed revision:** Positions LRT as rigid physical theory with explicit mechanisms.

**Recommendation:** Review proposed abstract in editorial report. Adopt if it better represents the theory without overclaiming.

---

## Action Checklist

### Phase 1 (Critical - do first) ✅ COMPLETE
- [x] Fix Part IV header: `#` → `##` (line 3023)
- [x] Renumber Section 19 theorems: 18.1→19.1, 18.3→19.2, 18.5→19.3, 18.6→19.4
- [x] Renumber Lemma 18.2 → 19.6
- [x] Renumber Definition 18.4 → 19.5
- [x] Update cross-references (Lemma 19.6, Theorem 19.1 in proofs)

### Phase 2 (Important - do second) ✅ COMPLETE
- [x] Renumber Section 22 conjectures/definitions: 21.x → 22.x
- [x] Add clarifying note for Axiom 3(b) derived status
- [x] Check for any remaining 21.x references that should be 22.x

### Phase 3 (Polish) ✅ COMPLETE
- [x] Review proposed abstract revision
- [x] Hybrid abstract drafted (Claude) + polished (Grok review)
- [x] Integrated into Master Paper
- [ ] Em dash review (deferred - minor)

---

## Estimated Effort

| Phase | Time | Complexity |
|-------|------|------------|
| Phase 1 | 1-2 hours | Medium (careful renumbering) |
| Phase 2 | 30-60 min | Low |
| Phase 3 | 1-2 hours | Low (decision + polish) |

**Total:** 2.5-5 hours

---

## Notes

- The editorial review's "Grade: B+" assessment is fair given structural issues
- Content quality is strong; issues are structural not substantive
- After Phase 1-2, document should be publication-ready pending final polish
- Abstract revision is high-impact but optional for structural correctness

---

## Resolution Criteria

**ISSUE 004 is CLOSED when:**
1. All Phase 1 items complete
2. All Phase 2 items complete
3. Document passes consistency check (no duplicate theorem/definition numbers)
4. Part headers use consistent formatting

---
