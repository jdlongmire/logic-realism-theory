# Issue 008: Technical Paper Mathematical Improvements

**Status**: OPEN
**Priority**: HIGH
**Created**: 2025-12-07
**Source**: Perplexity AI mathematical review
**Current Grade**: B+ (target: A+)

---

## Summary

The Technical paper (`Logic_Realism_Theory_Technical.md`) requires three specific mathematical fixes to achieve reconstruction-paper quality. The conceptual framework is sound and aligns with Hardy/Masanes-Müller reconstruction literature, but technical rigor gaps remain.

---

## Issues Identified

### Issue 8.1: Inconsistent Metric Definition (HIGH)

**Problem**: The paper uses two different functional forms for the distinguishability metric D:

| Location | Definition Used |
|----------|-----------------|
| Theorem 3.2 | `D(s₁,s₂) = 1 - |⟨s₁|s₂⟩|²` |
| Bloch sphere (§3.4.1) | `D(ψ₁,ψ₂) = √(1 - |⟨ψ₁|ψ₂⟩|²)` (trace distance) |
| Angle definition | `D_ij = sin²(θ_ij/2)` |

These are not equivalent. Must choose one and propagate consistently.

**Impact**:
- Cosine law formulas become incorrect
- Angle definitions inconsistent
- Inner product reconstruction affected

**Resolution Options**:
1. Use trace distance throughout: `D = √(1 - |⟨ψ₁|ψ₂⟩|²)`
2. Use fidelity-based: `D = 1 - |⟨ψ₁|ψ₂⟩|²`

**Recommendation**: Use trace distance (option 1) as it's standard in GPT/reconstruction literature and matches the supremum-over-TV definition in §2.2.

---

### Issue 8.2: Hardy Kernel Construction (HIGH)

**Problem**: The Hardy kernel as defined:

```
K(x,y;z) := 1 - ½[D(x,y) + D(x,z) - D(y,z)]
```

becomes trivial when all three states are pairwise perfectly distinguishable:
- If D(x,y) = D(x,z) = D(y,z) = 1
- Then K(x,y;z) = 1 - ½(1+1-1) = ½ (constant, independent of geometry)

**Issues**:
- Claimed to satisfy "axioms of abstract inner product kernel" but not demonstrated
- Positive-definiteness not proven
- Cannot derive non-degenerate inner product from this formula alone

**Resolution**: Replace with standard reconstruction-grade argument:

1. **Convex-geometry route**:
   - Define convex state spaces and reversible group
   - Use Continuous Reversibility to show pure state space is unit ball of invariant inner product
   - Use Subspace Axiom to show gbit has Bloch-ball geometry with d=3

2. **Alternative**: If keeping kernel approach, prove positive-definiteness using standard distance-embedding results (Schoenberg conditions)

**Reference**: Masanes-Müller (2011), de la Torre et al. (2012) for standard approach

---

### Issue 8.3: Binary Distinction → Qubit Step (MEDIUM)

**Problem**: The claim "any binary distinction = qubit structure" (MM4 derivation in §4.3) is stronger than what's proven in Masanes-Müller.

**Current text**: "Any system with 2+ distinguishable states admits a binary distinction. Binary distinction = qubit structure (by A1, distinction is Boolean)"

**Issue**: MM requires explicit assumptions about existence and structure of a "gbit" and proves its state space must be a Euclidean ball. The step from "Boolean two-valued" to "Bloch-ball geometry with correct symmetry group" is non-trivial.

**Resolution**: Either:
1. Provide explicit argument that Boolean two-outcome structure + continuous reversibility + other axioms → Bloch-ball form
2. Cite existing result that enforces this (with exact hypotheses)
3. State as assumption and clarify it's imported from MM framework

---

## Required for A+ Grade

### R1: State Single Reconstruction Theorem

Create a flagship "LRT Reconstruction Theorem":

> "Any finite-dimensional GPT satisfying A1-A5 is operationally equivalent to complex quantum theory, and no strictly stronger no-signaling GPT extension satisfies A1-A5 plus composition closure."

Prove by explicit chain:
1. LRT axioms → MM axioms (each step cited)
2. MM axioms → QT or classical
3. Stability criteria eliminate non-QT options

### R2: Isolate External Theorems

Create dedicated "External Theorems" section listing:
- Masanes-Müller (2011): exact hypotheses
- Lee-Selby (2016): exact hypotheses
- de la Torre et al. (2012): exact hypotheses
- Uhlmann's theorem: statement

Then reference by name in proofs rather than inline citations.

### R3: Worked Examples

Add 1-2 fully worked finite-dimensional examples:
- LRT axiom-satisfying system → explicit complex Hilbert model + Born rule
- Parallel construction of real/quaternionic model showing failure of stability condition

---

## Grading Criteria (Perplexity assessment)

| Level | Requirements | Status |
|-------|--------------|--------|
| B+ | Current state - conceptually sound, technical gaps | CURRENT |
| A- | Fix Issues 8.1-8.3 | |
| A | Add R1 (reconstruction theorem) | |
| A+ | Add R2-R3, full reconstruction-paper quality | TARGET |

---

## Action Plan (All Required for A+)

1. [ ] **Fix metric consistency** (Issue 8.1)
   - Audit all uses of D in paper
   - Choose trace distance as standard
   - Update angle/cosine-law formulas

2. [ ] **Revise Hardy kernel section** (Issue 8.2)
   - Option A: Replace with convex-geometry argument
   - Option B: Prove positive-definiteness rigorously
   - Align with MM reconstruction pattern

3. [ ] **Strengthen MM4 derivation** (Issue 8.3)
   - Add explicit gbit → Bloch-ball argument or citation
   - Clarify what's derived vs imported

4. [ ] **Add reconstruction theorem** (R1)
   - Single statement with proof chain
   - Explicit external theorem references

5. [ ] **Create External Theorems section** (R2)
   - Masanes-Müller exact hypotheses
   - Lee-Selby exact hypotheses
   - de la Torre et al. exact hypotheses
   - Uhlmann's theorem statement

6. [ ] **Add worked examples** (R3)
   - LRT → complex Hilbert model example
   - Real/quaternionic failure example

---

## Files Affected

- `theory/Logic_Realism_Theory_Technical.md` (primary)
- `theory/Logic_Realism_Theory_Technical-v2.md` (v2 copy)
- PDFs will need regeneration after fixes

---

## References

- Masanes, Ll. & Müller, M. P. "A derivation of quantum theory from physical requirements." New J. Phys. 13, 063001 (2011)
- Hardy, L. "Quantum Theory From Five Reasonable Axioms." arXiv:quant-ph/0101012 (2001)
- Lee, C. M. & Selby, J. H. "Deriving Grover's lower bound from simple physical principles." New J. Phys. 18, 093047 (2016)
- de la Torre, G. et al. "Deriving quantum theory from its local structure and reversibility." Phys. Rev. Lett. 109, 090403 (2012)
- Wootters, W. K. "Local accessibility of quantum states." (1990)

---

## Notes

Perplexity assessment: "The bones are there - the structural pieces match successful reconstruction papers. Reaching A+ is polish and rigor, not rethinking the foundational picture."

**Backup of original Perplexity review**: `Issue_008_Perplexity-Technical-paper-improvements_BACKUP.md`
