# Issue 011: Null Hypothesis Development

**Date**: 2025-12-13
**Status**: OPEN
**Priority**: High
**Source**: Reddit critique - "What's your null hypothesis?"

---

## Problem Statement

LRT has established falsification criteria, but lacks a clearly articulated **null hypothesis** that distinguishes it from standard QM. A critic correctly pointed out: if standard QM also never produces macroscopic P∧¬P, what exactly is the null hypothesis that LRT is testing against?

---

## Current Falsification Criteria

### Tier 1: Core LRT Falsification

| Criterion | Description | Status |
|-----------|-------------|--------|
| Macroscopic P∧¬P | A stable, contradictory measurement outcome at macroscopic scale | Never observed; would falsify LRT |
| β > 2 observation | Decoherence scaling faster than quadratic | Never observed; would falsify LRT |

### Tier 2: Derived Predictions

| Prediction | Derivation | Testable? |
|------------|------------|-----------|
| Complex QM uniqueness | From MM axioms via 3FLL | Confirmed (2021 reconstructions) |
| Born rule | From IIS structure | In development |
| Reversibility | From CBP + Global Parsimony | Standard QM feature |

---

## The Null Hypothesis Problem

### Current Framing

**LRT claims**: 3FLL are ontological constraints → β ≤ 2 is *necessary*
**Standard QM observes**: β ≤ 2 for all known mechanisms → β ≤ 2 is *contingent*

### The Critique

If both frameworks predict β ≤ 2, how do we distinguish them empirically?

**Possible answers:**

1. **Modal distinction**: LRT says β > 2 is *impossible in principle*; standard QM says it *happens not to occur*
2. **Explanatory depth**: LRT explains *why* β ≤ 2; standard QM takes it as empirical fact
3. **Future mechanism constraint**: If someone proposes a mechanism with β > 2, LRT rejects it a priori; standard QM evaluates it empirically

### The Gap

These distinctions are philosophical, not directly empirical. We need sharper criteria.

---

## Proposed Null Hypothesis Structure

### H₀ (Standard QM)

> Decoherence scaling exponent β is determined by the specific physical mechanism and environmental coupling. There is no principled upper bound; β ≤ 2 is an empirical regularity that could be violated by future mechanisms.

### H₁ (LRT)

> Decoherence scaling exponent β ≤ 2 is a necessary constraint derived from the logical structure of Boolean actualization. No physical mechanism can produce β > 2 because the N² coherent phase accumulation ceiling is set by the mathematics of actualization itself.

### Distinguishing Test

The hypotheses diverge when:
1. A mechanism is proposed that *should* produce β > 2 under standard QM
2. LRT predicts it will fail; standard QM predicts it could succeed
3. Experiment adjudicates

**Problem**: No such mechanism has been proposed. All known mechanisms (CSL, GRW, superradiance) give β ≤ 2.

---

## Tier 1 vs Tier 2 Analysis

### Tier 1 Criteria (Would Falsify Core LRT)

| Criterion | What Would Falsify LRT | What Would Falsify Standard QM |
|-----------|------------------------|--------------------------------|
| Macroscopic P∧¬P | Yes | Also yes (violates measurement postulates) |
| β > 2 observed | Yes | No (just new mechanism) |

**Key insight**: The β > 2 criterion is the **only** Tier 1 criterion where LRT and standard QM diverge in their predictions.

### Tier 2 Criteria (Would Require Revision, Not Falsification)

| Criterion | LRT Prediction | Standard QM Prediction |
|-----------|----------------|------------------------|
| Born rule derivable from logic | Yes (in development) | No (taken as axiom) |
| Complex numbers necessary | Yes (derived) | Yes (but as input) |
| Measurement problem solvable | Yes (Stage 2→3 transition) | Interpretation-dependent |

---

## Development Tasks

### Immediate

- [ ] Articulate precise null hypothesis H₀ vs H₁
- [ ] Identify any proposed mechanisms that would produce β > 2
- [ ] Survey collapse model literature for parameter spaces approaching β > 2
- [ ] Clarify what "principled impossibility" means operationally

### Medium-term

- [ ] Develop rigorous derivation of β ≤ 2 from LRT axioms (currently sketch only)
- [ ] Identify experimental regime where β approaches 2 (superdecoherence limit)
- [ ] Design protocol for testing whether β = 2 is saturated or merely approached

### Long-term

- [ ] Standalone paper: "The Null Hypothesis for Logic Realism Theory"
- [ ] Engage with collapse model community on LRT constraints
- [ ] Propose experiment to test LRT in sharp regime (N ≥ 10⁶)

---

## Key Questions

1. **Is "necessary vs contingent" empirically distinguishable?**
   - If no mechanism can produce β > 2, both frameworks agree on observations
   - The distinction becomes philosophical, not physical
   - This is acceptable if LRT provides explanatory depth (cf. thermodynamics)

2. **What would convince a skeptic?**
   - Skeptic: "You're just agreeing with QM and calling it necessary"
   - Response needed: Either (a) find a case where predictions diverge, or (b) articulate why explanatory depth matters even without divergent predictions

3. **Is LRT falsifiable in practice?**
   - Tier 1 criterion (β > 2) has never been observed
   - Is this because it's impossible (LRT) or because we haven't looked in the right regime (standard QM)?
   - The N ≥ 10⁶ regime with controlled decoherence is the target

---

## Related Documents

- `theory/supplementary/LRT_Prediction_Beta_Bound_Development.md` - β ≤ 2 derivation work
- `theory/supplementary/Scale_Law_Boolean_Actualization.md` - Empirical validation
- `theory/LRT_Internal_Assessment.md` - Honest evaluation
- `review_response/2025-12-13_Reddit_Detector_Superposition_Critique.md` - Critic response

---

## Success Criteria

Issue is RESOLVED when:
1. Clear null hypothesis H₀ is articulated
2. Distinguishing predictions (if any) are identified
3. Experimental path to test is documented
4. Honest assessment of "necessary vs contingent" distinction is complete

---

*Issue created 2025-12-13, Session 40.0*
