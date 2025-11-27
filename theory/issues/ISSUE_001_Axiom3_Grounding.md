# ISSUE 001: Grounding Axiom 3 (Physical Constraints)

**Status**: OPEN
**Priority**: CRITICAL
**Created**: 2025-11-26
**Source**: External reviews (Gemini, Grok, GPT synthesis)

---

## Problem Statement

LRT claims to derive quantum mechanics from logical foundations. However, **Axiom 3** (Physical Constraints) contains three sub-axioms that are **physical postulates, not logical necessities**:

- **3a: Continuity** - Between any two states, there exists a continuous path
- **3b: Reversibility** - All transformations have inverses
- **3c: Local Tomography** - Composites are determined by local measurements

These are exactly the axioms used in reconstruction theorems (Hardy, Masanes-Müller, CDP). LRT has not reduced the axiom count - it has repackaged them with philosophical narrative.

**Core critique (Grok):**
> "Logic alone does not demand 'Continuous Transformations' or 'Local Tomography.'"

**Core critique (Gemini):**
> "The derivation of Hilbert Space relies on Axiom 3... These are physical postulates, not logical ones."

---

## Current Status in LRT

| Sub-Axiom | Current Justification | Status |
|-----------|----------------------|--------|
| Continuity | "Required for dynamics to be well-defined" | Asserted |
| Reversibility | "Required for information preservation in IIS" | Asserted |
| Local Tomography | "Required for compositional physics" | Asserted |

All three are justified by appeal to what stable physics requires, not derived from 3FLL or distinguishability.

---

## The Challenge

Can these constraints be **derived** from more primitive LRT commitments (3FLL, distinguishability, IIS structure)?

### What Would Count as Derivation

A successful derivation would show:

1. **Continuity**: Given only 3FLL + distinguishability structure, continuous transformations are forced (not merely permitted)

2. **Reversibility**: Given only 3FLL + distinguishability structure, reversible dynamics are forced

3. **Local Tomography**: Given only 3FLL + distinguishability structure, composite states must be determinable from local measurements

### What Would NOT Count

- Circular arguments that assume the conclusion
- Arguments that merely show these are "natural" or "reasonable"
- Stability/anthropic selection (explains observation, not existence)

---

## Potential Derivation Approaches

### Approach A: From Information Preservation

**Hypothesis**: If IIS is the space of all distinguishable configurations, then:
- Transformations that destroy distinguishability information cannot be fundamental
- Therefore dynamics must be information-preserving
- Information-preserving = reversible + (possibly) continuous

**Problem**: Why continuous? Discrete reversible dynamics exist.

**Status**: Partial at best

---

### Approach B: From Distinguishability Metric Structure

**Hypothesis**: Distinguishability defines a metric on IIS. The metric structure may constrain transformations.

**Potential argument**:
1. Distinguishability D(x,y) defines a distance
2. Distances satisfy triangle inequality
3. Transformations preserving distinguishability must preserve metric structure
4. Metric-preserving transformations form a continuous group (?)

**Problem**: Step 4 is not obviously true. Discrete isometries exist.

**Status**: Needs investigation

---

### Approach C: From Compositional Distinguishability (Local Tomography)

**Hypothesis**: If distinguishability is fundamentally pairwise (Axiom 2), then global distinguishability must be reconstructible from pairwise comparisons.

**Potential argument**:
1. D(x,y) compares two states
2. For composite systems AB, distinguishability must still be pairwise
3. Pairwise comparison of composite states = comparing local subsystems pairwise
4. Therefore composite distinguishability is determined by local distinguishability
5. This is local tomography

**Problem**: Step 3 is the leap. Why can't composite pairwise comparison involve irreducibly global structure?

**Status**: Most promising direction

---

### Approach D: Constructor-Theoretic Grounding

**Hypothesis**: Axiom 3 constraints can be reformulated as constructor-theoretic impossibility conditions.

**Potential argument**:
1. A "constructor" is something that enables a task repeatedly
2. For the IIS→Boolean interface to function as a constructor, certain tasks must be possible/impossible
3. Continuity and reversibility may be necessary for the interface to be a reliable constructor
4. Local tomography may be necessary for composite tasks to be possible

**References**: Deutsch & Marletto, Constructor Theory

**Status**: Unexplored, flagged by Gemini review

---

### Approach E: From 3FLL Enforcement Requirements

**Hypothesis**: The specific structure of 3FLL enforcement at the interface constrains IIS dynamics.

**Potential argument**:
1. Boolean actuality requires Excluded Middle (every proposition has a truth value)
2. Non-Contradiction requires consistency across contexts
3. Identity requires states to be re-identifiable
4. For the interface to enforce these across all contexts, the underlying structure must have specific properties
5. These properties entail continuity, reversibility, local tomography

**Problem**: Very hand-wavy. The connection from 3FLL to continuous groups is not obvious.

**Status**: Needs rigorous development

---

### Approach F: Logical Time (Resolution Ordering)

**Hypothesis**: Time is the partial ordering of Boolean resolutions relative to IIS paths. If this is correct, Axiom 3 constraints may be derivable as requirements for coherent logical sequencing.

**Core claim**: Time = ordering of IIS→Boolean transitions
- Before resolution: propositions are modal (in IIS)
- After resolution: propositions are Boolean (in actuality)
- The transition defines a direction
- The ordering of transitions defines proto-time

**Potential derivations**:

1. **Continuity from coherent sequencing**:
   - Discontinuities would produce broken causal graphs
   - Impossible truthmaker assignments
   - Non-re-identifiable identity structures
   - Therefore: continuity is a constraint on coherent resolution-ordering

2. **Reversibility from pre-resolution structure**:
   - In IIS: no Boolean commitments made
   - No information is lost (no resolution has occurred)
   - All propositions remain open
   - Therefore: IIS dynamics must be reversible
   - Irreversibility only enters at the interface (Boolean stamping)

3. **Local Tomography from temporal interface-locality**:
   - Resolution must be localized (interaction boundaries)
   - Resolution applies to subsystems before composites
   - Sequential: resolved A, then resolved AB joint structure
   - Therefore: composite distinguishability = what can be resolved by temporally local sequences

**Key insight**: If we can derive *all three* from a single principle ("coherent logical sequencing"), this is a reduction even if that principle is additional.

**Potential problems**:
- "Coherent sequencing" may itself be a physical assumption
- Why must resolution ordering be coherent? (Stability assumption?)
- "Local resolution" may presuppose local tomography (circularity)
- "Pre-resolution has no information loss" may assume structure preservation

**Status**: INVESTIGATED - see DERIVATION_ATTEMPT_LogicalTime.md

**Investigation Results (2025-11-27)**:
- Reversibility: PARTIAL SUCCESS (gets injectivity from IIS maximality, needs additional principle for surjectivity)
- Continuity: NOT DERIVED ("coherent sequencing" not precise enough to force continuity)
- Local Tomography: NOT DERIVED (circular - assumes locality to derive it)

**Conclusion**: Better philosophical grounding than "physical axioms" but still not pure logical derivation. Upgrades framing from "selection" to "structural requirements on interface."

**References**:
- Sorkin, R. (causal sets)
- Isham, C. (quantum event structures)
- Lamport, L. (logical time/clocks)

---

## Specific Sub-Issues

### ISSUE 001a: Derive Continuity

**Question**: Can we show that IIS dynamics must be continuous, given only 3FLL + distinguishability?

**Leads**:
- Metric structure from distinguishability
- Topological requirements for consistent interface
- Information-theoretic continuity bounds

---

### ISSUE 001b: Derive Reversibility

**Question**: Can we show that IIS dynamics must be reversible, given only 3FLL + distinguishability?

**Leads**:
- Information preservation
- Landauer's principle connection
- Time-symmetry of distinguishability

---

### ISSUE 001c: Derive Local Tomography (HIGHEST PRIORITY)

**Question**: Can we show that composite distinguishability must be locally determined, given only 3FLL + pairwise distinguishability?

**Leads**:
- Compositional distinguishability argument (Approach C)
- Constructor theory (Approach D)
- Information-theoretic locality

**Grok assessment**: "If local tomography could be derived from more primitive distinguishability considerations, the theory would be vastly strengthened."

---

## Success Criteria

A derivation is successful if:

1. **Non-circular**: Does not assume what it proves
2. **Valid**: Each step follows logically
3. **Grounded**: Uses only 3FLL, distinguishability, IIS definition, and previously derived results
4. **Explicit**: All assumptions are stated

---

## Fallback Position

If derivations fail, the honest position is:

> "Axiom 3 (Physical Constraints) is not derived from logic alone. It represents the additional requirements for a stable, compositional interface. LRT's contribution is showing these requirements are not arbitrary but are precisely the conditions that enable Boolean actuality to interface with IIS structure."

This is the "meta-theoretical interpretation" framing that remains defensible.

---

## Investigation Results (2025-11-26)

### Detailed Derivation Attempts

See companion documents:
- `DERIVATION_ATTEMPT_LocalTomography.md` (7 approaches tested)
- `DERIVATION_ATTEMPT_Continuity_Reversibility.md` (5 approaches each)

### Summary of Findings

| Constraint | Derivation Status | Best Available Argument |
|------------|-------------------|------------------------|
| **Continuity** | NOT DERIVED | Stability selection (discontinuous dynamics prevents stable structures) |
| **Reversibility** | CONDITIONALLY DERIVED | Structure preservation (dynamics should be automorphisms of IIS) |
| **Local Tomography** | NOT DERIVED | Compositionality requirement (physics must be modular) |

### Key Finding

**None of the three Axiom 3 constraints can be derived from 3FLL + distinguishability alone.**

The attempts reveal:
1. Local tomography cannot follow from pairwise distinguishability - the two are independent properties
2. Reversibility can be motivated by structure preservation, but structure preservation is itself a physical principle
3. Continuity has only stability/selection arguments, not logical derivations

### Implications for LRT

1. **The honest position**: Axiom 3 is a physical axiom package, not logically derivable
2. **The achievable claim**: LRT provides philosophical justification for why these constraints are natural requirements for stable interface physics
3. **The open problem**: Deriving any of these from deeper principles remains the most important technical challenge for LRT

### Grounding Hierarchy

If we must rank how well-grounded each constraint is:

1. **Reversibility** (best): Follows from "dynamics preserve structure" - a natural principle for fundamental physics
2. **Local Tomography** (moderate): Follows from compositionality - physics must be modular
3. **Continuity** (weakest): Only stability selection - no logical argument found

---

## Recommended Action

1. ✅ Revise Section 16 with explicit "Derivation Status" subsection (COMPLETED 2025-11-27)
2. ✅ Adopt "meta-theoretical interpretation" framing per GPT recommendation (COMPLETED - Section 16.8)
3. ✅ Add Constructor Theory as future direction (COMPLETED - noted in Section 16.8)
4. Keep local tomography derivation as highest-priority open problem

---

## References

- Masanes, L. and Müller, M. P. (2011). "A derivation of quantum theory from physical requirements."
- Hardy, L. (2001). "Quantum theory from five reasonable axioms."
- Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). "Informational derivation of quantum theory."
- Deutsch, D. and Marletto, C. (2015). "Constructor theory of information."
