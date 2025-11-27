# Derivation Attempt: Local Tomography from Compositional Distinguishability

**Issue**: ISSUE 001c
**Date**: 2025-11-26
**Status**: IN PROGRESS

---

## Goal

Derive local tomography from:
- Axiom 1: 3FLL constitute distinguishability
- Axiom 2: Distinguishability is pairwise
- Definition: IIS is the space of distinguishable configurations

WITHOUT assuming local tomography or any reconstruction axiom that entails it.

---

## Attempt 1: From Pairwise Structure

### Argument

1. Distinguishability D: IIS × IIS → [0,1] is a binary relation (Axiom 2)
2. For composite systems AB, states ψ_AB live in some composite space
3. D(ψ_AB, φ_AB) must still be pairwise - it compares two composite states
4. The pairwise character means D factors through pairs...

### Problem

Step 4 doesn't follow. Pairwise comparison of composite states doesn't entail that the comparison factors through local comparisons. We're conflating:
- **Syntactic pairwise**: D takes two arguments
- **Semantic locality**: D can be computed from local data

These are independent properties.

### Verdict: FAILS

---

## Attempt 2: From Compositional Identity

### Argument

1. Identity law: x = x for all x ∈ IIS
2. For composite state ψ_AB, we have ψ_AB = ψ_AB
3. The identity of ψ_AB must be determinable
4. To determine identity, we need to check D(ψ_AB, φ_AB) = 0 for relevant φ_AB
5. If this required irreducibly global operations, identity would be "holistic"
6. But Identity should be "locally checkable" because...

### Problem

Step 6 is the question, not an answer. Nothing in the Identity law says identity must be locally checkable. A state could have identity determined by global properties.

### Verdict: FAILS (begs the question)

---

## Attempt 3: From Non-Contradiction Applied to Composites

### Argument

1. Non-Contradiction: ¬(P ∧ ¬P) for all propositions P
2. For composite AB, propositions include "state of A is ρ_A" and "state of B is ρ_B"
3. Non-Contradiction requires consistency: if ψ_AB assigns ρ_A to A and ρ_B to B, these cannot contradict
4. For consistency to be checkable, the local states ρ_A, ρ_B must determine the joint state
5. This is local tomography

### Problem

Step 4 is the leap. Consistency can be checked even if local states don't fully determine the joint state - we just check that the joint state is compatible with the local assignments. That's weaker than local tomography.

In fact, entangled states ARE consistent (no contradiction) but ARE NOT product states. Entanglement is precisely the case where local states don't determine the global state.

### Verdict: FAILS

---

## Attempt 4: From Information-Theoretic Locality

### Argument

1. Information is grounded in distinguishability (LRT core claim)
2. The information content of ψ_AB is the set of distinguishability relations it participates in
3. Information should satisfy locality: information about AB = information about A + information about B + correlations
4. If correlations are themselves expressible in local terms, we get local tomography

### Problem

Step 3 is an assumption, not a derivation. Why should information satisfy locality? Quantum mechanics violates this (entanglement has irreducibly global information).

More precisely: the Shannon mutual information I(A:B) can be non-zero for entangled states, which means AB carries information not reducible to A and B separately. But local tomography says the STATE is determined by local measurements - that's different from saying information is local.

### Verdict: FAILS (assumes what it should prove)

---

## Attempt 5: From Excluded Middle Applied to Measurement Contexts

### Argument

1. Excluded Middle: P ∨ ¬P for all propositions P
2. At the interface (Boolean actuality), every measurement has a definite outcome
3. For composite AB, measurements can be local (on A alone) or global (on AB jointly)
4. Excluded Middle applies to both local and global measurements
5. The joint state must assign probabilities to all measurements
6. If local measurements suffice to determine these probabilities, we have local tomography

### Problem

Step 6 assumes local measurements suffice. That's local tomography itself.

Actually, local tomography says: local measurement STATISTICS determine the STATE. The state then determines probabilities for global measurements. This is different from saying local measurements determine global measurement probabilities directly.

### Verdict: FAILS (wrong formulation)

---

## Attempt 6: From Reconstruction of Distinguishability

### Setup

Let's think about what local tomography really says:

**Local Tomography**: For any composite system AB, the state ρ_AB is uniquely determined by the set of all local measurement statistics:
{P(a|M_A, ρ_AB), P(b|M_B, ρ_AB)} for all local measurements M_A, M_B

Equivalently: two states ρ_AB and σ_AB are distinguishable (D > 0) iff they differ on some local measurement statistic.

### Argument

1. Distinguishability is the fundamental relation (LRT)
2. D(ρ_AB, σ_AB) > 0 iff ρ_AB and σ_AB can be differentiated
3. Differentiation requires a procedure that gives different results
4. **Key claim**: Any differentiation procedure can be decomposed into local operations
5. Therefore D(ρ_AB, σ_AB) > 0 iff they differ locally
6. This is local tomography

### Analysis of Step 4

Why should differentiation procedures be decomposable into local operations?

**For**:
- We physically implement measurements on subsystems
- Global measurements are built from local interactions
- No "holistic" measurement apparatus exists

**Against**:
- This is a physical assumption about how measurements work
- Nothing in 3FLL or distinguishability forces it
- Quantum mechanics itself has global observables (e.g., total spin) that aren't simple products of local observables

### Verdict: PARTIAL SUCCESS / CONDITIONAL

If we add the assumption:
> "All distinguishing procedures are composable from local procedures"

Then local tomography follows. But this assumption is physical, not logical.

---

## Attempt 7: From Constructor-Theoretic Principles

### Framing

In Constructor Theory, the fundamental objects are:
- **Tasks**: Transformations specified by input→output
- **Constructors**: Things that enable tasks and remain unchanged

### Argument

1. The IIS→Boolean interface is a constructor (enables measurement tasks repeatedly)
2. For composite systems, the interface must enable local tasks (measuring A) and global tasks (measuring AB)
3. A well-functioning constructor for composites must compose from constructors for parts
4. **Constructor composability principle**: If C_A enables tasks on A and C_B enables tasks on B, then C_AB = C_A ⊗ C_B enables tasks on AB
5. For this to work, the state of AB must be determinable from how it responds to C_A and C_B
6. This is local tomography

### Analysis

Step 4 (constructor composability) is a non-trivial assumption. It's essentially saying:
> "Physics must be modular - composite systems are built from components"

This is plausible but not derivable from pure logic.

### Verdict: CONDITIONAL

Local tomography follows from constructor composability. But constructor composability is itself a physical principle, not a logical one.

---

## Summary of Attempts

| Attempt | Approach | Result |
|---------|----------|--------|
| 1 | Pairwise structure | FAILS |
| 2 | Compositional identity | FAILS |
| 3 | Non-Contradiction | FAILS |
| 4 | Information locality | FAILS |
| 5 | Excluded Middle | FAILS |
| 6 | Decomposable differentiation | CONDITIONAL |
| 7 | Constructor composability | CONDITIONAL |

---

## Key Finding

**Local tomography cannot be derived from 3FLL + distinguishability alone.**

The best we can do is derive it from 3FLL + distinguishability + one of:
- "Differentiation procedures decompose locally"
- "Constructors compose modularly"
- "Information is locally accessible"

All of these are **physical principles** about how the world works, not logical necessities.

---

## Implications for LRT

### Option A: Accept Local Tomography as Physical Axiom

Be explicit that Axiom 3c is a physical postulate:

> "Local tomography captures the physical requirement that composite systems are not generically inscrutable. It is not derivable from logic alone but represents the requirement that physics be compositional."

### Option B: Reframe as Stability Requirement

Local tomography is necessary for stable, compositional physics:

> "Without local tomography, composite systems would have 'hidden' degrees of freedom inaccessible to local operations. Such systems could not support stable structures or reliable information processing."

### Option C: Flag as Highest-Priority Open Problem

Explicitly acknowledge:

> "Deriving local tomography from more primitive distinguishability considerations is the most important open problem for strengthening LRT's foundations."

---

## Recommended Position

Combine Options A and C:

1. **Acknowledge** local tomography is axiomatized, not derived
2. **Justify** it as a compositionality requirement (physical, not logical)
3. **Flag** its derivation as the key open problem
4. **Investigate** Constructor Theory and information-theoretic approaches

---

## Next Steps

1. Document this result in ISSUE 001
2. Attempt derivations for continuity and reversibility
3. Revise Section 16 to reflect honest status
4. Add Constructor Theory subsection per GPT recommendation
