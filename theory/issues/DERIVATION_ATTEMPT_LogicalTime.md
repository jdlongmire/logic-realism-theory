# Derivation Attempt: Axiom 3 from Logical Time (Approach F)

**Issue**: ISSUE 001
**Date**: 2025-11-27
**Status**: IN PROGRESS
**Source**: GPT synthesis proposal

---

## The Proposal

Treat time as **logical sequencing** - the ordering relation inherent in the IIS→Boolean interface:

- **Time** = partial ordering of Boolean resolutions relative to IIS paths
- **Before resolution**: propositions are modal (in IIS)
- **After resolution**: propositions are Boolean (in actuality)
- **The ordering** of these transitions defines proto-time

**Claim**: Axiom 3 constraints follow as requirements for *coherent logical sequencing*.

---

## Derivation Attempt 1: Reversibility from Pre-Resolution Structure

### Argument

1. IIS is the space of all distinguishable configurations (Definition 16.3)
2. Boolean actuality is where 3FLL are enforced - propositions have definite truth values
3. The interface maps IIS → Boolean outcomes
4. **Key observation**: Before resolution (within IIS), no Boolean commitment has been made
5. No Boolean commitment ⟹ no truth value has been "stamped"
6. Therefore no information about truth values has been created
7. But information creation is irreversible (Landauer's principle)
8. Therefore: within IIS, transformations create no information
9. Information-neutral transformations are reversible
10. **Conclusion**: IIS dynamics must be reversible

### Critical Analysis

**Step 4-6**: This is the key move. Is it valid?

The argument equates "no Boolean commitment" with "no information creation." But this conflates two notions:
- **Semantic information** (truth values about propositions)
- **Physical information** (distinguishability structure)

Within IIS, there is distinguishability structure. Transformations on IIS can alter this structure. If a transformation T maps two distinguishable states to one (T(x) = T(y) for x ≠ y), information about which state we had is lost - even without Boolean resolution.

**Step 7**: Landauer's principle says erasure of information requires heat dissipation. But we're not doing thermodynamics here; we're asking about the logical structure of IIS.

**Step 8**: "Information-neutral" is ambiguous. Does it mean:
- (a) No truth values created? Then it's tautological before resolution.
- (b) No distinguishability lost? Then we've assumed structure preservation.

### Refined Argument

Let me try a cleaner version:

1. IIS is defined as the maximal space closed under distinguishability
2. Distinguishability D is the fundamental structure of IIS (Axiom 1, 2)
3. Transformations T: IIS → IIS that reduce distinguishability (D(Tx, Ty) < D(x,y)) "lose" structure
4. If T loses structure, Tx and Ty are "less within" IIS than x and y were
5. But IIS is maximal - it contains all that can be distinguished
6. So T cannot map into a "smaller" distinguishability space while staying in IIS
7. Therefore T must preserve distinguishability: D(Tx, Ty) = D(x,y)
8. Distinguishability-preserving ⟹ injective ⟹ reversible

**Problem with Step 4-6**: This argument proves too much. It says *all* IIS transformations preserve distinguishability. But we allow transformations that increase D(x,y) too (entangling operations). The real constraint is just injectivity.

**Step 8 also has a gap**: Injective does not imply surjective. We need reversibility = bijective.

### Verdict on Reversibility

**PARTIAL SUCCESS** with caveats:

The argument establishes that fundamental IIS dynamics should not destroy distinguishability (should be injective). This follows from IIS being the maximal distinguishability space.

But:
- Why must dynamics also be surjective (onto)?
- This requires either: (a) compactness assumption, (b) conservation principle, or (c) time-reversal symmetry

**Status**: Better grounded than before, but still needs a surjectivity principle.

The "logical time" framing adds: if we interpret IIS dynamics as "pre-resolution," then there's no arrow of time yet, so time-reversal symmetry is natural. This is suggestive but not rigorous.

---

## Derivation Attempt 2: Continuity from Coherent Sequencing

### Argument (GPT's Version)

1. Time = ordering of IIS→Boolean resolutions
2. Discontinuous dynamics produce "jumps" in the resolution sequence
3. Such jumps create:
   - Broken causal graphs
   - Impossible truthmaker assignments
   - Non-re-identifiable identity structures
4. Therefore: coherent resolution-ordering requires continuous dynamics

### Critical Analysis

**Step 2**: What does "discontinuous dynamics" mean precisely?

In a metric space, T is discontinuous if ∃ε>0 such that for all δ>0, ∃x,y with d(x,y)<δ but d(Tx,Ty)>ε.

So discontinuity means: arbitrarily small changes in input can produce large changes in output.

**Step 3**: Why does this break things?

(a) **Broken causal graphs**: This assumes we have causal structure. But causality is what we're trying to derive. Circular.

(b) **Impossible truthmaker assignments**: How? If T is a valid map on IIS, it produces valid states. The truthmaker for "system is in state Tx" is just that state. No contradiction.

(c) **Non-re-identifiable identity structures**: This is the most promising angle.

### Identity Argument for Continuity

Let's pursue (c):

1. Identity law: x = x for all x ∈ IIS
2. States must be re-identifiable through time (to track "the same" system)
3. If T is discontinuous, an infinitesimal perturbation can send state x to a completely different region
4. We cannot then say "this is the same system" - identity through change is lost
5. Therefore: continuity is required for identity preservation through dynamics

**Problem**: Step 2 adds a requirement not in 3FLL. The Identity law says x = x at an instant. It doesn't say we must be able to track x through transformations.

However, there's a response: if we want to apply 3FLL to dynamics (not just statics), we need to identify what proposition "state is x at time t₁" refers to at time t₂. This requires tracking states.

**Counter-response**: We could have tracking without continuity. Discrete dynamical systems track states perfectly well.

### Alternative: Topological Argument

1. Distinguishability D induces a topology on IIS
2. "Meaningful" transformations should respect this topology
3. Topology-respecting = continuous

**Problem**: Step 2 is an assumption. Why must transformations respect the D-induced topology?

### Verdict on Continuity

**NOT DERIVED** - same conclusion as before.

The "logical time" framing provides suggestive language but no rigorous derivation:
- "Coherent sequencing" is not defined precisely enough to force continuity
- Identity-tracking argument requires assuming we want to track identity
- Topological argument assumes transformations should respect topology

The best available argument remains: discontinuous dynamics would prevent stable structures (selection argument).

---

## Derivation Attempt 3: Local Tomography from Temporal Interface-Locality

### Argument (GPT's Version)

1. Resolution = IIS→Boolean transition at the interface
2. Resolution must be "localized" in some sense
3. For composite system AB, resolution occurs on subsystems:
   - First resolve A (or B)
   - Joint structure AB then constrained by local resolutions + entanglement
4. This sequential, local resolution structure means: composite state is determined by local resolution statistics
5. This is local tomography

### Critical Analysis

**Step 2**: Why must resolution be localized?

This is the key question. GPT says "interaction boundaries" but that's physical, not logical.

**Attempt to derive locality**:

Consider the interface map Φ_C: IIS → Boolean for context C.

For composite system AB with state ψ_AB:
- Context C could be global (on AB jointly)
- Context C could be local (C_A on A, C_B on B)

**Claim**: If the interface "stamps" Boolean values, and systems A and B are spatially separated, then the interface must act locally.

**Problem**: We haven't derived spatial separation yet! This assumes a spatial structure that should emerge from the theory, not be presupposed.

### Alternative: Truthmaker Locality

1. Every Boolean proposition has a truthmaker (Axiom/Principle from Section 16)
2. The truthmaker for "measurement on A yields outcome a" must be localized to A
3. It cannot depend on distant structure (would violate some locality principle)
4. Therefore: local measurements have local truthmakers
5. If composite state is determined by truthmakers, and local truthmakers are sufficient, we get local tomography

**Problem with Step 3**: What locality principle? This assumes locality to derive it.

### The Circularity Problem

Local tomography says: local measurements determine global state.

Any argument of the form "because measurements are local, we have local tomography" is circular - it assumes measurements are local (which is part of what local tomography asserts).

### Can Logical Time Help?

The "logical time" framing says: resolution happens sequentially.

**Attempt**:
1. Resolutions happen in sequence (define proto-time)
2. Each resolution is a "single event"
3. A single event cannot simultaneously resolve multiple independent questions
4. Therefore: each resolution is "local" to a single question/subsystem
5. Global state = accumulation of local resolutions

**Problem with Step 3**: Why can't a single resolution event resolve multiple questions? This assumes events are atomic and local.

**Problem with Step 5**: Even if resolutions are sequential and local, the global state could have additional structure not captured by local resolutions (entanglement). Local tomography says there's NO such additional structure.

### Verdict on Local Tomography

**NOT DERIVED** - same conclusion as before.

The "logical time" framing does not escape the fundamental problem: local tomography is a claim about what determines the global state, and no amount of "sequential resolution" forces the global state to be locally determined.

The best available argument remains: compositionality requirement (physics must be modular).

---

## Summary of Approach F

| Constraint | Logical Time Argument | Status |
|------------|----------------------|--------|
| Reversibility | Pre-resolution = no Boolean commitment = no information loss | PARTIAL (gets injectivity, not full bijection) |
| Continuity | Coherent sequencing requires smooth ordering | NOT DERIVED (selection argument only) |
| Local Tomography | Temporal interface-locality | NOT DERIVED (circular - assumes locality) |

### Key Finding

The "logical time" framing provides:
1. **Better philosophical grounding** for reversibility (pre-resolution = open possibilities)
2. **Suggestive language** for continuity (coherent sequencing)
3. **No progress** on local tomography

It does NOT achieve non-circular derivation of any Axiom 3 constraint from 3FLL alone.

### What Would Be Needed

To derive these constraints from logical time, we would need to add:

**For Reversibility**: A surjectivity principle (time-reversal symmetry, conservation, or compactness)

**For Continuity**: A precise definition of "coherent sequencing" that forces continuity without assuming it

**For Local Tomography**: A principle that forces the interface to be local - but this seems to be exactly what we're trying to derive

### Honest Assessment

The proposal upgrades LRT's grounding from:
- "Physical constraints required for stable physics" (selection)

to:
- "Constraints on coherent logical sequencing" (structural)

This is philosophically preferable but still not a pure logical derivation.

**Recommendation**: Integrate the "logical time" perspective into Section 16.8 as improved grounding, while maintaining honesty that these are structural requirements on the interface, not pure logical necessities.

---

## References

- Sorkin, R. D. (2003). "Causal Sets: Discrete Gravity"
- Isham, C. J. (1994). "Quantum Logic and the Histories Approach to Quantum Theory"
- Lamport, L. (1978). "Time, Clocks, and the Ordering of Events in a Distributed System"
- Deutsch, D. and Marletto, C. (2015). "Constructor Theory of Information"

