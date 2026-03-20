# Section 1.1: Scope Addition (After Standard QM Postulates)

**Location**: Insert after listing the 5 standard QM postulates, before "The question persists..."

**Purpose**: Explicitly state what we derive and what we do NOT derive (addressing reviewer)

---

## Addition to Section 1.1

### Scope of This Work

This paper addresses **one** postulate from the standard formulation: **the Born rule** (Postulate 3 above). We derive Born probabilities P = |⟨a|ψ⟩|² for static quantum states from two foundational axioms (classical logic for measurement outcomes + identity permutation as reference) combined with information-theoretic principles (maximum entropy).

**What we successfully derive**:

1. ✅ **Born rule probabilities** - P(σ) = 1/|V_K| for valid states (Section 3)
2. ✅ **Hilbert space structure** - Orthogonality from distinguishability (Section 3.4)
3. ✅ **Superposition and interference** - From phase coherence (Section 3.5)
4. ✅ **Constraint threshold** - K(N) = N-2 multiply-determined by three independent proofs (Section 4.5)
5. ✅ **Amplitude hypothesis** - |a_σ|² = 1/|V_K| from MaxEnt on amplitude space (Section 3.2)

**What we do NOT derive** (limitations stated explicitly):

1. ❌ **Time evolution** - Schrödinger equation i∂|ψ⟩/∂t = Ĥ|ψ⟩ is not derived from first principles in this work. We show that the graph Laplacian Hamiltonian H = D - A emerges naturally from Fisher information geometry (preliminary result, Theorem D.1 in research notes), but the full derivation of quantum dynamics remains future work.

2. ❌ **General observable operators** - We construct specific observables relevant to our framework (inversion count Ĥ, position operators X̂_i, graph Laplacian L̂) but do not derive the general association of Hermitian operators with physical quantities (Postulate 2).

3. ❌ **Measurement collapse** - The projection postulate (Postulate 5) is not addressed. Our framework describes static probability distributions, not the dynamical process of measurement.

4. ❌ **Lorentz invariance** - This is a **non-relativistic framework**. The emergence of continuous spacetime symmetry SO(3,1) from discrete permutation group structure S_N remains an open problem, with preliminary observations but no rigorous derivation (Section 6.3.1).

**Honest assessment**: We have derived **static quantum probabilities in a non-relativistic setting**, not the complete structure of quantum mechanics. This represents a **partial but significant reduction** in the postulational basis of quantum theory.

**Comparison to standard QM**:
- **Standard**: 5 postulates (Hilbert space, observables, Born rule, evolution, collapse)
- **This work**: 2 axioms (logic, reference) → derives 3 elements (Born rule, Hilbert space, interference)
- **Reduction**: From 5 unexplained postulates to 2 justified axioms, with 3 derived results

Despite the limitations, this constitutes the **first derivation of Born rule probabilities from a principle external to quantum mechanics** (classical logic), using only information theory and mathematical necessity.

---

### Why This Matters (Keep in Section 1.1)

The question persists: **Why does the Born rule hold?**

Standard approaches [Gleason 1957, Hardy 2001, Chiribella et al. 2011] either:
- Assume Hilbert space and derive Born rule structure (Gleason)
- Trade quantum postulates for information postulates (Hardy, Chiribella)

**Our contribution**: Derive Born probabilities from **logical consistency** (external principle) without assuming quantum structure. Even though dynamics and relativity remain open, this answers a fundamental question: **Where do quantum probabilities come from?**

Answer: From the requirement that measurements obey classical logic, combined with maximum entropy under insufficient reason.

---

## Integration Notes

**Before** (current Section 1.1):
```
5. **Measurement Collapse**: Observation projects the state onto an eigenspace

[Currently jumps to:]
The question persists: **Why this structure and not another?**
```

**After** (with addition):
```
5. **Measurement Collapse**: Observation projects the state onto an eigenspace

### Scope of This Work

This paper addresses **one** postulate from the standard formulation: **the Born rule**...
[Full text above]

### Why This Matters

The question persists: **Why does the Born rule hold?**
[Rest of section continues...]
```

---

## Word Count Impact

**Addition**: ~400 words

**Original Section 1.1**: ~1,200 words

**New Section 1.1**: ~1,600 words (+33%)

**Justification**: Clarity on scope is essential. Reviewer specifically requested this. Worth the extra words.

---

## Peer Review Response

**Reviewer's concern**:
> "The paper's claims should be moderated. It has not derived 'quantum mechanics.'"

**This section directly addresses**:
- ✅ Lists exactly what IS derived (5 items)
- ✅ Lists exactly what is NOT derived (4 items)
- ✅ Honest assessment ("partial but significant reduction")
- ✅ Comparison to standard QM (2 axioms vs. 5 postulates)
- ✅ Clear statement: "static quantum probabilities in non-relativistic setting"

**Expected response**: ✅ "Scope clearly stated, claims appropriately moderated"

---

## Status

**Section 1.1 scope addition**: ✅ Drafted

**Next**:
1. Moderate Section 7 (Conclusion) - add limitations paragraph
2. Create final integrated paper with all changes

**Overall moderation**: 60% complete (Abstract ✅, Section 1.1 ✅, Section 7 pending)
