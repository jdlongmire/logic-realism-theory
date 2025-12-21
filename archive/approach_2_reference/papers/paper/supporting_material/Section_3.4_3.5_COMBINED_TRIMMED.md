# Sections 3.4-3.5: Quantum Structure (COMBINED & TRIMMED)

**Word Count Target**: 400 words (trimmed from 1,570)

---

## 3.4 Hilbert Space Emergence

The Born rule derivation (Section 3.2) assumes a basis {|σ⟩} without justifying orthogonality or Hilbert space structure. We address this gap.

**Construction**: Define ℋ_N = span{|σ⟩ : σ ∈ V_K} as the finite-dimensional vector space spanned by valid states.

**Orthogonality Justification**: Valid states are **perfectly distinguishable**—measurement always yields unique σ with certainty. By the quantum distinguishability principle [Fuchs & Peres 1996], perfectly distinguishable states must be orthogonal: ⟨σ|σ'⟩ = δ_{σσ'}.

**Inner Product**: The distinguishability requirement uniquely determines the inner product structure on ℋ_N.

**Dimension**: dim(ℋ_N) = |V_K|, matching the Born rule state space.

**MaxEnt State**: The uniform distribution P(σ) = 1/|V_K| corresponds to quantum state:

|ψ_MaxEnt⟩ = (1/√|V_K|) ∑_{σ∈V_K} e^{iφ_σ} |σ⟩

with Born probabilities P(σ) = |⟨σ|ψ⟩|² = 1/|V_K| recovered exactly.

**Observable Operators**: Natural candidates include:
- Inversion count Ĥ: Diagonal operator with eigenvalues h(σ)
- Position operators X̂_i: Measure σ(i)
- Graph Laplacian L̂: Encodes adjacency structure (Section 3.5)

**Result**: Hilbert space structure **emerges from distinguishability**, not postulated.

## 3.5 Superposition and Interference

**Superposition Principle**: General states are |ψ⟩ = ∑_σ a_σ |σ⟩ with complex amplitudes a_σ. Normalization: ∑_σ |a_σ|² = 1.

**Interference**: Measurement probability for inversion count k involves **quantum cross-terms**:

P(k) = ∑_{h(σ)=k} |a_σ|² + ∑_{σ≠σ', h(σ)=h(σ')=k} Re(a_σ* a_{σ'})

The second term—off-diagonal density matrix elements ρ_{σσ'} = a_σ* a_{σ'}—produces interference.

**Two-Path Interference** (N=3 example): Superposition of (1,3,2) and (2,1,3) (both h=1):

|ψ⟩ = (1/√2)[|1,3,2⟩ + e^{iφ}|2,1,3⟩]

Measurement probabilities: P(±) = (1/2)(1 ± cos φ), exhibiting standard quantum interference pattern.

**Phase Evolution**: Hamiltonian proposal—graph Laplacian Ĥ_LFT = D - A where D is degree matrix, A is adjacency matrix of permutohedron Cayley graph. This generates unitary evolution e^{-iĤt/ℏ} preserving superposition.

**L-Flow Connection**: The constraint h(σ) ≤ K creates dual dynamics:
- **Unitary** (phase evolution): Preserves quantum coherence
- **Dissipative** (L-flow): Monotonic h decrease → arrow of time

This duality connects reversible quantum mechanics to irreversible thermodynamics.

**Result**: Interference **derived from phases** in coherent superpositions. Combined with Section 3.4, quantum structure emerges from logical constraints + distinguishability + MaxEnt.

---

**Full derivations**: See supplementary material for complete proofs, worked examples, and entanglement extension.
