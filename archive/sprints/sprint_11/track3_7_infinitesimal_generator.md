# Track 3.7: Infinitesimal Generator (Hamiltonian)

**Sprint 11, Track 3**: Dynamics from Symmetry
**Phase 2, Deliverable 3.7**: Derive infinitesimal generator H from group structure
**Session**: 8.3
**Date**: 2025-11-03

---

## Objective

**Derive**: Infinitesimal generator H (Hamiltonian) from one-parameter unitary group U(t)

**Why this matters**: Establishes where Hamiltonian comes from and connects it to physical energy

---

## Background: From Track 3.6

### What We Have

**From Track 3.6**:
- U(t) is strongly continuous one-parameter unitary group (C₀-group)
- U(t + s) = U(t)U(s) (group law)
- U(t) is C^∞ (smooth, infinitely differentiable)
- U(t) is Lie group with ℝ as parameter space

**What's missing**: The **generator** H

### Intuitive Picture

**Idea**: U(t) describes evolution, dU/dt describes **rate of change**

**Analogy with ℝ**:
- Finite transformation: translation t → t + a
- Infinitesimal transformation: derivative d/dt
- Generator: d/dt operator

**For U(t)**:
- Finite evolution: U(t) (evolve by time t)
- Infinitesimal evolution: dU/dt|_{t=0}
- Generator: H such that dU/dt = -iHU(t)/ℏ

---

## Stone's Theorem

### Statement (Stone, 1932)

**Stone's Theorem**:

There is a **one-to-one correspondence** between:

**A.** Strongly continuous one-parameter unitary groups {U(t) | t ∈ ℝ}

**B.** Self-adjoint operators H on ℋ

**Given by the relations**:
```
U(t) = exp(-iHt/ℏ)  (forward direction: H → U(t))
```
```
iH = ℏ lim_{t→0} (U(t) - I)/t  (reverse direction: U(t) → H)
```

**More precisely**:

1. **Forward** (H → U(t)):
   - Let H be self-adjoint operator on domain D(H) ⊆ ℋ
   - Then exp(-iHt/ℏ) defines strongly continuous one-parameter unitary group

2. **Reverse** (U(t) → H):
   - Let {U(t)} be strongly continuous one-parameter unitary group
   - Then exists unique self-adjoint H such that:
     ```
     U(t) = exp(-iHt/ℏ)
     ```
   - Domain: D(H) = {ψ | lim_{t→0} (U(t)ψ - ψ)/t exists}

**Key properties**:
- H is **self-adjoint** (not just Hermitian): H† = H on maximal domain
- H typically **unbounded** (D(H) ⊊ ℋ, proper subset)
- D(H) is **dense** in ℋ
- Correspondence is **bijective** (one-to-one and onto)

### Why "Stone's Theorem"?

**Historical**:
- Marshall H. Stone (1932): "On one-parameter unitary groups in Hilbert space"
- Fundamental theorem in functional analysis
- Quantum mechanics foundation

**Also known as**:
- Stone-von Neumann theorem (related but different)
- Stone's representation theorem
- Infinitesimal generator theorem

---

## Circularity Assessment: Can We Ground Stone's Theorem?

### Question

**Is Stone's theorem**:
- **A.** Derivable from 3FLL (like Mazur-Ulam)?
- **B.** Mathematical fact we must accept (like Cauchy-Schwarz)?

### Analysis

**Nature of Stone's theorem**:
- Pure functional analysis result
- No physical input (works for any strongly continuous unitary group)
- Connects:
  - Topology (strong continuity)
  - Group structure (one-parameter)
  - Spectral theory (self-adjoint operators)

**Comparison with other theorems**:

| Theorem | Nature | Status in LRT |
|---------|--------|---------------|
| **Cauchy-Schwarz** | Pure algebra | Accept as mathematical fact |
| **Mazur-Ulam** | Geometric (isometries) | Accept, apply to D preservation |
| **Wigner** | Symmetry (transition probabilities) | Accept, apply to 3FLL symmetries |
| **Stone** | Functional analysis | ??? |

**Three options**:

**Option A: Derive from 3FLL**
- Pro: Most satisfying, complete grounding
- Con: Stone's theorem is abstract math (no obvious 3FLL connection)
- Feasibility: **Unlikely** - theorem doesn't reference logic

**Option B: Accept as mathematical fact**
- Pro: Standard approach, theorem well-established
- Con: Introduces mathematical axiom beyond 3FLL
- Feasibility: **Yes** - like accepting Mazur-Ulam

**Option C: Derive from weaker assumptions**
- Pro: More grounded than full acceptance
- Con: Still requires mathematical input
- Feasibility: **Possible** - could ground specific lemmas

### Decision: Option B (Accept Stone's Theorem)

**Justification**:

1. **Mathematical vs Logical**:
   - 3FLL = logical constraints
   - Stone's theorem = mathematical fact about Hilbert spaces
   - No circular dependency (theorem independent of physics)

2. **Precedent**:
   - We accepted Mazur-Ulam (Track 3.3)
   - We accepted Wigner (Track 3.2)
   - Stone's theorem in same category

3. **Scope of LRT**:
   - LRT grounds **physics** in logic
   - Mathematics (Hilbert space theory) is **tool**
   - Not claiming to derive all mathematics from logic

4. **Non-circularity preserved**:
   - Stone's theorem doesn't assume quantum mechanics
   - Applies to any C₀-unitary group (general theorem)
   - We derived C₀-unitary group from 3FLL (Track 3.6)
   - Applying Stone's theorem is **consistent**

**Conclusion**: Accept Stone's theorem as mathematical fact, like Mazur-Ulam ✓

**Transparency**: Acknowledge this is mathematical input, not derived from 3FLL

---

## Derivation of Infinitesimal Generator

### Definition 3.7.1 (Infinitesimal Generator)

The **infinitesimal generator** of U(t) is operator H defined by:

**Domain**:
```
D(H) = {ψ ∈ ℋ | lim_{t→0} (U(t)ψ - ψ)/t exists}
```

**Action**:
```
Hψ = iℏ lim_{t→0} (U(t)ψ - ψ)/t  for ψ ∈ D(H)
```

**Notation**: Sometimes written H = iℏ dU(t)/dt|_{t=0}

**Physical interpretation**: H measures rate of change of evolution at t = 0

### Theorem 3.7.1 (Existence and Uniqueness of Generator)

**Statement** (Stone's theorem, applied to our U(t)):

Given strongly continuous one-parameter unitary group {U(t)} from 3FLL, there exists **unique** self-adjoint operator H such that:

1. **Exponential form**: U(t) = exp(-iHt/ℏ)
2. **Differential form**: iℏ dU(t)/dt = HU(t) (on D(H))
3. **Self-adjoint**: H† = H on D(H)
4. **Dense domain**: D(H) dense in ℋ
5. **Typically unbounded**: ||Hψ|| can be arbitrarily large

**Proof**: Direct application of Stone's theorem (1932) ✓

**Consequence**: Every C₀-unitary group has self-adjoint generator

### Properties of Generator

**Property 1: Self-adjointness** (H† = H)

**Proof**:
From unitarity U(t)† = U(t)⁻¹ = U(-t):
```
[exp(-iHt/ℏ)]† = exp(+iH†t/ℏ)
                = U(t)†
                = U(-t)
                = exp(-iH(-t)/ℏ)
                = exp(+iHt/ℏ)
```
Therefore: H† = H (on appropriate domain) ✓

**Consequence**: H has real spectrum (eigenvalues are real)

**Property 2: Densely defined** (D(H) dense in ℋ)

**Proof**: Stone's theorem guarantees D(H) dense ✓

**Physical interpretation**: D(H) = "smooth states" (finite energy states)

**Property 3: Typically unbounded**

**Examples**:
- Free particle: H = p²/(2m) → unbounded above
- Harmonic oscillator: H = (p² + m²ω²x²)/(2m) → unbounded
- Finite-dimensional systems: H bounded (matrix)

**Consequence**: Must work with domains carefully (functional analysis)

---

## Connection to Schrödinger Equation

### Theorem 3.7.2 (Differential Equation for U(t))

**Statement**:

The generator H satisfies the operator differential equation:
```
iℏ dU(t)/dt = HU(t)
```
on domain D(H).

**Proof**:

From U(t) = exp(-iHt/ℏ):
```
dU(t)/dt = d/dt[exp(-iHt/ℏ)]
         = (-iH/ℏ) exp(-iHt/ℏ)  (chain rule for operator exponential)
         = (-iH/ℏ) U(t)
```

Multiply both sides by iℏ:
```
iℏ dU(t)/dt = HU(t)
```

**Note**: This is **operator** equation (U(t) acts on states)

### Corollary 3.7.3 (Schrödinger Equation for States)

**Statement**:

For state |ψ(t)⟩ = U(t)|ψ(0)⟩, we have:
```
iℏ d|ψ(t)⟩/dt = H|ψ(t)⟩
```
(provided |ψ(0)⟩ ∈ D(H))

**Proof**:

Given: |ψ(t)⟩ = U(t)|ψ(0)⟩

Differentiate both sides:
```
d|ψ(t)⟩/dt = dU(t)/dt |ψ(0)⟩
            = (-iH/ℏ)U(t)|ψ(0)⟩  (from Theorem 3.7.2)
            = (-iH/ℏ)|ψ(t)⟩
```

Multiply both sides by iℏ:
```
iℏ d|ψ(t)⟩/dt = H|ψ(t)⟩
```

**This is the Schrödinger equation!** ✓

**Significance**: Derived Schrödinger equation from:
1. 3FLL → unitarity (Track 3.4)
2. Identity → time homogeneity (Track 3.5)
3. Group structure (Track 3.6)
4. Stone's theorem (this track)

**Not postulated** - necessary consequence of logical + mathematical structure!

---

## Physical Interpretation: H as Energy

### Why is H the "Hamiltonian"?

**Question**: What does H represent physically?

**Answer**: H is the **energy operator** (total energy observable)

### Noether's Theorem: Symmetry → Conservation

**Noether's theorem** (1915):

Every continuous symmetry corresponds to a conserved quantity:
- **Time-translation symmetry** → **Energy conservation**
- Spatial translation symmetry → Momentum conservation
- Rotation symmetry → Angular momentum conservation

**Application to U(t)**:

**1. Time-translation symmetry**:
- Physics invariant under t → t + τ (any constant τ)
- From Identity law (Track 3.5): No privileged instant
- Symmetry: U(τ) for all τ ∈ ℝ

**2. Generator of time translations**:
- Infinitesimal: U(dt) ≈ I - (i/ℏ)H dt
- Generator: H (measures infinitesimal time shift)

**3. Noether's theorem**:
- Time-translation symmetry → conserved generator
- Generator: H
- **Conserved quantity: H = energy**

**Conclusion**: H is energy operator (from symmetry principle) ✓

### Energy Conservation

**Theorem 3.7.4 (Energy Conservation)**:

For state |ψ(t)⟩ evolving under U(t):
```
d⟨H⟩/dt = 0  (energy expectation value conserved)
```

**Proof**:

Energy expectation: ⟨H⟩(t) = ⟨ψ(t)|H|ψ(t)⟩

Differentiate:
```
d⟨H⟩/dt = d/dt ⟨ψ(t)|H|ψ(t)⟩
         = ⟨dψ/dt|H|ψ⟩ + ⟨ψ|H|dψ/dt⟩
```

Substitute Schrödinger equation dψ/dt = -iHψ/ℏ:
```
d⟨H⟩/dt = ⟨-iHψ/ℏ|H|ψ⟩ + ⟨ψ|H|-iHψ/ℏ⟩
         = (i/ℏ)⟨Hψ|H|ψ⟩ - (i/ℏ)⟨ψ|H|Hψ⟩
         = (i/ℏ)[⟨ψ|H²|ψ⟩ - ⟨ψ|H²|ψ⟩]  (H self-adjoint)
         = 0
```

**Conclusion**: Energy conserved in unitary evolution ✓

**Physical meaning**: Time-translation symmetry (from ID law) → energy conservation (from Noether's theorem)

---

## Spectral Properties of H

### Spectral Theorem for Self-Adjoint Operators

**Spectral theorem**:

Every self-adjoint operator H has **spectral decomposition**:
```
H = ∫ E dP(E)
```
where:
- E ∈ ℝ: Energy eigenvalues (real spectrum)
- P(E): Projection-valued measure (spectral projectors)

**For discrete spectrum** (e.g., harmonic oscillator):
```
H = ∑_n E_n |n⟩⟨n|
```
where |n⟩ eigenstates, E_n eigenvalues.

**For continuous spectrum** (e.g., free particle):
```
H = ∫ E |E⟩⟨E| dE
```

**Physical interpretation**:
- E_n: Allowed energy levels
- |n⟩: Energy eigenstates
- Measurement of H yields E_n with probability |⟨n|ψ⟩|²

### Energy Eigenstates

**Definition**: State |E⟩ is **energy eigenstate** if:
```
H|E⟩ = E|E⟩
```

**Evolution of eigenstate**:
```
|ψ(t)⟩ = U(t)|E⟩
        = exp(-iHt/ℏ)|E⟩
        = exp(-iEt/ℏ)|E⟩  (H|E⟩ = E|E⟩)
```

**Result**: Energy eigenstate picks up **phase** e^(-iEt/ℏ)

**Physical interpretation**:
- Stationary states (probability |⟨x|ψ(t)⟩|² time-independent)
- Phase rotates at frequency ω = E/ℏ
- Energy-time uncertainty: ΔE·Δt ≥ ℏ/2

### Ground State

**Definition**: **Ground state** |0⟩ = lowest energy eigenstate:
```
H|0⟩ = E₀|0⟩  where E₀ ≤ E_n for all n
```

**Physical properties**:
- Minimum energy configuration
- Often unique (non-degenerate)
- Stable (no spontaneous transitions in free evolution)

**Examples**:
- Harmonic oscillator: |0⟩, E₀ = ℏω/2 (zero-point energy)
- Hydrogen atom: |n=1, l=0, m=0⟩, E₀ = -13.6 eV
- QFT vacuum: |vac⟩ (no particles)

---

## Examples: Specific Hamiltonians

### Example 1: Free Particle

**Hamiltonian**:
```
H = p²/(2m)  (kinetic energy only)
```

**Domain**: D(H) = {ψ ∈ L²(ℝ) | ∫ k² |ψ̂(k)|² dk < ∞}

**Evolution**:
```
U(t) = exp(-ip²t/(2mℏ))
```

**Action in momentum space**:
```
[U(t)ψ̂](k) = exp(-ik²t/(2mℏ)) ψ̂(k)
```

**Schrödinger equation**:
```
iℏ ∂ψ/∂t = -(ℏ²/2m) ∂²ψ/∂x²
```

**Spectrum**: σ(H) = [0, ∞) (continuous, unbounded above)

### Example 2: Harmonic Oscillator

**Hamiltonian**:
```
H = (p² + m²ω²x²)/(2m)  (kinetic + potential energy)
```

**Spectrum**: E_n = ℏω(n + 1/2), n = 0, 1, 2, ... (discrete, unbounded)

**Ground state**: |0⟩, E₀ = ℏω/2

**Evolution**:
```
U(t) = exp(-iHt/ℏ)
```

**Eigenstates**: |n⟩ (Hermite polynomials)

**Evolution of eigenstate**:
```
|n, t⟩ = exp(-iE_n t/ℏ)|n⟩
       = exp(-iω(n + 1/2)t)|n⟩
```

**Schrödinger equation**:
```
iℏ ∂ψ/∂t = [-(ℏ²/2m) ∂²/∂x² + (mω²/2)x²]ψ
```

### Example 3: Hydrogen Atom

**Hamiltonian**:
```
H = p²/(2m) - e²/(4πε₀r)  (kinetic + Coulomb potential)
```

**Spectrum**:
- Discrete: E_n = -13.6 eV/n² (n = 1, 2, 3, ..., bound states)
- Continuous: E > 0 (ionized states)

**Ground state**: |n=1, l=0, m=0⟩, E₀ = -13.6 eV

**Evolution**: U(t) = exp(-iHt/ℏ)

**Physical**: Electron orbiting proton, energy levels quantized

---

## Where Does ℏ Come From?

### Planck's Constant: Dimensional Analysis

**Question**: What determines the value of ℏ?

**Answer**: ℏ is **dimensional constant** connecting:
- Time dimension: [t] = T
- Energy dimension: [E] = ML²T⁻²

**In generator definition**:
```
H = iℏ lim_{t→0} (U(t) - I)/t
```

**Dimensional analysis**:
```
[H] = [ℏ][1/t] = [ℏ]/T
```
For [H] = energy = ML²T⁻²:
```
[ℏ] = ML²T⁻¹  (action dimension)
```

**Physical meaning**:
- ℏ = quantum of action
- Fundamental scale relating energy ↔ frequency (E = ℏω)
- Value: ℏ ≈ 1.055 × 10⁻³⁴ J·s (measured experimentally)

**LRT perspective**:
- Structure of QM (unitarity, linearity) derived from 3FLL
- Scale ℏ is **empirical input** (links abstract structure to physical units)
- Analogous to: Speed of light c (empirical constant in SR)

**Not derived**: LRT derives structure, not numerical constants ✓

---

## Summary: Complete Derivation Chain

### 3FLL → Schrödinger Equation

**Complete chain** (Tracks 3.1-3.7):

```
3FLL (Identity, Non-Contradiction, Excluded Middle)
  ↓ Track 3.1
Symmetries (basis independence, reversibility, continuity)
  ↓ Track 3.2
D preservation (isometries, Wigner condition)
  ↓ Track 3.3
Linearity (Mazur-Ulam theorem)
  ↓ Track 3.4
Unitarity (U†U = I)
  ↓ Track 3.5
Continuous one-parameter group {U(t) | t ∈ ℝ}
  ↓ Track 3.6
Strongly continuous C₀-unitary group (Lie group structure)
  ↓ Track 3.7 (this track)
Infinitesimal generator H (Stone's theorem)
  ↓ Theorem 3.7.2
Schrödinger equation: iℏ ∂ψ/∂t = Hψ
```

**Result**: Schrödinger equation derived from pure logic + mathematics!

### What Was Derived vs Accepted

**Derived from 3FLL**:
- ✅ Unitarity (Track 3.4)
- ✅ Linearity (Track 3.3)
- ✅ Time homogeneity (Track 3.5)
- ✅ Group structure (Track 3.6)
- ✅ Schrödinger equation form (this track)

**Accepted as mathematics**:
- ✅ Hilbert space structure (standard math)
- ✅ Mazur-Ulam theorem (geometric fact)
- ✅ Wigner's theorem (symmetry result)
- ✅ Stone's theorem (functional analysis)

**Empirical input**:
- ✅ Value of ℏ (measured constant)
- ✅ Specific Hamiltonians H (system-dependent)

**Completely non-circular** ✓

---

## Physical Implications

### What Have We Achieved?

**Standard quantum mechanics**:
- **Postulate 1**: States are vectors in Hilbert space
- **Postulate 2**: Observables are Hermitian operators
- **Postulate 3**: Measurement gives eigenvalues (Born rule)
- **Postulate 4**: Evolution is unitary, iℏ ∂ψ/∂t = Hψ

**LRT approach**:
- **Postulate 1**: DERIVED (Track 1: ℂℙⁿ from 3FLL)
- **Postulate 2**: DERIVED (Track 2: observables from D)
- **Postulate 3**: DERIVED (Track 2: Born rule from Gleason + MaxEnt)
- **Postulate 4**: DERIVED (Tracks 3.1-3.7: Schrödinger from symmetry)

**Achievement**: Reduced QM postulates to **3FLL logical constraints** + standard mathematics!

### Why This Matters

**1. Explanatory power**:
- QM not arbitrary collection of postulates
- Necessary mathematical structure for consistent logic
- "Why quantum?" → "Why classical logic?"

**2. Foundational clarity**:
- Non-circular derivations
- Clear separation: logic (3FLL) vs math (Hilbert spaces) vs empirics (ℏ)
- Identifies what's fundamental vs conventional

**3. Predictive power**:
- Constrains modifications to QM
- Any "beyond QM" theory must either:
  - Modify 3FLL (reject classical logic)
  - Accept QM structure (only parameters change)

---

## Non-Circularity Check

### Did We Assume Schrödinger Equation?

**Question**: Did we use iℏ ∂ψ/∂t = Hψ to derive H?

**Answer**: **NO** - completely independent

**Derivation used**:
- ✅ Group structure U(t+s) = U(t)U(s)
- ✅ Strong continuity (from EM relaxation)
- ✅ Stone's theorem (mathematical fact)
- ✅ Definition: H = iℏ lim_{t→0} (U(t) - I)/t

**Derivation did NOT use**:
- ❌ Schrödinger equation (derived as consequence)
- ❌ Energy (identified via Noether's theorem)
- ❌ Specific Hamiltonians (system-dependent)

**Result**: Schrödinger equation is **theorem**, not axiom ✓

---

## Next Steps (Track 3.8)

**Deliverable 3.8**: Formalize Schrödinger equation U(t) = exp(-iHt/ℏ)

**Plan**:
1. Summarize complete derivation (Tracks 3.1-3.7)
2. State Schrödinger equation in multiple forms:
   - Operator form: iℏ dU/dt = HU(t)
   - State form: iℏ dψ/dt = Hψ
   - Integral form: ψ(t) = exp(-iHt/ℏ)ψ(0)
3. Verify equivalence of forms
4. Connect to standard QM formulation
5. Discuss physical interpretation and implications

**Expected**: ~300 lines, summary + formalization

**After 3.8**: Phase 2 complete, move to Phase 3 (Stone's theorem grounding + Lean formalization)

---

## References

### Stone's Theorem
- **Stone, M.H.** (1932). "On one-parameter unitary groups in Hilbert space". Annals of Mathematics 33(3): 643-648
- **Von Neumann, J.** (1932). "Mathematical Foundations of Quantum Mechanics" (Chapter III)
- **Reed & Simon** (1980). "Methods of Modern Mathematical Physics" Vol I (Theorem VIII.8)
- **Rudin, W.** (1991). "Functional Analysis" (Chapter 13)

### Spectral Theory
- **Kato, T.** (1995). "Perturbation Theory for Linear Operators" (Chapter V)
- **Teschl, G.** (2014). "Mathematical Methods in Quantum Mechanics" (Chapter 3)
- **Hall, B.C.** (2013). "Quantum Theory for Mathematicians" (Chapter 9)

### Noether's Theorem
- **Noether, E.** (1918). "Invariante Variationsprobleme"
- **Neuenschwander, D.** (2010). "Emmy Noether's Wonderful Theorem"
- **Goldstein, H.** (2002). "Classical Mechanics" (Chapter 13)

### Quantum Mechanics
- **Weinberg, S.** (1995). "The Quantum Theory of Fields" Vol 1 (Chapter 2.3)
- **Ballentine, L.** (1998). "Quantum Mechanics" (Chapter 3.2)
- **Sakurai, J.J.** (2017). "Modern Quantum Mechanics" (Chapter 2)

### LRT Foundations
- **Track 3.1-3.4**: Phase 1 (symmetry foundations, unitarity)
- **Track 3.5**: Continuous one-parameter symmetries from Identity law
- **Track 3.6**: One-parameter unitary group structure

---

**Track 3.7 Complete** ✅
**Phase 2**: 3/4 deliverables (75%)
**Track 3 Total**: 7/13 deliverables (~54%)
