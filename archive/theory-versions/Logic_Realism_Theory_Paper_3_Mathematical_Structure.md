# The Mathematical Structure of Logic Realism Theory

## From Logical Constraints to the Hilbert Space and Born Rule of Quantum Mechanics

**James (JD) Longmire**  
ORCID: 0009-0009-1383-7698  
Northrop Grumman Fellow (unaffiliated research)

---

## Abstract

This paper provides a rigorous mathematical formalization of Logic Realism Theory (LRT). The companion papers established the philosophical thesis (the Three Fundamental Logical Laws are constitutive of physical reality) and the physical interpretation (quantum mechanics is the unique stable interface between possibility and actuality). Here we state precise axioms, derive the Hilbert space structure of quantum mechanics via reconstruction theorems, derive the Born rule via Gleason's theorem, and show how existing interpretational frameworks (Bohmian mechanics, GRW, Many-Worlds, QBism, Relational QM) describe different domains of the LRT structure rather than competing ontologies. Novel conjectures connecting action and complexity are developed, and open mathematical problems are identified. The result is a unified mathematical framework for quantum foundations grounded in logical structure.

**Keywords:** quantum foundations, logic realism, Hilbert space, Born rule, Gleason's theorem, reconstruction theorems, quantum interpretations

Quantum mechanics is thereby shown to be the unique stable mathematical representation of the interface between logical distinguishability and Boolean actuality.

---

## 1. Introduction

The first paper of this series established Logic Realism Theory as a philosophical position: the Three Fundamental Logical Laws (identity, non-contradiction, excluded middle) are not cognitive conventions but ontological constraints constitutive of physical reality. The second paper extended this to quantum mechanics, arguing that quantum structure is the unique stable interface between the Infinite Information Space (IIS) and Boolean actuality.

This paper provides rigorous mathematical foundations. Our goals are:

1. **State precise axioms** for LRT
2. **Derive** (not assume) Hilbert space structure from these axioms
3. **Derive** (not assume) the Born rule
4. **Show how existing frameworks** describe different aspects of LRT
5. **Identify novel structures** and open problems

The central derivation chain is:

$$\text{3FLL + Continuity + Reversibility + Local Tomography} \xrightarrow{\text{Masanes-Müller}} \text{Complex Hilbert Space}$$

$$\text{Hilbert Space + Non-contextual Measure} \xrightarrow{\text{Gleason}} \text{Born Rule}$$

We do not claim to derive quantum mechanics from pure logic. We claim that quantum mechanics follows from logical structure plus physically motivated constraints (continuity, reversibility, local tomography). The physical constraints are not arbitrary - they are requirements for stable, informative physics.

---

## 2. Axioms of Logic Realism Theory

### 2.1 Primitive Terms

We begin with undefined primitive terms. These are not derived but taken as foundational.

**Definition 2.1 (Three Fundamental Logical Laws).** The 3FLL are:
- **Identity (I):** ∀x: x = x
- **Non-Contradiction (NC):** ∀x, P: ¬(P(x) ∧ ¬P(x))
- **Excluded Middle (EM):** ∀x, P: P(x) ∨ ¬P(x)

**Definition 2.2 (Distinguishability).** A binary relation D on a set S such that D(x,y) holds iff x and y can be differentiated by some predicate P satisfying 3FLL.

**Definition 2.3 (Infinite Information Space).** The maximal collection IIS of states closed under distinguishability:
$$\mathcal{I} = \{s : D \text{ is defined on } s \times \mathcal{I}\}$$

*Remark:* The maximality of IIS ensures it is infinite-dimensional. This will be relevant for applying Gleason's theorem, which requires dimension ≥ 3.

**Definition 2.4 (Boolean Structure).** A set B equipped with operations {∧, ∨, ¬} satisfying the Boolean algebra axioms, with carrier set {0,1}.

**Definition 2.5 (Context).** A partition C of (a subspace of) IIS into mutually exclusive, jointly exhaustive alternatives.

---

### 2.2 The Axioms

**Axiom 1 (Constitution).** 3FLL constitute distinguishability. For any x, y ∈ IIS:
$$D(x,y) \text{ is well-defined} \iff x, y \text{ satisfy I, NC, EM}$$

*This axiom asserts that distinguishability is not primitive but is constituted by logical structure. Without 3FLL, there is no basis for one state to differ from another.*

---

**Axiom 2 (Pairwise Structure).** Distinguishability is a binary relation. For any assessment of distinguishability, exactly two states are compared:
$$D: \mathcal{I} \times \mathcal{I} \rightarrow [0,1]$$

where D(x,y) = 0 means identical, D(x,y) = 1 means perfectly distinguishable.

*This axiom captures that distinguishability is relational - it compares pairs. This pairwise character grounds the quadratic structure of quantum mechanics.*

---

**Axiom 3 (Physical Constraints on IIS).** The space IIS admits:

**(a) Continuous transformations:** For any two states s₁, s₂ with D(s₁,s₂) < 1, there exists a continuous path of states connecting them.

**(b) Reversible transformations:** For any transformation T on IIS, there exists T⁻¹ such that T⁻¹T = TT⁻¹ = id.

**(c) Local tomography:** For any composite system with subsystems A and B, the state of the whole is uniquely determined by the statistics of local measurements on A and B separately.

*Remark on 3(c):* This axiom is crucial for determining the number field. It asserts that the distinguishability of a composite system is determined by local measurements on its parts. This rules out holistic theories where the whole cannot be reconstructed from the parts.

*Justification:* These constraints are not arbitrary. Continuity is required for dynamics to be well-defined. Reversibility is required for information preservation in IIS (non-reversible dynamics would lose distinguishability). Local tomography is required for physics to be compositional - for us to learn about wholes by studying parts.

---

**Axiom 4 (Boolean Actuality).** There exists a map Φ from IIS to Boolean outcomes:
$$\Phi_C: \mathcal{I} \rightarrow \{0,1\}^{|C|}$$

for each context C, satisfying:
- (a) **Totality:** Φ_C is defined for all s ∈ IIS (from EM)
- (b) **Single-valuedness:** For each s and C, Φ_C(s) is unique (from NC)
- (c) **Exclusivity:** Exactly one element of C receives value 1 (from EM + NC)

*This axiom asserts that actuality is Boolean - determinate, non-contradictory, complete. It does not yet specify HOW Φ assigns values, only that it does so consistently with 3FLL.*

---

**Axiom 5 (Non-Contextual Measure).** The interface map Φ induces a probability measure μ on outcomes satisfying:

**(a) Non-negativity:** μ(s, c) ≥ 0 for all states s and outcomes c

**(b) Normalization:** For any context C = {c₁, ..., cₙ}, we have Σᵢ μ(s, cᵢ) = 1

**(c) Distinguishability-respecting:** If D(s,s') = 0, then μ(s,c) = μ(s',c) for all c

**(d) Non-contextuality of measure:** The measure assigned to a subspace H is independent of the orthogonal complement H⊥ used to complete the context. That is, if H appears in two different contexts C and C', then μ(s, H) is the same in both.

*Remark on 5(d):* This is the crucial condition for Gleason's theorem. It asserts that the probability of an outcome depends only on the state and the outcome, not on what other outcomes were possible. Without this, Gleason's theorem does not apply.

*This axiom asserts that the interface has a probability measure with specific properties. It does NOT assert that this measure is |ψ|². That will be derived.*

---

**Axiom 6 (Parsimony).** Among all paths through IIS compatible with the constraints, actuality realizes paths of minimal complexity.

$$\text{Actual path} = \text{argmin}_{p \in \text{Admissible}} C(p)$$

where C is a complexity measure on paths.

*This axiom introduces the selection principle. It is the least grounded axiom and is treated as a motivated assumption rather than a derived result. See Section 12 for discussion of the action-complexity conjecture that would ground this axiom.*

---

### 2.3 Derived Structure

From these axioms, we derive the mathematical structure of quantum mechanics.

**Theorem 2.1 (Inner Product Structure).**
If IIS satisfies Axioms 1-3, then the distinguishability relation D induces an inner product ⟨·|·⟩ on IIS.

*Proof:*

Axiom 2 establishes that D is pairwise - a function of two states.

Axiom 3(a) establishes continuity: state space is connected.

Axiom 3(b) establishes reversibility: transformations are invertible.

Axiom 3(c) establishes local tomography: composites determined by parts.

By the Masanes-Müller reconstruction theorem (Masanes & Müller, 2011), any state space satisfying:
1. Continuous reversible dynamics
2. Local tomography
3. Existence of entangled states (non-trivial composites)

admits a unique representation as a complex Hilbert space with standard quantum operations.

Conditions 1 and 2 are Axioms 3(a-c). Condition 3 follows from the richness of IIS - since IIS contains all distinguishable configurations (Definition 2.3), it contains composite states that are not product states.

Therefore IIS admits complex inner product structure. ∎

---

**Theorem 2.2 (Complex Numbers).**
The field over which the inner product is defined is ℂ (complex numbers), not ℝ (reals) or ℍ (quaternions).

*Proof:*

This follows from Axiom 3(c) (Local Tomography) via Masanes & Müller (2011).

Consider the alternatives:

**Real quantum mechanics (ℝ):** Satisfies continuity and reversibility but has impoverished interference structure. More critically, real QM does not satisfy local tomography in general - there exist real quantum states of composite systems that cannot be distinguished by local measurements alone (see also Stueckelberg, 1960).

**Quaternionic quantum mechanics (ℍ):** Satisfies continuity and reversibility but violates local tomography. In quaternionic QM, the joint state of a composite system contains more information than can be extracted from local measurements on the parts (Baez, 2012).

**Complex quantum mechanics (ℂ):** Uniquely satisfies all three conditions. Complex numbers provide exactly the right structure for interference (via phases) while maintaining local tomography.

Therefore, Axiom 3(c) forces the field to be ℂ. ∎

---

**Theorem 2.3 (Hilbert Space).**
IIS, equipped with the inner product from Theorem 2.1, is a complex Hilbert space ℋ.

*Proof:*

The inner product from Theorem 2.1 satisfies:
- Conjugate symmetry: ⟨x|y⟩ = ⟨y|x⟩*
- Linearity in second argument: ⟨x|αy + βz⟩ = α⟨x|y⟩ + β⟨x|z⟩
- Positive definiteness: ⟨x|x⟩ ≥ 0, with equality iff x = 0

Completeness (every Cauchy sequence converges) follows from the maximality of IIS (Definition 2.3). Any limit point of a sequence of distinguishable states is itself distinguishable from other states, hence in IIS. ∎

---

**Corollary 2.4 (Dimension).**
dim(ℋ) ≥ 3, satisfying the requirement for Gleason's theorem.

*Proof:*
IIS is maximal (Definition 2.3) and contains composite systems with entanglement (proof of Theorem 2.1). Any such space has dimension at least 4 (two qubits). More generally, IIS is infinite-dimensional, containing arbitrarily complex distinguishable configurations. ∎

*Remark:* Gleason's theorem fails for dim = 2 (a single qubit admits non-Born probability measures). However, this is not a limitation for LRT. The physical universe is never a single isolated qubit - IIS contains all configurations, making its effective dimension infinite. The dim ≥ 3 requirement is trivially satisfied for any physically realistic subsystem embedded in IIS.

---

### 2.4 Status of the Axioms

| Axiom | Type | Justification |
|-------|------|---------------|
| 1 (Constitution) | Definitional | 3FLL define distinguishability |
| 2 (Pairwise) | Structural | Distinguishability compares two things |
| 3a (Continuity) | Physical | Required for well-defined dynamics |
| 3b (Reversibility) | Physical | Required for information preservation |
| 3c (Local Tomography) | Physical | Required for compositional physics |
| 4 (Boolean Actuality) | From 3FLL | Actuality must satisfy logic |
| 5 (Non-Contextual Measure) | Structural | Interface must have consistent statistics |
| 6 (Parsimony) | Motivated | Selection principle; see Section 12 |

---

### 2.5 The Derivation Chain

We summarize the logical structure:

```
3FLL (Axiom 1)
    ↓ constitutes
Distinguishability (Def 2.2, Axiom 2)
    ↓ + physical constraints (Axiom 3)
Complex Hilbert Space (Theorems 2.1-2.3, via Masanes-Müller)
    ↓ + non-contextual measure (Axiom 5)
Born Rule (Theorem 4.2, via Gleason)
    ↓ + Boolean actuality (Axiom 4)
Quantum Mechanics
```

---

## 3. The IIS Formalism

### 3.1 IIS as Generalized Probabilistic Theory Space

The framework of Generalized Probabilistic Theories (GPTs) provides a natural mathematical home for IIS. A GPT is defined by:

**Definition 3.1 (GPT).** A generalized probabilistic theory consists of:
- A **state space** Ω (convex set of possible states)
- An **effect space** E (measurements yielding probabilities)
- A **transformation group** G (allowed dynamics)

Standard examples:
- Classical probability: Ω = simplex, G = stochastic maps
- Quantum mechanics: Ω = density matrices, G = completely positive maps
- Boxworld: Ω = hypercube, G = restricted

**Proposition 3.2.** IIS contains all consistent GPTs as substructures.

*Argument:* Any GPT defines distinguishable states (via effects). By Definition 2.3, any distinguishable configuration is in IIS. Therefore every GPT embeds in IIS.

---

### 3.2 The Distinguishability Metric

**Definition 3.3 (Distinguishability Distance).** For states x, y ∈ IIS:
$$d(x,y) = \sqrt{1 - |\langle x|y\rangle|^2}$$

This is the **Fubini-Study metric** on projective Hilbert space.

**Properties:**
- d(x,y) = 0 iff x = y (up to phase)
- d(x,y) = 1 iff x ⊥ y (perfectly distinguishable)
- Triangle inequality holds

**Proposition 3.4.** The distinguishability metric is the natural metric on IIS induced by Axiom 2.

*Proof:* Axiom 2 defines D: IIS × IIS → [0,1]. Given Hilbert space structure (Theorem 2.3), the inner product ⟨x|y⟩ measures overlap. The Fubini-Study metric converts this to a distance satisfying metric axioms. ∎

---

### 3.3 Complexity on IIS

**Definition 3.5 (State Complexity).** For a state |ψ⟩ ∈ IIS, the complexity C(ψ) is the minimum information required to specify ψ to a given precision ε.

For finite-dimensional systems:
$$C(\psi) = \sum_i |c_i|^2 \log_2 |c_i|^{-2} + O(\log(1/\varepsilon))$$

where |ψ⟩ = Σᵢ cᵢ|i⟩ in some reference basis.

*Remark:* This connects to von Neumann entropy for mixed states:
$$S(\rho) = -\text{Tr}(\rho \log \rho)$$

**Definition 3.6 (Path Complexity).** For a path γ: [0,T] → IIS, the path complexity is:
$$C(\gamma) = \int_0^T \left\| \frac{d\gamma}{dt} \right\|_{FS} dt$$

where ||·||_FS is the Fubini-Study norm.

**Proposition 3.7.** Path complexity equals action (up to constants) for Hamiltonian evolution.

*Sketch:* For |ψ(t)⟩ evolving under H:
$$\left\| \frac{d\psi}{dt} \right\|_{FS} = \frac{\Delta H}{\hbar}$$

where ΔH is the energy uncertainty. Integrating gives the quantum speed limit, connecting path length to action.

---

### 3.4 Topology of IIS

**Proposition 3.8.** IIS, as a complex Hilbert space, has the following topological properties:
- Infinite-dimensional (separable)
- Complete metric space
- Contractible (hence simply connected)
- Not locally compact

**The Projective Structure:**

Physical states correspond to rays, not vectors. The projective Hilbert space:
$$\mathbb{P}(\mathcal{H}) = (\mathcal{H} \setminus \{0\}) / \mathbb{C}^*$$

is the space of physical states.

**Proposition 3.9.** For finite-dimensional ℋ with dim = n, the projective space is:
$$\mathbb{P}(\mathcal{H}) \cong \mathbb{CP}^{n-1}$$

with rich topological structure (non-trivial π₂, symplectic structure, Kähler metric).

---

### 3.5 Symmetries of IIS

**Definition 3.10 (IIS Symmetry).** A symmetry of IIS is a bijection S: IIS → IIS preserving distinguishability:
$$D(Sx, Sy) = D(x, y) \quad \forall x, y$$

**Theorem 3.11 (Wigner).** Every symmetry of IIS is implemented by either:
- A unitary operator U: ⟨Ux|Uy⟩ = ⟨x|y⟩, or
- An antiunitary operator A: ⟨Ax|Ay⟩ = ⟨x|y⟩*

*Proof:* Standard Wigner theorem. Distinguishability-preserving maps on projective Hilbert space are (anti)unitary. ∎

**Corollary 3.12.** The symmetry group of IIS is:
$$\text{Sym}(\mathcal{I}) = U(\mathcal{H}) \rtimes \mathbb{Z}_2$$

where U(ℋ) is the unitary group and ℤ₂ is time-reversal (complex conjugation).

---

## 4. The Interface Map

### 4.1 Formal Definition

Having established that IIS has Hilbert space structure (Section 2), we now characterize the interface map Φ that takes IIS states to Boolean actuality.

**Definition 4.1 (Context as Orthonormal Basis).**
A context C is an orthonormal basis {|c₁⟩, ..., |cₙ⟩} of the relevant Hilbert subspace:
$$\langle c_i|c_j\rangle = \delta_{ij}$$

*Remark:* This connects Definition 2.5 to Hilbert space structure. Mutual exclusivity becomes orthogonality; joint exhaustiveness becomes completeness of the basis.

---

**Definition 4.2 (Interface Map).**
For a state |ψ⟩ ∈ ℋ and context C = {|cᵢ⟩}, the interface map is:
$$\Phi_C: \mathcal{H} \rightarrow \{0,1\}^{|C|}$$

such that exactly one component equals 1 and the rest equal 0.

---

### 4.2 The Born Rule Derived

**Theorem 4.1 (Gleason, 1957).**
Let ℋ be a Hilbert space of dimension ≥ 3. Any measure μ on the closed subspaces of ℋ satisfying:
- μ(H) ≥ 0 for all subspaces H
- μ(ℋ) = 1
- μ(⊕ᵢHᵢ) = Σᵢμ(Hᵢ) for orthogonal subspaces

is of the form μ(H) = Tr(ρ · P_H) for some density operator ρ.

For pure states ρ = |ψ⟩⟨ψ|, this yields:
$$\mu(|c\rangle) = |\langle c|\psi\rangle|^2$$

*Remark:* By Corollary 2.4, IIS has dimension ≥ 3, so Gleason's theorem applies.

---

**Theorem 4.2 (Born Rule from LRT Axioms).**
The probability that Φ_C(|ψ⟩) assigns 1 to outcome cᵢ is:
$$P(\Phi_C(|\psi\rangle) = c_i) = |\langle c_i|\psi\rangle|^2$$

*Proof:*

1. By Axiom 5, there exists a measure μ on outcomes satisfying non-negativity, normalization, and non-contextuality.

2. By Theorem 2.3, IIS has Hilbert space structure with dim ≥ 3.

3. Contexts are orthonormal bases (Definition 4.1), so the measure μ is defined on closed subspaces of ℋ.

4. By Axiom 5(d), μ is non-contextual: the measure assigned to a subspace is independent of how it is embedded in a context.

5. By Gleason's theorem (Theorem 4.1), any such measure has the form Tr(ρ · P_H).

6. For pure states |ψ⟩, we have ρ = |ψ⟩⟨ψ|, giving μ(|c⟩) = |⟨c|ψ⟩|².

Therefore the Born rule is the unique measure satisfying Axiom 5 given Hilbert space structure. ∎

---

**Corollary 4.3 (Born Rule Not Assumed).**
The Born rule is derived, not assumed. Axiom 5 asserts only that a measure exists with certain structural properties. The specific form |ψ|² follows from Gleason's theorem applied to the Hilbert space structure derived in Section 2.

---

### 4.3 Properties of the Interface

**Theorem 4.4 (Totality).**
Φ_C is defined for all |ψ⟩ ∈ ℋ.

*Proof:*
By Axiom 4(a), the interface is total. Any state in IIS can interface with Boolean actuality. This follows from Excluded Middle: for any state and any context, an outcome must occur. ∎

---

**Theorem 4.5 (Single-Valuedness).**
For each |ψ⟩ and C, exactly one outcome occurs.

*Proof:*
By Axiom 4(b) and 4(c). Non-Contradiction forbids multiple simultaneous outcomes; Excluded Middle requires at least one. Together: exactly one. ∎

---

**Theorem 4.6 (Context Dependence).**
Different contexts C, C' generally yield different outcome distributions for the same state |ψ⟩.

*Proof:*
Let C = {|cᵢ⟩} and C' = {|c'ⱼ⟩} be different orthonormal bases. Then:
$$P(\Phi_C = c_i) = |\langle c_i|\psi\rangle|^2$$
$$P(\Phi_{C'} = c'_j) = |\langle c'_j|\psi\rangle|^2$$

These are generally different unless |ψ⟩ is a simultaneous eigenstate of observables associated with both bases. ∎

---

**Theorem 4.7 (Kochen-Specker).**
For dim(ℋ) ≥ 3, there exists no global map Φ: ℋ → {0,1}^∞ independent of context that assigns definite values to all observables simultaneously while respecting functional relationships.

*Proof:*
Standard Kochen-Specker theorem. For dim(ℋ) ≥ 3, no consistent truth-value assignment exists for all projection operators that respects the algebraic relationships among observables.

*LRT interpretation:* This is not a defect but a feature. The interface is constitutively context-dependent. Boolean values are not "revealed" by measurement but "generated" at the interface. There is no pre-existing Boolean structure in IIS; Boolean structure is created at the interface. ∎

---

### 4.4 Contextuality as Interface Signature

**Proposition 4.8.**
Contextuality is the mathematical signature of the IIS → Boolean interface.

*Argument:*

Suppose Boolean values existed in IIS prior to and independent of measurement. Then:
- A global, context-independent Φ would exist
- Kochen-Specker would not hold
- Quantum mechanics would be a hidden variable theory

But Kochen-Specker does hold. Therefore Boolean values do not pre-exist in IIS. They are generated at the interface.

Contextuality is not a quantum anomaly requiring special explanation. It is the necessary consequence of mapping non-Boolean IIS structure to Boolean actuality. Different contexts (bases) partition IIS differently; different partitions yield different Boolean patterns.

*The physical meaning:* When we "measure" a quantum system, we are not passively reading pre-existing values. We are actively interfacing IIS with Boolean actuality in a specific way (determined by the measurement context). The outcome is real, but it did not exist before the interface event.

---

### 4.5 The Layer Structure

Different mathematical frameworks describe different layers of the LRT structure:

```
┌─────────────────────────────────────────────────────────────┐
│  LAYER 4: BOOLEAN ACTUALITY                                 │
│  ─────────────────────────────────────────────────────────  │
│  Frameworks: Copenhagen (outcomes), QBism (agent's bets)    │
│  Math: Boolean algebra, classical probability               │
│  What happens: Definite outcomes; one result per context    │
├─────────────────────────────────────────────────────────────┤
│  LAYER 3: THE INTERFACE                                     │
│  ─────────────────────────────────────────────────────────  │
│  Frameworks: Decoherence, GRW (collapse statistics)         │
│  Math: Lindblad equation, stochastic Schrödinger equation   │
│  What happens: Transition from quantum to classical         │
├─────────────────────────────────────────────────────────────┤
│  LAYER 2: PROBABILITY FLOW                                  │
│  ─────────────────────────────────────────────────────────  │
│  Frameworks: Bohmian mechanics (guidance equation)          │
│  Math: Probability currents, quantum equilibrium            │
│  What happens: |ψ|² distribution maintained; flow structure │
├─────────────────────────────────────────────────────────────┤
│  LAYER 1: IIS DYNAMICS                                      │
│  ─────────────────────────────────────────────────────────  │
│  Frameworks: Unitary QM, Many-Worlds (wave function realism)│
│  Math: Schrödinger equation, Hilbert space                  │
│  What happens: Unitary evolution; all branches present      │
└─────────────────────────────────────────────────────────────┘
```

**Figure 4.1: The LRT Layer Cake.** Each layer describes a different aspect of the IIS-to-actuality structure. Frameworks that seem incompatible (e.g., MWI vs. Copenhagen) are describing different layers.

---

### 4.6 Domain Assignments

| Framework | Layer | Mathematical Content | LRT Interpretation |
|-----------|-------|---------------------|-------------------|
| **Unitary QM / MWI** | 1 | Schrödinger: i∂ₜ\|ψ⟩ = H\|ψ⟩ | Evolution in IIS; all branches exist |
| **Bohmian** | 2 | Guidance: dQ/dt = (ℏ/m)Im(∇ψ/ψ) | Probability flow in IIS |
| **Decoherence** | 3 | Lindblad: ρ̇ = -i[H,ρ] + L[ρ] | Approach to interface threshold |
| **GRW** | 3 | Collapse rate: λ · N | Statistics of interface transitions |
| **QBism** | 4 | Dutch book coherence | Agent's rational bets on outcomes |
| **Copenhagen** | 4 | Born rule + collapse | Description of actualized outcomes |
| **Relational** | 2-4 | Perspectival states | Context-dependence across layers |

---

### 4.7 Non-Contradiction of Frameworks

**Proposition 4.9.**
LRT does not contradict existing frameworks; it assigns them non-overlapping domains.

*Potential contradiction 1:* Bohmian mechanics preserves probability current (unitary). GRW modifies unitarity (stochastic collapse).

*Resolution:* Bohm describes Layer 2 (flow within IIS). GRW describes Layer 3 (interface transition). Unitarity holds within IIS; non-unitarity describes the interface.

*Potential contradiction 2:* Many-Worlds says all branches are actual. Copenhagen says one outcome occurs.

*Resolution:* MWI describes Layer 1 (all branches exist in IIS). Copenhagen describes Layer 4 (one outcome in actuality). Both are correct in their domains.

*Potential contradiction 3:* QBism says probabilities are subjective. Bohmian mechanics says probabilities are objective (from particle distribution).

*Resolution:* Bohmian describes objective flow in IIS (Layer 2). QBism describes agent's knowledge at Layer 4. Subjective knowledge tracks objective structure.

*Potential contradiction 4:* Hidden variables are ruled out (Bell). Bohm has hidden variables (positions).

*Resolution:* Bell rules out LOCAL hidden variables. Bohmian positions are non-local (guidance equation depends on entire wave function). LRT: the IIS state is the "hidden variable," but it is not local and does not pre-assign Boolean values.

---

## 5. Decoherence as Interface Mechanism

### 5.1 The Decoherence Framework

Decoherence describes how quantum superpositions become effectively classical through environmental interaction. In LRT terms, decoherence is the mechanism by which IIS states approach the Boolean interface threshold.

**Definition 5.1 (System-Environment Split).** A composite state:
$$|\Psi\rangle_{SE} = \sum_i c_i |s_i\rangle_S \otimes |e_i\rangle_E$$

where S is the system, E is the environment, and {|sᵢ⟩} is the pointer basis.

**Definition 5.2 (Reduced Density Matrix).** The system state after tracing out the environment:
$$\rho_S = \text{Tr}_E[|\Psi\rangle_{SE}\langle\Psi|] = \sum_{i,j} c_i c_j^* \langle e_j|e_i\rangle |s_i\rangle\langle s_j|$$

---

### 5.2 Einselection and Pointer Basis

**Definition 5.3 (Pointer Observable).** An observable A is a pointer observable if eigenstates of A are stable under environmental interaction:
$$H_{SE} |a_i\rangle_S |e_0\rangle_E = |a_i\rangle_S |e_i(t)\rangle_E$$

The eigenstates |aᵢ⟩ form the **pointer basis**.

**Theorem 5.4 (Zurek).** The pointer basis is selected by the interaction Hamiltonian H_SE. States that commute with H_SE (in the relevant sense) are einselected.

**LRT Interpretation:** The pointer basis is the basis in which Φ operates. Einselection determines which partition of IIS interfaces with Boolean actuality.

---

### 5.3 Decoherence Dynamics

**Definition 5.5 (Lindblad Equation).** The general form of Markovian open-system dynamics:
$$\frac{d\rho}{dt} = -\frac{i}{\hbar}[H, \rho] + \sum_k \gamma_k \left( L_k \rho L_k^\dagger - \frac{1}{2}\{L_k^\dagger L_k, \rho\} \right)$$

where Lₖ are Lindblad operators and γₖ are decoherence rates.

**Theorem 5.6 (Off-Diagonal Decay).** For a system coupled to an environment, off-diagonal elements of ρ in the pointer basis decay:
$$\rho_{ij}(t) = \rho_{ij}(0) \cdot e^{-t/\tau_D} \quad (i \neq j)$$

where τ_D is the decoherence time.

---

### 5.4 Decoherence Timescales

**Theorem 5.7 (Decoherence Time).** For a massive object in a thermal environment:
$$\tau_D \sim \frac{\hbar^2}{m k_B T (\Delta x)^2} = \tau_R \left( \frac{\lambda_{dB}}{\Delta x} \right)^2$$

where:
- m is mass
- T is temperature
- Δx is superposition separation
- λ_dB is thermal de Broglie wavelength
- τ_R is relaxation time

**Example Calculations:**

| System | Δx | τ_D |
|--------|-----|-----|
| Electron in lab | 1 nm | ~ 10⁻¹³ s |
| Dust grain (10⁻⁵ g) | 1 nm | ~ 10⁻³¹ s |
| Bowling ball | 1 cm | ~ 10⁻⁴³ s |

**Corollary 5.8.** For macroscopic objects, τ_D → 0 effectively. The interface transition is instantaneous at human scales.

**LRT Interpretation:** This resolves the "when does collapse happen?" objection. For macro systems, the interface is crossed so rapidly that the question of precise timing becomes physically meaningless. The transition is effectively instantaneous.

---

### 5.5 Quantum Darwinism

**Definition 5.9 (Redundant Encoding).** A state is redundantly encoded in the environment if multiple environment fragments contain complete information about the system's pointer state.

**Theorem 5.10 (Zurek et al.).** After decoherence, pointer states are redundantly recorded in the environment. Many observers can independently determine the system state without disturbing it.

**LRT Interpretation:** Quantum Darwinism explains the emergence of objective, classical-looking reality. The Boolean outcome is not just recorded once but proliferates through the environment. This is how actuality becomes intersubjectively accessible.

---

### 5.6 Decoherence as Interface Threshold

**Proposition 5.11.** Decoherence marks the approach to, not the moment of, Boolean actuality.

*Argument:* Decoherence converts:
$$\rho = \sum_{ij} c_i c_j^* |i\rangle\langle j| \quad \rightarrow \quad \rho_{dec} = \sum_i |c_i|^2 |i\rangle\langle i|$$

The decohered state is still a density matrix in IIS - a classical mixture. The final step to Boolean actuality (one outcome) is the interface proper.

**Relation to GRW:** GRW models the statistics of this final step. Decoherence explains why the pointer basis is preferred; GRW (in LRT interpretation) describes the transition rate to definite outcome within that basis.

---

## 6. Bohmian Statistics Without Bohmian Ontology

### 6.1 The Bohmian Framework

Bohmian mechanics supplements the wave function with definite particle positions. LRT does not adopt the ontology (particles always have positions) but leverages the mathematics (guidance equation, quantum equilibrium).

**Definition 6.1 (Guidance Equation).** For a particle with wave function ψ(x,t):
$$\frac{dQ}{dt} = \frac{\hbar}{m} \text{Im} \frac{\nabla\psi(Q,t)}{\psi(Q,t)} = \frac{j(Q,t)}{|\psi(Q,t)|^2}$$

where Q is position and j is probability current.

**Definition 6.2 (Quantum Equilibrium).** A distribution ρ(x,t) is in quantum equilibrium if:
$$\rho(x,t) = |\psi(x,t)|^2$$

---

### 6.2 Equivariance

**Theorem 6.3 (Dürr-Goldstein-Zanghì).** Quantum equilibrium is preserved under Bohmian evolution. If ρ(x,0) = |ψ(x,0)|² then ρ(x,t) = |ψ(x,t)|² for all t.

*Proof Sketch:* The continuity equation for probability:
$$\frac{\partial \rho}{\partial t} + \nabla \cdot (\rho v) = 0$$

combined with the guidance equation yields:
$$\frac{\partial |\psi|^2}{\partial t} + \nabla \cdot (|\psi|^2 v) = 0$$

which is exactly the quantum continuity equation. Hence if ρ = |ψ|² initially, it remains so. ∎

**LRT Interpretation:** The Born distribution |ψ|² is not just a probability rule but a dynamical equilibrium. IIS flow preserves this distribution. Actualization samples from an equilibrium distribution that is self-maintaining.

---

### 6.3 Origin of Quantum Randomness

**Theorem 6.4 (Dürr-Goldstein-Zanghì).** For typical initial conditions (in a measure-theoretic sense), subsystems are in quantum equilibrium even if the universe as a whole is in a definite state.

*Argument:* Consider the universal wave function Ψ(q,Q) where q is subsystem coordinates and Q is everything else. For typical Q, the conditional distribution of q is |ψ(q)|² where ψ is the effective wave function of the subsystem.

**LRT Interpretation:** Randomness in outcomes is not fundamental indeterminism but reflects our ignorance of the full IIS state. However, unlike classical hidden variables, this "ignorance" is structural - it follows from the entanglement structure of IIS, not from practical limitations.

---

### 6.4 Probability Current Structure

**Definition 6.5 (Probability Current).** For wave function ψ:
$$\mathbf{j} = \frac{\hbar}{2mi}(\psi^* \nabla\psi - \psi \nabla\psi^*) = \frac{\hbar}{m}|\psi|^2 \nabla S$$

where ψ = |ψ|e^{iS/ℏ}.

**Proposition 6.6.** The probability current defines a flow field on IIS. Integral curves are the Bohmian trajectories.

**LRT Interpretation:** This flow exists in IIS whether or not we adopt Bohmian ontology. It describes the structure of probability distribution evolution. Actualization can be thought of as "sampling from the flow" at the interface.

---

### 6.5 Arrival Times

**Problem:** Standard QM does not have a time-of-arrival observable. Bohmian mechanics does.

**Definition 6.7 (Arrival Time Distribution).** For a particle with initial distribution ρ₀(x) and guidance velocity v(x,t), the arrival time distribution at detector position X is:
$$\Pi(t) = |j(X,t)| = |\psi(X,t)|^2 |v(X,t)|$$

**LRT Application:** Arrival time predictions from Bohmian mechanics are LRT predictions. We inherit this predictive structure without committing to always-definite positions.

---

### 6.6 What LRT Takes from Bohm

| Bohmian Element | LRT Adoption | LRT Interpretation |
|-----------------|--------------|-------------------|
| Guidance equation | Yes | Flow structure in IIS |
| Quantum equilibrium | Yes | Born rule as equilibrium |
| Equivariance | Yes | Interface samples from preserved distribution |
| Always-definite positions | **No** | Positions definite only after interface |
| Preferred foliation | **No** | Global constraint, not preferred frame |
| Determinism | **No** | Epistemic, not ontic; interface is stochastic |

---

### 6.7 Surreal Trajectories

**Observation (Englert et al.):** In some experiments, Bohmian trajectories are "surreal" - they do not match naive intuitions about particle paths.

**LRT Response:** This is expected. Bohmian trajectories describe probability flow in IIS, not classical paths in space. The "surreal" character reflects the non-classical structure of IIS. Since LRT does not claim particles have trajectories prior to actualization, surreal trajectories are not a problem - they are a feature of IIS flow structure.

---

## 7. Collapse Dynamics Reinterpreted

### 7.1 The GRW Model

**Definition 7.1 (GRW Dynamics).** In the Ghirardi-Rimini-Weber model, wave functions undergo spontaneous localization:
$$|\psi\rangle \rightarrow \frac{L_x|\psi\rangle}{\|L_x|\psi\rangle\|}$$

with rate λ per particle, where:
$$L_x(\mathbf{q}) = \left(\frac{1}{\pi a^2}\right)^{3/4} e^{-(\mathbf{q}-\mathbf{x})^2/2a^2}$$

is a localization operator centered at random position x.

**Parameters:**
- λ ≈ 10⁻¹⁶ s⁻¹ (collapse rate per nucleon)
- a ≈ 10⁻⁷ m (localization width)

---

### 7.2 Mass Scaling

**Theorem 7.2 (Amplification).** For a rigid body of N nucleons, the effective collapse rate is:
$$\Lambda = N \cdot \lambda$$

**Consequence:** Microscopic systems (N ~ 1) undergo rare collapses. Macroscopic systems (N ~ 10²³) collapse almost instantly:

| System | N | Mean collapse time |
|--------|---|-------------------|
| Electron | 1 | ~ 10⁸ years |
| Protein | 10⁵ | ~ 10³ years |
| Virus | 10⁷ | ~ 10 years |
| Dust grain | 10¹⁴ | ~ 10⁻⁶ s |
| Cat | 10²⁷ | ~ 10⁻¹¹ s |

**LRT Interpretation:** This scaling explains why microscopic systems exhibit quantum behavior while macroscopic systems appear classical. The interface transition rate scales with system complexity.

---

### 7.3 Continuous Spontaneous Localization (CSL)

**Definition 7.3 (CSL Dynamics).** The continuous version of GRW:
$$d|\psi\rangle = \left[-\frac{i}{\hbar}H dt + \sqrt{\gamma}\int d^3x (N(\mathbf{x}) - \langle N(\mathbf{x})\rangle)dW_t(\mathbf{x}) - \frac{\gamma}{2}\int d^3x (N(\mathbf{x}) - \langle N(\mathbf{x})\rangle)^2 dt\right]|\psi\rangle$$

where N(x) is mass density, γ is collapse strength, and dW is a Wiener process.

**Properties:**
- Continuous evolution (no discrete jumps)
- Preserves energy on average
- Reproduces Born rule statistics

---

### 7.4 LRT Reinterpretation

**Proposition 7.4.** GRW/CSL mathematics describes interface statistics, not fundamental dynamics.

| GRW Concept | LRT Interpretation |
|-------------|-------------------|
| Spontaneous collapse | Interface transition from IIS to actuality |
| Collapse rate λ | Probability of interface per unit time |
| Localization width a | Precision of Boolean actualization |
| Mass scaling N·λ | More complex systems interface faster |
| Stochasticity | Genuine indeterminacy at interface |

**Key Difference:** GRW modifies the Schrödinger equation fundamentally. LRT says Schrödinger evolution is exact in IIS; GRW statistics describe the interface.

---

### 7.5 Energy Non-Conservation

**Problem:** GRW dynamics do not strictly conserve energy. Collapse events inject small amounts of energy.

**GRW Response:** The energy injection is small (~ 10⁻²⁵ W per nucleon) and currently undetectable.

**LRT Response:** If GRW describes interface statistics rather than fundamental dynamics, energy is exactly conserved in IIS (unitary evolution). The apparent non-conservation is a feature of the interface, not a modification of physics.

---

### 7.6 Relativistic Extensions

**Problem:** GRW is non-relativistic. Relativistic extensions (Tumulka's rGRW) exist but are complex.

**LRT Perspective:** The difficulty of relativistic collapse models reflects the tension between:
- Global constraint (collapse affects entire wave function)
- Local causality (no preferred foliation)

LRT's "global constraint" interpretation suggests that relativistic collapse should be understood not as a dynamical process but as global consistency condition - which may be more naturally relativistic.

---

### 7.7 What LRT Takes from GRW

| GRW Element | LRT Adoption | LRT Interpretation |
|-------------|--------------|-------------------|
| Collapse mathematics | Yes | Interface statistics |
| Stochasticity | Yes | Genuine randomness at interface |
| Mass scaling | Yes | Complexity determines interface rate |
| Modified Schrödinger equation | **No** | Schrödinger exact in IIS |
| Collapse as physical process | **No** | Collapse as category transition |
| Energy non-conservation | **No** | Energy exactly conserved in IIS |

---

## 8. QBist Probability Theory

### 8.1 The QBist Framework

Quantum Bayesianism (QBism) treats quantum states as expressions of an agent's beliefs, not objective features of reality. LRT is realist where QBism is anti-realist, but LRT can leverage QBist probability theory.

**Core QBist Claims:**
1. Quantum states are degrees of belief
2. The Born rule is a normative coherence constraint
3. Measurement outcomes are personal experiences
4. There is no "view from nowhere"

---

### 8.2 Dutch Book Arguments

**Definition 8.1 (Dutch Book).** A Dutch book is a set of bets that guarantees loss regardless of outcome. An agent is **coherent** if no Dutch book can be made against them.

**Theorem 8.2 (de Finetti).** Coherent betting requires probabilities satisfying Kolmogorov axioms.

**Theorem 8.3 (Caves-Fuchs-Schack).** In the quantum setting, coherent betting on measurement outcomes requires probabilities given by the Born rule.

*Sketch:* Consider bets on outcomes of SIC-POVM measurements (see below). Coherence requires that probabilities form a valid quantum state. The unique coherent probability assignment is |⟨outcome|ψ⟩|².

**LRT Interpretation:** The Born rule is not just true but rationally required. Any agent betting on interface outcomes, regardless of their metaphysical views, must use Born probabilities on pain of guaranteed loss.

---

### 8.3 SIC-POVMs

**Definition 8.4 (SIC-POVM).** A Symmetric Informationally Complete POVM in dimension d consists of d² elements {Πᵢ = (1/d)|πᵢ⟩⟨πᵢ|} where:
$$|\langle\pi_i|\pi_j\rangle|^2 = \frac{1}{d+1} \quad (i \neq j)$$

**Properties:**
- Minimal complete measurement (d² outcomes for d-dimensional system)
- Maximal symmetry
- Equal a priori probability (1/d²) for each outcome

**Theorem 8.5.** SIC-POVMs exist in all dimensions tested (d ≤ 193) and are conjectured to exist in all finite dimensions.

**LRT Interpretation:** SIC-POVMs are the "natural" interface structure - the most symmetric way to extract Boolean information from IIS states. They represent optimal probing of the IIS.

---

### 8.4 The Urgleichung

**Theorem 8.6 (Fundamental Probability Rule).** For a SIC-POVM {Πᵢ} and outcomes Dⱼ of a subsequent measurement:
$$P(D_j|H_i) = (d+1)P(H_i)P(D_j) - 1$$

where Hᵢ is the hypothesis "outcome i occurred in the SIC measurement."

**Interpretation:** This is the quantum analogue of Bayes' theorem. It shows how beliefs update through quantum measurements.

**LRT Interpretation:** The Urgleichung describes how an agent's knowledge of the IIS state updates through interface events. It is the rational update rule for tracking IIS structure.

---

### 8.5 Quantum States as Beliefs About What?

**QBist Answer:** Quantum states are beliefs about future experiences. There is no further "what."

**LRT Answer:** Quantum states are beliefs about IIS structure. The IIS is real; beliefs track it.

This explains why QBism works: QBist probability rules are correct because they track objective IIS structure. QBist agents are (unknowingly) rational trackers of IIS.

---

### 8.6 Intersubjective Agreement

**Problem for QBism:** If quantum states are subjective beliefs, why do different agents agree on predictions?

**QBist Response:** Agents who communicate and share experiences align their beliefs.

**LRT Response:** Agents agree because they're tracking the same objective IIS structure. Intersubjective agreement is evidence for IIS realism, not just social coordination.

---

### 8.7 What LRT Takes from QBism

| QBist Element | LRT Adoption | LRT Interpretation |
|---------------|--------------|-------------------|
| Born rule as coherence | Yes | Rational requirement for interface betting |
| SIC-POVMs | Yes | Optimal interface structure |
| Urgleichung | Yes | Rational update rule |
| Agent perspective | Partial | Context matters; agent is part of context |
| Anti-realism about states | **No** | IIS states are real |
| Subjectivism | **No** | Beliefs track objective structure |
| No "view from nowhere" | Partial | Actualization is context-relative; IIS is objective |

---

## 9. Relational Structures

### 9.1 Relational Quantum Mechanics

Rovelli's Relational QM (RQM) holds that quantum states are always relative to an observer-system. There are no absolute, observer-independent states.

**Core RQM Claims:**
1. Properties are relative to interactions
2. No privileged observer
3. The wave function describes correlations, not intrinsic properties
4. Different observers may assign different states to the same system

---

### 9.2 Perspectival States

**Definition 9.1 (Relative State).** For composite system AB in state |Ψ⟩_AB, the state of B relative to A being in state |a⟩ is:
$$|\psi\rangle_{B|a} = \frac{\langle a|\Psi\rangle_{AB}}{\|\langle a|\Psi\rangle_{AB}\|}$$

**Proposition 9.2.** Different "observers" (subsystems) assign different states to the same system.

*Example:* Consider |Ψ⟩_AB = (1/√2)(|0⟩_A|0⟩_B + |1⟩_A|1⟩_B).
- Relative to A in |0⟩: B is in |0⟩
- Relative to A in |1⟩: B is in |1⟩
- Relative to an external observer: AB is in entangled state

All descriptions are correct relative to their reference system.

---

### 9.3 LRT Interpretation of Relationality

**Proposition 9.3.** Relational states describe context-dependent interface structure.

In LRT:
- The IIS state |Ψ⟩_AB is objective
- Different contexts (different subsystem chosen as "observer") yield different interfaces
- "Relative to A" means "interfacing with A as the Boolean context"

**Key Insight:** RQM's relationality is the context-dependence of the interface (Theorem 4.6). Different contexts partition IIS differently, yielding different Boolean outcomes.

---

### 9.4 Partial Observables

**Definition 9.4 (Partial Observable).** An observable O is partial if it does not commute with all other observables - its value depends on context.

**Theorem 9.5 (Kochen-Specker, restated).** Most quantum observables are partial. Only observables in the center of the algebra (multiples of identity) are context-independent.

**LRT Interpretation:** Partial observables reflect the fact that IIS does not have pre-existing Boolean values. The "value" of an observable is generated at the interface, and different interfaces (contexts) generate different values.

---

### 9.5 Relational Observables in Constrained Systems

**Definition 9.6 (Relational Observable).** For a system with constraint C(q,p) = 0, a relational observable O[f,T] answers: "What is the value of f when T = τ?"

*Example:* In general relativity, "position of particle at time t" is meaningless (no background time). But "position of particle when clock reads t" is well-defined.

**Application to LRT:** Relational observables are the physically meaningful quantities. They survive to actuality because they are defined relative to an interface context.

---

### 9.6 Gauge Invariance

**Definition 9.7 (Gauge Transformation).** A transformation G on IIS that does not change physical (actualizable) quantities.

**Proposition 9.8.** Physical observables are gauge-invariant. Only gauge-invariant quantities interface with Boolean actuality.

**Examples:**
- Phase of wave function: gauge (unobservable)
- Relative phase: physical (interference)
- Absolute position in empty space: gauge
- Relative position: physical

**LRT Interpretation:** Gauge freedom reflects redundancy in IIS description. Only gauge-invariant structures reach actuality.

---

### 9.7 What LRT Takes from Relational QM

| RQM Element | LRT Adoption | LRT Interpretation |
|-------------|--------------|-------------------|
| Perspectival states | Yes | Interface is context-relative |
| No absolute state | Partial | IIS state is objective; Boolean outcome is relative |
| All observers equivalent | Yes | Any Boolean context can serve as interface |
| Relationality of properties | Yes | Properties generated at interface |
| Correlations primary | Partial | IIS structure is primary; correlations are projections |
| Full anti-realism | **No** | IIS is real; outcomes are real relative to context |

---

## 10. Global Constraints

### 10.1 Time-Symmetric Formulations

The Wheeler-Feynman absorber theory and Cramer's transactional interpretation use time-symmetric formulations. LRT reinterprets these as global constraint mathematics without retrocausation.

**Definition 10.1 (Advanced and Retarded Solutions).** The wave equation has two solutions:
- Retarded: depends on past sources
- Advanced: depends on future absorbers

Standard QM uses only retarded solutions. Time-symmetric formulations use both.

---

### 10.2 Two-State Vector Formalism

**Definition 10.2 (Two-State Vector).** A system is described by:
- Pre-selected state |ψ⟩ (prepared at initial time)
- Post-selected state ⟨φ| (measured at final time)

The complete description is the two-state vector: ⟨φ| · |ψ⟩

**Proposition 10.3 (Aharonov-Bergmann-Lebowitz).** Probabilities for intermediate measurements depend on both pre- and post-selection:
$$P(a_n | \psi, \phi) = \frac{|\langle\phi|a_n\rangle|^2 |\langle a_n|\psi\rangle|^2}{\sum_m |\langle\phi|a_m\rangle|^2 |\langle a_m|\psi\rangle|^2}$$

**LRT Interpretation:** The two-state vector describes boundary conditions on the IIS path. Both initial and final constraints determine the admissible IIS configurations. This is constraint satisfaction, not backward causation.

---

### 10.3 Weak Values

**Definition 10.4 (Weak Value).** For observable A with pre-selection |ψ⟩ and post-selection ⟨φ|:
$$A_w = \frac{\langle\phi|A|\psi\rangle}{\langle\phi|\psi\rangle}$$

**Properties:**
- Can be complex
- Can lie outside eigenvalue spectrum
- Observed in weak measurement limit

**Example:** A spin-1/2 particle can have weak value σ_z = 100 under appropriate pre/post-selection.

**LRT Interpretation:** Weak values are not "values" in the Boolean sense. They are features of the IIS configuration constrained by both boundary conditions. They become relevant when the interface is "weak" (does not fully enforce Boolean structure).

---

### 10.4 Transactional Interpretation Reframed

**Cramer's View:**
- Offer wave: ψ travels forward in time
- Confirmation wave: ψ* travels backward in time
- Transaction: handshake between source and absorber

**LRT Reframe:**
- Offer wave: IIS configuration from initial conditions
- Confirmation wave: constraint from final conditions
- Transaction: global consistency of IIS path

The mathematics is the same; the interpretation differs. LRT does not require literal backward-in-time propagation, only global constraints that formally resemble it.

---

### 10.5 Destiny States

**Definition 10.5 (Destiny State, Aharonov et al.).** A post-selected state that constrains intermediate evolution, analogous to how initial states constrain future evolution.

**Proposition 10.6.** In the two-state formalism, past and future are symmetric. Both provide constraints on the intermediate evolution.

**LRT Interpretation:** This symmetry reflects that IIS is atemporal. The "direction of time" is a feature of actuality (thermodynamic arrow), not of IIS structure. Logical constraints (3FLL) do not have temporal direction.

---

### 10.6 The Block Universe Connection

**Definition 10.7 (Block Universe).** The view that past, present, and future all equally exist. Time is a dimension, not a flow.

**Relation to LRT:**
- IIS is block-like: all possible configurations coexist
- Actuality has temporal structure: events are ordered
- The interface creates the "now" - the point of Boolean actualization

**Proposition 10.8.** Global constraints in LRT are naturally block-universe compatible. 3FLL operate over the entire IIS, not moment-by-moment.

---

### 10.7 What LRT Takes from Time-Symmetric Approaches

| Element | LRT Adoption | LRT Interpretation |
|---------|--------------|-------------------|
| Two-state vector | Yes | Boundary conditions on IIS |
| Weak values | Yes | Features of constrained IIS |
| Advanced solutions | Yes | Global constraints (not retrocausation) |
| Transaction | Yes | Constraint satisfaction |
| Time-symmetry | Partial | IIS is atemporal; actuality has arrow |
| Backward causation | **No** | Constraints are global, not causal |

---

## 11. Reconstruction Theorems as Validation

### 11.1 The Reconstruction Program

Multiple research programs have derived quantum theory from operational or informational axioms. These reconstructions validate LRT by showing that quantum structure follows from constraints LRT motivates.

---

### 11.2 Hardy's Axioms (2001)

**Axioms:**
1. **Probabilities:** States are characterized by probabilities
2. **Simplicity:** The number of degrees of freedom is minimal
3. **Subspaces:** Systems have subsystems; composite rule holds
4. **Composite systems:** States of composites determined by local states
5. **Continuity:** Between any two pure states, there's a continuous reversible path

**Theorem 11.1 (Hardy).** These axioms uniquely determine quantum theory (complex Hilbert space + Born rule).

**LRT Mapping:**
| Hardy Axiom | LRT Grounding |
|-------------|---------------|
| Probabilities | Interface must have measure (Axiom 5) |
| Simplicity | Parsimony (Axiom 6) |
| Subspaces | IIS has compositional structure |
| Composite systems | Local tomography (Axiom 3c) |
| Continuity | Axiom 3a |

---

### 11.3 Chiribella-D'Ariano-Perinotti (CDP, 2011)

**Axioms:**
1. **Causality:** No signaling from future to past
2. **Perfect distinguishability:** Any two states can be distinguished
3. **Ideal compression:** Information can be compressed without loss
4. **Local distinguishability:** Global states distinguished by local measurements
5. **Pure conditioning:** Conditioning on pure states preserves purity

**Theorem 11.2 (CDP).** These axioms uniquely determine quantum theory among GPTs.

**LRT Mapping:**
| CDP Axiom | LRT Grounding |
|-----------|---------------|
| Causality | Interface respects causal order |
| Perfect distinguishability | 3FLL constitute distinguishability |
| Ideal compression | Parsimony; no redundancy |
| Local distinguishability | Local tomography (Axiom 3c) |
| Pure conditioning | Structure preservation in IIS |

---

### 11.4 Masanes-Müller (2011)

**Axioms:**
1. **Continuous reversibility:** State space connected; dynamics invertible
2. **Local tomography:** Joint states determined by local measurements
3. **Existence of entangled states:** Some composite states are not product states

**Theorem 11.3 (Masanes-Müller).** These three axioms uniquely determine complex Hilbert space.

*This is the key theorem used in LRT Section 2 to derive Hilbert space structure.*

**LRT Mapping:**
| MM Axiom | LRT Grounding |
|----------|---------------|
| Continuous reversibility | Axioms 3a, 3b |
| Local tomography | Axiom 3c |
| Entangled states | IIS richness (Definition 2.3) |

---

### 11.5 Dakić-Brukner (2011)

**Axioms:**
1. **Finiteness:** Elementary systems have finite information capacity
2. **Locality:** Joint states from local measurements
3. **Reversibility:** Time evolution is reversible
4. **Continuity:** State space is continuous

**Theorem 11.4 (Dakić-Brukner).** These axioms yield quantum theory with the bit as fundamental unit.

**LRT Connection:** The bit appears explicitly as the fundamental unit - directly aligning with LRT's "bit from fit" thesis.

---

### 11.6 Höhn-Wever (2017)

**Axioms:** Rules for information acquisition by agents:
1. Agents can acquire information via questions
2. Questions have yes/no answers (bits)
3. Composition rules for multiple questions

**Theorem 11.5.** These rules yield quantum theory.

**LRT Connection:** Directly parallels LRT's interface structure - bits (yes/no answers) acquired at the Boolean interface.

---

### 11.7 The Convergence

All reconstruction theorems converge on the same result: quantum theory is uniquely determined by natural constraints.

**Common Elements:**
- Continuity/Reversibility → Axiom 3a,b
- Local tomography → Axiom 3c
- Compositional structure → IIS richness
- Probabilities → Axiom 5

**LRT Interpretation:** The reconstruction axioms are not arbitrary. They are requirements for:
- Stable dynamics (continuity, reversibility)
- Compositional physics (local tomography)
- Informative measurement (distinguishability, probabilities)

These are exactly the constraints needed for IIS to stably interface with Boolean actuality.

---

### 11.8 Uniqueness as Fine-Tuning

**Proposition 11.6.** The reconstruction theorems collectively demonstrate structural fine-tuning.

*Argument:* The theorems show that quantum theory is the UNIQUE structure satisfying natural constraints. Any deviation - real instead of complex numbers, non-reversible dynamics, holistic instead of local tomography - yields a different theory (or no consistent theory at all).

This is precisely the "fine-tuning" claim of LRT Paper 2: quantum structure is not one option among many but the unique stable interface structure.

---

## 12. The Action-Complexity Correspondence

### 12.1 The Central Conjecture

**Conjecture 12.1 (Action-Complexity Equivalence).** There exists a global correspondence between physical action and informational complexity:

$$S = \hbar \cdot C$$

Where:
- S is action (physical units of energy × time)
- C is complexity (information-theoretic, measured in bits)
- ℏ is Planck's constant (the conversion factor)

### 12.2 Supporting Evidence

**Bekenstein bound:** Maximum entropy of a region is proportional to area in Planck units:
$$S_{max} = \frac{2\pi k_B E R}{\hbar c}$$

This bounds information by action.

**Black hole entropy:** The Bekenstein-Hawking formula:
$$S_{BH} = \frac{k_B c^3 A}{4 G \hbar}$$

Entropy (bits) scales with area in Planck units.

**Landauer limit:** Minimum energy to erase one bit:
$$E_{min} = k_B T \ln 2$$

Information erasure costs energy.

### 12.3 Implication for Parsimony

If S = ℏC, then the principle of least action becomes the principle of minimal complexity:

$$\delta S = 0 \iff \delta C = 0$$

This would ground Axiom 6: parsimony (minimal complexity) is equivalent to the variational principle (stationary action).

### 12.4 Status

This conjecture is speculative. We present it as motivation for Axiom 6 and as an open problem, not as an established result.

---

## 13. Novel Mathematical Structures

### 13.1 The IIS Manifold

**Question:** What is the global structure of IIS?

**Definition 13.1 (IIS as Manifold).** IIS, as infinite-dimensional projective Hilbert space, has:
- Local structure: Charts homeomorphic to open sets in ℂ^∞
- Global structure: Complex projective space ℂP^∞
- Metric: Fubini-Study metric (from inner product)

**Properties:**
- Infinite-dimensional Kähler manifold
- Symplectic structure: ω = -i∂∂̄ log⟨ψ|ψ⟩
- Contractible (π_n = 0 for all n)
- Not locally compact

**Open Problem 13.2.** Does IIS have additional structure beyond Hilbert space? Are there constraints on which Hilbert space structures are physically realizable?

---

### 13.2 Complexity Geometry

**Definition 13.3 (Complexity Distance).** An alternative metric on IIS based on circuit complexity:
$$d_C(\psi, \phi) = \min\{C(U) : U|\psi\rangle = |\phi\rangle\}$$

where C(U) is the complexity of unitary U (minimal gate count to implement).

**Properties:**
- Asymmetric in general (complexity of U ≠ complexity of U†)
- Satisfies triangle inequality
- Related to holographic complexity (Brown-Susskind)

**Conjecture 13.4 (Nielsen).** Complexity geometry is related to geodesics in a Riemannian metric on unitary group:
$$ds^2 = \sum_I p_I |\langle I|dU U^\dagger|I\rangle|^2$$

where pᵢ are penalty factors favoring local operations.

**LRT Connection:** If S = ℏC, complexity geometry is action geometry. Paths of minimal complexity are paths of minimal action - classical trajectories.

---

### 13.3 The Interface Category

**Definition 13.5 (Category of IIS).** Objects are IIS states; morphisms are unitary transformations:
- **Ob(IIS):** States |ψ⟩ ∈ ℋ
- **Mor(ψ,φ):** Unitaries U with U|ψ⟩ = |φ⟩
- **Composition:** U₂ ∘ U₁ = U₂U₁
- **Identity:** I_ψ = 1

**Definition 13.6 (Category of Actuality).** Objects are Boolean configurations; morphisms are Boolean functions:
- **Ob(Act):** Elements of {0,1}^n
- **Mor(a,b):** Boolean functions f with f(a) = b
- **Composition:** Standard function composition

**Definition 13.7 (Interface Functor).** The interface Φ defines a functor:
$$\Phi: \mathbf{IIS} \rightarrow \mathbf{Act}$$

satisfying:
- Φ(|ψ⟩) ∈ {0,1}^n (objects map to Boolean configurations)
- Φ(U) ∈ Mor(Φ(ψ), Φ(Uψ)) (morphisms map to Boolean functions)

**Open Problem 13.8.** Is Φ a specific type of functor (e.g., left/right adjoint)? What categorical structure captures the Born rule?

---

### 13.4 Logical Constraint Algebra

**Definition 13.9 (3FLL Algebra).** An algebra 𝔏 generated by three elements {I, NC, EM} with relations:
- I ∘ I = I (identity is idempotent)
- NC ∘ NC = NC (non-contradiction is idempotent)
- EM ∘ EM = EM (excluded middle is idempotent)
- Commutativity and associativity

**Question:** What is the representation theory of 𝔏? How does it relate to orthomodular lattices?

**Definition 13.10 (Orthomodular Lattice).** The lattice of closed subspaces of Hilbert space, with:
- Meet: H₁ ∧ H₂ = H₁ ∩ H₂
- Join: H₁ ∨ H₂ = span(H₁ ∪ H₂)
- Orthocomplement: H⊥

**Proposition 13.11.** The orthomodular lattice is the quantum analogue of Boolean algebra. It satisfies weakened distributivity (orthomodularity) rather than full distributivity.

**Conjecture 13.12.** The 3FLL algebra 𝔏 acts on IIS by constraining which lattice structures are admissible. Boolean subalgebras (contexts) are the maximal sublattices where 3FLL are fully satisfied.

---

### 13.5 Information Geometry

**Definition 13.13 (Fisher Information Metric).** On the space of probability distributions:
$$ds^2 = \sum_{i,j} g_{ij} d\theta^i d\theta^j, \quad g_{ij} = E\left[\frac{\partial \log p}{\partial \theta^i}\frac{\partial \log p}{\partial \theta^j}\right]$$

**Application to QM:** The quantum Fisher information defines a metric on state space:
$$ds^2_Q = 4(1 - |\langle\psi|\psi + d\psi\rangle|^2) = 4 \langle d\psi|(1-|\psi\rangle\langle\psi|)|d\psi\rangle$$

This equals the Fubini-Study metric.

**LRT Interpretation:** Information geometry is the natural geometry of IIS. The Fubini-Study metric is both:
- Distinguishability metric (from 3FLL)
- Information metric (Fisher information)

This unifies logical and informational perspectives.

---

### 13.6 Tensor Network Structure

**Definition 13.14 (Tensor Network).** A representation of quantum states as contractions of tensors:
$$|\psi\rangle = \sum_{i_1...i_n} T_{i_1...i_n} |i_1...i_n\rangle$$

where T factors into local tensors connected by contracted indices.

**Examples:**
- Matrix Product States (MPS): 1D chains
- PEPS: 2D lattices
- MERA: Hierarchical (holographic)

**Application to LRT:** Tensor networks provide a complexity measure:
- Bond dimension χ controls expressiveness
- Complexity ~ log(χ)
- Low-complexity states have efficient tensor network representation

**Conjecture 13.15.** Physical states (those that actualize) have efficient tensor network descriptions. High-complexity states in IIS do not actualize - they violate parsimony (Axiom 6).

---

### 13.7 Holographic Structure

**Definition 13.16 (AdS/CFT Correspondence).** A duality between:
- Gravity in (d+1)-dimensional Anti-de Sitter space
- Conformal field theory on d-dimensional boundary

**Holographic Principle:** Bulk physics encoded on boundary with maximum entropy:
$$S_{max} = \frac{A}{4G\hbar}$$

**LRT Interpretation:** The holographic principle reflects fundamental limits on distinguishability. The boundary encodes the Boolean interface; the bulk is IIS. The Bekenstein bound is not just thermodynamic but logical - a limit on how many bits (distinctions) can be actualized in a region.

---

## 14. Open Problems

The LRT framework raises precise mathematical questions. We organize these by type and difficulty.

### 14.1 Foundational Problems

**Problem 14.1 (Grounding Local Tomography).** Can Axiom 3(c) be derived from 3FLL, or is it an independent physical assumption?

*Current status:* Axiom 3(c) is motivated (compositional physics requires it) but not derived. A derivation would strengthen LRT's logical foundation.

*Approach:* Investigate whether local tomography follows from distinguishability being pairwise (Axiom 2). If distinguishing composite systems requires only pairwise comparisons, local measurements might suffice.

---

**Problem 14.2 (Complex Numbers from Logic).** Can the requirement for complex (not real or quaternionic) numbers be derived from more primitive assumptions?

*Current status:* Masanes-Müller derive complex numbers from local tomography. But why local tomography?

*Approach:* Investigate whether the sesquilinearity of the inner product (needed for non-negative probabilities) combined with interference (needed for non-trivial dynamics) forces complex numbers.

*Partial result (Stueckelberg):* Real QM lacks interference; quaternionic QM has non-local state determination. Only complex QM has both local tomography and interference.

---

**Problem 14.3 (Parsimony Derivation).** Can Axiom 6 (parsimony) be derived from stability requirements?

*Current status:* Axiom 6 is motivated by the action-complexity conjecture but not proven.

*Approach:* If S = ℏC (Problem 14.6), then δS = 0 ⟺ δC = 0. Parsimony would follow from the variational principle, which itself follows from unitarity + stability.

---

### 14.2 Structural Problems

**Problem 14.4 (Hilbert Space Dimension).** Why do physical systems have specific finite-dimensional state spaces?

*Examples:*
- Electron spin: dim = 2
- Photon polarization: dim = 2
- Hydrogen atom energy levels: dim = ∞ (but discrete)

*Current status:* LRT does not derive specific dimensions. This is fine-tuning.

*Approach:* Investigate whether representation theory of symmetry groups (Poincaré, gauge groups) constrains dimensions. Likely requires physics beyond LRT.

---

**Problem 14.5 (Specific Fields).** Why U(1) × SU(2) × SU(3) gauge symmetry? Why three generations of fermions?

*Current status:* Completely open within LRT. This is parameter-level fine-tuning.

*Approach:* Beyond current LRT scope. May require string/M-theory or other unification framework.

---

**Problem 14.6 (Action-Complexity Correspondence).** Prove or refute S = ℏC.

*Current status:* Conjectural, supported by:
- Bekenstein bound (information bounded by action)
- Black hole entropy (bits per Planck area)
- Landauer limit (energy per bit erasure)
- Margolus-Levitin theorem (operations per unit action)

*Approaches:*
1. Derive from holographic principle
2. Prove in simple models (qubit systems)
3. Find counterexamples

*Key test:* If S = ℏC, then the quantum speed limit (minimum time for state change) equals the complexity distance divided by available action.

---

### 14.3 Interface Problems

**Problem 14.7 (Physical Interface Criterion).** What physical process marks the transition from Layer 2 (IIS flow) to Layer 4 (Boolean actuality)?

*Candidates:*
| Criterion | Proponent | Testable? |
|-----------|-----------|-----------|
| Decoherence threshold | Zurek, Zeh | Yes (indirect) |
| Gravitational collapse | Penrose | Yes (in principle) |
| Irreversible amplification | Various | Partially |
| Thermodynamic threshold | Various | Yes |
| Consciousness | Wigner (historical) | No |

*Current status:* LRT is compatible with any of these. The question is empirical.

*Experimental approach:* Test Penrose-Diósi model predictions for collapse rate vs. mass.

---

**Problem 14.8 (Interface Timing).** Is there a precise "moment" of actualization, or is the interface a continuous transition?

*Options:*
1. Discrete: Sharp transition at threshold (GRW-like)
2. Continuous: Gradual approach to Boolean (decoherence-like)
3. Contextual: Depends on what we count as "actualization"

*LRT stance:* The question may be ill-posed. "When" presupposes temporal structure that may not apply to the interface itself.

---

### 14.4 Relativistic Problems

**Problem 14.9 (Lorentz Invariance of IIS).** How does Lorentz symmetry act on IIS?

*Current status:* Non-relativistic QM is well-understood in LRT. Relativistic extension requires:
- Poincaré group representation on IIS
- Covariant interface map
- Consistency with QFT

*Approach:* Use algebraic QFT framework. Local algebras of observables may provide covariant interface structure.

---

**Problem 14.10 (Interface and Causality).** How does the interface respect the light-cone structure?

*Issue:* "Global constraint" sounds non-local. But Bell non-locality is compatible with no-signaling.

*Resolution approach:* Show that while IIS state is global, the interface outputs respect causal structure. Outcomes at spacelike separation are correlated but not causally connected.

---

**Problem 14.11 (Quantum Gravity Interface).** Does gravity modify the interface?

*Penrose conjecture:* Gravitational self-energy causes objective collapse:
$$\tau \sim \frac{\hbar}{E_G}$$

where E_G is gravitational self-energy of superposition.

*LRT question:* Is this a modification of the interface, or an additional constraint from general relativity?

---

### 14.5 Mathematical Problems

**Problem 14.12 (Categorical Interface).** What categorical structure describes the interface functor Φ?

*Questions:*
- Is Φ a left/right adjoint?
- What is the kernel/cokernel?
- How does composition interact with Born rule?

---

**Problem 14.13 (Complexity Measure on IIS).** Define a rigorous complexity measure satisfying:
1. Computable (at least approximately)
2. Additive for independent systems
3. Connected to action via S = ℏC

*Issue:* Kolmogorov complexity is uncomputable. Resource-bounded variants may work.

---

**Problem 14.14 (3FLL Algebra Representation).** Characterize representations of the 3FLL algebra.

*Question:* What mathematical structure emerges from taking 3FLL as axioms of an algebraic system?

---

### 14.6 Number-Field Problem

**Problem 14.15 (Deriving ℂ from Interface Requirements).** Is the choice of complex numbers forced by requiring:
1. Non-negative probabilities (|⟨a|ψ⟩|² ≥ 0)
2. Interference (non-trivial dynamics)
3. Local tomography (compositionality)

*Partial answer (Masanes-Müller):* Conditions 1-3 uniquely determine ℂ among ℝ, ℂ, ℍ.

*Remaining question:* Can we derive these conditions from 3FLL + distinguishability?

---

### 14.7 Summary of Problem Status

| Problem | Difficulty | Approach | Status |
|---------|------------|----------|--------|
| 14.1 Local tomography | Hard | Logical analysis | Open |
| 14.2 Complex numbers | Medium | Interference + probability | Partial |
| 14.3 Parsimony | Hard | Action-complexity | Open |
| 14.4 Dimension | Very Hard | Representation theory | Open |
| 14.5 Specific fields | Beyond LRT | Unification physics | Open |
| 14.6 S = ℏC | Hard | Holography, simple models | Conjectural |
| 14.7 Physical criterion | Empirical | Experiment | Testable |
| 14.8 Interface timing | Medium | Conceptual analysis | Unclear if well-posed |
| 14.9 Lorentz IIS | Hard | Algebraic QFT | Open |
| 14.10 Causality | Medium | No-signaling proofs | Tractable |
| 14.11 Quantum gravity | Very Hard | Penrose-Diósi tests | Experimentally open |
| 14.12 Category theory | Medium | Mathematical | Open |
| 14.13 Complexity measure | Hard | Information theory | Open |
| 14.14 3FLL algebra | Medium | Algebra | Open |
| 14.15 Number field | Medium | Reconstruction | Partial |

---

## 15. Conclusion

### 15.1 Summary of Results

This paper has provided rigorous mathematical foundations for Logic Realism Theory. The main results are:

**Derivations:**

1. **Hilbert space structure** (Theorems 2.1-2.3): From Axioms 1-3 (3FLL constitution, pairwise distinguishability, continuity, reversibility, local tomography), IIS has the structure of a complex Hilbert space. This follows via the Masanes-Müller reconstruction theorem.

2. **Born rule** (Theorem 4.2): From Axiom 5 (non-contextual measure) and Hilbert space structure, the interface probability is |⟨outcome|ψ⟩|². This follows via Gleason's theorem.

3. **Contextuality** (Theorem 4.7, Proposition 4.8): The Kochen-Specker theorem follows from LRT structure. Contextuality is not a quantum anomaly but the signature of the IIS → Boolean interface.

**Unifications:**

4. **Layer structure** (Section 4.5): Existing interpretations describe different layers of LRT:
   - Layer 1: Unitary QM / Many-Worlds (IIS dynamics)
   - Layer 2: Bohmian mechanics (probability flow)
   - Layer 3: Decoherence / GRW (interface approach)
   - Layer 4: Copenhagen / QBism (Boolean outcomes)

5. **Domain assignments** (Sections 5-10): Each framework's mathematics is valid in its domain:
   - Bohmian guidance equation: probability flow in IIS
   - GRW collapse rate: interface transition statistics
   - QBist coherence: rational betting on outcomes
   - Relational states: context-dependent interface

**Conjectures:**

6. **Action-complexity correspondence** (Section 12): S = ℏC connects physical action to informational complexity, potentially grounding parsimony (Axiom 6).

7. **Novel structures** (Section 13): IIS has rich mathematical structure (Kähler manifold, information geometry, categorical interface) inviting further investigation.

---

### 15.2 The Derivation Chain

The logical structure of LRT is:

```
THREE FUNDAMENTAL LOGICAL LAWS
        │
        │ Axiom 1: constitute
        ▼
   DISTINGUISHABILITY
        │
        │ Axiom 2: pairwise
        ▼
  BINARY RELATION D(x,y)
        │
        │ Axiom 3a,b: continuity + reversibility
        │ Axiom 3c: local tomography
        ▼
    ┌───────────────────────┐
    │  MASANES-MÜLLER       │
    │  RECONSTRUCTION       │
    └───────────────────────┘
        │
        ▼
 COMPLEX HILBERT SPACE
        │
        │ Axiom 4: Boolean actuality
        │ Axiom 5: non-contextual measure
        ▼
    ┌───────────────────────┐
    │  GLEASON'S            │
    │  THEOREM              │
    └───────────────────────┘
        │
        ▼
     BORN RULE
        │
        │ Axiom 6: parsimony
        ▼
  QUANTUM MECHANICS
```

---

### 15.3 What LRT Achieves

**Conceptually:**
- Grounds quantum mechanics in logical structure
- Dissolves measurement problem (category transition, not dynamical process)
- Explains contextuality (interface signature)
- Unifies competing interpretations (different layers)

**Mathematically:**
- Provides axiomatic foundation
- Derives (not assumes) Born rule
- Inherits 200+ person-years of interpretational mathematics
- Identifies precise open problems

**Physically:**
- Makes no new empirical predictions (interpretation, not new physics)
- Compatible with all standard QM predictions
- Compatible with candidate interface mechanisms (decoherence, GRW, Penrose)

---

### 15.4 What LRT Does Not Achieve

**Not derived:**
- Specific Hilbert space dimensions
- Specific quantum fields
- Particle masses and coupling constants
- Spacetime dimension
- Why 3FLL (taken as primitive)

**Not resolved:**
- Physical criterion for interface timing
- Relativistic formulation
- Quantum gravity interface
- Full grounding of parsimony

These remain fine-tuning facts or open problems.

---

### 15.5 Relation to Other Programs

| Program | Relation to LRT |
|---------|-----------------|
| Reconstruction theorems | LRT uses them to derive Hilbert space |
| Bohmian mechanics | LRT inherits flow mathematics, rejects always-definite positions |
| GRW | LRT inherits collapse statistics, rejects modified dynamics |
| Many-Worlds | LRT shares wave function realism, restores single actuality |
| QBism | LRT grounds QBist probability theory in objective IIS |
| Relational QM | LRT explains relationality via context-dependent interface |
| It from Bit (Wheeler) | LRT provides mechanism: bit from fit (3FLL + stability) |
| Structural realism | LRT is structuralist: 3FLL are structural, not substantial |

---

### 15.6 The Trilogy

This paper completes a three-part development:

**Paper 1: Logic Realism Theory**
- Thesis: 3FLL are constitutive of physical reality
- Method: Philosophical argument (inference to best explanation)
- Result: Establishes ontological foundation

**Paper 2: It from Bit, Bit from Fit**
- Thesis: Quantum mechanics is the unique stable interface
- Method: Physical/structural argument
- Result: Grounds quantum mechanics in LRT

**Paper 3: Mathematical Structure (this paper)**
- Thesis: LRT has rigorous mathematical formulation
- Method: Axiomatic derivation
- Result: Provides formal foundations

Together, the three papers offer:
- A philosophical position (logic realism)
- A physical interpretation (interface theory)
- A mathematical framework (axiomatic QM)

---

### 15.7 Future Directions

**Near-term:**
1. Prove or refute S = ℏC in simple models
2. Develop relativistic LRT using algebraic QFT
3. Formalize the interface category

**Medium-term:**
4. Derive local tomography from 3FLL
5. Connect LRT to quantum gravity proposals
6. Test Penrose-Diósi collapse predictions

**Long-term:**
7. Derive specific field content from LRT
8. Unify LRT with cosmological structure
9. Resolve the arrow of time within LRT

---

### 15.8 Final Remarks

Logic Realism Theory proposes that quantum mechanics is not a mysterious departure from classical physics but a natural consequence of logical structure interfacing with Boolean actuality. The "weirdness" of quantum mechanics - superposition, entanglement, contextuality, measurement - dissolves when we recognize the distinction between IIS (where 3FLL structure but not determine) and actuality (where 3FLL fully enforce Boolean outcomes).

The framework is conservative in one sense: it makes no new empirical predictions beyond standard quantum mechanics. It is radical in another: it claims that the structure of quantum mechanics follows from logic plus stability requirements.

This paper has shown that the claim is mathematically precise. The derivation chain from 3FLL to Born rule is rigorous, leveraging established theorems (Masanes-Müller, Gleason). The unification of interpretations is not hand-waving but domain assignment. The open problems are well-defined mathematical questions.

Whether LRT is correct is, ultimately, a question about the nature of reality - specifically, whether logical structure is merely descriptive or genuinely constitutive. This paper cannot settle that question. What it can do - and has done - is show that the constitutive view has a coherent, rigorous mathematical formulation.

The laws of logic may indeed be the laws of physics. And quantum mechanics is what it looks like when those laws are forced to produce a stable, observable world.

---

## Appendix A: Proof Compendium

This appendix provides key proofs in LRT notation, adapted from their original sources.

### A.1 Gleason's Theorem (1957)

**Theorem (Gleason).** Let ℋ be a Hilbert space with dim(ℋ) ≥ 3. Let μ be a function from closed subspaces of ℋ to [0,1] satisfying:
1. μ(ℋ) = 1
2. For mutually orthogonal subspaces {Hᵢ}: μ(⊕ᵢHᵢ) = Σᵢμ(Hᵢ)

Then there exists a positive semi-definite operator ρ with Tr(ρ) = 1 such that:
$$\mu(H) = \text{Tr}(\rho \cdot P_H)$$

where P_H is the projection onto H.

**Proof Sketch:**

*Step 1:* For one-dimensional subspaces (rays), μ defines a function f on the unit sphere:
$$f(v) = \mu(\mathbb{C}v)$$

*Step 2:* Additivity implies f is a "frame function": for any orthonormal basis {eᵢ}:
$$\sum_i f(e_i) = 1$$

*Step 3:* The key lemma (Gleason's hard work): Any continuous frame function on a sphere in dim ≥ 3 has the form:
$$f(v) = \langle v | \rho | v \rangle$$

for some positive operator ρ with Tr(ρ) = 1.

*Step 4:* Extend from rays to arbitrary subspaces using additivity.

**LRT Application:** Axiom 5 provides such a measure μ. Gleason's theorem shows μ must have the Born rule form.

---

### A.2 Kochen-Specker Theorem (1967)

**Theorem (Kochen-Specker).** For dim(ℋ) ≥ 3, there is no function v: P(ℋ) → {0,1} from projection operators to {0,1} satisfying:
1. v(P) + v(P⊥) = 1 for complementary projections
2. v(P₁ + P₂) = v(P₁) + v(P₂) for orthogonal P₁, P₂

**Proof Sketch:**

*Construction:* Find a set of projection operators (vectors) such that no consistent {0,1} assignment exists.

*For dim = 3:* The original KS construction uses 117 vectors. Simpler constructions (Peres: 33 vectors, Conway-Kochen: 31 vectors) exist.

*The obstruction:* Consider vectors {vᵢ} forming multiple orthogonal triples. Each triple needs exactly one "1" (by condition 1). The geometric arrangement makes this impossible.

**LRT Application:** Kochen-Specker proves that Boolean values cannot pre-exist in IIS. They are generated at the interface.

---

### A.3 Masanes-Müller Reconstruction (2011)

**Theorem (Masanes-Müller).** A state space satisfying:
1. Continuous reversible dynamics
2. Local tomography
3. Existence of entangled states

is a complex Hilbert space with standard quantum operations.

**Proof Structure:**

*Step 1 (State space geometry):* Conditions 1-2 imply state space is a symmetric cone. Reversibility gives group action; continuity makes it a Lie group.

*Step 2 (Jordan algebra):* Symmetric cones correspond to formally real Jordan algebras. The self-adjoint part of B(ℋ) is such an algebra.

*Step 3 (Complex structure):* Local tomography rules out real and quaternionic cases:
- Real: Joint states not determined by local measurements
- Quaternionic: Same problem (Baez's analysis)
- Complex: Unique solution

*Step 4 (Composite systems):* Condition 3 (entanglement) rules out classical probability. Combined with Steps 1-3, only quantum mechanics remains.

**LRT Application:** Axiom 3(a,b,c) provides conditions 1-2. IIS richness provides condition 3. Therefore IIS is complex Hilbert space.

---

### A.4 Wigner's Theorem (1931)

**Theorem (Wigner).** Any bijection S: ℋ → ℋ preserving transition probabilities:
$$|\langle S\psi | S\phi \rangle|^2 = |\langle \psi | \phi \rangle|^2$$

is implemented by a unitary or antiunitary operator.

**Proof Sketch:**

*Step 1:* S preserves orthogonality (|⟨ψ|φ⟩|² = 0 iff |⟨Sψ|Sφ⟩|² = 0).

*Step 2:* S preserves inner product magnitudes.

*Step 3:* For any phase convention, either:
- ⟨Sψ|Sφ⟩ = ⟨ψ|φ⟩ (unitary), or
- ⟨Sψ|Sφ⟩ = ⟨ψ|φ⟩* (antiunitary)

*Step 4:* Consistency requires one choice throughout.

**LRT Application:** Symmetries of IIS (Definition 3.10) are exactly (anti)unitary operators.

---

### A.5 Quantum Equilibrium (Dürr-Goldstein-Zanghì, 1992)

**Theorem (Equivariance).** If ρ(x,0) = |ψ(x,0)|² under Bohmian evolution, then ρ(x,t) = |ψ(x,t)|² for all t.

**Proof:**

*Step 1:* The continuity equation for probability:
$$\frac{\partial \rho}{\partial t} + \nabla \cdot (\rho v) = 0$$

where v is the Bohmian velocity field.

*Step 2:* Bohmian velocity:
$$v = \frac{\hbar}{m} \text{Im}\left(\frac{\nabla\psi}{\psi}\right) = \frac{j}{|\psi|^2}$$

where j is the quantum probability current.

*Step 3:* Substituting ρ = |ψ|²:
$$\frac{\partial |\psi|^2}{\partial t} + \nabla \cdot j = 0$$

This is exactly the quantum continuity equation (from Schrödinger equation).

*Step 4:* Since |ψ|² satisfies the same equation as ρ, if they agree initially, they agree always.

**LRT Application:** Born distribution is dynamically stable. Interface samples from an equilibrium that maintains itself.

---

### A.6 Decoherence Timescale (Zurek, Joos-Zeh)

**Derivation:** For a particle in superposition of positions separated by Δx, interacting with thermal environment at temperature T:

*Step 1:* Scattering rate from environmental particles:
$$\Gamma \sim n \sigma v$$

where n is particle density, σ is cross-section, v is thermal velocity.

*Step 2:* Each scattering event localizes to within thermal de Broglie wavelength:
$$\lambda_{dB} = \frac{\hbar}{\sqrt{2\pi m k_B T}}$$

*Step 3:* Decoherence occurs when enough scatterings distinguish the two positions:
$$\tau_D^{-1} \sim \Gamma \left(\frac{\Delta x}{\lambda_{dB}}\right)^2$$

*Step 4:* Simplifying:
$$\tau_D \sim \frac{\hbar^2}{m k_B T (\Delta x)^2}$$

**LRT Application:** This gives the timescale for approach to Boolean interface. For macroscopic objects, τ_D → 0.

---

### A.7 Hardy's Five Axioms (2001)

**Axioms:**

1. **Probabilities:** A state is characterized by N ≤ K independent probabilities, where K is the maximum.

2. **Simplicity:** K = N for pure states (no redundancy).

3. **Subspaces:** Systems have well-defined subsystems.

4. **Composite systems:** K_AB = K_A · K_B (no holism).

5. **Continuity:** Reversible transformations form continuous group.

**Theorem:** These axioms uniquely determine quantum theory with K = d² - 1 for dimension d.

**Derivation Key Steps:**
- Axiom 4 rules out theories with K_AB > K_A · K_B (like Popescu-Rohrlich boxes)
- Axiom 5 gives continuous group structure
- Axiom 2 forces pure states to be extremal
- Together: complex Hilbert space

---

### A.8 Dutch Book Theorem for Born Rule (Caves-Fuchs-Schack)

**Setup:** Agent bets on outcomes of quantum measurements. Bookie can offer any bet.

**Theorem:** If agent's betting quotients are not Born probabilities, bookie can construct a Dutch book (guaranteed win).

**Proof Sketch:**

*Step 1:* Consider SIC-POVM measurements (d² outcomes in dimension d).

*Step 2:* Coherence requires probability assignments form a valid quantum state.

*Step 3:* For any state, Born rule gives unique coherent probabilities.

*Step 4:* Any deviation allows Dutch book construction via convex analysis.

**LRT Application:** Born rule is rationally mandatory for betting on interface outcomes.

---

## Appendix B: Translation Tables

These tables provide systematic mappings between LRT terminology and the terminology of major interpretational frameworks.

### B.1 Core Ontological Terms

| LRT | Copenhagen | Bohmian | GRW | MWI | QBism | Relational |
|-----|------------|---------|-----|-----|-------|------------|
| IIS state \|ψ⟩ | Wave function | Guiding wave | Pre-collapse state | Universal wave function | Belief state | Relative state |
| Boolean actuality | Measurement outcome | Particle position | Post-collapse state | Branch content | Personal experience | Fact for observer |
| Interface | Measurement / Collapse | Position actualization | Collapse event | Branching | Experience | Interaction |
| Context | Observable / Basis | Position basis | Localization basis | Branch basis | Measurement choice | Interaction frame |
| 3FLL | (Not explicit) | (Assumed) | (Assumed) | (Assumed) | Coherence norms | (Not explicit) |

### B.2 Dynamical Terms

| LRT | Copenhagen | Bohmian | GRW | MWI | QBism | Relational |
|-----|------------|---------|-----|-----|-------|------------|
| IIS evolution | Schrödinger evolution | Wave evolution | Pre-collapse evolution | Universal evolution | Belief update | Relative evolution |
| Unitary dynamics | Process 2 | Guidance + Schrödinger | Modified Schrödinger | Only dynamics | (Not fundamental) | Unitary |
| Interface transition | Process 1 / Collapse | (Not fundamental) | Spontaneous localization | Branching | Experience | Information update |
| Decoherence | Effective collapse | Effective collapse | Pre-collapse | Branch decoherence | (Not fundamental) | Relative decoherence |

### B.3 Probability Terms

| LRT | Copenhagen | Bohmian | GRW | MWI | QBism | Relational |
|-----|------------|---------|-----|-----|-------|------------|
| Born probability | Measurement probability | Position distribution | Collapse probability | Branch weight | Credence | Relative probability |
| \|ψ\|² | Probability density | Particle distribution | Pre-collapse density | Branch measure | Betting quotient | Correlation measure |
| Quantum equilibrium | (Assumed) | Fundamental distribution | (Not explicit) | Branch typicality | Coherent beliefs | (Not explicit) |

### B.4 Structural Terms

| LRT | Copenhagen | Bohmian | GRW | MWI | QBism | Relational |
|-----|------------|---------|-----|-----|-------|------------|
| Hilbert space | State space | Configuration space | State space | Universal space | Belief space | Correlation space |
| Distinguishability | Orthogonality | Distinguishability | Distinguishability | Branch orthogonality | Distinguishability | Distinguishability |
| Superposition | Quantum state | Wave superposition | Pre-collapse state | Branch superposition | Uncertainty | Relational indefiniteness |
| Entanglement | Non-separability | Wave entanglement | Pre-collapse correlation | Branch entanglement | Correlated beliefs | Correlation |

### B.5 Interpretational Terms

| LRT | Copenhagen | Bohmian | GRW | MWI | QBism | Relational |
|-----|------------|---------|-----|-----|-------|------------|
| Wave function real? | Calculational tool | Yes (guides) | Yes (collapses) | Yes (fundamental) | No (belief) | Yes (relational) |
| Collapse real? | Yes (unexplained) | No (apparent) | Yes (dynamical) | No (apparent) | No (belief update) | No (relational) |
| Single outcome? | Yes | Yes | Yes | No (all branches) | Yes (for agent) | Yes (relative to observer) |
| Deterministic? | No | Yes (hidden) | No | Yes (globally) | N/A (beliefs) | No |
| Local? | No (collapse) | No (guidance) | No (collapse) | Yes | Yes (experiences) | Yes (interactions) |

### B.6 Mathematical Objects

| LRT Object | Standard QM | Bohmian | GRW | Information Theory |
|------------|-------------|---------|-----|-------------------|
| IIS | Hilbert space ℋ | Configuration space | Hilbert space | State space |
| Interface map Φ | Projection postulate | Position measurement | Collapse operator | Measurement channel |
| Context C | Observable basis | Position basis | Localization basis | POVM |
| Distinguishability D | Inner product \|⟨·\|·⟩\| | Overlap | Overlap | Fidelity |
| Complexity C | (Not standard) | (Not standard) | (Not standard) | Entropy / Kolmogorov |

### B.7 Layer Assignments

| Layer | Content | Frameworks | Key Equation |
|-------|---------|------------|--------------|
| 1 (IIS Dynamics) | Unitary evolution | MWI, Unitary QM | i∂ₜ\|ψ⟩ = H\|ψ⟩ |
| 2 (Flow) | Probability structure | Bohmian | dQ/dt = (ℏ/m)Im(∇ψ/ψ) |
| 3 (Interface) | Transition dynamics | Decoherence, GRW | Lindblad, τ_D |
| 4 (Actuality) | Boolean outcomes | Copenhagen, QBism | P(a) = \|⟨a\|ψ⟩\|² |

### B.8 Reconstruction Axiom Mapping

| LRT Axiom | Hardy | CDP | Masanes-Müller | Dakić-Brukner |
|-----------|-------|-----|----------------|---------------|
| 1 (Constitution) | (Implicit) | Perfect distinguishability | (Implicit) | (Implicit) |
| 2 (Pairwise) | (Implicit) | (Implicit) | (Implicit) | (Implicit) |
| 3a (Continuity) | Continuity | (Implicit) | Continuous dynamics | Continuity |
| 3b (Reversibility) | (In Continuity) | Causality | Reversible dynamics | Reversibility |
| 3c (Local tomography) | Composite systems | Local distinguishability | Local tomography | Locality |
| 4 (Boolean actuality) | Probabilities | (Implicit) | (Implicit) | Finiteness |
| 5 (Measure) | Probabilities | Pure conditioning | (From structure) | (From structure) |
| 6 (Parsimony) | Simplicity | Ideal compression | (Not explicit) | (Not explicit) |

### B.9 Problem-Solution Mapping

| QM Problem | LRT Dissolution | Mathematical Tool |
|------------|-----------------|-------------------|
| Measurement problem | Category transition (not dynamical) | Layer structure |
| Preferred basis | Einselection via decoherence | Lindblad dynamics |
| Born rule origin | Gleason's theorem at interface | Non-contextual measure |
| Wave function reality | Real in IIS, not in actuality | Two-domain ontology |
| Non-locality | Global constraint, not signaling | 3FLL as constraint field |
| Contextuality | Interface signature | Kochen-Specker |
| Classical limit | Decoherence timescale | τ_D → 0 for macro |

---

## References

Aharonov, Y., Bergmann, P. G., and Lebowitz, J. L. "Time symmetry in the quantum process of measurement." *Physical Review* 134(6B), 1964: B1410.

Aharonov, Y. and Vaidman, L. "The two-state vector formalism: An updated review." *Lecture Notes in Physics* 734, 2008: 399-447.

Baez, J. C. "Division algebras and quantum theory." *Foundations of Physics* 42, 2012: 819-855.

Bell, J. S. "On the Einstein Podolsky Rosen paradox." *Physics* 1(3), 1964: 195-200.

Bohm, D. "A suggested interpretation of the quantum theory in terms of 'hidden' variables." *Physical Review* 85(2), 1952: 166-193.

Brown, A. R. and Susskind, L. "Complexity geometry of a single qubit." *Physical Review D* 100(4), 2019: 046020.

Caves, C. M., Fuchs, C. A., and Schack, R. "Quantum probabilities as Bayesian probabilities." *Physical Review A* 65(2), 2002: 022305.

Chiribella, G., D'Ariano, G. M., and Perinotti, P. "Informational derivation of quantum theory." *Physical Review A* 84(1), 2011: 012311.

Conway, J. and Kochen, S. "The free will theorem." *Foundations of Physics* 36(10), 2006: 1441-1473.

Cramer, J. G. "The transactional interpretation of quantum mechanics." *Reviews of Modern Physics* 58(3), 1986: 647-687.

Dakić, B. and Brukner, Č. "Quantum theory and beyond: Is entanglement special?" In H. Halvorson (ed.), *Deep Beauty: Understanding the Quantum World through Mathematical Innovation*. Cambridge University Press, 2011.

de Finetti, B. "La prévision: Ses lois logiques, ses sources subjectives." *Annales de l'Institut Henri Poincaré* 7(1), 1937: 1-68.

Dürr, D., Goldstein, S., and Zanghì, N. "Quantum equilibrium and the origin of absolute uncertainty." *Journal of Statistical Physics* 67, 1992: 843-907.

Englert, B.-G., Scully, M. O., Süssmann, G., and Walther, H. "Surrealistic Bohm trajectories." *Zeitschrift für Naturforschung A* 47(12), 1992: 1175-1186.

Everett, H. "Relative state formulation of quantum mechanics." *Reviews of Modern Physics* 29(3), 1957: 454-462.

Fuchs, C. A. "QBism, the perimeter of quantum Bayesianism." arXiv:1003.5209, 2010.

Fuchs, C. A. and Schack, R. "Quantum-Bayesian coherence." *Reviews of Modern Physics* 85(4), 2013: 1693-1715.

Ghirardi, G. C., Rimini, A., and Weber, T. "Unified dynamics for microscopic and macroscopic systems." *Physical Review D* 34(2), 1986: 470-491.

Gleason, A. M. "Measures on the closed subspaces of a Hilbert space." *Journal of Mathematics and Mechanics* 6(6), 1957: 885-893.

Hardy, L. "Quantum theory from five reasonable axioms." arXiv:quant-ph/0101012, 2001.

Höhn, P. A. and Wever, C. S. P. "Quantum theory from rules on information acquisition." *Entropy* 19(3), 2017: 98.

Joos, E. and Zeh, H. D. "The emergence of classical properties through interaction with the environment." *Zeitschrift für Physik B* 59(2), 1985: 223-243.

Kochen, S. and Specker, E. P. "The problem of hidden variables in quantum mechanics." *Journal of Mathematics and Mechanics* 17(1), 1967: 59-87.

Landauer, R. "Irreversibility and heat generation in the computing process." *IBM Journal of Research and Development* 5(3), 1961: 183-191.

Longmire, J. D. "Logic Realism Theory: The Ontological Status of the Laws of Logic." Companion paper, 2025.

Longmire, J. D. "It from Bit, Bit from Fit: Why Quantum Mechanics Survives." Companion paper, 2025.

Margolus, N. and Levitin, L. B. "The maximum speed of dynamical evolution." *Physica D* 120(1-2), 1998: 188-195.

Masanes, L. and Müller, M. P. "A derivation of quantum theory from physical requirements." *New Journal of Physics* 13, 2011: 063001.

Nielsen, M. A. "A geometric approach to quantum circuit lower bounds." *Quantum Information and Computation* 6(3), 2006: 213-262.

Pearle, P. "Combining stochastic dynamical state-vector reduction with spontaneous localization." *Physical Review A* 39(5), 1989: 2277-2289.

Penrose, R. "On gravity's role in quantum state reduction." *General Relativity and Gravitation* 28(5), 1996: 581-600.

Peres, A. "Two simple proofs of the Kochen-Specker theorem." *Journal of Physics A* 24(4), 1991: L175.

Rovelli, C. "Relational quantum mechanics." *International Journal of Theoretical Physics* 35(8), 1996: 1637-1678.

Schlosshauer, M. *Decoherence and the Quantum-to-Classical Transition*. Springer, 2007.

Stueckelberg, E. C. G. "Quantum theory in real Hilbert space." *Helvetica Physica Acta* 33, 1960: 727-752.

Tumulka, R. "A relativistic version of the Ghirardi-Rimini-Weber model." *Journal of Statistical Physics* 125(4), 2006: 821-840.

Wheeler, J. A. "Information, physics, quantum: The search for links." In W. Zurek (ed.), *Complexity, Entropy, and the Physics of Information*. Addison-Wesley, 1990.

Wigner, E. P. "Gruppentheorie und ihre Anwendung auf die Quantenmechanik der Atomspektren." Friedrich Vieweg und Sohn, 1931. (English translation: *Group Theory and Its Application to the Quantum Mechanics of Atomic Spectra*. Academic Press, 1959.)

Zeh, H. D. "On the interpretation of measurement in quantum theory." *Foundations of Physics* 1(1), 1970: 69-76.

Zurek, W. H. "Pointer basis of quantum apparatus: Into what mixture does the wave packet collapse?" *Physical Review D* 24(6), 1981: 1516-1525.

Zurek, W. H. "Decoherence, einselection, and the quantum origins of the classical." *Reviews of Modern Physics* 75(3), 2003: 715-775.

Zurek, W. H. "Quantum Darwinism." *Nature Physics* 5(3), 2009: 181-188.

## Appendix C: Notation

### C.1 Logical Symbols

| Symbol | Meaning |
|--------|---------|
| 3FLL | Three Fundamental Logical Laws |
| I | Law of Identity: x = x |
| NC | Law of Non-Contradiction: ¬(P ∧ ¬P) |
| EM | Law of Excluded Middle: P ∨ ¬P |
| ∀ | Universal quantifier |
| ∃ | Existential quantifier |
| ∧ | Logical conjunction (and) |
| ∨ | Logical disjunction (or) |
| ¬ | Logical negation (not) |
| ⟺ | If and only if |

### C.2 Set-Theoretic Symbols

| Symbol | Meaning |
|--------|---------|
| ∈ | Element of |
| ⊂ | Subset |
| ∪ | Union |
| ∩ | Intersection |
| × | Cartesian product |
| {0,1} | Boolean set |
| {0,1}ⁿ | n-bit Boolean configurations |
| ℕ, ℤ, ℝ, ℂ, ℍ | Natural, integer, real, complex, quaternion numbers |

### C.3 LRT-Specific Symbols

| Symbol | Meaning | Definition Location |
|--------|---------|---------------------|
| 𝓘 or IIS | Infinite Information Space | Definition 2.3 |
| D(x,y) | Distinguishability relation | Definition 2.2 |
| Φ_C | Interface map for context C | Definition 4.2 |
| C | Context (orthonormal basis) | Definition 4.1 |
| 𝔏 | 3FLL Algebra | Definition 13.9 |
| C(ψ) | Complexity of state | Definition 3.5 |
| d(x,y) | Distinguishability metric | Definition 3.3 |

### C.4 Quantum Mechanical Symbols

| Symbol | Meaning |
|--------|---------|
| ℋ | Hilbert space |
| \|ψ⟩ | Ket (state vector) |
| ⟨ψ\| | Bra (dual vector) |
| ⟨φ\|ψ⟩ | Inner product |
| \|⟨φ\|ψ⟩\|² | Transition probability |
| ρ | Density operator |
| P_H | Projection onto subspace H |
| Tr | Trace |
| U | Unitary operator |
| H | Hamiltonian |
| ℏ | Reduced Planck constant |
| ⊗ | Tensor product |
| ⊕ | Direct sum |

### C.5 Operators and Functions

| Symbol | Meaning |
|--------|---------|
| ∂/∂t | Partial time derivative |
| ∇ | Gradient operator |
| δ | Variation (in variational principle) |
| δᵢⱼ | Kronecker delta |
| Tr_E | Partial trace over environment |
| Im | Imaginary part |
| Re | Real part |
| \|\|·\|\| | Norm |
| argmin | Argument of minimum |

### C.6 Physical Constants

| Symbol | Meaning | Value |
|--------|---------|-------|
| ℏ | Reduced Planck constant | 1.055 × 10⁻³⁴ J·s |
| k_B | Boltzmann constant | 1.381 × 10⁻²³ J/K |
| c | Speed of light | 2.998 × 10⁸ m/s |
| G | Gravitational constant | 6.674 × 10⁻¹¹ m³/(kg·s²) |
| λ | GRW collapse rate | ~10⁻¹⁶ s⁻¹ |
| a | GRW localization width | ~10⁻⁷ m |

### C.7 Abbreviations

| Abbreviation | Full Term |
|--------------|-----------|
| LRT | Logic Realism Theory |
| QM | Quantum Mechanics |
| QFT | Quantum Field Theory |
| GPT | Generalized Probabilistic Theory |
| MWI | Many-Worlds Interpretation |
| GRW | Ghirardi-Rimini-Weber (collapse theory) |
| CSL | Continuous Spontaneous Localization |
| RQM | Relational Quantum Mechanics |
| POVM | Positive Operator-Valued Measure |
| SIC-POVM | Symmetric Informationally Complete POVM |
| KS | Kochen-Specker |
| CDP | Chiribella-D'Ariano-Perinotti |

---

*Correspondence:* James (JD) Longmire | jdlongmire@outlook.com | ORCID: 0009-0009-1383-7698
