# Logic Realism Theory: Core Derivation
## From X to the Schrödinger Equation

**Version**: 1.1
**Date**: 2026-03-12
**Author**: James D. Longmire
**Status**: Publishable Draft (Revised)
**Epistemic Discipline**: Each step marked ESTABLISHED, ARGUED, CONJECTURED, or PARTIALLY ARGUED

---

## Abstract

This document presents the complete derivation chain from the primitive ontic state **X** to the Schrödinger equation. The derivation proceeds through 13 steps, each with explicit assumptions and epistemic status. The chain demonstrates that quantum mechanics emerges from logical necessity given the structure of actuality itself.

$$\mathbf{X} \to A_\Omega \to \text{Id} \to \text{Local Tomography} \to \mathbb{C}\mathcal{H} \to \text{PVM} \to \text{Born} \to \text{UNS} \to t \to G\text{-eq} \to H \to i\hbar\frac{d}{dt}\lvert\psi\rangle = H\lvert\psi\rangle$$

**Terminological Note**: "ESTABLISHED" means logically immediate from definitions or proven in peer-reviewed mathematics. It does not mean formally machine-checked.

---

## Dependency Graph

The following conjectural steps, if they fail, would break downstream derivations:

```
┌─────────────────────────────────────────────────────────────────┐
│                    CRITICAL DEPENDENCIES                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Step 3 (Local Tomography) ─── CONJECTURED ────┐               │
│         │                                       │               │
│         ▼                                       │               │
│  Step 4 (ℂℋ) ◄──────────────────────────────────┘               │
│         │                                                       │
│         ▼                                                       │
│  Step 5 (PVM) ─── CONJECTURED ─────────┐                       │
│         │                               │                       │
│         ▼                               │                       │
│  Step 6 (Gleason) ◄─────────────────────┘                       │
│         │                                                       │
│         ▼                                                       │
│  Step 7 (Born Rule) ◄───── Inherits conjectural status         │
│                                                                 │
│  Step 10 (Continuous t) ─── PARTIALLY ARGUED ──┐               │
│         │                                       │               │
│         ▼                                       │               │
│  Steps 11-13 (Dynamics) ◄──────────────────────┘               │
│                                                                 │
│  IF Step 3 fails: Steps 4-7 collapse                           │
│  IF Step 5 fails: Steps 6-7 require alternative                │
│  IF Step 10 fails: Steps 11-13 are conditional                 │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Part I: The Primitive Ontic State

### Definition 1: X

$$\mathbf{X} \equiv [L_3 : I_\infty : \mathbf{A}]$$

A co-constitutive unity of three irreducible aspects:

| Aspect | Symbol | Role |
|--------|--------|------|
| Three Laws of Logic | $L_3$ | Admissibility filter (Identity, Non-Contradiction, Excluded Middle) |
| Infinite Information Space | $I_\infty$ | All representable configurations |
| Continuous Binary Action | $\mathbf{A}$ | Instantiation primitive (actual vs. non-actual) |

**Epistemic Status**: ESTABLISHED (definitional)

**Key Properties**:
- X is fundamental (no ground for X; it is the terminus of grounding chains)
- The three aspects are co-constitutive: none can exist without the others
- $\mathbf{A}$ and LEM are categorically distinct (different sorts; no collapse)

---

## Part II: From X to Actuality

### Step 1: Transcendental Constitution

**Claim**: X ⊣ $A_\Omega$

**Reading**: X grounds the total actual structure $A_\Omega$.

**Argument**: $A_\Omega$ is the structural expression of X at Level 2. While X is the primitive ontic state (Level 1: *why* does actuality obtain?), $A_\Omega = L_3(I_\infty)$ is *what* actuality looks like: the set of all configurations that survive the admissibility filter.

**Framework**: Fine/Schaffer grounding theory. X transcendentally constitutes $A_\Omega$ because:
1. X is ontologically prior to $A_\Omega$
2. $A_\Omega$ obtains in virtue of X
3. The grounding relation is non-causal and non-temporal

**Note**: This step rests on accepting the Bridge Principle from the synthesis paper. The Bridge Principle is an explicit axiom; it is not derivable within standard grounding frameworks alone.

**Epistemic Status**: ESTABLISHED (within LRT framework, given Bridge Principle)

---

### Step 2: Determinate Identity

**Definition**: Every actual configuration $c \in A_\Omega$ satisfies:

$$c = c \quad \text{(from } L_3\text{)}$$

**Consequence**: Each actual configuration is determinately self-identical. There are no "fuzzy" identities in $A_\Omega$.

**Epistemic Status**: ESTABLISHED (direct consequence of $L_3$ as admissibility filter)

---

## Part III: The Structure of Quantum Theory

### Step 3: Local Tomography

**Claim**: Any theory describing actual configurations must satisfy local tomography.

**Definition**: A theory is *locally tomographic* if the state of a composite system is completely determined by the statistics of local measurements on its subsystems.

**Argument**: Given Determinate Identity, each subsystem possesses a determinate state. We argue:

1. **(H1) Metaphysical supervenience**: Each subsystem has determinate identity. The composite is nothing over and above its subsystems relationally organized.

2. **(H2) Operational accessibility**: All relations between subsystems are operationally accessible via local measurements.

**The Gap**: H1 (metaphysical anti-holism) does not automatically produce H2 (operational local tomography). The inference requires showing that any relation which is *not* locally accessible would violate Determinate Identity. This is the crux of the argument and remains unproven.

**Specifically**: A metaphysical supervenience claim ("no extra stuff beyond the parts") is distinct from an operational reconstruction theorem ("state determined by local statistics"). We argue they are equivalent in this context, but the equivalence is not established.

**Epistemic Status**: CONJECTURED

**Note**: This is a critical step. If the H1→H2 equivalence fails, Steps 4-7 may require alternative foundations.

---

### Step 4: Complex Hilbert Space from Local Tomography

**Theorem (Masanes-Müller 2011)**: Among generalized probabilistic theories, local tomography plus additional operational axioms uniquely selects complex Hilbert space quantum mechanics.

**Imported Result**: Given:
1. Local tomography (Step 3) — **CONJECTURED**
2. Continuous reversible dynamics
3. Existence of entangled states
4. No restriction on observables

Then the state space is $\mathbb{C}\mathcal{H}$ (complex Hilbert space over $\mathbb{C}$).

**Conditional Status**: This step is mathematically established but depends on the conjectured Step 3.

**Epistemic Status**: ESTABLISHED (peer-reviewed mathematics, conditional on Step 3)

**Citation**: Masanes, L. & Müller, M.P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13, 063001.

---

### Step 5: Projection-Valued Measures (Problem 2)

**Claim**: Measurements in $\mathbb{C}\mathcal{H}$ correspond to projection-valued measures (PVMs), not general POVMs.

**Argument Structure**:

We distinguish two maps:
- **Truth-value map**: $A(\text{event}) \in \{0,1\}$ — whether an event is actual
- **Probability map**: $p(\text{event}|\psi) \in [0,1]$ — the probability given state $\psi$

The argument proceeds:
1. The action primitive $\mathbf{A}$ is Boolean: configurations are either actual (1) or non-actual (0)
2. Measurement outcomes must correspond to actualization events
3. Actualization events require operators with eigenvalues in $\{0,1\}$ (the Boolean outputs of $\mathbf{A}$)
4. Operators with eigenvalues only in $\{0,1\}$ are projections
5. Families of projections satisfying normalization = PVMs

**The Conjectured Lemma**: Step 3 above (Boolean outputs ⇒ 0/1 spectrum ⇒ PVM-only events) is not yet proven. The eigenvalue-restriction argument requires formal demonstration.

**POVM Status**: POVMs arise via Naimark dilation as effective descriptions when part of a larger system is traced out. They are not fundamental event operators in LRT.

**Gap**: Absent the conjectured lemma, quantum logic with POVMs as primitive events remains a live alternative.

**Epistemic Status**: CONJECTURED

---

### Step 6: Gleason's Theorem

**Theorem (Gleason 1957)**: Any probability measure on the projection lattice of a Hilbert space of dimension ≥ 3 has the form:

$$p(P) = \text{Tr}(\rho P)$$

for some density operator $\rho$.

**Application**: Given PVMs (Step 5 — **CONJECTURED**), Gleason's theorem provides the unique probability assignment compatible with the lattice structure.

**Conditional Status**: Mathematically established, but application depends on the conjectured PVM structure.

**Epistemic Status**: ESTABLISHED (peer-reviewed mathematics)

**Citation**: Gleason, A.M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6, 885-893.

---

### Step 7: The Born Rule

**Derivation**: Combining Steps 5 and 6:

For a pure state $\lvert\psi\rangle$ and projector $P = \lvert\phi\rangle\langle\phi\rvert$:

$$p(\phi|\psi) = \text{Tr}(\lvert\psi\rangle\langle\psi\rvert \cdot \lvert\phi\rangle\langle\phi\rvert) = \lvert\langle\phi|\psi\rangle\rvert^2$$

**Key Point**: The Born rule is *derived*, not postulated. It follows from:
1. Determinate Identity (from X)
2. Local tomography (from Determinate Identity) — **CONJECTURED**
3. PVM structure (from determinacy requirement) — **CONJECTURED**
4. Gleason's theorem (from PVM lattice)

**Epistemic Status**: ARGUED (inherits conjectural status from Steps 3 and 5)

**Vehicle Invariance**: The Born rule is vehicle-invariant: any physical system that can represent $\lvert\psi\rangle$ yields the same probabilities. This is crucial for measurement theory.

---

## Part IV: Time and Dynamics

### Step 8: Unique Next State (UNS)

**Definition**: Given a configuration $c \in A_\Omega$, the unique next state is:

$$\text{UNS}(c) = c' \text{ such that } L_3(c \cup c') \text{ is admissible}$$

**Theorem (Steps A & B)**:
- **Step A**: For each $c$, there exists at most one $c'$ satisfying joint admissibility
- **Step B**: For each $c$, there exists at least one such $c'$

**Argument**:
- If two distinct $c'_1, c'_2$ both satisfied joint admissibility, then $c'_1 \neq c'_2$ would violate Identity for the "next state of $c$"
- Non-existence would mean $c$ has no admissible continuation, violating the structure of $A_\Omega$

**Scope Clarification**: UNS establishes uniqueness *within a given dynamical scheme*. It does not by itself determine *which* dynamical law (which Hamiltonian H) governs the system. That requires the additional symmetry constraints in Steps 11-12.

**Epistemic Status**: ESTABLISHED (Steps A & B proven in earlier work; scope clarified)

---

### Step 9: Temporal Ordering from Joint Inadmissibility

**Construction**: Define a relation $\prec$ on configurations:

$$c \prec c' \Leftrightarrow \text{UNS}(c) = c' \wedge L_3(c \cup c') \text{ admissible}$$

**Claim**: $\prec$ is a strict total order on maximal admissibility chains.

**Argument**:
1. Irreflexivity: $c \not\prec c$ (a configuration is not its own next state)
2. Asymmetry: if $c \prec c'$ then $c' \not\prec c$ (no backward causation in admissibility)
3. Transitivity: UNS chains compose
4. Totality on chains: every configuration in a maximal chain is comparable

**Result**: This gives us **ordinal time** — a strict total order.

**Epistemic Status**: ARGUED

---

### Step 10: Ordinal to Continuous Time

**Problem**: Step 9 gives ordinal structure; physics requires continuous $t \in \mathbb{R}$.

**Approach**: Debreu-Nachbin metric extension theorem.

**Theorem (Debreu 1954, Nachbin)**: If $(S, \prec)$ is a totally ordered set with appropriate topological properties (separability, order-density, continuity in the relevant topology), then there exists an order-preserving embedding $\phi: S \to \mathbb{R}$.

**Conditional Statement**: *If* the Debreu-Nachbin continuity conditions can be derived from the structure of $A_\Omega$, *then* there exists an embedding of ordinal time into $\mathbb{R}$.

**Gap**: The required topological properties (specifically, continuity of the order in the Fubini-Study topology of CP($\mathcal{H}$)) must be derived from the structure of $A_\Omega$. This derivation is not yet complete.

**Epistemic Status**: PARTIALLY ARGUED (conditional on deriving topological properties)

**Note**: Steps 11-13 below assume continuous time. They should be read as conditional on the success of this step.

---

### Step 11: G-Equivariance

**Claim**: Dynamics on $\mathbb{C}\mathcal{H}$ must be G-equivariant for appropriate symmetry group G.

**Conditional Note**: This step assumes continuous time (Step 10). Assuming the Debreu-Nachbin continuity conditions hold:

**Argument**:
1. $A_\Omega$ is invariant under relabeling of configurations (no privileged labels)
2. Label invariance → symmetry group G acting on $\mathcal{H}$
3. Dynamics must commute with G-action (otherwise labels would affect physics)

**For non-relativistic QM**: G includes spatial rotations SO(3), translations $\mathbb{R}^3$, and time translations $\mathbb{R}$.

**Epistemic Status**: ARGUED (conditional on Step 10)

---

### Step 12: Stone's Theorem and the Hamiltonian

**Theorem (Stone 1930)**: Every strongly continuous one-parameter unitary group $\{U(t)\}_{t \in \mathbb{R}}$ on a Hilbert space has the form:

$$U(t) = e^{-iHt/\hbar}$$

for some self-adjoint operator H (the generator).

**Application**: Time-translation symmetry (from G-equivariance, Step 11) gives a one-parameter unitary group. Stone's theorem yields the Hamiltonian H.

**Conditional Note**: This application assumes continuous time from Step 10.

**Epistemic Status**: ESTABLISHED (peer-reviewed mathematics; application conditional on Steps 10-11)

---

### Step 13: The Schrödinger Equation

**Derivation**: From Stone's theorem, for a state $\lvert\psi(t)\rangle = U(t)\lvert\psi(0)\rangle$:

$$\frac{d}{dt}\lvert\psi(t)\rangle = \frac{d}{dt}e^{-iHt/\hbar}\lvert\psi(0)\rangle = \frac{-iH}{\hbar}e^{-iHt/\hbar}\lvert\psi(0)\rangle = \frac{-iH}{\hbar}\lvert\psi(t)\rangle$$

Rearranging:

$$\boxed{i\hbar\frac{d}{dt}\lvert\psi\rangle = H\lvert\psi\rangle}$$

**Epistemic Status**: ESTABLISHED (follows from Stone's theorem; conditional on Steps 10-11)

---

## Part V: For Physicists — QM Primitives to LRT Origins

| Standard QM Primitive | LRT Origin | Derivation Step |
|-----------------------|------------|-----------------|
| Hilbert space $\mathcal{H}$ | Local tomography from Determinate Identity | Steps 3-4 |
| Complex coefficients $\mathbb{C}$ | Masanes-Müller reconstruction | Step 4 |
| Projective measurements (PVM) | Boolean action primitive $\mathbf{A}$ | Step 5 |
| Born rule $\lvert\langle\phi\|\psi\rangle\rvert^2$ | Gleason's theorem + PVM structure | Steps 6-7 |
| Time parameter $t$ | Joint inadmissibility ordering | Steps 9-10 |
| Unitary evolution $U(t)$ | G-equivariance + Stone's theorem | Steps 11-12 |
| Schrödinger equation | Differentiation of $U(t)$ | Step 13 |
| Hamiltonian $H$ | Generator of time-translation symmetry | Step 12 |

**What X provides**: The primitive $\mathbf{X} = [L_3 : I_\infty : \mathbf{A}]$ grounds all of the above. The three laws of logic $L_3$ enforce determinacy and admissibility. The information space $I_\infty$ provides the configuration domain. The action primitive $\mathbf{A}$ selects what is actual.

---

## Part VI: Summary and Open Problems

### Complete Derivation Chain

| Step | Content | Status | Dependencies |
|------|---------|--------|--------------|
| 0 | X ≡ [L₃ : I∞ : A] (definition) | ESTABLISHED | — |
| 1 | X ⊣ $A_\Omega$ (transcendental constitution) | ESTABLISHED | Bridge Principle (axiom) |
| 2 | Determinate Identity | ESTABLISHED | Step 1 |
| 3 | Local tomography | **CONJECTURED** | Step 2; H1→H2 equivalence unproven |
| 4 | Complex Hilbert space (Masanes-Müller) | ESTABLISHED | Step 3 (conjectured) |
| 5 | PVM structure (Problem 2) | **CONJECTURED** | Step 4; eigenvalue lemma unproven |
| 6 | Gleason's theorem | ESTABLISHED | Step 5 (conjectured) |
| 7 | Born rule derived | ARGUED | Steps 3, 5 (conjectured) |
| 8 | UNS (Steps A & B) | ESTABLISHED | Step 2 |
| 9 | Temporal ordering (ordinal) | ARGUED | Step 8 |
| 10 | Ordinal → continuous time | **PARTIALLY ARGUED** | Step 9; Debreu-Nachbin conditions unproven |
| 11 | G-equivariance | ARGUED | Step 10 (partially argued) |
| 12 | Stone's theorem → Hamiltonian | ESTABLISHED | Step 11 |
| 13 | Schrödinger equation | ESTABLISHED | Step 12 |

### Epistemic Summary

| Status | Count | Description |
|--------|-------|-------------|
| ESTABLISHED | 8 | Definitional, logically immediate, or imported from peer-reviewed mathematics |
| ARGUED | 3 | Defended with explicit reasoning; not yet formally proven |
| CONJECTURED | 2 | Central to the derivation; explicit gaps identified |
| PARTIALLY ARGUED | 1 | Conditional statement; requires additional derivation |

### Critical Conjectures

The derivation chain depends on three unproven claims:

1. **H1→H2 Equivalence (Step 3)**: Metaphysical supervenience entails operational local tomography. *If this fails*: Steps 4-7 require alternative foundations.

2. **Eigenvalue Lemma (Step 5)**: Boolean action outputs entail 0/1 operator spectrum (PVM-only). *If this fails*: POVM-based quantum logic remains viable.

3. **Debreu-Nachbin Conditions (Step 10)**: Ordinal time admits continuous embedding. *If this fails*: Steps 11-13 hold only conditionally.

### Open Problems (Priority Order)

1. **H1→H2 Equivalence** (Step 3): Prove or derive conditions under which metaphysical supervenience implies operational local tomography

2. **Eigenvalue Lemma** (Step 5): Formal proof that Boolean action → projection operators

3. **Debreu-Nachbin Extension** (Step 10): Derive required topological properties from $A_\Omega$ structure

4. **Lean 4 Formalization**: Machine-check Steps 3, 5, 7, 9, 11

5. **Fine-Structure Constant**: No current strategy for deriving α ≈ 1/137

### What This Derivation Achieves

1. **Born rule derived**, not postulated (conditional on Steps 3, 5)
2. **Complex Hilbert space derived** from local tomography (conditional on Step 3)
3. **Time derived** from joint inadmissibility structure
4. **One-world realism** with Everettian structure but without branch multiplication
5. **Wheeler's "it from bit"** grounded in the action primitive A (not taken as primitive)

### What This Derivation Does Not (Yet) Achieve

1. Specific Hamiltonians (requires additional structure)
2. Relativistic extension (Lorentz covariance not addressed)
3. Fine-structure constant derivation
4. Cosmological applications
5. Proof of the three critical conjectures

---

## References

Debreu, G. (1954). Representation of a preference ordering by a numerical function. *Decision Processes*, 3, 159-165.

Fine, K. (2012). Guide to ground. In F. Correia & B. Schnieder (Eds.), *Metaphysical Grounding* (pp. 37-80). Cambridge University Press.

Gleason, A.M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6, 885-893.

Masanes, L. & Müller, M.P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13, 063001.

Schaffer, J. (2009). On what grounds what. In D. Chalmers, D. Manley, & R. Wasserman (Eds.), *Metametaphysics* (pp. 347-383). Oxford University Press.

Stone, M.H. (1930). Linear transformations in Hilbert space. III. Operational methods and group theory. *Proceedings of the National Academy of Sciences*, 16, 172-175.

---

*Document generated: 2026-03-12 (v1.1 — revised per external review)*
*Logic Realism Theory Project*
*ORCID: 0009-0009-1383-7698*
