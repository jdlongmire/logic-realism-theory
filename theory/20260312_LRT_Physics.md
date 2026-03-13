# Deriving Quantum Mechanics from the Structure of Actuality

## A Physicist's Guide to Logic Realism Theory

**Author:** James D. Longmire
**Date:** 2026-03-12
**ORCID:** 0009-0009-1383-7698

---

## 1. Introduction: What Problem Are We Solving?

Quantum mechanics gives precise constraints on possible configurations of physical systems. The Born rule tells us the probability of finding a system in state $\lvert\phi\rangle$ given that it was prepared in state $\lvert\psi\rangle$. The Schrödinger equation tells us how states evolve. These tools work extraordinarily well.

But they leave something unexplained. QM tells us what might happen and with what probability. It says nothing about why anything is *actual* rather than merely possible. The formalism describes a filter on configurations, but not why there is a running filter at all.

This is the **actualization gap**. It is not a gap that more dynamics can fill. The Schrödinger equation describes how possibilities evolve; it does not explain why one possibility becomes fact and others do not. Decoherence reshuffles the problem without solving it. Many-worlds denies the problem exists by declaring all possibilities actual, at the cost of observer duplication.

Logic Realism Theory (LRT) takes a different approach. It proposes a primitive ontic condition **X** such that:

1. Standard complex Hilbert-space QM with Born rule and Schrödinger dynamics can be **derived** from the structure of actuality.
2. X explains why all measurement records are Boolean (yes/no, detected/not-detected) and why Wheeler's "it from bit" has an ontological ground.
3. The theory is explicit about assumptions, makes no hidden appeal to probability as primitive, and is open to refutation.

**Goal of this paper:** Show, in outline with references to detailed derivations, how you get from X to the standard Hilbert-space formalism and dynamics.

---

## 2. The Primitive X in Physicist's Terms

### 2.1 Three Components

Define:

**$L_3$** (Laws of Logic): Constraints on records. Any recorded outcome is determinate (has definite identity), non-contradictory (not both A and not-A), and satisfies excluded middle (either A or not-A).

**$I_\infty$** (Information Space): The space of all representable configurations. Every mathematically consistent description of a physical arrangement lives here. No ontic commitment at this level.

**$\mathbf{A}$** (Continuous Binary Action): The yes/no operation that makes some admissible configurations actual as records. $\mathbf{A}$ takes configurations and returns 0 (not actual) or 1 (actual).

### 2.2 The Package

$$\mathbf{X} \equiv [L_3 : I_\infty : \mathbf{A}]$$

These three are co-constitutive. None exists without the others. The laws of logic constrain which configurations can be actualized; the configuration space provides the domain; the action primitive selects what is actual.

### 2.3 Two-Level Architecture

**Level 1:** X as ontic ground. This is why there is any actualized structure at all. X is fundamental; it has no further ground.

**Level 2:** Domain equation $A_\Omega = L_3(I_\infty)$. This is the structure of admissible actual records. $A_\Omega$ is the set of all configurations that survive the $L_3$ filter when $\mathbf{A}$ operates.

### 2.4 Minimal Grounding

The phrase "in virtue of" means: X is the condition under which any record exists at all. We are not appealing to causal or temporal relations. X does not *cause* actuality; X *is* the primitive whose operation constitutes actuality.

---

## 3. From X to Standard QM Kinematics

This is the core payoff. We derive Hilbert space, the Born rule, and measurement structure.

### Summary Table

| QM Primitive | LRT Origin | Derivation Step |
|--------------|------------|-----------------|
| Hilbert space $\mathcal{H}$ | Local tomography from Determinate Identity | 3-4 |
| Complex coefficients $\mathbb{C}$ | Masanes-Müller reconstruction | 4 |
| Projective measurements (PVM) | Boolean action primitive $\mathbf{A}$ | 5 |
| Born rule $\lvert\langle\phi\lvert\psi\rangle\rvert^2$ | Gleason's theorem + PVM structure | 6-7 |
| Time parameter $t$ | Joint inadmissibility ordering | 9-10 |
| Unitary evolution $U(t)$ | G-equivariance + Stone's theorem | 11-12 |
| Schrödinger equation | Differentiation of $U(t)$ | 13 |
| Hamiltonian $H$ | Generator of time-translation symmetry | 12 |

### 3.1 Determinate Records and Local Tomography

From $L_3$: any actual configuration has determinately self-identical records. A detector either clicked or it didn't. A spin measurement returned up or down. There are no fuzzy identities at the record level.

**Consequence:** Each subsystem of a composite system has determinate identity. A theory describing such composites, where the whole supervenes on the parts plus their relations, must satisfy **local tomography**: the composite state is completely determined by statistics of local measurements on subsystems.

The inference from metaphysical supervenience (no floating holistic facts) to operational local tomography requires an explicit bridge: the **Operational Determinacy** principle. If a relation between subsystems is physically real (contributes to the composite's identity), it must be operationally distinguishable. Otherwise it is not subject to $L_3$. Under LRT's operational grounding, all identity-determining relations are locally accessible.

**Cite:** Full argument in *H1-H2 Tomography Bridge* (2026-03-12).

**Result (Masanes-Müller 2011):** Among generalized probabilistic theories, local tomography plus standard operational axioms (continuous reversible dynamics, existence of entangled states, no restriction on observables) uniquely selects **complex Hilbert space** as the state space.

### 3.2 Why Events Are PVMs (Not Primitive POVMs)

The central idea:

1. The action primitive $\mathbf{A}$ is Boolean. Every actualization event returns 0 or 1, not an intermediate value.

2. Event operators, whose eigenvalues encode actualization status, must therefore have spectrum in $\{0,1\}$.

3. By the spectral theorem, bounded self-adjoint operators with spectrum $\subseteq \{0,1\}$ are exactly projections ($P^2 = P$).

4. Families of projections satisfying normalization are **projection-valued measures (PVMs)**.

**What about POVMs?** Positive operator-valued measures appear as effective descriptions when you trace over apparatus or environment. By Naimark's dilation theorem, every POVM on $\mathcal{H}$ arises as the reduction of a PVM on a larger space $\mathcal{H} \otimes \mathcal{K}$. Ontologically, events are PVMs; POVMs are epistemic reductions.

**Cite:** Full argument in *Eigenvalue Restriction Proof* (2026-03-12).

### 3.3 Born Rule from Gleason

Once you have:
- Hilbert space (from local tomography)
- PVMs (from Boolean actualization)

Gleason's theorem gives the unique probability measure on the projection lattice of dimension $\geq 3$:

$$p(P) = \text{Tr}(\rho P)$$

For pure state $\lvert\psi\rangle$ and projector $P = \lvert\phi\rangle\langle\phi\rvert$:

$$p(\phi\lvert\psi) = \lvert\langle\phi\lvert\psi\rangle\rvert^2$$

The Born rule is **derived**, not postulated. The only non-trivial inputs are:
- Local tomography (from Determinate Identity)
- Boolean event structure (from $\mathbf{A}$)
- Standard regularity conditions of Gleason

---

## 4. From X to Time and Schrödinger Dynamics

### 4.1 Ordinal Time from Joint Inadmissibility

The **Unique Next State (UNS)** theorem establishes: given a configuration $c \in A_\Omega$, there exists exactly one configuration $c'$ such that the joint configuration $c \cup c'$ is $L_3$-admissible. If two distinct next states existed, Identity would be violated for "the next state of $c$."

UNS gives a strict total order on each actualization trajectory:

$$c \prec c' \Leftrightarrow \text{UNS}(c) = c' \wedge L_3(c \cup c') \text{ admissible}$$

This is **ordinal time**: a strict order, no metric yet.

### 4.2 Continuous Time via Debreu-Nachbin

The Debreu-Nachbin theorem: a totally ordered set with appropriate topological properties (separability, order-density, connectedness) admits an order-preserving embedding into $\mathbb{R}$.

These conditions are satisfied by $\Gamma_{A_\Omega}$ (the actualization trajectory):

| Condition | Source |
|-----------|--------|
| Separability | Separability of Hilbert space |
| Order-density | Continuity of UNS dynamics in Fubini-Study topology |
| Connectedness | Connectedness of evolution paths in CP($\mathcal{H}$) |

**Result:** The ordinal time structure embeds into $\mathbb{R}$ as a continuous time parameter $t$.

The natural choice of temporal metric is Fubini-Study arc length along the trajectory:

$$t(q) - t(p) = \int_p^q d_{FS}(\gamma(s), \gamma(s + ds))$$

This makes $t$ physically meaningful: it measures accumulated distinguishability along the evolution path.

**Cite:** Full argument in *Debreu-Nachbin Derivation* (2026-03-12).

### 4.3 Symmetry, Stone, and Schrödinger

**G-equivariance:** $A_\Omega$ is invariant under relabeling of configurations. No label is physically privileged. This entails symmetry group G acting on $\mathcal{H}$, and dynamics must commute with G-action.

For non-relativistic QM, G includes spatial rotations SO(3), translations $\mathbb{R}^3$, and time translations $\mathbb{R}$.

**Stone's theorem:** Every strongly continuous one-parameter unitary group $\{U(t)\}_{t \in \mathbb{R}}$ has the form:

$$U(t) = e^{-iHt/\hbar}$$

for some self-adjoint operator $H$ (the generator). Time-translation symmetry from G-equivariance gives precisely such a group. Stone's theorem yields the Hamiltonian.

**Schrödinger equation:** Differentiating $\lvert\psi(t)\rangle = U(t)\lvert\psi(0)\rangle$:

$$\frac{d}{dt}\lvert\psi(t)\rangle = \frac{-iH}{\hbar}\lvert\psi(t)\rangle$$

Rearranging:

$$\boxed{i\hbar\frac{d}{dt}\lvert\psi\rangle = H\lvert\psi\rangle}$$

**Frame:** Standard reconstruction proofs, but with premises that come from X and $\mathbf{A}$, not from arbitrary operational axioms.

---

## 5. What X Buys You Beyond Reconstruction

### 5.1 Explanation of Classical Logic at the Record Level

Why are measurement outcomes always Boolean even though pre-measurement states are not? The question dissolves under LRT. Records are Boolean because $\mathbf{A}$ is Boolean. The action primitive does not "collapse" a superposition; it determines what is actual, and actuality is binary by definition.

Quantum logic (Birkhoff-von Neumann) applies to propositions about states in $I_\infty$. Classical logic ($L_3$) applies to records in $A_\Omega$. No conflict.

### 5.2 Grounding Wheeler's "It from Bit"

Wheeler proposed that information is fundamental: "every it, every particle, every field of force, even the spacetime continuum itself, derives its function, its meaning, its very existence entirely from binary yes-no questions."

LRT provides the ground: the bit arises as the signature of $\mathbf{A}$'s binary action, not as primitive informational stuff. The "yes/no" is the operation of actualization, not an unexplained given.

### 5.3 One-World Realism

LRT keeps Everettian-like structure in the pre-actualization domain (states in $I_\infty$ can be superposed, entangled, etc.) but avoids branch multiplication at the level of actual records. There is one actual configuration at each moment. No duplication of observers.

### 5.4 What This Doesn't Do (Yet)

- **No derivation of particular Hamiltonians.** LRT shows that dynamics takes Schrödinger form; it does not determine the specific $H$ for electrons in a potential. That requires further physical input (symmetries, boundary conditions, empirical data).

- **No relativistic extension yet.** Lorentz covariance is not addressed. The framework is non-relativistic QM.

- **No prediction of constants like $\alpha$.** The fine-structure constant is not derived. There is no current strategy for this.

---

## 6. Status, Falsifiability, and Open Problems

### 6.1 Falsifiability

LRT is falsifiable. The falsifiability criterion: any stable, reproducible $L_3$-violating record would refute the core of the theory.

What would count:
- A record that is both A and not-A (contradiction at vehicle level)
- A record that is neither A nor not-A (violation of Excluded Middle at vehicle level)
- Stable experimental violation of classical logic in completed measurement outcomes

What would not count:
- Superposition before measurement (this is in $I_\infty$, not $A_\Omega$)
- Weak measurement statistics (ensemble averages, not single-shot actualization)
- Interpretive disagreements about "what the wavefunction means"

### 6.2 Epistemic Status

| Status | Count | Description |
|--------|-------|-------------|
| ESTABLISHED | 8 | Definitional, logically immediate, or imported from peer-reviewed mathematics |
| ARGUED | 6 | Defended with explicit reasoning; not yet formally proven |

**No steps remain CONJECTURED or PARTIALLY ARGUED.** All three critical gaps (H1-H2 bridge, eigenvalue restriction, Debreu-Nachbin conditions) have been addressed in technical documents dated 2026-03-12.

### 6.3 Current Priorities

1. **Lean 4 formalization** of key lemmas (especially Steps 3, 5, 10)
2. **Relativistic extension** (Lorentz covariance, QFT compatibility)
3. **Discriminating empirical or structural consequences** (if any)

---

## 7. If You Only Remember Three Things

1. **X = [logical constraints on records + information space + binary action]** is proposed as the primitive ontic ground. It is not further explained; it is the terminus of explanation.

2. **From X, with a small set of clearly stated bridge principles, you derive:** complex Hilbert space, PVM-only measurement, the Born rule, and Schrödinger dynamics. Nothing is smuggled in through implicit assumptions about probability or measurement.

3. **The theory is fully explicit about assumptions, conceptually closes the actualization gap, and is open to being refuted** by any stable violation of classical logic at the level of recorded outcomes.

---

## References

Debreu, G. (1954). Representation of a preference ordering by a numerical function. *Decision Processes*, 3, 159-165.

Gleason, A.M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6, 885-893.

Masanes, L. & Müller, M.P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13, 063001.

Naimark, M. A. (1943). Positive definite operator functions on a commutative group. *Izvestiya Rossiiskoi Akademii Nauk*, 7(5), 237-244.

Stone, M.H. (1930). Linear transformations in Hilbert space. III. *Proceedings of the National Academy of Sciences*, 16, 172-175.

Wheeler, J.A. (1990). Information, physics, quantum: The search for links. In *Complexity, Entropy, and the Physics of Information* (pp. 3-28). Addison-Wesley.

---

## Technical Documents

- *Core Derivation v1.2* (2026-03-12): Full 13-step chain with epistemic status
- *Eigenvalue Restriction Proof* (2026-03-12): Boolean action → PVM structure
- *H1-H2 Tomography Bridge* (2026-03-12): Supervenience → local tomography
- *Debreu-Nachbin Derivation* (2026-03-12): Ordinal → continuous time

---

*Logic Realism Theory Project*
*ORCID: 0009-0009-1383-7698*
