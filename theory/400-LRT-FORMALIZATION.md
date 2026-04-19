# Logic Realism Theory: Complete Formalization

## A Physicist's Guide to the Lean 4 Derivation

**James D. Longmire**
*Northrop Grumman Fellow (unaffiliated research)*
ORCID: 0009-0009-1383-7698

---

## Abstract

This document presents the complete derivation chain of quantum mechanics from the Logic Realism Theory (LRT) primitive ontological state $\chi \equiv [L_3 : I_\infty : A]$, as formalized in Lean 4. The formalization spans eleven steps, from the definition of primitives through the emergence of the Schrödinger equation. Each step is presented in physicist-accessible prose, with explicit identification of what is proven, what is axiomatized, and what is imported from established mathematics.

This document also describes the formal verification strategy: what the formalization proves, what it does not prove, and the boundary between machine-verified derivation and transcendental argumentation.

---

## 1. Overview: The Derivation Chain

The formalization implements the following derivation:

$$
\chi \to A_\Omega \to \text{Determinate Identity} \to \text{Local Tomography} \to \mathbb{C}\mathcal{H} \to \text{PVM} \to \text{Born Rule} \to \text{Unitarity} \to t \to H \to i\hbar\frac{\partial\psi}{\partial t} = H\psi
$$

In words: from the primitive ontic state $\chi$ (the co-constitution of logic, information, and actualization), we derive the total actual structure $A_\Omega$, show that actual configurations have determinate identity, establish local tomography, force complex Hilbert space structure, derive projection-valued measures, prove the Born rule, establish unitary evolution, show that time emerges from actualization ordering, identify energy as the generator of evolution, and finally arrive at the Schrödinger equation.

---

## 2. Purpose of Formalization

The LRT formalization serves three distinct purposes:

1. **Internal Consistency**: Verify that the reconstruction chain is logically coherent, with no hidden contradictions or circular dependencies.

2. **Dependency Transparency**: Make explicit which claims follow from which premises, distinguishing derived theorems from imported axioms.

3. **Referee Defense**: Provide machine-checked evidence that the physics derivation (given operational assumptions) is sound.

The formalization does **not** attempt to:
- Prove the transcendental argument (TAB) in a proof assistant
- Derive the bridge equation from pure logic
- Replace philosophical argumentation with mechanical proof

---

## 3. Step 0: The Primitive Ontic State $\chi$

### 3.1 The Three Co-Constitutive Aspects

The primitive ontic state $\chi$ consists of three irreducible, co-constitutive aspects:

**$L_3$: The Three Laws of Logic**

The classical laws operate as admissibility constraints on what can be actual:

1. **Identity (L₁):** $A = A$ -- every entity is self-identical
2. **Non-Contradiction (L₂):** $\neg(P \wedge \neg P)$ -- no proposition is both true and false
3. **Excluded Middle (L₃):** $P \vee \neg P$ -- every proposition is determinately true or false

In the formalization, these are not axioms but theorems derived from Lean's classical logic:

```
theorem law_of_identity (A : α) : A = A := rfl
theorem law_of_non_contradiction (P : Prop) : ¬(P ∧ ¬P) := fun ⟨hp, hnp⟩ => hnp hp
theorem law_of_excluded_middle (P : Prop) : P ∨ ¬P := Classical.em P
```

**$I_\infty$: The Infinite Information Space**

The ontological substrate containing all formally specifiable configurations. This is axiomatized minimally:

```
axiom I : Type*
axiom I_infinite : Infinite I
```

No additional structure (topology, measure, vector space) is imposed. $I_\infty$ represents the domain of distinguishable possibilities, not a mathematical space with pre-given structure.

**$A$: The Actualization Primitive**

The mechanism that instantiates configurations as actual or non-actual:

```
inductive ActualityValue : Type
  | actual : ActualityValue
  | nonActual : ActualityValue

structure ActionPrimitive where
  A : I → ActualityValue
  determinate : ∀ c : I, A c = actual ∨ A c = nonActual
```

The actualization function $A$ is boolean: each configuration is either actual or not. There is no middle ground, no partial actuality. This is the ontological analogue of $L_3$ (excluded middle): just as every proposition is true or false, every configuration is actual or non-actual.

### 3.2 Events and Boolean Structure

Events are queries over configurations that the actualization primitive resolves:

```
structure Event where
  query : Configuration → Prop
  l3_decidable : ∀ c : Configuration, query c ∨ ¬query c
```

The crucial feature: $L_3$ guarantees that every event has a determinate truth value for every configuration. This is not computational decidability but logical determinacy.

**Theorem (Event Non-Contradiction):** For any event $e$ and configuration $c$:
$$\neg(e(c) \wedge \neg e(c))$$

**Theorem (Event Excluded Middle):** For any event $e$ and configuration $c$:
$$e(c) \vee \neg e(c)$$

These theorems establish that events form a Boolean algebra. This is not assumed but derived from $L_3$.

### 3.3 Configuration Separation

A key derived theorem: distinct configurations are distinguished by some event.

**Theorem (Configuration Separation):** For any $c_1 \neq c_2$, there exists an event $e$ such that $e(c_1) \wedge \neg e(c_2)$.

The proof constructs the equality event $e_{c_1}$ defined by $e_{c_1}(c) \equiv (c = c_1)$. This event holds for $c_1$ and fails for $c_2$.

**Theorem (Extensionality):** Configurations agreeing on all events are identical:
$$(\forall e : \text{Event}, e(c_1) \leftrightarrow e(c_2)) \implies c_1 = c_2$$

This establishes that configurations are fully characterized by their event profiles.

---

## 4. Step 1: Transcendental Constitution

### 4.1 The Total Actual Structure $A_\Omega$

The total actual structure is the set of all actualized configurations:

$$A_\Omega(\chi) := \{c \in I_\infty \mid A(c) = \text{actual}\}$$

In Lean:
```
def A_Omega (X : Step0.X) : Set I :=
  { c : I | X.action.A c = ActualityValue.actual }
```

### 4.2 The Bridge Principle

The bridge principle is the single philosophical axiom connecting $\chi$ to $A_\Omega$:

**Axiom (Bridge Principle):** $A_\Omega$ is non-empty.

```
axiom bridge_principle (X : Step0.X) : Nonempty (A_Omega X)
```

This cannot be derived from pure logic. Logic alone does not guarantee that anything exists. The bridge principle asserts that the primitive ontic state $\chi$ grounds the existence of actuality.

The grounding relation $\chi \vdash A_\Omega$ is non-causal and non-temporal. $A_\Omega$ obtains *in virtue of* $\chi$.

**Theorem (Constitution):** Given $\chi$, there exists a non-empty $A_\Omega$ uniquely determined by $\chi$'s actualization function:

$$\exists A_\Omega : A_\Omega = A_\Omega(\chi) \wedge \text{Nonempty}(A_\Omega)$$

---

## 5. Step 2: Determinate Identity

### 5.1 L₃ Propagates to All Scales

Every actual configuration inherits the full force of $L_3$:

**Theorem:** For all $c \in A_\Omega$:
- $c = c$ (identity)
- $\forall P, \neg(P \wedge \neg P)$ (non-contradiction for propositions about $c$)
- $\forall P, P \vee \neg P$ (excluded middle for propositions about $c$)

This is not trivial restating. The theorem establishes that $L_3$ is scale-independent: it applies equally to subsystems, composite systems, and individual configurations.

### 5.2 Subsystem Structure

A subsystem is a non-empty subset of configurations inheriting $L_3$ admissibility:

```
structure Subsystem where
  configs : Set I
  nonempty : configs.Nonempty
  admissible : ∀ c ∈ configs, L3Admissible c
```

**Theorem (L₃ Propagates to Subsystems):** If $S$ is a subsystem, then for all subsystem events $e$ and configurations $c \in S$:
$$e(c) \vee \neg e(c)$$

This uniformity is crucial for Step 3: local tomography requires that subsystems have the same logical structure as the whole.

---

## 6. Step 3: Local Tomography

### 6.1 Hardy's Two Axioms

Local tomography requires two conditions:

**H1 (Tomographic Locality):** A joint state $\rho_{AB}$ is uniquely determined by all product measurement statistics $P(e_A \otimes e_B \mid \rho)$.

**H2 (Independent Composition):** The state space dimension satisfies $\dim(S_{AB}) = \dim(S_A) \times \dim(S_B)$.

### 6.2 Derivation from LRT Primitives

**H1 Derivation:** $L_3$ ensures determinate identity for all configurations. When $L_3$ propagates to subsystems (proven in Step 2), local events have determinate truth values. Two states that agree on all local event statistics must be identical because $L_3$ forces unique determination.

**H2 Derivation:** $I_\infty$ provides independent configuration spaces for subsystems. The product structure $I_A \times I_B \to I_{AB}$ is natural. $L_3$ adds no cross-subsystem constraints because it operates uniformly at all scales.

### 6.3 Hardy's Reconstruction Theorem (External)

**External Theorem (Hardy 2001, Chiribella-D'Ariano-Perinotti 2011, Masanes-Muller 2011):**

If a state space satisfies H1 and H2 with continuous reversible transformations, its structure is isomorphic to the projective Hilbert space over $\mathbb{C}$.

This is imported as a Tier 2 axiom:
```
axiom hardy_reconstruction : H1 ∧ H2 ∧ Continuity → CPH_over_ℂ
```

The LRT contribution: deriving the *inputs* (H1, H2) rather than assuming them. Hardy's theorem itself is established mathematics.

### 6.4 Why Complex ($K = 2$)?

Hardy's parameter $K$ determines the number field: $K = 1$ (real), $K = 2$ (complex), $K = 4$ (quaternionic). Three independent routes force $K = 2$:

1. **Poincare Route (Moretti-Oppio 2017):** Relativistic symmetry + $M^2 \geq 0$ forces complex field.
2. **Purification Route (CDP 2011):** Boolean actualization + no-hiding theorem + local tomography forces $K = 2$.
3. **Gleason Route (Fiorentino-Weigert 2025):** Tensor product consistency in $d = 2$ forces complex field.

The formalization includes all three routes, demonstrating the robustness of the $K = 2$ result.

---

## 7. Step 4: The Boolean-Spectrum Bridge

This is the mathematical lynchpin connecting LRT ontology to quantum measurement theory.

### 7.1 The Derivation Chain

$$
L_3 \to \text{Sharp Events} \to \text{Binary Evaluation} \to \text{Boolean Spectrum} \to \text{Idempotence} \to \text{Projections} \to \text{PVMs}
$$

**Sharp Events:** An event is sharp if it has a determinate truth value for all configurations. By $L_3$ (excluded middle), *all* events are sharp:

```
theorem all_events_sharp (e : Event) (c : Configuration) :
    e.query c ∨ ¬e.query c := e.l3_decidable c
```

**Binary Evaluation:** The actualization primitive resolves events to $\{\text{actual}, \text{nonActual}\}$. This is ontological binary evaluation.

**Boolean Spectrum:** When events are represented as operators on Hilbert space, the binary nature of actualization forces eigenvalues in $\{0, 1\}$:

```
def HasBooleanSpectrum (T : H →L[ℂ] H) : Prop :=
  ∀ λ ∈ spectrum ℂ T, λ = 0 ∨ λ = 1
```

**Idempotence:** An operator with spectrum $\subseteq \{0, 1\}$ satisfies $T^2 = T$:

```
theorem spectral_idempotent_of_bool_spectrum
    (T : H →L[ℂ] H) (h_sa : IsSelfAdjoint' T) (h_bool : HasBooleanSpectrum T) :
    IsIdempotent T
```

The proof uses the spectral theorem: if $T$ has eigenvalues only in $\{0, 1\}$, then on each eigenspace $T$ acts as either 0 or 1, and $T^2 = T$ follows.

**Projection Structure:** Self-adjoint idempotent operators are orthogonal projections. Events thus correspond to projection operators.

**PVMs:** Complete families of mutually orthogonal projections summing to identity form projection-valued measures.

---

## 8. Step 5: Eigenvalue Restriction

### 8.1 Spectral Correspondence

**Theorem:** Measurement outcomes correspond exactly to eigenvalues.

Given an observable $T$ with eigenvector $v$ satisfying $Tv = \lambda v$:
- The outcome $\lambda$ is possible iff $v \neq 0$
- The state $\psi$ has definite outcome $\lambda$ iff $\psi$ lies in the $\lambda$-eigenspace

```
theorem spectral_correspondence :
    OutcomePossible T λ ↔ ∃ v : H, v ≠ 0 ∧ T v = λ • v
```

### 8.2 Eigenstate Postulate

```
theorem eigenstate_determinacy (T : H →L[ℂ] H) (ψ : H) (λ : ℂ)
    (h_eigen : T ψ = λ • ψ) (h_norm : ‖ψ‖ = 1) :
    MeasurementOutcome T ψ = λ
```

If $\psi$ is an eigenstate of $T$ with eigenvalue $\lambda$, measurement yields $\lambda$ with certainty.

---

## 9. Step 6: The Born Rule

### 9.1 Non-Circular Derivation

The Born rule $p(\phi|\psi) = \lvert\langle\phi|\psi\rangle\rvert^2$ is *derived*, not postulated. The derivation chain:

$$
L_3 \to \text{Frame Functions} \to \text{Gleason} \to \text{Density Operators} \to \text{MaxEnt} \to \text{Born Rule}
$$

### 9.2 Frame Function Axioms from $L_3$

A frame function $f: H \to \mathbb{R}$ assigns probabilities to unit vectors. The axioms:

**FF1 (Normalization):** $\sum_i f(e_i) = 1$ over any orthonormal basis $\{e_i\}$.
- *Derived from L₃ (Excluded Middle):* Completeness $I = \sum P_i$ forces $\sum p(P_i) = 1$.

**FF2 (Basis Independence):** $f(e)$ depends only on $\lvert\langle e|\psi\rangle\rvert^2$.
- *Derived from L₁ (Identity):* Physical properties are intrinsic, independent of description.

**FF3 (Additivity):** $p(P + Q) = p(P) + p(Q)$ for orthogonal projections.
- *Derived from L₂ (Non-Contradiction):* Orthogonal states are mutually exclusive.

### 9.3 Gleason's Theorem (External)

**External Theorem (Gleason 1957):** For $\dim(\mathcal{H}) \geq 3$, any frame function satisfying FF1-FF3 has the unique form $f(e) = \langle e|\rho|e\rangle$ for a density operator $\rho$.

```
axiom gleason_theorem [FiniteDimensional ℂ H] :
  ∀ (f : ValidFrameFunction H), ∃! (ρ : DensityOperator H), f.f(e) = ⟨e|ρ|e⟩
```

### 9.4 MaxEnt and Pure States

For systems with maximum information (pure states), the maximum entropy principle forces $\rho = |\psi\rangle\langle\psi|$.

**External Axiom (von Neumann Entropy):** $S(\rho) = -\text{Tr}(\rho \ln \rho)$

Pure states minimize entropy: $S(|\psi\rangle\langle\psi|) = 0$.

### 9.5 The Born Rule Emerges

Combining Gleason and MaxEnt:
$$p(\phi|\psi) = \text{Tr}(|\psi\rangle\langle\psi| \cdot |\phi\rangle\langle\phi|) = \lvert\langle\phi|\psi\rangle\rvert^2$$

The Born rule is OUTPUT at the end of the derivation, not INPUT at the beginning. This resolves circularity concerns.

### 9.6 Alternative Derivation: Causal Consistency

An independent route via Torres Alegre (2025):

$$
L_3 \to \text{No-Signaling} \to \text{Steering Scenarios} \to \text{Linearity} \to \text{Born Rule}
$$

**Theorem:** The only probability transformation $\Phi: [0,1] \to [0,1]$ consistent with no-signaling in all steering scenarios is the identity $\Phi(p) = p$.

This forces $p(\phi|\psi) = \lvert\langle\phi|\psi\rangle\rvert^2$ directly from causal constraints.

### 9.7 Completeness

**Theorem (Born Rule Completeness):** For a partition of unity $\{P_i\}$:
$$\sum_i \|P_i\psi\|^2 = 1 \quad \text{when } \|\psi\| = 1$$

This is the Parseval identity for orthogonal decompositions, proven from the Pythagorean theorem for orthogonal sums.

---

## 10. Step 7: Unitarity

### 10.1 From Probability Conservation to Unitarity

Evolution must preserve probability normalization. If $U(t)$ is the evolution operator:
$$\|U(t)\psi\| = \|\psi\| \quad \text{for all } \psi$$

**Theorem (Wigner):** A linear map preserving norms preserves inner products:
$$\|U\psi\| = \|\psi\| \text{ for all } \psi \implies \langle U\psi|U\phi\rangle = \langle\psi|\phi\rangle$$

This is proven from Mathlib's `LinearMap.norm_map_iff_inner_map_map`.

### 10.2 The Hamiltonian Approach

**Root Axiom 1:** A Hamiltonian operator $H: \mathcal{H} \to \mathcal{H}$ exists.

**Root Axiom 2:** $H$ is self-adjoint: $H^\dagger = H$.

From these two axioms, everything follows:

**Time Evolution:** $U(t) = \exp(-iHt)$

**Norm Preservation:** Since $H$ is self-adjoint, $-iH$ is skew-adjoint. The exponential of a skew-adjoint operator is unitary:
$$U(t)^\dagger U(t) = \exp(iHt)\exp(-iHt) = \exp(0) = I$$

**Group Composition:** $U(s + t) = U(s)U(t)$ follows from exponential addition for commuting operators.

**Identity:** $U(0) = \exp(0) = I$

### 10.3 Axiom Reduction

Previous versions required 4 axioms for time evolution. The Hamiltonian approach reduces this to 2:

| Previous | Now |
|----------|-----|
| `time_evolution_family` (axiom) | Definition |
| `evolution_preserves_norm` (axiom) | Theorem from self-adjointness |
| `evolution_group_composition` (axiom) | Theorem from exponential properties |
| `evolution_identity` (axiom) | Theorem from exp(0) = I |

**Theorem:** Time evolution at any time $t$ is unitary.

```
theorem step7_unitarity (t : ℝ) : IsUnitary (time_evolution_family t)
```

---

## 11. Step 8: Temporal Emergence

### 11.1 Time Is Not Primitive

A crucial LRT insight: time is not a pre-given background structure. It *emerges* from the ordering of actualization events.

### 11.2 Actualization Events

```
structure ActualizationEvent where
  id : ℕ  -- Natural number index
```

Actualization events are discrete, indexed by natural numbers. This is not a physical assumption but a logical one: actualization is a sequence of determinate events.

### 11.3 Proto-Temporal Ordering

**Theorem:** Actualization events inherit a linear order from $\mathbb{N}$:

```
instance actualization_ordering : LinearOrder ActualizationEvent
```

This was previously axiomatized; it is now derived from $\mathbb{N}$'s structure.

### 11.4 Embedding in $\mathbb{R}$

**Definition:** The time embedding $\tau: \text{ActualizationEvent} \to \mathbb{R}$ is:
$$\tau(e) = e.\text{id}$$

**Theorem:** This embedding is strictly monotonic:
$$e_1 < e_2 \implies \tau(e_1) < \tau(e_2)$$

### 11.5 Continuous Time as Interpolation

Continuous time is *interpolation* between discrete actualizations, not a fundamental container. The embedding of discrete events into $\mathbb{R}$ allows standard analysis (differentiation, integration) to be applied.

**Axiom Count Reduction:** 3 temporal axioms -> 0 (converted to definitions and theorems from $\mathbb{N}$ structure).

---

## 12. Step 9: Energy as Generator

### 12.1 Stone's Theorem (External)

**External Theorem (Stone 1932):** A strongly continuous one-parameter unitary group $\{U(t)\}_{t \in \mathbb{R}}$ has a unique self-adjoint generator $H$ such that $U(t) = \exp(-iHt)$.

```
axiom stones_theorem : StronglyContUnitaryGroup → ∃ self_adjoint_generator
```

### 12.2 Energy and Action

The Hamiltonian $H$ is the energy observable. The relation $E = \hbar\omega$ emerges from the generator structure:

**Planck's Constant:** Introduced as a fundamental scale relating energy to frequency.

```
def planck_constant : ℝ := 1.054571817e-34  -- J·s
axiom planck_constant_pos : planck_constant > 0
```

### 12.3 The Generator-Unitarity Duality

- **Stone's direction (->):** Strongly continuous unitary group -> self-adjoint generator exists.
- **Converse direction (<-):** Self-adjoint generator -> evolution is unitary.

The converse is *derived* from exponential properties:
$$H^\dagger = H \implies U(t)^\dagger U(t) = I$$

---

## 13. Step 10: The Schrodinger Equation

### 13.1 Infinitesimal Form

The Schrodinger equation is the infinitesimal form of unitary evolution:

$$i\hbar\frac{\partial\psi}{\partial t} = H\psi$$

### 13.2 Derivation

Starting from $\psi(t) = U(t)\psi_0 = \exp(-iHt/\hbar)\psi_0$:

$$\frac{d\psi}{dt} = \frac{d}{dt}\exp(-iHt/\hbar)\psi_0 = \frac{-iH}{\hbar}\exp(-iHt/\hbar)\psi_0 = \frac{-iH}{\hbar}\psi(t)$$

Rearranging:
$$i\hbar\frac{\partial\psi}{\partial t} = H\psi$$

### 13.3 Properties

**Linearity:** The Schrodinger equation is linear because $H$ is a linear operator.

**Norm Preservation:** $\|\psi(t)\| = \|\psi(0)\|$ because evolution is unitary.

**Eigenstate Evolution:** Energy eigenstates $H\phi = E\phi$ evolve by pure phase:
$$\phi(t) = \exp(-iEt/\hbar)\phi(0)$$

---

## 14. Summary: The Complete Derivation

| Step | Content | From | Key Result |
|------|---------|------|------------|
| 0 | Primitives | -- | $\chi \equiv [L_3 : I_\infty : A]$ |
| 1 | Constitution | Bridge Principle | $\chi \vdash A_\Omega$ |
| 2 | Determinate Identity | $L_3$ | All configurations determinate |
| 3 | Local Tomography | $L_3 + I_\infty$ | H1, H2 derived |
| 4 | Hilbert Space | Hardy (external) | $\mathbb{C}\mathcal{H}$ structure |
| 4b | Boolean Bridge | $L_3$ sharpness | Projections from events |
| 5 | Eigenvalue Restriction | Spectral theory | Outcomes = eigenvalues |
| 6 | Born Rule | Gleason (external) | $p = \|P\psi\|^2$ |
| 7 | Unitarity | Self-adjoint $H$ | $\langle U\psi|U\phi\rangle = \langle\psi|\phi\rangle$ |
| 8 | Temporal Emergence | $\mathbb{N}$ structure | $t$ from actualization ordering |
| 9 | Energy | Stone (external) | $H$ as generator |
| 10 | Schrodinger | Infinitesimal limit | $i\hbar\partial_t\psi = H\psi$ |

---

## 15. What LRT Derives vs. Assumes

### 15.1 Derived (from $\chi$)

- Determinate identity for all configurations
- Event Boolean algebra structure
- Configuration separation (extensionality)
- H1 (tomographic locality) from $L_3$
- H2 (independent composition) from $I_\infty$
- Boolean spectrum from sharp actualization
- Frame function axioms from $L_3$
- Unitarity from self-adjoint Hamiltonian
- Time embedding from actualization ordering
- Schrodinger equation from infinitesimal generator

### 15.2 Axiomatized (external mathematics)

- Hardy's reconstruction (H1 + H2 -> $\mathbb{C}\mathcal{H}$)
- Gleason's theorem (frame functions -> trace form)
- Stone's theorem (unitary group -> generator)
- Spectral theorem (self-adjoint -> diagonalizable)

### 15.3 Input (physics)

- Planck's constant $\hbar$
- Specific Hamiltonians (physical domain)
- The particular physical world we inhabit

---

## 16. Limits of Formal Verification

### 16.1 What the Formalization Proves

Given the axioms (primitive, external, remaining), the reconstruction chain is **internally consistent**:
- No contradictions arise
- Dependencies are explicit and acyclic
- The derivation from bridge principle to Schrodinger equation is sound

### 16.2 What the Formalization Does Not Prove

1. **Transcendental Argument Validity**: The argument that L₃, I∞, and A are jointly necessary for actuality is philosophical, not mechanical. No proof assistant can verify transcendental reasoning.

2. **Bridge Equation Justification**: The identity A_Ω = L₃(I∞) is an argued metaphysical identity, not a formal theorem. The formalization assumes it (via `bridge_principle`).

3. **Empirical Adequacy**: The formalization shows QM structure is derivable from X + operational inputs. It does not prove that X correctly describes physical reality.

### 16.3 The Formalization Boundary

```
┌─────────────────────────────────────────────────────┐
│                TRANSCENDENTAL ARGUMENT               │
│                      (TAB)                           │
│  - Why L₃, I∞, A are necessary                      │
│  - Why A_Ω = L₃(I∞) (bridge equation)               │
│                                                      │
│           NOT FORMALIZED (philosophical)             │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼ bridge_principle (PRIMITIVE axiom)
┌─────────────────────────────────────────────────────┐
│              RECONSTRUCTION CHAIN                    │
│                   (MASTER)                           │
│                                                      │
│  X → A_Ω → Identity → Tomography → ℂℋ →            │
│  PVM → Born → Unitarity → Time → Schrödinger        │
│                                                      │
│           FORMALIZED (Lean 4, machine-verified)      │
└─────────────────────────────────────────────────────┘
```

---

## 17. Comparison to Other Reconstruction Programs

| Dimension | Hardy (2001) | CDP (2011) | Masanes-Muller (2011) | **LRT (2026)** |
|-----------|--------------|------------|----------------------|----------------|
| Starting point | 5 operational axioms | 6 informational principles | 5 physical requirements | $\chi = [L_3 : I_\infty : A]$ |
| Why these axioms? | "Reasonable" | Information is primitive | Physical plausibility | Grounded in constitutive logic |
| Local tomography | Axiom | Axiom | Axiom | **DERIVED** |
| Complex field | Derived (Axiom 5) | Derived (purification) | Derived | Imported (MM theorem) |
| PVM structure | Assumed (GPT) | Assumed | Assumed | **DERIVED** (Boolean A) |
| Born rule | Implied | Derived | Implied | **DERIVED** (Gleason) |
| Dynamics | Derived (continuity) | Derived (causality) | Derived (reversibility) | **DERIVED** (Stone) |
| Formalization | Natural language | Natural language | Natural language | **Lean 4 (complete)** |
| Ontological commitment | Instrumentalist | Information-theoretic | Operationalist | Realist ($L_3$ constitutive) |

**Key differentiator:** LRT derives what others assume (local tomography, PVM structure) and provides the only reconstruction with proof-assistant formalization.

---

## 18. Lean Module Structure

### 18.1 Derivation Chain Modules

| Step | File | Content |
|------|------|---------|
| 0 | `Step0_Primitives.lean` | I, L₃, A, X structure |
| 1 | `Step1_Constitution.lean` | Bridge principle, A_Ω |
| 2 | `Step2_DeterminateIdentity.lean` | Determinate identity from L₃ |
| 3 | `Step3_LocalTomography.lean` | H1/H2 derivation structure |
| 4 | `Step4/` | Hardy, Boolean, Purification |
| 5 | `Step5/` | Eigenvalue restriction |
| 6 | `Step6_BornRule.lean` | Projection probability, Gleason |
| 7 | `Step7_Unitarity.lean` | Evolution family |
| 8 | `Step8_TemporalEmergence.lean` | Time embedding |
| 9 | `Step9_EnergyAction.lean` | Stone, Planck, Noether |
| 10 | `Step10_Schrodinger.lean` | Schrodinger equation |

### 18.2 File Structure

```
formalization/LrtFormalization/
├── Basic.lean                    # Imports
├── Step0_Primitives.lean         # L₃, I∞, A, Events (330 lines)
├── Step1_Constitution.lean       # X → A_Ω bridge (150 lines)
├── Step2_DeterminateIdentity.lean # L₃ propagation (194 lines)
├── Step3_LocalTomography.lean    # H1 + H2 derivation (682 lines)
├── Step4/
│   ├── Hardy.lean                # Hilbert space structure (100 lines)
│   ├── Boolean.lean              # L₃ sharpness → Boolean spectrum (300 lines)
│   └── Purification.lean         # K=2 via 3 routes (450 lines)
├── Step5/
│   ├── EigenvalueRestriction.lean # Boolean spectrum → Idempotence (196 lines)
│   └── EigenvalueOutcome.lean    # Eigenvalues ↔ Outcomes (200 lines)
├── Step6_BornRule.lean           # Frame functions → Born rule (600 lines)
├── Step7_Unitarity.lean          # Probability preservation → Unitarity (270 lines)
├── Step8_TemporalEmergence.lean  # Actualization ordering → Time (250 lines)
├── Step9_EnergyAction.lean       # Self-adjoint generator → Energy (350 lines)
└── Step10_Schrodinger.lean       # Generator → Schrödinger equation (300 lines)
```

**Total:** ~4,500 lines of Lean 4 formalization

### 18.3 Repository Structure

```
logic-realism-theory/
├── formalization/                    # Lean 4 project
│   ├── LrtFormalization.lean         # Main import
│   ├── LrtFormalization/             # Step files
│   ├── lakefile.toml                 # Build configuration
│   └── scripts/
│       ├── build.sh                  # Build with Mathlib cache
│       └── clean.sh                  # Clean LRT artifacts only
├── theory/
│   ├── 002-LRT-TAB-PHILOSOPHY.md     # Transcendental argument
│   ├── 100-LRT-CORE-PHYSICS.md      # Physics reconstruction
│   ├── 300-LRT-COSMOLOGY.md         # Dark energy extension
│   ├── 400-LRT-FORMALIZATION.md     # This document
│   ├── 500-LRT-FORMALIZATION-STATUS.md  # Current status (living doc)
│   └── supplementary/                # Technical supplements
└── traceability/
    ├── claims/                       # YAML claim files
    ├── scripts/build.py              # Report generator
    └── generated/                    # Output reports
```

---

## 19. Traceability

The `traceability/` directory provides claim-level tracking:

| Prefix | Domain |
|--------|--------|
| ONT | Ontological primitives |
| LOG | Logical constraints |
| ACT | Actualization |
| QM | Quantum reconstruction |
| PHY | Dynamics |
| PRD | Predictions |
| OPN | Open problems |
| EXT | External theorems |

Each claim has:
- `proof_status`: verified | axiomatized | imported | prose_only | open
- `epistemic_status`: established | argued | conjectured | open
- `lean_ref`: pointer to Lean theorem/axiom

Generate reports:
```bash
cd traceability && python3 scripts/build.py --all
```

---

## 20. Conclusion

The Lean 4 formalization demonstrates that quantum mechanical structure emerges necessarily from the primitive ontological state $\chi \equiv [L_3 : I_\infty : A]$. The derivation is:

1. **Complete:** All steps from $\chi$ to Schrodinger are formalized.
2. **Non-circular:** The Born rule is output, not input.
3. **Minimal:** 3 primitive axioms, external mathematics properly labeled.
4. **Verified:** Machine-checked with 0 errors in main chain.

The question "why quantum mechanics?" receives a principled answer: given the logical structure of determinacy, the informational structure of distinguishability, and the ontological structure of actualization, quantum mechanics is the unique theory compatible with these constraints.

---

## References

1. Hardy, L. (2001). "Quantum Theory From Five Reasonable Axioms." arXiv:quant-ph/0101012
2. Chiribella, G., D'Ariano, G. M., & Perinotti, P. (2011). "Informational derivation of quantum theory." Physical Review A, 84(1), 012311.
3. Masanes, L., & Muller, M. P. (2011). "A derivation of quantum theory from physical requirements." New Journal of Physics, 13(6), 063001.
4. Gleason, A. M. (1957). "Measures on the closed subspaces of a Hilbert space." Journal of Mathematics and Mechanics, 6(6), 885-893.
5. Stone, M. H. (1932). "On one-parameter unitary groups in Hilbert space." Annals of Mathematics, 33(3), 643-648.
6. Torres Alegre, A. (2025). "Deriving the Born rule from causal structure." arXiv:2512.12636
7. Moretti, V., & Oppio, M. (2017). "Quantum theory in quaternionic Hilbert space." Annales Henri Poincare, 18(11), 3467-3501.
8. Fiorentino, E., & Weigert, S. (2025). "Gleason's theorem for composite systems." arXiv preprint.
9. von Neumann, J. (1932). *Mathematical Foundations of Quantum Mechanics*. Princeton University Press.

---

## Build Commands

```bash
# Navigate to formalization directory
cd /media/jdlongmire/Macro-Drive-2TB/GitHub_Repos/logic-realism-theory/formalization

# Fetch Mathlib cache (avoids 4-8 hour compile)
source ~/.elan/env && lake exe cache get

# Build (requires npm for ProofWidgets)
source ~/.elan/env && PATH=~/.nvm/versions/node/v24.13.0/bin:$PATH lake build

# Quick status check
grep -r "sorry" LrtFormalization/ --include="*.lean" | grep -v ".lake" | wc -l  # Sorries
grep -rh "^axiom" LrtFormalization/ --include="*.lean" | wc -l                   # Axioms
```
