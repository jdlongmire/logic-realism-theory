# Deriving the Born Rule from Logical Constraint: A Logic Realism Theory Approach

**James D. Longmire**
ORCID: 0009-0009-1383-7698
jdlongmire@outlook.com

---

## Abstract

We present a derivation of the Born rule from the ontological constraints imposed by the Three Fundamental Laws of Logic (L₃) within the Logic Realism Theory (LRT) framework. The central argument proceeds through five stages: (1) L₃ constraints at the vehicle level require that physical systems possess determinate dispositions toward measurement outcomes; (2) these dispositions must satisfy vehicle-weight invariance—probability assignments cannot depend on the descriptive decomposition chosen; (3) vehicle-weight invariance, combined with finite additivity, yields the premises of Gleason-type theorems; (4) Gleason's theorem then forces the trace form μ(P) = Tr(ρP) for all projectors; (5) for pure states, this reduces to the Born rule p = \|⟨φ\|ψ⟩\|². We provide both an intuitive derivation chain and a formal axiom presentation (A1–A7) suitable for rigorous development. The derivation is non-circular: L₃ constraints are conceptually and logically prior to the probability measure they entail. We situate this result within the quantum reconstruction literature and discuss implications for foundational physics.

**Keywords:** Born rule, Gleason's theorem, quantum foundations, logic realism, quantum reconstruction, probability, measurement problem

---

## 1. Introduction

The Born rule—that the probability of observing a system in state \|φ⟩ given preparation \|ψ⟩ equals \|⟨φ\|ψ⟩\|²—is the bridge between the mathematical formalism of quantum mechanics and experimental prediction. Despite nearly a century of use, its status remains contested. Is it a fundamental postulate? A theorem derivable from deeper principles? An empirical regularity lacking deeper explanation?

Max Born introduced the probability interpretation in 1926, initially as a footnote added in proof (Born, 1926). The rule has since been subjected to various derivation attempts:

1. **Gleason's theorem** (Gleason, 1957) shows that any probability measure on the projection lattice of a Hilbert space (dim ≥ 3) must take the trace form, from which the Born rule follows.

2. **Quantum reconstruction programs** (Hardy, 2001; Chiribella et al., 2011; Masanes & Müller, 2011) derive quantum theory, including the Born rule, from operational axioms about information processing.

3. **Decision-theoretic approaches** (Deutsch, 1999; Wallace, 2010) attempt to derive Born probabilities from rational betting behavior in Everettian quantum mechanics.

4. **QBism** (Caves et al., 2002) treats quantum probabilities as Bayesian degrees of belief, constrained by consistency requirements.

Each approach has merits and limitations. Gleason's theorem requires assuming a Hilbert space structure. Reconstruction programs derive quantum theory but do not explain why those particular axioms hold. Decision-theoretic approaches face circularity objections. QBism dissolves the question by deflating probability's ontological status.

Logic Realism Theory (LRT) offers a different path. Rather than assuming quantum structure and deriving probability, or assuming probability and constraining its form, LRT begins with the Three Fundamental Laws of Logic (L₃) as ontological constraints on physical reality:

- **Identity (L₁):** A physical configuration is determinately what it is
- **Non-Contradiction (L₂):** No configuration instantiates both P and ¬P
- **Excluded Middle (L₃):** Every applicable property is either instantiated or not

The central claim is that these constraints, applied at the "vehicle level" (the physical structure doing the representing, not the content represented), force a unique probability measure on measurement outcomes—the Born rule.

This paper develops that derivation in detail, provides formal axioms, situates the result within existing literature, and addresses potential objections.

---

## 2. Conceptual Framework

*This section defines the core concepts used throughout the paper. Subsequent sections refer back here rather than repeating definitions.*

### 2.1 The Vehicle/Content Distinction

A measurement outcome involves two conceptual levels:

**Content:** What is represented—the logical proposition "spin is up" or "particle detected in region A."

**Vehicle:** The physical structure doing the representing—the measurement apparatus, the recording medium, the macroscopic pointer position.

This distinction is central to LRT's derivation. The L₃ constraints apply primarily at the vehicle level. A detector either clicks or it doesn't (L₃ at vehicle level), even if what the click represents admits quantum indeterminacy at the content level.

### 2.2 Ontological Nullity

LRT introduces the concept of *ontological nullity* (∅_L): the limiting condition where all three logical laws fail simultaneously. A configuration that lacks determinate identity (L₁ failure), both is and is not P (L₂ failure), and neither is nor is not P (L₃ failure) would possess no ontological status whatsoever.

Physical systems exhibit what LRT calls "logic pressure"—a tendency away from ∅_L toward determinate existence.

**Important clarification:** "Ontological nullity" and "logic pressure" are *heuristic metaphors*, not additional dynamical postulates. They provide conceptual scaffolding for understanding why L₃ compliance is necessary for physical existence, but they do not introduce new forces or mechanisms. The formal content of LRT is exhausted by Axioms A1–A7; these metaphors aid intuition without adding to the mathematical structure. One could strip them entirely and the derivation would proceed unchanged—they serve pedagogical, not logical, roles.

### 2.3 I∞ and A_Ω

LRT distinguishes two domains:

**I∞ (Infinite Information Space):** The space of all representable configurations, including those that may not satisfy classical logic (quantum superpositions, for instance, represent configurations that are neither simply P nor simply ¬P at the content level).

**A_Ω (Logical Actuality Layer):** The domain of completed measurement outcomes, where L₃ constraints hold without exception. Every actual detector record is Boolean—it either registered or it didn't.

The measurement process is an interface map f_M : I∞ → A_Ω that, in each run, produces exactly one L₃-admissible record.

---

## 3. The Derivation Chain

The argument proceeds through five steps:

```
L₃ (Identity, Non-Contradiction, Excluded Middle)
    ↓
Determinate Identity at Vehicle Level
    ↓
Vehicle-Weight Invariance
    ↓
Additivity + Non-Contextuality
    ↓
Gleason's Theorem
    ↓
Born Rule: p = |⟨φ|ψ⟩|²
```

### 3.1 Step 1: Vehicle-Weight Objectivity

**Premise:** Macroscopic measurement records have determinate identity (L₁-Weak).

**Consequence:** Pre-measurement physical states must possess objective dispositions toward outcomes.

*Argument:* Consider a measurement that produces record R. This record satisfies L₁: it is determinately what it is. The transition from pre-measurement state S to record R either:

(a) Introduces determinacy ex nihilo—the disposition toward R emerges from nothing, or
(b) Preserves determinacy already present in S—the disposition was objectively there before measurement.

Option (a) violates the principle that determinacy requires grounding. If R is determinately "spin up," this determinacy must trace to something in S, not appear miraculously. Therefore option (b): S already possessed objective dispositions toward its possible measurement outcomes.

These dispositions constitute what we call *vehicle-weights*: the system's objective, pre-measurement propensities toward each possible outcome.

### 3.2 Step 2: Vehicle-Weight Invariance

**Definition:** A measure μ on projection operators satisfies *vehicle-weight invariance* if and only if, for every maximal orthonormal resolution {P_i} of the identity:

$$\sum_i \mu(P_i) = 1$$

with this total constant across all such decompositions.

**Constraint from L₁:** Vehicle-weights characterize what the system *is*, not how we describe it. If a system were "70% disposed toward outcome A" in one measurement basis but "50% disposed toward A" in another basis, the system would lack determinate identity. The question "what is this system's disposition toward A?" would have no fact of the matter—a violation of Determinate Identity at the vehicle level.

Therefore: Vehicle-weight invariance is a necessary consequence of L₁.

### 3.2.1 Contextuality, Kochen–Specker, and What LRT Forbids/Allows

A crucial clarification: LRT's vehicle-invariance (A5) is a claim about **event non-contextuality**, not about hidden variables.

**Kochen–Specker theorem** (1967): No non-contextual hidden variable model assigns pre-existing values to all observables consistently with quantum predictions (in dim ≥ 3).

**What Kochen–Specker forbids:** Hidden variable theories where each observable has a definite pre-measurement value independent of which other observables are measured alongside it.

**What LRT requires (and what is different):** Vehicle-invariance is a constraint on *probability measures*, not on value assignments. It says:

> If event *e* (a Boolean record in A_Ω) can be reached via different experimental decompositions, its probability is independent of which decomposition is used.

Formally, for projector P appearing in two maximal orthonormal decompositions D₁ = {P, Q₁, Q₂, ...} and D₂ = {P, R₁, R₂, ...}:

$$\mu_{D_1}(P) = \mu_{D_2}(P)$$

This is non-contextuality *for events*, not for values. Kochen–Specker shows that **value assignments** cannot be non-contextual. LRT shows that **probability assignments** must be non-contextual at the vehicle level—and Gleason's theorem confirms that such measures exist (the trace measures).

**Why this distinction matters:**

- Kochen–Specker refutes deterministic hidden variables
- LRT's vehicle-invariance constrains probabilistic theories
- Both are consistent: quantum theory has non-contextual probabilities but contextual (or absent) values

**Clarification of "same event":** Two decompositions involve the "same event" P when they correspond to the same Boolean record in A_Ω. For example, "spin measured up along z-axis" is the same A_Ω record regardless of whether the measurement apparatus also distinguishes x-spin or y-spin. The *pointer position* (vehicle) recording "z-spin up" is identical in both cases.

### 3.3 Step 3: Vehicle-Weight Invariance Forces Gleason's Premises

**Lemma 1 (Transitivity).** Any two maximal orthonormal decompositions of the identity are related by a unitary transformation U.

*Proof.* If {|e_i⟩} and {|f_j⟩} are both orthonormal bases, define U by U|e_i⟩ = |f_i⟩. This U is unitary, and UΣ_i |e_i⟩⟨e_i| U† = Σ_i |f_i⟩⟨f_i| = I. □

**Lemma 2 (Unitary Invariance).** Vehicle-weight invariance implies μ(UPU†) = μ(P) for all unitaries U and all projectors P.

*Proof sketch.* Consider projector P appearing in some orthonormal decomposition D₁. The transformed projector UPU† appears in the unitarily related decomposition UD₁U†. Vehicle-weight invariance requires both decompositions to sum to 1 with the same distribution of weights. Tracing through the relations, μ(UPU†) = μ(P). □

**Lemma 3 (Trace Form).** Any unitarily invariant, finitely additive probability measure on the projection lattice P(H) of a Hilbert space with dim(H) ≥ 3 takes the form:

$$\mu(P) = \mathrm{Tr}(\rho P)$$

for a unique density operator ρ.

*Proof.* This is the content of Gleason's theorem (Gleason, 1957). The original proof is technically demanding. Busch (2003) provides a simplified proof using positive operator-valued measures. The essential point: the constraints of unitarily invariant additivity, applied to the geometry of Hilbert space in dimension ≥ 3, uniquely determine the trace form. □

### 3.4 Step 4: From Trace Form to Born Rule

**Theorem (Vehicle-Weight Invariance → Born Rule).**
If vehicle-weight invariance holds, then for pure states the probability measure on outcomes takes the Born form.

*Proof:*

1. Vehicle-weight invariance (from L₁ at vehicle level) [Step 2]
2. Implies unitary invariance of μ [Lemma 2]
3. Combined with additivity, yields trace form μ(P) = Tr(ρP) [Lemma 3]
4. For pure states, ρ = |ψ⟩⟨ψ| is a rank-1 projector
5. For measurement outcome corresponding to rank-1 projector P = |φ⟩⟨φ|:

$$\mu(|\phi\rangle\langle\phi|) = \mathrm{Tr}(|\psi\rangle\langle\psi| \cdot |\phi\rangle\langle\phi|) = |\langle\phi|\psi\rangle|^2$$

**This is the Born rule. QED** □

### 3.5 Dimension-2 Edge Case and Additivity

**The dim-2 problem:** Gleason's theorem requires dim(H) ≥ 3. In a two-dimensional Hilbert space (qubit), non-Gleasonian measures exist that satisfy additivity but not the trace form. Specifically, one can define probability measures on a qubit's projection lattice that are not of the form Tr(ρP).

**Resolution via composition (standard move):** Any physical qubit capable of interaction with other systems lives in a composite Hilbert space. Consider a qubit A measured jointly with another qubit B. The composite system AB inhabits H_A ⊗ H_B, which has dimension 4. Gleason's theorem applies to the composite, forcing:

$$\mu_{AB}(P_A \otimes P_B) = \mathrm{Tr}(\rho_{AB} (P_A \otimes P_B))$$

By marginalization, the local measure on A inherits the trace form:

$$\mu_A(P_A) = \mu_{AB}(P_A \otimes I_B) = \mathrm{Tr}(\rho_A P_A)$$

where ρ_A = Tr_B(ρ_{AB}). Hence even qubits satisfy the Born rule once we recognize they never exist in complete isolation.

**LRT's take:** Axiom A6 (local tomography) implicitly handles this. Systems are defined via their compositional behavior. A "qubit" that cannot participate in any composite would violate A6, since its state could not be determined from correlations. Physical qubits satisfy A6 and hence Gleason via composition.

**Countable vs. finite additivity:** Gleason's original theorem assumes countable (σ-) additivity: for any countable collection of mutually orthogonal projections {P_i} with Σ_i P_i = P, we have μ(P) = Σ_i μ(P_i).

LRT's A4 states finite additivity explicitly. For finite-dimensional Hilbert spaces, finite and countable additivity coincide (all sums are finite). For infinite-dimensional spaces, the extension to σ-additivity follows from a regularity assumption: μ must be continuous in the strong operator topology. This is physically natural—small changes in projectors should produce small changes in probability—and is implied by the requirement that probability measures arise from density operators (which are trace-class and hence satisfy the needed continuity).

**Alternative route:** Masanes–Müller reconstruction does not require dim ≥ 3. Their Theorem 1 derives quantum structure (including Born rule) for all dimensions from local tomography, continuous reversibility, and non-classicality—exactly what LRT axiomatizes in A5–A7. This provides a complementary path avoiding the dim-2 technicality entirely.

---

## 4. No Circularity

A derivation is circular if its conclusion appears among its premises. Let us audit the dependency structure:

**Inputs:**
- L₃ constraints (Identity, Non-Contradiction, Excluded Middle)
- Vehicle/content distinction
- Hilbert space structure of quantum states (or: derivable via reconstruction)

**Intermediate constructs:**
- Vehicle-weight objectivity
- Vehicle-weight invariance
- Unitary invariance of measure

**Mathematical machinery:**
- Gleason-Busch theorem

**Output:**
- Born rule: p = \|⟨φ\|ψ⟩\|²

The Born rule appears nowhere in the premises. The derivation is acyclic.

One might object: doesn't assuming Hilbert space structure smuggle in quantum theory, including the Born rule? Two responses:

1. Hilbert space structure can itself be derived from operational axioms (reconstruction programs). The Born rule is *not* among those axioms; it is a *consequence*.

2. Even taking Hilbert space as input, Gleason's theorem is non-trivial. Many conceivable probability measures on a Hilbert space exist; Gleason shows only one family (the trace measures) satisfies the required constraints. The Born rule is not presupposed but proven.

### 4.1 Assumptions Imported from the Literature

For transparency, we list the external mathematical results treated as "black boxes" in this derivation:

| Result | Citation | What It Provides | What LRT Adds |
|--------|----------|------------------|---------------|
| **Gleason's theorem** | Gleason (1957), Busch (2003) | Unique trace-form measures on P(H) for dim ≥ 3 | Grounds *why* Gleason's premises hold (vehicle-invariance from L₁) |
| **Masanes–Müller reconstruction** | Masanes & Müller (2011) | Derives quantum formalism from operational axioms | Maps A3–A7 to their requirements; grounds *why* those axioms hold |
| **Complex Hilbert space selection** | Renou et al. (2021) | Empirical distinction between real and complex QM | Confirms the selection in Step 2 of the formal proof |
| **Local tomography** | Chiribella et al. (2011) | Composite states from marginals + correlations | Follows from Boolean product structure in A_Ω (Axiom A6) |
| **Continuous reversibility** | Hardy (2001) | Dynamics form connected Lie group | Follows from L₁: discontinuous dynamics would create identification ambiguity |

**What is genuinely new in LRT:** The vehicle/content distinction, the grounding of non-contextuality in L₁ (Determinate Identity), and the claim that reconstruction axioms are *consequences* of deeper logical constraints rather than primitive postulates.

---

## 5. Formal Axiom Presentation (IIS-LRT)

For rigorous development, we provide a minimal axiom set sufficient for a Born-rule theorem, framed in LRT terminology.

### Axiom A1 (Logical Actuality Layer)

There is a distinguished set A_Ω of actual outcome records. For any well-formed proposition P about an outcome in A_Ω, at a given time and in a single reference frame:

- P = P (Identity)
- Not (P ∧ ¬P) (Non-Contradiction)
- Exactly one of P, ¬P holds (Excluded Middle)

Each completed measurement yields a single, Boolean, L₃-admissible record.

### Axiom A2 (Infinite Information Space and Interface)

There exists an Infinite Information Space I∞ of representable configurations (non-Boolean, possibly nonlocal). A measurement with setting M is an interface map

$$f_M : I_\infty \to A_\Omega$$

that, in each run, produces exactly one record in A_Ω.

### Axiom A3 (Boolean Event Algebra at the Interface)

Let E be the set of events definable over A_Ω (modulo logical equivalence). Then E is a Boolean σ-algebra with operations ∧, ∨, ¬, null event 0, and unit event 1.

### Axiom A4 (States as Probability Measures on Events)

A physical state at the IIS-LRT interface is a function

$$s: \mathcal{E} \to [0,1]$$

such that, for all e, f ∈ E:

1. s(1) = 1, s(0) = 0
2. If e ∧ f = 0, then s(e ∨ f) = s(e) + s(f)
3. s(¬e) = 1 - s(e)

So s is a normalized, finitely additive probability measure on the Boolean event algebra.

### Axiom A5 (Vehicle-Invariance / Logical Non-Contextuality)

If an event e ∈ E can be represented, in different measurement contexts, as distinct disjoint unions of finer events,

$$e = \bigvee_{i} e_i = \bigvee_{j} f_j$$

where each {e_i} and {f_j} is a partition (mutually exclusive, jointly exhaustive) in its context, then for every state s:

$$s(e) = \sum_i s(e_i) = \sum_j s(f_j)$$

Probabilities depend only on the **logical content** of e in A_Ω, not on the "vehicle" by which it is realized in I∞.

### Axiom A6 (Local Tomography for Composites)

For systems A, B, composite events are generated by products e_A ∧ e_B with e_A ∈ E_A, e_B ∈ E_B. A joint state s_{AB} is fully determined by the joint probabilities

$$s_{AB}(e_A \land e_B) \quad \text{for all } e_A, e_B$$

The global state is fixed by statistics of local outcomes and their correlations (local tomography).

### Axiom A7 (Non-Classicality and Continuous Reversibility)

1. **Non-classicality:** There exist incompatible measurements on a single system whose statistics cannot be embedded in a single Kolmogorovian probability space (interference).

2. **Continuous reversibility:** For any two pure states s₁, s₂ there exists a continuous one-parameter family of reversible transformations connecting them, T_t(s₁) = s(t), with s(0) = s₁, s(1) = s₂.

These capture LRT's "logical-information" requirements: non-classical structure plus information-preserving, reversible dynamics.

### 5.1 Explicit Mapping to Reconstruction Theorems

**Proposition.** Axioms A3–A7 satisfy the assumptions of the Masanes–Müller reconstruction theorem.

*Mapping:*

| LRT Axiom | Masanes–Müller Requirement |
|-----------|---------------------------|
| A3 (Boolean event algebra) | Sharp measurements form a Boolean algebra |
| A4 (States as probability measures) | States are convex, normalized functionals on effects |
| A5 (Vehicle-invariance) | Non-contextuality: probability depends only on the event, not the context |
| A6 (Local tomography) | Composite states determined by local statistics |
| A7a (Non-classicality) | State space is non-simplex (interference) |
| A7b (Continuous reversibility) | Reversible transformations form a connected Lie group |

**Corollary.** By Masanes & Müller (2011, Theorem 1), any system satisfying A3–A7 is represented by quantum theory over a (real, complex, or quaternionic) Hilbert space.

*What LRT adds:* The reconstruction theorems take local tomography, non-classicality, and continuous reversibility as *given*. LRT provides a potential *grounding* for these axioms: they follow from the requirement that physical systems maintain determinate identity (L₁) at the vehicle level while interfacing with a richer information space (I∞). The vehicle/content distinction explains *why* local tomography holds (composite records in A_Ω are Boolean products of local records) and *why* dynamics must be continuous and reversible (discontinuity or irreversibility would create identification ambiguity at the vehicle level).

---

## 6. Born-Rule Theorem (IIS-LRT)

### 6.1 Theorem Statement

**Theorem (Born Rule from A1–A7).** Suppose Axioms A1–A7 hold. Then there exists a complex Hilbert space H such that:

- Pure physical states correspond to rays [ψ] ∈ H
- Sharp events correspond to orthogonal projectors P on H
- For each pure state, the interface probability map is uniquely

$$s_\psi(P) = \langle \psi | P | \psi \rangle$$

and in particular, for any rank-1 projector P = \|φ⟩⟨φ\|,

$$s_\psi(P) = |\langle \phi | \psi \rangle|^2$$

**The Born rule holds.**

### 6.2 Proof Outline

**Step 1: IIS-LRT ↔ Generalized Probabilistic Theory**

From A3–A4, each system has:
- A convex set of states S: normalized probability measures s on E
- An effect algebra E of events

Composition rule A6 and non-classical structure A7 give exactly the data of a generalized probabilistic theory (GPT) with local tomography and nonclassical state space.

**Step 2: Reconstruction to Quantum Formalism**

By reconstruction results (Masanes & Müller, 2011; Chiribella et al., 2011), any GPT satisfying:
- Local tomography (A6)
- Non-classical state space and continuous reversible dynamics (A7)

is isomorphic to quantum theory on a (real/complex/quaternionic) Hilbert space.

Empirical results (Renou et al., 2021) and LRT's further constraints select the **complex** case: real quantum theory makes different predictions in Bell-type network scenarios, and experiments favor the complex formulation.

Representation:
- States by density operators ρ on complex Hilbert space H
- Sharp events by projectors P ∈ P(H)
- General effects by positive operators E with 0 ≤ E ≤ I

At this stage we have a Hilbert-space representation but no Born rule yet.

**Step 3: Interface States as Measures on Projectors**

Axioms A4–A5 imply that each IIS-LRT state s restricts to a map

$$s: P(\mathcal{H}) \to [0,1]$$

on the lattice of orthogonal projectors such that:

- **Normalization:** s(I) = 1
- **Non-negativity:** s(P) ≥ 0 for all projectors
- **Additivity on orthogonal projectors:** If P_i P_j = 0 for i ≠ j and Σ_i P_i = P, then s(P) = Σ_i s(P_i)
- **Non-contextuality:** If the same projector P appears in different decompositions (different "vehicles"), its probability is independent of decomposition (A5)

So s is a (countably) additive, non-contextual probability measure on P(H).

**Step 4: Gleason-Type Theorem**

By Gleason's theorem (Gleason, 1957) for dim H ≥ 3, or by Busch's generalization (Busch, 2003):

> Every such probability measure s on the projection lattice is given by a unique density operator ρ such that s(P) = Tr(ρP) for all projectors P.

Thus each IIS-LRT state corresponds to a density operator:

$$s(P) = \mathrm{Tr}(\rho_s P)$$

**Step 5: Pure States → Born Rule**

Define pure IIS-LRT states as extremal points of the convex state space (non-decomposable into distinct convex combinations). In the Hilbert-space representation, these are rank-1 projectors \|ψ⟩⟨ψ\|. For such a pure state,

$$s_\psi(P) = \mathrm{Tr}(|\psi\rangle\langle\psi| P) = \langle \psi | P | \psi \rangle$$

For a rank-1 projector P = \|φ⟩⟨φ\|,

$$s_\psi(P) = |\langle \phi | \psi \rangle|^2$$

**QED** □

---

## 7. Why Only the Born Rule?

Given the constraints derived from L₃, is any other probability rule possible?

**Uniqueness:** The Born rule is the *unique* measure satisfying:
1. Vehicle-weight invariance (from L₁)
2. Finite additivity over orthogonal projections
3. Non-contextuality (from A5)

Any alternative measure would make the system's disposition toward outcomes vary with the descriptive decomposition chosen. The question "what is the probability of outcome A?" would have different answers depending on which other outcomes we consider alongside A—even when A itself is unchanged. This violates Determinate Identity.

### 7.1 A Toy Alternative: Fourth-Power Rule

Consider the hypothesis that probability follows a "fourth-power rule":

$$p(\phi|\psi) = \frac{|\langle\phi|\psi\rangle|^4}{\sum_i |\langle\phi_i|\psi\rangle|^4}$$

where {φ_i} is a complete orthonormal basis. This satisfies normalization (probabilities sum to 1) and non-negativity. Why doesn't it work?

**Failure of additivity:** Consider a qutrit (3-dimensional system) in state \|ψ⟩ = (1/√3)(\|0⟩ + \|1⟩ + \|2⟩).

For the Born rule with projector P = \|0⟩⟨0\| + \|1⟩⟨1\|:
$$p_{\text{Born}}(P) = |\langle 0|\psi\rangle|^2 + |\langle 1|\psi\rangle|^2 = \frac{1}{3} + \frac{1}{3} = \frac{2}{3}$$

For the fourth-power rule:
- Individual: p(\|0⟩) = (1/9)/(3 × 1/9) = 1/3, similarly p(\|1⟩) = 1/3
- But p(P) computed directly from the rule would require defining the fourth-power measure for rank-2 projectors

The problem: the fourth-power rule does not decompose additively. Given orthogonal projectors P₁ and P₂:

$$\frac{|\langle\psi|P_1 + P_2|\psi\rangle|^4}{\text{normalization}} \neq \frac{|\langle\psi|P_1|\psi\rangle|^4 + |\langle\psi|P_2|\psi\rangle|^4}{\text{normalization}}$$

This violates LRT's A4 (finite additivity over orthogonal events) and hence fails vehicle-weight invariance.

**General failure:** Any rule of the form p ∝ \|⟨φ\|ψ⟩\|^(2n) for n ≠ 1 fails additivity. Only n = 1 (the Born rule) yields a measure that is both additive and non-contextual.

### 7.2 Gleason Uniqueness in Dim ≥ 3

Once the projector lattice and invariance conditions (A4–A5) are in place, **Gleason's theorem provides mathematical uniqueness**: the only measures satisfying the constraints are trace measures. LRT's contribution is *conceptual*—explaining why those constraints hold—not providing an independent mathematical uniqueness proof. The argument structure is:

1. **L₁ (conceptual)** → Vehicle-weight invariance must hold
2. **Vehicle-weight invariance (formal)** → Satisfies Gleason's premises
3. **Gleason's theorem (mathematical)** → Unique trace-form measures
4. **Pure states (calculation)** → Born rule

LRT grounds Step 1; Steps 2–4 are known mathematics.

**No Escape Routes:**
- Non-additive measures fail basic probability theory requirements
- Contextual measures make probability decomposition-dependent, violating L₁
- Measures not of trace form (in dim ≥ 3) violate Gleason's constraints

The Born rule is not merely *a* consistent choice; it is the *only* consistent choice given L₃ constraints at the vehicle level.

---

## 8. Connection to Existing Literature

### 8.1 Quantum Reconstruction Programs

LRT's derivation complements quantum reconstruction programs:

| Program | Starting Point | Derives |
|---------|----------------|---------|
| Hardy (2001) | 5 reasonable axioms | Quantum state space |
| Chiribella et al. (2011) | Informational axioms + purification | Quantum theory |
| Masanes & Müller (2011) | Physical requirements | Quantum formalism |
| Dakić & Brukner (2011) | Information + reversibility | Entanglement structure |
| **LRT** | L₃ constraints | Born rule (+ connects to above) |

LRT provides a potential grounding for the operational axioms these programs assume. Why should physical theories satisfy local tomography? Continuous reversibility? LRT suggests: because these properties are downstream of more fundamental logical constraints.

### 8.2 Gleason's Theorem and Contextuality

The Kochen-Specker theorem (Kochen & Specker, 1967) establishes that no non-contextual hidden variable model can reproduce quantum predictions for dim ≥ 3. LRT's derivation invokes a positive form of this: quantum probability *must* be non-contextual at the vehicle level (A5), which then forces the Gleasonian form.

### 8.3 QBism and Probability Interpretation

Caves, Fuchs, and Schack (2002) argue that quantum probabilities are Bayesian degrees of belief, not objective propensities. LRT takes a different view: vehicle-weights are *objective* features of physical systems, constrained by L₃. However, both approaches agree that consistency requirements (coherence for QBism, vehicle-invariance for LRT) constrain the form of quantum probability.

### 8.4 Many-Worlds and Probability

The Everettian interpretation faces the "probability problem": if all branches exist, what grounds the Born weights? Decision-theoretic approaches (Wallace, 2010) attempt derivations from rational agency. LRT offers an alternative: the Born rule emerges from logical constraint, independent of branching structure or agent beliefs.

### 8.5 Complex vs. Real Hilbert Spaces

Renou et al. (2021) showed that real and complex quantum theories make different predictions in network scenarios. Experimental results favor the complex formulation. This supports LRT's selection of complex Hilbert space in Step 2 of the formal proof.

---

## 9. Potential Objections

### 9.1 "You've Assumed Hilbert Space Structure"

*Objection:* The derivation requires Hilbert space, which already contains quantum structure.

*Response:* Hilbert space structure is derivable from operational axioms (reconstruction programs) that do not include the Born rule. Alternatively, LRT's axioms A1–A7 derive Hilbert space from more basic requirements about events, states, and composition. The Born rule is a *consequence*, not an assumption, of these structures.

### 9.2 "L₃ Constraints Are Too Weak"

*Objection:* Many probability measures satisfy basic logical consistency. Why does L₃ force the Born rule specifically?

*Response:* The crucial constraint is not L₃ in general but L₃ *at the vehicle level* combined with *vehicle-weight invariance*. It is this invariance—that probability assignments cannot depend on descriptive decomposition—that, combined with Hilbert space geometry, forces Gleason's theorem and hence the Born rule.

### 9.3 "What About Non-Standard Logics?"

*Objection:* Paraconsistent and quantum logics relax L₂ or L₃. Doesn't this undermine LRT?

*Response:* LRT applies L₃ to the *vehicle level*—completed measurement records—not to the content level (quantum states in superposition). At the vehicle level, no physical measurement record has ever violated L₃. Every detector either clicks or doesn't. Alternative logics describe relationships at the content level, which LRT accommodates via I∞.

### 9.4 "This Is Just Gleason's Theorem in Disguise"

*Objection:* The derivation reduces to "assume Gleason's premises, get Gleason's conclusion."

*Response:* The contribution is showing *why* Gleason's premises hold. Gleason's theorem takes additivity and non-contextuality as given; LRT derives them from L₃ constraints on physical identity. This grounds mathematical assumptions in metaphysical principles.

---

## 10. Implications and Future Directions

### 10.1 For Quantum Foundations

If the Born rule follows from logical constraint rather than being a fundamental postulate, this shifts the burden of explanation. The question "why the Born rule?" becomes "why L₃?"—and L₃, being self-grounding (any denial presupposes what it denies), may be the appropriate terminus of explanation.

### 10.2 For Quantum Gravity

In regimes where spacetime itself may be quantum-superposed, LRT suggests that L₃ constraints still apply at the vehicle level of any actualized measurement. This may constrain approaches to quantum gravity that would permit true L₃ violations.

### 10.3 For Experimental Physics

LRT predicts: no completed measurement will ever violate L₃. This is consistent with all observations to date and continues to be empirically falsifiable. Additionally, the selection of complex over real Hilbert space (supported by Renou et al., 2021) aligns with LRT's framework.

### 10.4 Open Questions

1. Can Masanes-Müller axioms be fully derived from L₃ + parsimony?
2. What is the precise relationship between LRT and other non-collapse interpretations?
3. Can Lean formalization strengthen the proof chain?

---

## 11. Conclusion

The Born rule can be derived from the Three Fundamental Laws of Logic applied at the vehicle level of physical measurement. The derivation proceeds through vehicle-weight objectivity, vehicle-weight invariance, Gleason's theorem premises, trace-form probability measures, and finally the Born rule for pure states.

This derivation is non-circular: L₃ constraints are conceptually prior to the probability measure they entail. It provides a principled answer to "why the Born rule?"—not as an arbitrary postulate, but as a necessary consequence of what it means for physical systems to possess determinate identity.

The framework connects naturally to quantum reconstruction programs, suggests constraints on quantum gravity, and maintains clear empirical content. Logic Realism Theory offers the Born rule not as a mystery to be accepted but as a theorem to be understood.

---

## References

### Primary Sources

Born, M. (1926). Zur Quantenmechanik der Stoßvorgänge. *Zeitschrift für Physik*, 37, 863–867. https://doi.org/10.1007/BF01397477

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(4), 885–893. https://www.jstor.org/stable/24900629

Kochen, S., & Specker, E. P. (1967). The problem of hidden variables in quantum mechanics. *Journal of Mathematics and Mechanics*, 17(1), 59–87. https://doi.org/10.1512/iumj.1968.17.17004

### Quantum Reconstruction

Chiribella, G., D'Ariano, G. M., & Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311. https://doi.org/10.1103/PhysRevA.84.012311

Dakić, B., & Brukner, Č. (2011). Quantum theory and beyond: Is entanglement special? In H. Halvorson (Ed.), *Deep Beauty: Understanding the Quantum World through Mathematical Innovation* (pp. 365–392). Cambridge University Press. arXiv:0911.0695

Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012. https://arxiv.org/abs/quant-ph/0101012

Masanes, L., & Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13, 063001. https://doi.org/10.1088/1367-2630/13/6/063001

Masanes, L., Müller, M. P., Augusiak, R., & Pérez-García, D. (2013). Existence of an information unit as a postulate of quantum theory. *Proceedings of the National Academy of Sciences*, 110(41), 16373–16378. https://doi.org/10.1073/pnas.1304884110

### Gleason-Type Theorems

Busch, P. (2003). Quantum states and generalized observables: A simple proof of Gleason's theorem. *Physical Review Letters*, 91(12), 120403. https://doi.org/10.1103/PhysRevLett.91.120403

Wright, V. J., & Weigert, S. (2021). General probabilistic theories with a Gleason-type theorem. *Quantum*, 5, 588. https://doi.org/10.22331/q-2021-11-25-588

### Complex Hilbert Space Selection

Renou, M. O., Trillo, D., Weilenmann, M., Le, T. P., Tavakoli, A., Gisin, N., Acín, A., & Navascués, M. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600(7890), 625–629. https://doi.org/10.1038/s41586-021-04160-4

### Probability and Interpretation

Caves, C. M., Fuchs, C. A., & Schack, R. (2002). Quantum probabilities as Bayesian probabilities. *Physical Review A*, 65(2), 022305. https://doi.org/10.1103/PhysRevA.65.022305

Saunders, S., Barrett, J., Kent, A., & Wallace, D. (Eds.). (2010). *Many Worlds? Everett, Quantum Theory, and Reality*. Oxford University Press. https://doi.org/10.1093/acprof:oso/9780199560561.001.0001

### Logic Realism Theory

Longmire, J. D. (2025). Logic Realism Theory: A co-constitutive framework for quantum foundations. Position paper. Zenodo. https://doi.org/10.5281/zenodo.14575657

---

## Appendix A: Notation Summary

| Symbol | Meaning |
|--------|---------|
| L₁, L₂, L₃ | Identity, Non-Contradiction, Excluded Middle |
| L₃ (collective) | The Three Fundamental Laws of Logic |
| I∞ | Infinite Information Space (representable configurations) |
| A_Ω | Logical Actuality Layer (L₃-admissible outcomes) |
| ∅_L | Ontological Nullity (total logical failure) |
| H | Hilbert space |
| P(H) | Projection lattice of H |
| ρ | Density operator |
| \|ψ⟩, \|φ⟩ | State vectors |
| Tr(·) | Trace operation |
| μ, s | Probability measures |

---

## Appendix B: Gleason's Theorem (Statement)

**Theorem (Gleason, 1957).** Let H be a separable Hilbert space with dim(H) ≥ 3. Let μ be a function from the projection operators on H to [0,1] such that:

1. μ(I) = 1 (normalization)
2. For any countable collection {P_i} of mutually orthogonal projections with Σ_i P_i = P, we have μ(P) = Σ_i μ(P_i) (σ-additivity)

Then there exists a unique density operator ρ (positive, trace-class, Tr(ρ) = 1) such that:

$$\mu(P) = \mathrm{Tr}(\rho P)$$

for all projections P.

**Corollary.** For pure states (ρ = \|ψ⟩⟨ψ\|) and rank-1 projectors (P = \|φ⟩⟨φ\|):

$$\mu(|\phi\rangle\langle\phi|) = |\langle\phi|\psi\rangle|^2$$

---

*Correspondence: jdlongmire@outlook.com*
*Repository: https://github.com/jdlongmire/logic-realism-theory*

---

**Word count:** ~6,500
**Last updated:** 2026-02-24 (revised with Perplexity review feedback)
