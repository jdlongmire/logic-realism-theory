# Logic Realism Theory: Quantum Reconstruction from Logical Constraint

**Author:** James D. Longmire
**Affiliation:** Northrop Grumman Fellow (unaffiliated research)
**ORCID:** 0009-0009-1383-7698
**Correspondence:** jdlongmire@outlook.com
**Date:** March 2026
**Version:** 2.0
**Status:** Pre-print
**Companion paper:** *The Actualized Bridge: Transcendental Constitution of Physical Reality* (TAB)

---

**Abstract**

**Background:** Quantum mechanics lacks an agreed-upon ontological foundation. Reconstruction programs (Hardy 2001, CDP 2011, Masanes-Müller 2011) derive quantum structure from operational axioms but leave unexplained why those axioms hold.

**Method:** Assuming the result established in the companion paper TAB (The Actualized Bridge), that physical actuality is constituted by the primitive ontic state $\chi \equiv [L_3 : I_\infty : \mathbf{A}]$ yielding $A_\Omega = L_3(I_\infty)$, this paper reconstructs non-relativistic quantum mechanics in ten steps. Each step imports established mathematical theorems (Gleason, Stone, Masanes-Müller) or develops argued derivations from $\chi$. The reconstruction is formalized in Lean 4.

**Results:** The reconstruction yields complex Hilbert space, projection-valued measures, the Born rule, unitary dynamics, and the Schrödinger equation. Standing problems (measurement, EPR, wave-particle duality) dissolve: each presupposes a framework LRT replaces. The formalization has 22 axioms (3 primitive, 19 imported) and zero proof gaps.

**Conclusion:** LRT grounds the operational axioms that reconstruction programs assume. The categorical falsifier (Boolean outcome violation) remains unobserved. Complex field selection is empirically confirmed (Renou et al. 2021).

**Keywords:** quantum reconstruction, logical realism, information ontology, Born rule, measurement problem, foundations of physics

---

## 1. Foundational Assumption

This paper assumes the result established in the companion paper *The Actualized Bridge* (TAB): physical actuality is constituted by the primitive ontic state $\chi \equiv [L_3 : I_\infty : \mathbf{A}]$, yielding the bridge equation $A_\Omega = L_3(I_\infty)$. The argument for this result is developed fully in TAB; here we fix notation and proceed to physics.

The three primitives are co-constitutive: $L_3$ (Identity, Non-Contradiction, Excluded Middle) constrains admissibility; $I_\infty$ supplies the complete domain of possible configurations; $\mathbf{A}$ actualizes. Each requires the others. The colon notation marks mutual constitution, not conjunction.

![Figure 1: The Primitive Ontology](../figures/chi-constitution.svg)

From $\chi$, TAB derives $A_\Omega = L_3(I_\infty)$: the actualized domain consists of $L_3$-admissible configurations that $\mathbf{A}$ instantiates. This is the starting point for physics.

### 1.1 The Physical Proposition Criterion

TAB establishes that $L_3$'s constitutive status entails:

> **Physical Proposition Criterion (PPC):** A claim Q counts as a physical proposition iff Q satisfies $L_3$, which requires that Q-true and Q-false are operationally distinguishable.

The PPC follows from taking $L_3$ as a constitutive condition on physical facts rather than a filter on pre-formed propositions.

### 1.2 PPC as a Fork in the Road

The PPC represents a substantive commitment. One might accept $\chi$ yet deny that $L_3$-satisfiability entails operational distinguishability. This would yield an alternative theory in which $A_\Omega$ contains non-operational facts.

LRT takes the operational route: $L_3$ is not merely a logical constraint but a constitutive condition with physical bite. This explains why reconstruction programs (Hardy, CDP, Masanes-Müller) can derive quantum structure from operational axioms: they implicitly presuppose the PPC without grounding it. LRT makes this grounding explicit.

### 1.3 Scope and Limits

**What this paper does:**
- Reconstructs non-relativistic quantum mechanics from $\chi$
- Imports established mathematical theorems (Gleason, Stone, Hardy, Masanes-Müller)
- Shows that reconstruction axioms follow from $\chi$ rather than being postulated

**What this paper does not do:**
- Derive relativistic quantum mechanics or QFT (open problem)
- Prove imported theorems within LRT (they are external inputs)
- Explain why $\chi$ obtains rather than some other primitive structure (metaphysical stopping point)
- Predict new empirical phenomena beyond standard QM (LRT reconstructs existing structure)

**Epistemic commitment:** Lean 4 formalization verifies the logical structure of the reconstruction conditional on stated axioms. It does not verify metaphysical claims or empirical adequacy.

### 1.4 What This Paper Does

Given the TAB result, this paper reconstructs the structure of non-relativistic quantum mechanics:

- Complex Hilbert space $\mathbb{C}\mathcal{H}$ (Step 4)
- Projection-valued measures (Step 5)
- The Born rule (Step 6)
- Unitary dynamics (Step 7)
- Continuous time (Step 8)
- The Schrodinger equation (Step 10)

Each step is marked with epistemic status:
- **ESTABLISHED:** Imported from peer-reviewed mathematics
- **ARGUED:** Defended with explicit reasoning; LRT's original contribution
- **OPEN:** Identified for future work

---

## 2. From $\chi$ to Quantum Structure

### 2.1 Determinate Identity

**Claim:** Every actual configuration $c \in A_\Omega$ satisfies Determinate Identity. *[ESTABLISHED]*

**Definition:** A configuration $c \in A_\Omega$ has Determinate Identity if and only if:

$$c = c \quad \text{(Identity)}$$
$$\neg(P(c) \land \neg P(c)) \quad \text{for any property } P \text{ (Non-Contradiction)}$$
$$P(c) \lor \neg P(c) \quad \text{for any well-defined property } P \text{ (Excluded Middle)}$$

This follows directly from $A_\Omega = L_3(I_\infty)$. Configurations in $A_\Omega$ are $L_3$-admissible by definition.

### 2.2 Local Tomography

**Claim:** Any theory describing actual configurations in $A_\Omega$ must satisfy local tomography. *[ARGUED]*

**Definition:** A theory is *locally tomographic* if the state of a composite system is completely determined by the statistics of local measurements on its subsystems.

The argument proceeds in two stages:

**H1 (Metaphysical Supervenience):** Each subsystem has determinate identity. The composite is nothing over and above its subsystems relationally organized. *[ESTABLISHED---direct consequence of Determinate Identity]*

**H2 (Operational Local Tomography):** The composite state is completely determined by local measurement statistics. *[ARGUED---follows from H1 + PPC]*

**The H1 to H2 argument:** For any relation R between subsystems to be a genuine physical relation, R must satisfy $L_3$. This requires operational distinguishability (PPC). Therefore every relation in H1's supervenience base is operationally accessible. Local tomography follows.

**Alternative view:** Local tomography is philosophically controversial. One might accept H1 (metaphysical supervenience) while denying H2 (operational accessibility), holding that some identity-constituting relations resist operational probing. Such a position would require revising the PPC or accepting non-physical facts in $A_\Omega$. LRT takes the stronger line: the PPC follows from $L_3$'s constitutive role, making H2 mandatory given H1. Readers who reject this should note where the argument would need revision.

#### 2.2.1 Bell State Example

Consider $\lvert\Phi^+\rangle = \frac{1}{\sqrt{2}}(\lvert 00\rangle + \lvert 11\rangle)$. The composite identity is non-decomposable (no product form exists), yet every identity-determining relation is locally measurable: $\sigma_z \otimes I$ gives $p(0) = p(1) = 1/2$; joint measurement $\sigma_z \otimes \sigma_z$ reveals perfect correlation. $\mathbf{A}$ operates globally (selecting $\lvert 00\rangle$ or $\lvert 11\rangle$), but the relations $\mathbf{A}$ evaluates are locally accessible. This satisfies both H1 (supervenience) and H2 (local tomography).

### 2.3 Complex Hilbert Space

**Claim:** The state space is complex Hilbert space $\mathbb{C}\mathcal{H}$. *[ESTABLISHED]*

**Theorem (Masanes and Muller, 2011):** Among generalized probabilistic theories, local tomography + continuous reversible dynamics + entanglement existence + no restriction on observables uniquely select complex Hilbert space quantum mechanics.

Local tomography is derived at Step 3. The remaining axioms are physical inputs characterizing the domain. Given these inputs, the state space is $\mathbb{C}\mathcal{H}$. The field is complex, not real (Renou et al. 2021 confirms experimentally).

### 2.4 Projection-Valued Measures

**Claim:** Event operators on $\mathbb{C}\mathcal{H}$ representing actualization predicates are projections. *[ARGUED]*

The actualization primitive $\mathbf{A}$ is Boolean:

$$\mathbf{A} : D \to \{0, 1\}$$

For any configuration c and event E, $\mathbf{A}(E, c) \in \{0, 1\}$. There is no intermediate actualization.

**The eigenvalue restriction:**

1. $\mathbf{A}$'s Boolean character entails Boolean actualization values
2. Measurement outcomes are eigenvalues (spectral theorem)
3. Therefore eigenvalues $\in \{0, 1\}$
4. Bounded self-adjoint operators with spectrum $\subseteq \{0, 1\}$ satisfy $P^2 = P$

Event operators are projections. Collections form projection-valued measures (PVMs).

POVMs arise derivatively through Naimark dilation: every POVM on $\mathcal{H}$ is the restriction of a PVM on an extended space. At the fundamental level where $\mathbf{A}$ constitutes actuality, only PVMs are admissible; apparent non-Boolean measurements are incomplete descriptions of Boolean facts in extended configurations.

### 2.5 The Born Rule

**Claim:** The unique probability measure on PVM structure is the Born rule. *[ESTABLISHED]*

**Theorem (Gleason, 1957):** For dim(H) $\geq$ 3, any frame function on closed subspaces has the form $\mu(P) = \text{Tr}(\rho P)$ for a unique density operator $\rho$.

The PVM structure from Step 5 provides the frame function conditions. Gleason's theorem delivers:

$$p(E\lvert\psi) = \langle \psi \lvert P_E \lvert \psi \rangle$$

The Born rule is not postulated. It is the unique consistent probability measure the PVM structure admits.

**Probability interpretation:** The Born probability $p(E\lvert\psi)$ is neither Bayesian (subjective credence) nor frequentist (long-run limit) in its primary meaning. It is dispositional: given configuration $\psi \in I_\infty$, $p(E\lvert\psi)$ measures the structural weight of $E$ within $\psi$'s projection. $\mathbf{A}$ actualizes one outcome; the probability reflects $\psi$'s compositional structure, not observer uncertainty. This differs from Everettian branch-counting (which faces the measure problem) by grounding probability in the structure $\mathbf{A}$ operates on rather than in subjective ignorance about which branch "I" will occupy.

### 2.6 Unitarity

**Claim:** Time evolution is unitary. *[ESTABLISHED]*

Determinate Identity at the sequence level requires that transitions preserve structural determinacy. Combined with norm preservation (Born rule consistency) and the symmetry group of $A_\Omega$, this forces:

- Time evolution operators $U(t)$ form a strongly continuous one-parameter group
- $U(t)$ preserves inner products (unitarity)

This is Wigner's theorem applied to the LRT context.

### 2.7 Temporal Structure

**Claim:** Ordinal time emerges from $\mathbf{A}$'s Boolean character; continuous time from trajectory topology. *[ARGUED]*

**Unique Next State (UNS):** For every $c \in A_\Omega$, there exists a unique successor $c'$ that $\mathbf{A}$ selects. This follows from Determinate Identity + Boolean $\mathbf{A}$: Excluded Middle rules out indeterminate succession; Non-Contradiction rules out multiple successors.

UNS induces ordinal time. The Debreu-Nachbin theorem lifts ordinal structure to continuous $\mathbb{R}$-parameterization, given the Fubini-Study topology on state space.

### 2.8 The Schrodinger Equation

**Claim:** The equation of motion is the Schrodinger equation. *[ESTABLISHED]*

**Theorem (Stone, 1930):** A strongly continuous one-parameter unitary group $U(t)$ has a unique self-adjoint generator $H$ with $U(t) = \exp(-iHt/\hbar)$.

Differentiation yields:

$$i\hbar \frac{d}{dt}\lvert\psi(t)\rangle = H\lvert\psi(t)\rangle$$

The Schrodinger equation is derived, not postulated. Specific Hamiltonians remain empirical inputs.

### 2.9 Summary of Derivation Chain

| Step | Content | Status | Formalized |
|------|---------|--------|------------|
| 0 | Primitives: $\chi \equiv [L_3 : I_\infty : \mathbf{A}]$ | ASSUMED (TAB) | Yes |
| 1 | Bridge: $A_\Omega = L_3(I_\infty)$ | ASSUMED (TAB) | Yes |
| 2 | Determinate Identity | ESTABLISHED | Yes |
| 3 | Local Tomography | ARGUED | Yes |
| 4 | Complex Hilbert Space | ESTABLISHED | Yes |
| 5 | PVM Structure | ARGUED | Yes |
| 6 | Born Rule | ESTABLISHED | Yes |
| 7 | Unitarity | ESTABLISHED | Yes |
| 8 | Temporal Emergence | ARGUED | Yes |
| 9 | Energy-Action | ESTABLISHED | Yes |
| 10 | Schrodinger Equation | ESTABLISHED | Yes |

![Figure 2: Derivation Chain](../figures/derivation-chain.svg)

---

## 3. Resolution of Standing Problems

![Figure 3: Problem Dissolution Map](../figures/problem-dissolution.svg)

The standing problems of quantum foundations dissolve under LRT. Each arises from a presupposition LRT does not share.

**Two-level ontology:** The key to dissolution is the distinction between $I_\infty$ (possibility space) and $A_\Omega$ (actualized domain). Superpositions, interference, and entanglement exist in $I_\infty$. Definite outcomes exist in $A_\Omega$. Measurement is $\mathbf{A}$ selecting from $I_\infty$ under $L_3$ constraints. The problems arise from conflating these levels.

### 3.1 The Measurement Problem

**Problem:** Unitary evolution is linear; measurement yields one definite outcome. What produces the transition?

**Presupposition:** Measurement outcomes require dynamical explanation.

**Dissolution:** $\mathbf{A}$ is the primitive dynamic aspect of $\chi$, not a process within $A_\Omega$. There is no collapse because nothing collapses---the superposition $\lvert\psi\rangle$ is the state in $\mathbb{C}\mathcal{H}$; $\mathbf{A}$ selects one Boolean outcome from its PVM decomposition. The measurement problem does not arise because LRT does not treat measurement as requiring a dynamical account.

**Clarification:** This dissolution transforms rather than eliminates the question. What LRT dissolves is the *dynamical* measurement problem: why does linear unitary evolution yield definite outcomes? The answer is that outcomes are not produced by evolution but constituted by $\mathbf{A}$.

The residual question---why does $\mathbf{A}$ select one outcome rather than another?---remains. But this is a question about $\mathbf{A}$'s primitive character, not about physics within $A_\Omega$. It is analogous to "why is there something rather than nothing?": a legitimate metaphysical question, but not one that physics must answer or could answer. Admitting a primitive stopping point does not undermine the physics that proceeds from it. The dynamical problem dissolves; the selection question is relocated to where it belongs---the primitive layer.

### 3.2 Wave-Particle Duality

**Problem:** Quantum systems exhibit wave behavior (interference) and particle behavior (definite outcomes). What are they?

**Presupposition:** A system must be one kind of thing.

**Dissolution:** The wave aspect is the configuration in $I_\infty$; the particle aspect is what $\mathbf{A}$ selects into $A_\Omega$. These are not competing descriptions but descriptions at two levels: possibility space ($I_\infty$) and actuality ($A_\Omega$).

### 3.3 EPR and Nonlocality

**Problem:** Entangled systems exhibit correlations violating Bell inequalities. No local hidden variables can reproduce them.

**Presupposition:** Correlations require either local hidden variables or nonlocal causal influence.

**Dissolution:** Entangled states are non-decomposable configurations in $I_\infty$---their identity cannot be factored into subsystem identities. $A_\Omega$ is global; $\mathbf{A}$ evaluates joint configurations, not local subsystems independently. Correlations are constitutive constraints on actualization, not causal influences between spatially separated regions.

Einstein's locality is correct---no superluminal signaling. What fails is separability: the assumption that composite states factor. EPR presupposes that measurement reveals pre-existing local facts. Under LRT, $\mathbf{A}$ *constitutes* facts globally. The paradox dissolves because its framing is category-mistaken.

### 3.4 Schrodinger's Cat

**Problem:** Macroscopic superpositions seem to exist before observation.

**Presupposition:** Superpositions of macroscopic states are physically real configurations.

**Dissolution:** The superposition $\lvert\text{alive}\rangle + \lvert\text{dead}\rangle$ exists in $I_\infty$---it is representable and evolves unitarily. It is not in $A_\Omega$ as a superposition. $\mathbf{A}$ selects one $L_3$-admissible outcome. The cat is not both; it is not indeterminate. The paradox arises from treating $I_\infty$ configurations as $A_\Omega$ configurations.

### 3.5 Preferred Basis

**Problem:** Quantum mechanics does not single out a measurement basis.

**Presupposition:** Basis selection is a problem about the state.

**Dissolution:** $\mathbf{A}$ selects from the PVM determined by the physical interaction Hamiltonian. The interaction selects the relevant PVM; $\mathbf{A}$ selects one outcome from it. No preferred basis is needed in $I_\infty$ because the interaction structure provides it in $A_\Omega$.

### 3.6 The Observer

**Problem:** Many formulations make observers constitutive.

**Presupposition:** Quantum states are defined relative to observers.

**Dissolution:** $A_\Omega$ is defined by $L_3$ admissibility, not by observers. Observers are physical systems in $A_\Omega$, not constitutive elements. This is strong realism: $\mathbf{A}$ selects outcomes independently of observation.

---

## 4. Discussion

### 4.1 Comparison to Reconstruction Programs

LRT stands in a specific relation to operational reconstruction programs (Hardy 2001; CDP 2011; Masanes-Muller 2011):

| Framework | Starting Point | What Remains Unexplained |
|-----------|----------------|--------------------------|
| Hardy (2001) | 5 operational axioms | Why these axioms? |
| CDP (2011) | 6 informational principles | Why information is primitive? |
| Masanes-Muller (2011) | 5 physical requirements | Why these requirements? |
| **LRT** | $\chi = [L_3 : I_\infty : \mathbf{A}]$ | Grounds the above |

**The subsumption claim:** LRT does not compete with these programs---it subsumes them. Hardy's axioms become derivable given $\chi$. CDP's purification principle follows from Boolean actualization. Masanes-Muller's requirements are consequences of $I_\infty$ structure.

**What LRT derives that competitors assume:**

| Feature | Competitor Status | LRT Status |
|---------|-------------------|------------|
| Local tomography | Axiom | Derived (H1/H2 bridge) |
| Boolean measurement | Assumed | Derived ($\mathbf{A}$ binary) |
| PVM structure | Assumed | Derived (eigenvalue restriction) |
| Born rule | Derived (Gleason) or assumed | Derived (Gleason on derived PVM) |
| Temporal structure | Assumed | Derived (UNS + Debreu-Nachbin) |

### 4.2 Comparison to Interpretations

| Interpretation | What LRT Inherits | What LRT Avoids |
|----------------|-------------------|-----------------|
| Copenhagen | Boolean outcomes | Observer-dependence |
| Many-Worlds | Unitary structure, branching in $I_\infty$ | Branch multiplication |
| Bohmian | Realism about states | Pilot wave, primitive nonlocality |
| GRW | Empirical bet | Ad hoc parameters |

**MWI subsumption:** Deutsch-Wallace decision-theoretic axioms are derivative of $L_3$. What MWI assumes (ordering, consistency, indifference conditions), LRT derives from Identity, Non-Contradiction, Excluded Middle. The branching structure exists in $I_\infty$; only one branch is actualized in $A_\Omega$. Wallace (2012) provides the most rigorous defense of MWI probability; LRT's claim is that his axioms follow from $L_3$ rather than requiring independent justification.

**Structural realism connection:** Ladyman (2014) argues that physics reveals structure rather than individual substances. LRT is compatible: $\chi$ is structural (relational constraints among primitives) rather than substantival. The state space $\mathbb{C}\mathcal{H}$ is a structural consequence of $\chi$, not a container for pre-existing entities. Timpson (2013) notes that quantum information approaches face foundational questions about what information *is*; LRT answers: $I_\infty$ is the complete domain of distinguishable configurations, not a derived or epistemic notion.

**Categorical QM subsumption:** Every dagger-SMC axiom is derivable from $L_3$. Physics forms dagger categories because logic demands it.

### 4.3 Explanatory Power Inventory

| Phenomenon | Standard Status | LRT Status |
|------------|-----------------|------------|
| Born rule | Postulated / derived | Derived (Gleason + Boolean $\mathbf{A}$) |
| Measurement problem | Interpretation-dependent | Dissolved ($\mathbf{A}$ constitutes) |
| Superposition | Ontologically ambiguous | Incomplete specification in $I_\infty$ |
| Entanglement | Nonlocal correlations | Global $L_3$ constraint |
| Decoherence | Empirical add-on | Derived (subsystem $L_3$) |
| Local tomography | Axiom | Derived (H1/H2) |
| K=2 (complex field) | Axiom | Derived (multiple routes) |
| EPR paradox | Interpretation-dependent | Dissolved ($\mathbf{A}$ is global) |
| Wave-particle duality | Mystery | $I_\infty$/$A_\Omega$ distinction |
| Preferred basis | Unsolved | Interaction-determined |
| Observer role | Constitutive | None |

**Comparison with reconstruction programs:**

| Feature | Hardy | CDP | Masanes-Müller | LRT |
|---------|-------|-----|----------------|-----|
| Grounds operational axioms | — | — | — | ✓ |
| Derives complex field | ✓ | ✓ | ✓ | imports |
| Derives Born rule | implied | ✓ | implied | ✓ (Gleason) |
| Derives local tomography | — | — | — | ✓ |
| Derives temporal structure | ✓ | ✓ | ✓ | ✓ (Stone) |
| Proof-assistant verified | — | — | — | ✓ |
| Requires continuous reversibility | ✓ | ✓ | ✓ | — |
| Requires purification axiom | — | ✓ | — | imports |
| Ontological commitment | minimal | information-theoretic | operationalist | realist |

The key distinction: LRT answers "why these axioms?" while reconstruction programs deliberately bracket this question. The programs show that quantum structure follows from operational constraints; LRT grounds those constraints in $\chi$.

### 4.4 Predictive Constraints

LRT rules out:

- Non-Boolean measurement (contradicts $L_3$)
- Finite configuration space (contradicts $I_\infty$ completeness)
- Non-unitary evolution (contradicts actualization continuity)
- K $\neq$ 2 fields (contradicts reconstruction chain)
- Super-quantum correlations beyond Tsirelson bound (contradicts $\mathbb{C}\mathcal{H}$ structure)
- Primitive POVMs (must dilate to PVMs)

### 4.5 Falsification and Null Hypothesis

**Null hypothesis (H0):** Operational constraints suffice without ontological grounding. QM's axioms are "just the way things are" or are operationally motivated but ungrounded.

**LRT's claim against H0:** The axioms are not arbitrary---they follow from $\chi$. LRT adds explanatory value by answering "why these axioms?"

**Falsification hierarchy:**

| Level | Falsifier | Severity |
|-------|-----------|----------|
| Categorical | $L_3$ violation in completed physical record | Fatal to hard core |
| Structural | Super-quantum correlations, primitive POVMs, non-unitary dynamics | Revision of argued steps |
| Empirical | Real QM confirmed over complex (Renou et al.), black hole FC-2b | Test downstream predictions |

**Lakatosian structure:**

- **Hard core:** $\chi \equiv [L_3 : I_\infty : \mathbf{A}]$, bridge equation $A_\Omega = L_3(I_\infty)$
- **Protective belt:** Argued steps (local tomography, PVM structure, UNS, continuous time)
- **Progressive predictions:** Complex field selection (confirmed), MWI/categorical subsumption, EPR dissolution

**Popper criterion:** Satisfied. Categorical falsifier: stable, reproducible measurement outcome that is both actual and not-actual, or has no determinate truth value. No such violation observed.

---

## 5. Formalization

The derivation chain has been formalized in Lean 4.

### 5.1 Formalization Status

| Metric | Value |
|--------|-------|
| Build | Verified (2491 jobs) |
| Axioms | 22 |
| Proof gaps (sorries) | 0 |

**Axiom classification:**

| Category | Count | Description |
|----------|-------|-------------|
| PRIMITIVE | 3 | $I$, $I_\infty$ completeness, bridge principle |
| EXTERNAL | 19 | Established theorems (Gleason, Stone, Hardy, CDP, etc.) |

Axioms classified as EXTERNAL represent established mathematical results imported to avoid re-proving standard mathematics in the proof assistant. The 3 PRIMITIVE axioms are the irreducible LRT commitments corresponding to the constitutive elements of $\chi$.

### 5.2 What Lean Verifies (and Does Not)

**Lean verifies:**
- Logical consistency of the reconstruction chain
- Dependency structure: which theorems depend on which axioms
- That sorries (proof gaps) have been filled or explicitly axiomatized

**Lean does not verify:**
- Metaphysical validity of the primitives $\chi$
- Physical correctness of imported theorems (Gleason, Stone, Hardy)
- Empirical adequacy of the reconstruction
- That the 3 primitive axioms are truly irreducible

The formalization is a consistency check on the logical structure, not a proof of LRT's metaphysical claims.

### 5.3 Open Problems

| Problem | Type | Status |
|---------|------|--------|
| K=2 forcing (OPN-004) | Derivation | Three routes identified; full proof pending |
| $I_\infty \to \mathcal{H}$ embedding | Technical | Distinguishability → inner product construction open |
| Relativistic extension | Extension | Algebraic QFT path identified |
| Interface criterion | Conceptual | Candidates identified; specification open |
| Bekenstein-Hawking connection | Speculative | High priority if cosmology extension pursued |

---

## 6. Conclusion

Assuming the TAB result---that physical actuality is constituted by $\chi \equiv [L_3 : I_\infty : \mathbf{A}]$, yielding $A_\Omega = L_3(I_\infty)$---this paper has reconstructed the complete structure of non-relativistic quantum mechanics. The derivation is formalized in Lean 4 with 22 axioms (3 primitive, 19 imported) and zero proof gaps.

LRT's contribution is precisely located: not new mathematics, but a new grounding argument for existing mathematics. The reconstruction programs of Hardy, CDP, and Masanes-Muller are subsumed---their axioms become consequences of $\chi$ rather than postulates. Standing problems dissolve: measurement, EPR, wave-particle duality, Schrodinger's cat, preferred basis, the observer. Each arises from a presupposition LRT does not share.

The null hypothesis---that operational constraints suffice without grounding---is rejected. LRT answers the question reconstruction programs leave open: *why these axioms?*

The categorical falsifier remains unobserved: no physical record violates Boolean outcome structure. The structural prediction---complex field selection---is confirmed by Renou et al. (2021). The program is open; the foundation is secure.

---

## References

Busch, P. (2003). Quantum states and generalized observables: A simple proof of Gleason's theorem. *Physical Review Letters*, 91(12), 120403.

Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Debreu, G. (1954). Representation of a preference ordering by a numerical function. In R. M. Thrall et al. (Eds.), *Decision Processes* (pp. 159-165). Wiley.

Fine, K. (2012). Guide to ground. In F. Correia and B. Schnieder (Eds.), *Metaphysical Grounding* (pp. 37-80). Cambridge University Press.

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885-893.

Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.

Kochen, S. and Specker, E. P. (1967). The problem of hidden variables in quantum mechanics. *Journal of Mathematics and Mechanics*, 17(1), 59-87.

Masanes, L. and Muller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Renou, M.-O., et al. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600, 625-629.

Stone, M. H. (1930). Linear transformations in Hilbert space III. *PNAS*, 16(2), 172-175.

Timpson, C. G. (2013). *Quantum Information Theory and the Foundations of Quantum Mechanics*. Oxford University Press.

Wallace, D. (2012). *The Emergent Multiverse: Quantum Theory According to the Everett Interpretation*. Oxford University Press.

Ladyman, J. (2014). Structural realism. *Stanford Encyclopedia of Philosophy*.

---

## Appendix A: QM Primitives to LRT Origins

| QM Primitive | Standard Status | LRT Origin | Step |
|--------------|-----------------|------------|------|
| Hilbert space $\mathbb{C}\mathcal{H}$ | Postulated | Masanes-Muller | 4 |
| Complex field | Postulated | Local tomography | 4 |
| Pure states | Postulated | $\mathbb{C}\mathcal{H}$ structure | 4 |
| Observables | Postulated | PVM + spectral theorem | 5 |
| Born rule | Postulated | Gleason on PVM | 6 |
| Tensor products | Postulated | Local tomography | 4 |
| Unitary evolution | Postulated | G-equivariance + Stone | 7-9 |
| Schrodinger equation | Postulated | Stone on $U(t)$ | 10 |
| Definite outcomes | Postulated | $\mathbf{A}$ primitive | 2 |

## Appendix B: Axiom Classification

**PRIMITIVE (3):** Irreducible LRT commitments
- `I : Type*` --- configuration space
- `I_infinite` --- $I_\infty$ completeness
- `bridge_principle` --- $\chi$ grounds $A_\Omega$

**EXTERNAL (19):** Established mathematics, axiomatized for Lean efficiency
- Hardy reconstruction (2)
- Quantum state space (2)
- Purification / CDP (2)
- Born rule / Gleason (4)
- Unitarity / Hamiltonian (2)
- Functional analysis (5)
- Physical constants (2)

The 22 axioms partition into 3 irreducible primitive commitments and 19 established mathematical results imported for proof-assistant efficiency.

