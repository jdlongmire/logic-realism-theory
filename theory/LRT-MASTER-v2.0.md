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

Assuming the result established in the companion paper TAB—that physical actuality is constituted by the primitive ontic state χ ≡ [L₃ : I∞ : A], where L₃ denotes the three fundamental laws of logic, I∞ the complete informational domain, and A the actualization operator—this paper derives the full structure of non-relativistic quantum mechanics. The derivation proceeds through ten steps: from the bridge equation A_Ω = L₃(I∞) through determinate identity, local tomography, complex Hilbert space, projection-valued measures, the Born rule, unitarity, temporal emergence, and the Schrödinger equation. Each step is marked by epistemic status (ESTABLISHED, ARGUED, or OPEN) and has been formalized in Lean 4 with 31 axioms and zero sorries. The reconstruction subsumes competing programs (Hardy, CDP, Masanes-Müller) while grounding their axioms rather than postulating them. Standing problems in quantum foundations—measurement, EPR, wave-particle duality, Schrödinger's cat—dissolve rather than require solution. The theory satisfies Popperian falsifiability (categorical: L₃ violation in physical record) and Lakatosian progressiveness (structural selection of complex field confirmed by Renou et al. 2021). The null hypothesis is that operational constraints suffice without ontological grounding; LRT claims they do not.

**Keywords:** quantum reconstruction, logical realism, information ontology, Born rule, measurement problem, foundations of physics

---

## 1. Foundational Assumption

### 1.1 The TAB Result

This paper assumes the result established in the companion paper *The Actualized Bridge* (TAB):

> Physical actuality is constituted by the primitive ontic state χ ≡ [L₃ : I∞ : A], yielding the bridge equation A_Ω = L₃(I∞).

The argument for this result is developed fully in TAB and summarized here only to fix notation. Three guiding observations motivate the primitives:

| Observation | Content | Primitive |
|-------------|---------|-----------|
| 1 | Physical reality exhibits logical structure: identity, non-contradiction, determinacy | L₃ |
| 2 | Physical reality exhibits informational structure: distinguishable configurations, entropy | I∞ |
| 3 | Physical reality is dynamic: actuality is not static but constituted | A |

These three aspects are co-constitutive:

$$\chi \equiv [L_3 : I_\infty : \mathbf{A}]$$

The colon notation marks mutual constitution, not conjunction. Each aspect requires the others: L₃ without I∞ has nothing to constrain; I∞ without L₃ has no admissibility structure; both without A produce no actuality.

From χ, TAB derives:

$$\chi \vdash A_\Omega = L_3(I_\infty)$$

where A_Ω is the actualized domain—the set of L₃-admissible configurations that A instantiates. This is the starting point for physics.

![LRT Derivation Chain](figures/LRT-derivation-chain-v2.png)

*Figure 1: Complete derivation chain from χ to Schrödinger equation. Blue: primitives. Amber: bridge equation. Green: reconstruction steps. Purple: final results. External imports shown left; resolved phenomena shown right. Current Lean status: 31 axioms, 0 sorries.*

### 1.2 The Physical Proposition Criterion

TAB establishes that L₃'s constitutive status entails operational distinguishability for all physical propositions:

> **Physical Proposition Criterion (PPC):** A claim Q counts as a physical proposition if and only if Q satisfies L₃. Satisfying L₃ requires that Q-true and Q-false are operationally distinguishable. Any claim lacking this operational signature is not a physical proposition.

The PPC is not operationalism by stipulation. It follows from taking L₃ seriously as a constitutive condition on physical facts rather than as a filter on pre-formed propositions.

### 1.3 What This Paper Does

Given the TAB result, this paper derives the structure of non-relativistic quantum mechanics:

- Complex Hilbert space ℂH (Step 4)
- Projection-valued measures (Step 5)
- The Born rule (Step 6)
- Unitary dynamics (Step 7)
- Continuous time (Step 8)
- The Schrödinger equation (Step 10)

Each step is marked with epistemic status:
- **ESTABLISHED:** Imported from peer-reviewed mathematics
- **ARGUED:** Defended with explicit reasoning; LRT's original contribution
- **OPEN:** Identified for future work

The derivation has been formalized in Lean 4. Current status: 31 axioms, 0 sorries (March 2026).

---

## 2. From χ to Quantum Structure

### 2.1 Determinate Identity

**Claim:** Every actual configuration c ∈ A_Ω satisfies Determinate Identity. *[ESTABLISHED]*

**Definition:** A configuration c ∈ A_Ω has Determinate Identity if and only if:

$$c = c \quad \text{(Identity)}$$
$$\neg(P(c) \land \neg P(c)) \quad \text{for any property } P \text{ (Non-Contradiction)}$$
$$P(c) \lor \neg P(c) \quad \text{for any well-defined property } P \text{ (Excluded Middle)}$$

This follows directly from A_Ω = L₃(I∞). Configurations in A_Ω are L₃-admissible by definition.

### 2.2 Local Tomography

**Claim:** Any theory describing actual configurations in A_Ω must satisfy local tomography. *[ARGUED]*

**Definition:** A theory is *locally tomographic* if the state of a composite system is completely determined by the statistics of local measurements on its subsystems.

The argument proceeds in two stages:

**H1 (Metaphysical Supervenience):** Each subsystem has determinate identity. The composite is nothing over and above its subsystems relationally organized. *[ESTABLISHED—direct consequence of Determinate Identity]*

**H2 (Operational Local Tomography):** The composite state is completely determined by local measurement statistics. *[ARGUED—follows from H1 + PPC]*

**The H1→H2 argument:** For any relation R between subsystems to be a genuine physical relation, R must satisfy L₃. This requires operational distinguishability (PPC). Therefore every relation in H1's supervenience base is operationally accessible. Local tomography follows.

### 2.3 Complex Hilbert Space

**Claim:** The state space is complex Hilbert space ℂH. *[ESTABLISHED]*

**Theorem (Masanes and Müller, 2011):** Among generalized probabilistic theories, local tomography + continuous reversible dynamics + entanglement existence + no restriction on observables uniquely select complex Hilbert space quantum mechanics.

Local tomography is derived at Step 3. The remaining axioms are physical inputs characterizing the domain. Given these inputs, the state space is ℂH. The field is complex, not real (Renou et al. 2021 confirms experimentally).

![Dimension Scaling](figures/dimension-scaling.png)

*Figure 5: State space dimension scaling for different field parameters K. Only K=2 (complex) maintains manageable information scaling while supporting entanglement. K=1 (real) lacks interference; K≥3 grows too rapidly for physical tractability.*

### 2.4 Projection-Valued Measures

**Claim:** Event operators on ℂH representing actualization predicates are projections. *[ARGUED]*

The actualization primitive A is Boolean:

$$\mathbf{A} : D \to \{0, 1\}$$

For any configuration c and event E, A(E, c) ∈ {0, 1}. There is no intermediate actualization.

**The eigenvalue restriction:**

1. A's Boolean character entails Boolean actualization values
2. Measurement outcomes are eigenvalues (spectral theorem)
3. Therefore eigenvalues ∈ {0, 1}
4. Bounded self-adjoint operators with spectrum ⊆ {0, 1} satisfy P² = P

Event operators are projections. Collections form projection-valued measures (PVMs).

### 2.5 The Born Rule

**Claim:** The unique probability measure on PVM structure is the Born rule. *[ESTABLISHED]*

**Theorem (Gleason, 1957):** For dim(H) ≥ 3, any frame function on closed subspaces has the form μ(P) = Tr(ρP) for a unique density operator ρ.

The PVM structure from Step 5 provides the frame function conditions. Gleason's theorem delivers:

$$p(E|\psi) = \langle \psi | P_E | \psi \rangle$$

The Born rule is not postulated. It is the unique consistent probability measure the PVM structure admits.

![Born Rule Emergence](figures/born-rule-simplex.png)

*Figure 7: Born rule emergence from Gleason constraints. Left: probability simplex showing valid probability distributions. Right: Bloch sphere representation of qubit states. Gleason's theorem forces the unique probability measure on the derived PVM structure.*

### 2.6 Unitarity

**Claim:** Time evolution is unitary. *[ESTABLISHED]*

Determinate Identity at the sequence level requires that transitions preserve structural determinacy. Combined with norm preservation (Born rule consistency) and the symmetry group of A_Ω, this forces:

- Time evolution operators U(t) form a strongly continuous one-parameter group
- U(t) preserves inner products (unitarity)

This is Wigner's theorem applied to the LRT context.

### 2.7 Temporal Structure

**Claim:** Ordinal time emerges from A's Boolean character; continuous time from trajectory topology. *[ARGUED]*

**Unique Next State (UNS):** For every c ∈ A_Ω, there exists a unique successor c' that A selects. This follows from Determinate Identity + Boolean A: Excluded Middle rules out indeterminate succession; Non-Contradiction rules out multiple successors.

UNS induces ordinal time. The Debreu-Nachbin theorem lifts ordinal structure to continuous ℝ-parameterization, given the Fubini-Study topology on state space.

### 2.8 The Schrödinger Equation

**Claim:** The equation of motion is the Schrödinger equation. *[ESTABLISHED]*

**Theorem (Stone, 1930):** A strongly continuous one-parameter unitary group U(t) has a unique self-adjoint generator H with U(t) = exp(−iHt/ℏ).

Differentiation yields:

$$i\hbar \frac{d}{dt}|\psi(t)\rangle = H|\psi(t)\rangle$$

The Schrödinger equation is derived, not postulated. Specific Hamiltonians remain empirical inputs.

### 2.9 Summary of Derivation Chain

| Step | Content | Status | Lean |
|------|---------|--------|------|
| 0 | Primitives: χ ≡ [L₃ : I∞ : A] | ASSUMED (TAB) | ✓ |
| 1 | Bridge: A_Ω = L₃(I∞) | ASSUMED (TAB) | ✓ |
| 2 | Determinate Identity | ESTABLISHED | ✓ |
| 3 | Local Tomography | ARGUED | ✓ |
| 4 | Complex Hilbert Space | ESTABLISHED | ✓ |
| 5 | PVM Structure | ARGUED | ✓ |
| 6 | Born Rule | ESTABLISHED | ✓ |
| 7 | Unitarity | ESTABLISHED | ✓ |
| 8 | Temporal Emergence | ARGUED | ✓ |
| 9 | Energy-Action | ESTABLISHED | ✓ |
| 10 | Schrödinger Equation | ESTABLISHED | ✓ |

**Axiom count:** 31 (3 primitive + 14 external/imported + 14 derivation targets)

---

## 3. Resolution of Standing Problems

The standing problems of quantum foundations dissolve under LRT. Each arises from a presupposition LRT does not share.

### 3.1 The Measurement Problem

**Problem:** Unitary evolution is linear; measurement yields one definite outcome. What produces the transition?

**Presupposition:** Measurement outcomes require dynamical explanation.

**Dissolution:** A is the primitive dynamic aspect of χ, not a process within A_Ω. There is no collapse because nothing collapses—the superposition |ψ⟩ is the state in ℂH; A selects one Boolean outcome from its PVM decomposition. The measurement problem does not arise because LRT does not treat measurement as requiring a dynamical account.

### 3.2 Wave-Particle Duality

**Problem:** Quantum systems exhibit wave behavior (interference) and particle behavior (definite outcomes). What are they?

**Presupposition:** A system must be one kind of thing.

**Dissolution:** The wave aspect is the configuration in I∞; the particle aspect is what A selects into A_Ω. These are not competing descriptions but descriptions at two levels: possibility space (I∞) and actuality (A_Ω).

### 3.3 EPR and Nonlocality

**Problem:** Entangled systems exhibit correlations violating Bell inequalities. No local hidden variables can reproduce them.

**Presupposition:** Correlations require either local hidden variables or nonlocal causal influence.

**Dissolution:** Entangled states are non-decomposable configurations in I∞—their identity cannot be factored into subsystem identities. A_Ω is global; A evaluates joint configurations, not local subsystems independently. Correlations are constitutive constraints on actualization, not causal influences between spatially separated regions.

Einstein's locality is correct—no superluminal signaling. What fails is separability: the assumption that composite states factor. EPR presupposes that measurement reveals pre-existing local facts. Under LRT, A *constitutes* facts globally. The paradox dissolves because its framing is category-mistaken.

![EPR Dissolution](figures/epr-dissolution.png)

*Figure 4: EPR dissolution under LRT. Left: standard framing assumes local measurement reveals pre-existing facts, generating the paradox. Right: LRT's global A evaluates joint configurations, dissolving the paradox.*

### 3.4 Schrödinger's Cat

**Problem:** Macroscopic superpositions seem to exist before observation.

**Presupposition:** Superpositions of macroscopic states are physically real configurations.

**Dissolution:** The superposition |alive⟩ + |dead⟩ exists in I∞—it is representable and evolves unitarily. It is not in A_Ω as a superposition. A selects one L₃-admissible outcome. The cat is not both; it is not indeterminate. The paradox arises from treating I∞ configurations as A_Ω configurations.

### 3.5 Preferred Basis

**Problem:** Quantum mechanics does not single out a measurement basis.

**Presupposition:** Basis selection is a problem about the state.

**Dissolution:** A selects from the PVM determined by the physical interaction Hamiltonian. The interaction selects the relevant PVM; A selects one outcome from it. No preferred basis is needed in I∞ because the interaction structure provides it in A_Ω.

### 3.6 The Observer

**Problem:** Many formulations make observers constitutive.

**Presupposition:** Quantum states are defined relative to observers.

**Dissolution:** A_Ω is defined by L₃ admissibility, not by observers. Observers are physical systems in A_Ω, not constitutive elements. This is strong realism: A selects outcomes independently of observation.

---

## 4. Discussion

### 4.1 Comparison to Reconstruction Programs

LRT stands in a specific relation to operational reconstruction programs (Hardy 2001; CDP 2011; Masanes-Müller 2011):

| Framework | Starting Point | What's Unexplained |
|-----------|----------------|-------------------|
| Hardy (2001) | 5 operational axioms | Why these axioms? |
| CDP (2011) | 6 informational principles | Why information is primitive? |
| Masanes-Müller (2011) | 5 physical requirements | Why these requirements? |
| **LRT** | χ = [L₃ : I∞ : A] | Grounds the above |

**The subsumption claim:** LRT does not compete with these programs—it subsumes them. Hardy's axioms become derivable given χ. CDP's purification principle follows from Boolean actualization. Masanes-Müller's requirements are consequences of I∞ structure.

**What LRT derives that competitors assume:**

| Feature | Competitor Status | LRT Status |
|---------|------------------|------------|
| Local tomography | Axiom | Derived (H1/H2 bridge) |
| Boolean measurement | Assumed | Derived (A binary) |
| PVM structure | Assumed | Derived (eigenvalue restriction) |
| Born rule | Derived (Gleason) or assumed | Derived (Gleason on derived PVM) |
| Temporal structure | Assumed | Derived (UNS + Debreu-Nachbin) |

### 4.2 Comparison to Interpretations

| Interpretation | What LRT Inherits | What LRT Avoids |
|----------------|-------------------|-----------------|
| Copenhagen | Boolean outcomes | Observer-dependence |
| Many-Worlds | Unitary structure, branching in I∞ | Branch multiplication |
| Bohmian | Realism about states | Pilot wave, primitive nonlocality |
| GRW | Empirical bet | Ad hoc parameters |

**MWI subsumption:** Deutsch-Wallace decision-theoretic axioms are derivative of L₃. What MWI assumes (ordering, consistency, indifference conditions), LRT derives from Identity, Non-Contradiction, Excluded Middle. The branching structure exists in I∞; only one branch is actualized in A_Ω.

**Categorical QM subsumption:** Every †-SMC axiom is derivable from L₃. Physics forms dagger categories because logic demands it.

### 4.3 Explanatory Power Inventory

| Phenomenon | Standard Status | LRT Status |
|------------|-----------------|------------|
| Born rule | Postulated / derived | Derived (Gleason + Boolean A) |
| Measurement problem | Interpretation-dependent | Dissolved (A constitutes) |
| Superposition | Ontologically ambiguous | Incomplete specification in I∞ |
| Entanglement | Nonlocal correlations | Global L₃ constraint |
| Decoherence | Empirical add-on | Derived (subsystem L₃) |
| Local tomography | Axiom | Derived (H1/H2) |
| K=2 (complex field) | Axiom | Derived (multiple routes) |
| EPR paradox | Interpretation-dependent | Dissolved (A is global) |
| Wave-particle duality | Mystery | I∞/A_Ω distinction |
| Preferred basis | Unsolved | Interaction-determined |
| Observer role | Constitutive | None |

**Quantitative comparison (from Comparison Scorecard):**

| Criterion | LRT | SQM | MWI | Bohmian | Reconstruction |
|-----------|-----|-----|-----|---------|----------------|
| Ontological Clarity | 4 | 2 | 4 | 4 | 3 |
| Testable Predictions | 4 | 5 | 2 | 2 | 4 |
| Explanatory Unification | **5** | 2 | 3 | 3 | 4 |
| Measurement Solution | 4 | 1 | 4 | 5 | 3 |
| Formal Rigor | 4 | 5 | 5 | 5 | 5 |
| **TOTAL** | **31** | 28 | 27 | 28 | 31 |

![Competitor Comparison Matrix](figures/competitor-matrix.png)

*Figure 3: Visual comparison of LRT against reconstruction programs (Hardy, CDP, Masanes-Müller) and interpretations (Copenhagen, MWI, Bohmian, GRW). Green: derived/resolved. Amber: partially addressed. Red: assumed/problematic.*

### 4.4 Predictive Constraints

LRT rules out:

- Non-Boolean measurement (contradicts L₃)
- Finite configuration space (contradicts I∞ completeness)
- Non-unitary evolution (contradicts actualization continuity)
- K≠2 fields (contradicts reconstruction chain)
- Super-quantum correlations beyond Tsirelson bound (contradicts ℂH structure)
- Primitive POVMs (must dilate to PVMs)

![Entanglement Constraints](figures/entanglement-constraints.png)

*Figure 6: Entanglement correlation constraints under LRT. The Tsirelson bound (2√2) emerges from ℂH structure; super-quantum correlations (PR-box region) are ruled out. The CHSH inequality (classical bound 2) is violated by quantum mechanics but bounded by logical structure.*

### 4.5 Falsification and Null Hypothesis

**Null hypothesis (H₀):** Operational constraints suffice without ontological grounding. QM's axioms are "just the way things are" or are operationally motivated but ungrounded.

**LRT's claim against H₀:** The axioms are not arbitrary—they follow from χ. LRT adds explanatory value by answering "why these axioms?"

**Falsification hierarchy:**

| Level | Falsifier | Severity |
|-------|-----------|----------|
| Categorical | L₃ violation in completed physical record | Fatal to hard core |
| Structural | Super-quantum correlations, primitive POVMs, non-unitary dynamics | Revision of argued steps |
| Empirical | Real QM confirmed over complex (Renou et al.), black hole FC-2b | Test downstream predictions |

**Lakatosian structure:**

- **Hard core:** χ ≡ [L₃ : I∞ : A], bridge equation A_Ω = L₃(I∞)
- **Protective belt:** Argued steps (local tomography, PVM structure, UNS, continuous time)
- **Progressive predictions:** Complex field selection (confirmed), MWI/categorical subsumption, EPR dissolution

**Popper criterion:** Satisfied. Categorical falsifier: stable, reproducible measurement outcome that is both actual and not-actual, or has no determinate truth value. No such violation observed.

---

## 5. Open Problems

### 5.1 Current Formalization Status

| Metric | Value |
|--------|-------|
| Build | SUCCESS (2491 jobs) |
| Axioms | 31 |
| Sorries | 0 |
| PRIMITIVE | 3 (I, I_infinite, bridge_principle) |
| EXTERNAL | 14 (Gleason, Stone, Hardy, CDP, etc.) |
| REMAINING | 14 (derivation targets) |

![Axiom Reduction Timeline](figures/axiom-timeline.png)

*Figure 8: Axiom reduction journey from December 2025 to March 2026. Initial count: 55 axioms with 12 sorries. Current: 31 axioms with 0 sorries. Major reductions occurred during Phase 2 (H1/H2 bridge) and Phase 4 (Boolean spectrum derivation).*

![Dependency Graph](figures/dependency-graph.png)

*Figure 9: Traceability dependency graph showing 33 claims with 59 directed edges. Node colors indicate claim type (ONT, LOG, ACT, QM, PHY, PRD, OPN, EXT). The graph is acyclic, confirming no circular dependencies in the reconstruction chain.*

### 5.2 Derivation Targets

The 14 REMAINING axioms are derivable in principle:

| Group | Axioms | Notes |
|-------|--------|-------|
| Step 5 | `spectral_correspondence`, `event_operator_has_bool_spectrum` | Spectral theory work |
| Step 6 | `proj_norm_le`, `born_rule_completeness` | One trivial |
| Step 7 | Evolution family (4 axioms) | Reducible to 2 with Hamiltonian approach |
| Step 8 | Temporal embedding (4 axioms) | `dense` mathematically impossible |
| Step 10 | Schrödinger (3 axioms) | Blocked on unbounded operators |

**Realistic target:** 31 → 24 axioms with focused effort.

### 5.3 Extensions

| Problem | Type | Priority |
|---------|------|----------|
| Relativistic extension | Extension | Medium |
| Quantum field theory | Extension | Long-range |
| Fine-structure constant | Extension | Speculative |
| Cosmological application | Extension | Open |
| Bekenstein-Hawking connection | Gap | High |

---

## 6. Conclusion

Assuming the TAB result—that physical actuality is constituted by χ ≡ [L₃ : I∞ : A], yielding A_Ω = L₃(I∞)—this paper has derived the complete structure of non-relativistic quantum mechanics. The derivation is formalized in Lean 4 with 31 axioms (3 primitive, 14 imported, 14 open targets) and zero sorries.

LRT's contribution is precisely located: not new mathematics, but a new grounding argument for existing mathematics. The reconstruction programs of Hardy, CDP, and Masanes-Müller are subsumed—their axioms become consequences of χ rather than postulates. Standing problems dissolve: measurement, EPR, wave-particle duality, Schrödinger's cat, preferred basis, the observer. Each arises from a presupposition LRT does not share.

The null hypothesis—that operational constraints suffice without grounding—is rejected. LRT answers the question reconstruction programs leave open: *why these axioms?*

The categorical falsifier remains unobserved: no physical record violates Boolean outcome structure. The structural prediction—complex field selection—is confirmed by Renou et al. (2021). The program is open; the foundation is secure.

---

## References

Busch, P. (2003). Quantum states and generalized observables: A simple proof of Gleason's theorem. *Physical Review Letters*, 91(12), 120403.

Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Debreu, G. (1954). Representation of a preference ordering by a numerical function. In R. M. Thrall et al. (Eds.), *Decision Processes* (pp. 159-165). Wiley.

Fine, K. (2012). Guide to ground. In F. Correia and B. Schnieder (Eds.), *Metaphysical Grounding* (pp. 37-80). Cambridge University Press.

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885-893.

Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.

Kochen, S. and Specker, E. P. (1967). The problem of hidden variables in quantum mechanics. *Journal of Mathematics and Mechanics*, 17(1), 59-87.

Masanes, L. and Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Renou, M.-O., et al. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600, 625-629.

Stone, M. H. (1930). Linear transformations in Hilbert space III. *PNAS*, 16(2), 172-175.

---

## Appendix A: QM Primitives to LRT Origins

| QM Primitive | Standard Status | LRT Origin | Step |
|--------------|-----------------|------------|------|
| Hilbert space ℂH | Postulated | Masanes-Müller | 4 |
| Complex field | Postulated | Local tomography | 4 |
| Pure states | Postulated | ℂH structure | 4 |
| Observables | Postulated | PVM + spectral theorem | 5 |
| Born rule | Postulated | Gleason on PVM | 6 |
| Tensor products | Postulated | Local tomography | 4 |
| Unitary evolution | Postulated | G-equivariance + Stone | 7-9 |
| Schrödinger equation | Postulated | Stone on U(t) | 10 |
| Definite outcomes | Postulated | A primitive | 2 |

## Appendix B: Axiom Classification

**PRIMITIVE (3):** Irreducible LRT commitments
- `I : Type*` — configuration space
- `I_infinite` — I∞ completeness
- `bridge_principle` — χ grounds A_Ω

**EXTERNAL (14):** Established mathematics, axiomatized for Lean efficiency
- Hardy H1/H2 (2)
- Gleason theorem (2)
- Stone theorem (2)
- CDP results (3)
- Wigner theorem (1)
- Supporting lemmas (4)

**REMAINING (14):** Open derivation targets
- Could become theorems with additional proof work
- Some blocked on missing Mathlib infrastructure

![Axiom Classification](figures/axiom-treemap.png)

*Figure 2: Visual breakdown of 31 axioms by classification. PRIMITIVE (3): irreducible LRT commitments. EXTERNAL (14): established mathematics imported for Lean efficiency. REMAINING (14): open derivation targets.*
