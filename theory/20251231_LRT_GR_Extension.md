# Spacetime from Determinate Identity: A Logic Realism Theory Approach to General Relativity

**Working Paper**

**James (JD) Longmire**\
ORCID: 0009-0009-1383-7698\
Correspondence: jdlongmire@outlook.com

---

## Abstract

We explore the consequences of Determinate Identity (Id) for spacetime structure, proposing that key features of general relativity emerge from logical constraints on physical instantiation. The derivation proceeds in stages: temporal ordering emerges from joint inadmissibility of configurations (Theorem 1); Lorentzian signature is forced by the asymmetry between jointly-inadmissible and jointly-admissible configuration pairs (Theorem 2); closed timelike curves are excluded by identity-preservation requirements (Theorem 3); singularities are constrained by the requirement that identity cannot be destroyed (Theorem 4); and identity continuity imposes bounded distinguishability constraints on temporal evolution, forcing a quadratic leading-order structure for identity strain that points toward variational dynamics. These results are programmatic (rigorous formalization requires additional mathematical development), but they suggest that spacetime geometry and dynamics, like Hilbert space structure, may be derivable from $L_3$ constraints rather than postulated independently.

**Keywords:** spacetime, general relativity, Determinate Identity, temporal ordering, Lorentzian signature, closed timelike curves, singularities, logic realism

---

## 1. Introduction

### 1.1 The Problem

General relativity treats spacetime as a dynamical arena whose geometry is determined by matter-energy content via Einstein's field equations (Wald, 1984). But the framework assumes rather than derives several structural features:

- **Lorentzian signature**: Why (1,3) rather than (4,0) or (2,2)?
- **Temporal ordering**: Why is there a distinguished "timelike" direction?
- **Causal structure**: Why can't effects precede causes?
- **Singularity behavior**: What happens when geometry breaks down?

Standard GR takes these as inputs. We ask: can they be derived from more fundamental constraints?

### 1.2 The LRT Approach

Logic Realism Theory (LRT) proposes that $L_3$ (Determinate Identity, Non-Contradiction, Excluded Middle) constrains physical instantiation (Longmire, 2025). For quantum mechanics, this yields:
- Complex Hilbert space (from local tomography)
- Born rule (from vehicle-invariance)
- Tsirelson bound (from Hilbert space structure)

Can similar reasoning constrain spacetime structure?

### 1.3 Strategy

We derive spacetime features from Id applied to configurations and their relations:

| Spacetime Feature | Forced by |
|------------------|-----------|
| Temporal ordering | Joint inadmissibility (Theorem 1) |
| Lorentzian signature | Asymmetry in admissibility relations (Theorem 2) |
| CTC exclusion | Identity preservation (Theorem 3) |
| Singularity constraints | Information preservation (Theorem 4) |
| Identity strain quadratic | Compositional constraints (§6.4) |
| Variational structure | Identity preservation (§6.5, conjectured) |

### 1.4 Caveats

This paper is more programmatic than the Hilbert space derivation. We sketch arguments rather than provide rigorous proofs. The goal is to show that LRT's constraint-based approach extends naturally to spacetime, not to claim complete derivations.

### 1.5 Relation to Companion Papers

This paper is part of the Logic Realism Theory (LRT) programme:

- **Position Paper** (Longmire, 2025): Establishes the $L_3$ framework (Id, NC, EM) as ontological constraint
- **Hilbert Space Paper**: Derives complex Hilbert space from Determinate Identity
- **Born Rule Paper**: Derives Born rule from vehicle-weight invariance
- **QFT Statistics Paper**: Derives the symmetrization postulate from Determinate Identity
- **This Paper**: Explores spacetime implications (programmatic)

The papers can be read independently, but together form a unified derivation from foundational logic to quantum mechanics and beyond.

---

## 2. Temporal Ordering from Joint Inadmissibility

### 2.1 Setup

Let $A_\Omega$ be the set of $L_3$-admissible configurations. Consider pairs of configurations $c_1, c_2 \in A_\Omega$.

**Definition (Joint Admissibility)**: Configurations $c_1, c_2$ are *jointly admissible* if their conjunction is also admissible:
$$c_1 \land c_2 \in A_\Omega$$

**Definition (Joint Inadmissibility)**: Configurations $c_1, c_2$ are *jointly inadmissible* if:
$$c_1 \land c_2 \notin A_\Omega$$

This occurs when the conjunction violates NC or EM, for instance "particle at position $x_1$" and "same particle at position $x_2 \neq x_1$" at the same time.

### 2.2 Theorem 1: Temporal Ordering Emerges

**Theorem 1 (Temporal Ordering)**. If two $L_3$-admissible configurations are jointly inadmissible but both are instantiated, then they must be temporally ordered.

**Proof sketch**.

Suppose $c_1, c_2 \in A_\Omega$ but $c_1 \land c_2 \notin A_\Omega$.

If both $c_1$ and $c_2$ are instantiated, they cannot be co-instantiated (since their conjunction violates $L_3$).

Three options:
1. Only $c_1$ is instantiated (not $c_2$)
2. Only $c_2$ is instantiated (not $c_1$)
3. Both are instantiated, but at different "times"

Option 3 requires an ordering relation: "$c_1$ before $c_2$" or "$c_2$ before $c_1$".

**Definition**: The *temporal ordering* $<$ on instantiated configurations is the minimal ordering such that jointly-inadmissible but both-instantiated configurations are separated:
$$c_1 \land c_2 \notin A_\Omega \text{ and both instantiated} \Rightarrow c_1 < c_2 \text{ or } c_2 < c_1$$

**Conclusion**: Time emerges as the logical sequencing necessitated by joint inadmissibility. $\square$

**Remark**: This does not yet give metric structure (duration, intervals). It gives only ordinal structure: before/after relations forced by $L_3$ constraints.

### 2.3 Physical Interpretation

Temporal ordering is not an additional postulate. It is the logical structure that permits individually-admissible configurations to both be instantiated despite being jointly inadmissible.

Consider: a particle cannot be at two locations simultaneously (NC violation). Yet both locations can be occupied at different times. Time is what makes this possible.

---

## 3. Lorentzian Signature from Admissibility Asymmetry

### 3.1 The Signature Problem

A 4D spacetime metric has signature $(p, q)$ with $p + q = 4$. Options:
- $(4, 0)$: Euclidean (all positive)
- $(3, 1)$: Lorentzian (one negative)
- $(2, 2)$: Split signature (two negative)

Empirically, spacetime has Lorentzian signature $(3, 1)$. Why?

### 3.2 Theorem 2: Lorentzian Signature Forced

**Theorem 2 (Lorentzian Signature)**. If temporal ordering arises from joint inadmissibility and spatial separation permits joint admissibility, then the metric signature must be Lorentzian.

**Argument** (sketch, not rigorous proof):

**(Step 1: Two types of separation)**

Consider two configurations localized in spacetime. They can be:
- **Timelike separated**: One is in the causal past/future of the other
- **Spacelike separated**: Neither is in the causal past/future of the other

**(Step 2: Admissibility asymmetry)**

For jointly-inadmissible configurations (e.g., same particle at two locations):
- Timelike separation permits sequential instantiation
- Spacelike separation does not apply (they must be separated in time)

For jointly-admissible configurations (e.g., different particles at different locations):
- Both timelike and spacelike separation permit co-instantiation
- Spacelike separation is "cheaper," requiring no ordering constraint

**(Step 3: Metric signature encodes this asymmetry)**

A metric with signature $(3, 1)$ treats one dimension (time) differently from the other three (space):
- Timelike intervals: $ds^2 < 0$ (ordering constrained)
- Spacelike intervals: $ds^2 > 0$ (no ordering constraint)
- Null intervals: $ds^2 = 0$ (boundary case)

The Lorentzian signature is the unique signature that:
1. Distinguishes one dimension (time) from the others (space)
2. Permits joint admissibility for spacelike-separated configurations
3. Forces ordering for timelike-separated jointly-inadmissible configurations

**(Step 4: Other signatures fail)**

- $(4, 0)$: No distinguished temporal direction; all directions equivalent. Cannot represent the asymmetry between jointly-admissible and jointly-inadmissible pairs.
- $(2, 2)$: Two "timelike" directions. Would permit multiple independent temporal orderings, violating the requirement that jointly-inadmissible configurations have a *unique* ordering relation.

**Conclusion**: Lorentzian signature is forced by the structure of $L_3$ admissibility. $\square$

**Caveat**: This argument is heuristic. A rigorous derivation would require formalizing the relationship between joint admissibility and metric signature.

### 3.3 Relation to Causality

The Lorentzian signature encodes causal structure:
- Timelike curves connect causally-related events
- Spacelike surfaces connect causally-independent events
- Null curves are the boundary (light cones)

LRT interprets this as:
- Timelike = sequential instantiation of jointly-inadmissible configurations
- Spacelike = possible co-instantiation of jointly-admissible configurations
- Null = limiting case where ordering is just barely required

---

## 4. CTC Exclusion from Identity Preservation

### 4.1 The CTC Problem

Closed timelike curves (CTCs) are worldlines that loop back on themselves, allowing an observer to return to their own past. General relativity permits CTC solutions (Gödel universe, Kerr black holes, wormholes).

Are CTCs compatible with $L_3$?

### 4.2 Theorem 3: CTCs Violate Id

**Theorem 3 (CTC Exclusion)**. Closed timelike curves violate Determinate Identity and are therefore excluded from $A_\Omega$.

**Proof**.

Suppose a worldline $\gamma$ is a CTC. Then there exists an event $e$ on $\gamma$ such that $e$ is in its own causal past.

Let $c_e$ be the configuration at event $e$. On a CTC:
- $c_e$ causes some later configuration $c_{e'}$
- $c_{e'}$ eventually causes $c_e$ again (the loop closes)

Apply Determinate Identity (Id-3: Persistence Principle): identity persists through transformation unless the transformation constitutes a change of identity.

On a CTC:
- The "first" occurrence of $c_e$ has identity $i_1$
- The "second" occurrence of $c_e$ (after the loop) has identity $i_2$
- But they are the same event: $i_1 = i_2$

**The problem**: Is $i_1$ causally prior to $i_2$, or is $i_2$ causally prior to $i_1$? On a CTC, both. But this violates the antisymmetry of causal ordering:

$$i_1 < i_2 \text{ and } i_2 < i_1 \Rightarrow i_1 \neq i_2$$

Yet $i_1 = i_2$ by assumption (same event). Contradiction.

**Conclusion**: CTCs violate Id. Spacetimes containing CTCs are not in $A_\Omega$. $\square$

**Physical interpretation**: You cannot be your own ancestor. Identity requires a consistent causal history. CTCs create loops where an entity is both cause and effect of itself, destroying determinate identity.

### 4.3 Chronology Protection

Hawking conjectured that physics conspires to prevent CTC formation ("chronology protection"). LRT provides a *logical* version: CTCs are excluded not by dynamical mechanisms but by the requirement that instantiated configurations have determinate identity.

This doesn't explain *how* CTC formation is prevented, only *why* it must be.

---

## 5. Singularity Constraints from Information Preservation

### 5.1 The Singularity Problem

General relativity predicts singularities: points where curvature diverges and the metric is undefined. Examples:
- Black hole singularities
- Big Bang singularity
- Potential future Big Crunch

At singularities, geodesics terminate. What happens to the identity of configurations that reach a singularity?

### 5.2 Theorem 4: Identity Cannot Be Destroyed

**Theorem 4 (Identity Preservation)**. If Determinate Identity holds, then no physical process can destroy identity-constituting information.

**Proof**.

Let $c$ be a configuration with determinate identity $i$. By Id-3, identity persists through transformation unless the transformation constitutes a change of identity.

Suppose $c$ evolves to a singularity where it "ceases to exist." Two options:

**(Option A)**: Identity $i$ is destroyed (no successor configuration).

This violates Id-3: identity cannot simply vanish. If $i$ was determinate, it must either persist or transform into a new identity $i'$, but not disappear.

**(Option B)**: Identity $i$ transforms into a new configuration $c'$ with identity $i'$.

This is compatible with Id, but requires the singularity to be a transformation, not an endpoint.

**Conclusion**: Physical singularities cannot destroy identity. Either:
1. Singularities are not genuine endpoints (information escapes)
2. Singularities involve identity transformation (not destruction)
3. Classical singularities are artifacts of incomplete physics $\square$

### 5.3 Black Hole Information

This has implications for the black hole information paradox:

**Standard problem**: Hawking radiation is thermal (carries no information) (Hawking, 1975). If black holes evaporate completely, the information about what fell in is destroyed, violating unitarity.

**LRT prediction**: Information (identity-constituting structure) cannot be destroyed. Therefore:
- Black hole evaporation must be unitary
- Information must escape, either in Hawking radiation correlations or through other mechanisms
- Singularities inside black holes cannot be genuine information-destroying endpoints

This aligns with modern views from AdS/CFT, but LRT provides a *logical* reason: Id forbids information destruction.

### 5.4 Big Bang and Cosmological Singularities

The Big Bang singularity poses similar questions:
- Was there a "before" the Big Bang?
- Where did the universe's initial information come from?

LRT perspective:
- The Big Bang cannot be a genuine creation ex nihilo of identity-bearing configurations
- Either: the Big Bang is a transformation from a prior state, or "before" is not applicable
- Initial conditions carry determinate identity; they are not arbitrary

This is speculative but suggests that LRT may constrain cosmological models.

---

## 6. Identity Continuity and Kinematic Constraints

### 6.1 The Problem of Temporal Persistence

The previous sections established that temporal ordering emerges from joint inadmissibility (§2), but they did not address a deeper question: what makes successive configurations belong to the *same* system over time?

In classical mechanics, continuous trajectories provide identity continuity: particle A at time $t_1$ is the same particle as A at time $t_2$ because a continuous path connects them. But quantum mechanics lacks classical trajectories. What grounds temporal identity when configuration space is discrete or non-classical?

### 6.2 Bounded Distinguishability

**Lemma (Identity Continuity).** For a system to persist through time, successive configurations must satisfy a bounded distinguishability constraint: the configuration at $t_2$ must be sufficiently similar to the configuration at $t_1$ for there to be a determinate fact that they are the same system.

*Proof sketch.* Suppose configurations $c_1$ (at $t_1$) and $c_2$ (at $t_2$) are arbitrarily distinguishable: they share no properties that would ground identity across time. Then there is no fact of the matter that $c_2$ is the *continuation* of $c_1$ rather than a replacement. By Id, if identity is indeterminate, the system does not persist. Therefore, persistence requires bounded distinguishability. $\square$

This constraint has structural consequences: physical evolution cannot change configurations arbitrarily fast. There is a maximal rate of change compatible with identity preservation.

### 6.3 Identity Strain

**Definition (Identity Strain).** The *identity strain* between configurations $c_1$ and $c_2$ is a measure of how close they are to violating the bounded distinguishability constraint. Zero strain means identity is robustly preserved; strain approaching the bound means identity is marginally preserved; strain exceeding the bound means identity fails.

Formally, let $D(c_1, c_2)$ be a distinguishability measure (see Hilbert Space Paper for the construction from inner product). Identity strain is:

$$\varepsilon(c_1, c_2) = D(c_1, c_2)$$

subject to the constraint $\varepsilon \leq \varepsilon_{\max}$ for identity preservation.

### 6.4 Quadratic Leading-Order Form

**Lemma (Quadratic Structure).** Identity strain has a quadratic leading-order form in the displacement between configurations.

*Proof sketch.* The identity strain function $\varepsilon(\Delta c)$ must satisfy:

1. **Non-negativity**: $\varepsilon \geq 0$ (strain measures departure from identity)
2. **Evenness**: $\varepsilon(\Delta c) = \varepsilon(-\Delta c)$ (direction of change doesn't affect identity strain)
3. **Locality**: $\varepsilon$ depends only on local configuration differences
4. **Additivity under composition**: For independent subsystems, $\varepsilon_{AB} = \varepsilon_A + \varepsilon_B$

These constraints force the leading-order term to be quadratic:

$$\varepsilon(\Delta c) = \sum_{ij} g_{ij} \Delta c^i \Delta c^j + O((\Delta c)^4)$$

where $g_{ij}$ is a positive-definite metric on configuration space. $\square$

### 6.5 Connection to Dynamics

The quadratic form of identity strain has a suggestive structure: it resembles the kinetic term in a Lagrangian. This observation points toward a deep connection between identity preservation and least-action principles.

**Conjecture (Variational Structure).** Admissible dynamics (those preserving identity) extremize accumulated identity strain over paths through configuration space.

If this conjecture holds, the principle of least action would emerge as a consequence of identity preservation, not as an independent postulate. Dynamics would be constrained to paths that minimize identity strain, naturally yielding extremal (geodesic) motion.

**Caveat.** This is a pointer, not a derivation. Establishing the full connection requires additional work: specifying the relationship between identity strain and the Lagrangian, handling gauge degrees of freedom, and addressing quantum corrections. The present result establishes only that admissible dynamics fall within a constrained class characterized by quadratic kinematic structure.

---

## 7. Metric Structure and Einstein's Equations

### 7.1 What We Have Not Derived

The arguments above derive:
- Temporal ordering (from joint inadmissibility)
- Lorentzian signature (from admissibility asymmetry)
- CTC exclusion (from Id)
- Information preservation at singularities (from Id)

We have *not* derived:
- The specific form of the metric (curvature, geodesics)
- Einstein's field equations $G_{\mu\nu} = 8\pi T_{\mu\nu}$
- The equivalence principle
- The specific value of constants (Newton's G, speed of light)

### 7.2 Programmatic Suggestions

**Einstein's equations from vehicle-invariance?**

In QM, vehicle-invariance (probability assignments independent of decomposition choice) forces the Born rule. Could an analogous principle apply to spacetime?

Conjecture: The metric must be determined by a *vehicle-invariant* procedure from matter-energy content. Einstein's equations might be the unique such procedure satisfying:
1. Lorentzian signature
2. Diffeomorphism invariance (coordinate independence = descriptive invariance)
3. Local determination (metric at a point depends only on local matter-energy)

This is speculative and requires substantial development.

**Equivalence principle from Id?**

The equivalence principle states that gravitational and inertial mass are identical. Could this follow from Id?

Conjecture: If the identity of a massive configuration is determinate, then there is a unique mass associated with it, not separate "gravitational" and "inertial" masses. The equivalence principle is forced by the requirement that identity is unitary.

Again, speculative.

---

## 8. Discussion

### 8.1 What This Paper Achieves

We have shown that $L_3$ constraints, specifically Determinate Identity, have natural implications for spacetime structure:

| Result | Status |
|--------|--------|
| Temporal ordering emerges | Argued (Theorem 1) |
| Lorentzian signature forced | Sketched (Theorem 2) |
| CTCs excluded | Argued (Theorem 3) |
| Singularities constrained | Argued (Theorem 4) |
| Identity strain quadratic | Argued (§6.4) |
| Variational structure | Conjectured (§6.5) |

These are not complete derivations but programmatic proposals showing that LRT's logic-first approach extends beyond quantum mechanics.

### 8.2 Comparison with Other Approaches

**Causal set theory** (Sorkin, 2003): Spacetime emerges from discrete causal relations. LRT's "joint inadmissibility → ordering" is compatible but grounded differently (logic, not discrete structure postulate). Malament (1977) established that causal structure determines spacetime topology, supporting the primacy of causal ordering that LRT derives from $L_3$.

**Loop quantum gravity** (Rovelli, 2004): Quantizes spacetime geometry directly. LRT would ask: does LQG's structure satisfy $L_3$ constraints? Are its predictions $L_3$-admissible?

**String theory**: Requires specific dimensions and structure. LRT might constrain which string vacua are $L_3$-admissible.

### 8.3 Open Questions

1. **Metric derivation**: Can Einstein's equations be derived from $L_3$ + vehicle-invariance?
2. **Quantum gravity**: How does $L_3$ constrain the interface between quantum and gravitational structure?
3. **Cosmology**: What does $L_3$ imply for initial conditions and cosmic evolution?
4. **Constants**: Can $G$, $c$, or other constants be derived from $L_3$?

### 8.4 Meta-Proof Summary

The argument establishes that identity in physics is not exhausted by qualitative difference. Quantum systems force a distinction between qualitative identity (what kind of thing something is) and quantitative identity (how many such things exist). The law of identity requires both to be determinate wherever multiplicity claims are meaningful. For identical quantum particles, this rules out states that encode ungrounded distinctions of "which is which," explaining the necessity of permutation invariance.

Extending this reasoning in time shows that identity continuity is not automatic once classical trajectories disappear. Successive states must remain sufficiently similar for there to be a determinate fact that the system persists. This imposes a constraint on how rapidly physical states may change. Minimal logical requirements on such constraints force a quadratic leading-order structure, suggesting a deep connection between identity preservation and least-action principles.

No specific dynamics are assumed; the result is a constraint on admissibility, not a derived equation of motion.

---

## 9. Objections and Replies

### 9.1 "This merely redescribes known quantum postulates in philosophical language."

**Reply.** The derivation does not presuppose the symmetrization postulate, least-action principle, or classical dynamical laws. It begins from Determinate Identity applied to multiplicity and temporal persistence. The exclusion of permutation-sensitive states follows from identity coherence, not from empirical regularity. Likewise, the quadratic kinematic structure is derived as a leading-order necessity from compositional and locality constraints, not imported from classical mechanics. The result is a reduction in primitive postulates, not a relabeling of them.

### 9.2 "Quantitative identity is just set-theoretic cardinality, not a physical constraint."

**Reply.** If quantitative identity were merely representational, relabeling operations would have no physical consequences. Yet quantum theory sharply constrains admissible states based on multiplicity and permutation invariance. Particle number enters conservation laws, coupling constants, and empirical predictions. The argument does not reify abstract sets; it shows that determinate multiplicity is a physical fact constrained by identity coherence. Treating it as purely formal fails to account for why permutation-asymmetric states are inadmissible.

### 9.3 "Identity continuity is epistemic, not ontological."

**Reply.** The argument does not concern what observers can track, but what must be determinate for physical configurations to exist over time. If no identity-preserving mapping exists between successive states, then there is no fact of the matter that the later configuration is the same system as the earlier one. This is an ontological failure of persistence, not a limitation of knowledge. The bounded distinguishability requirement follows from this distinction.

### 9.4 "The quadratic form is an arbitrary modeling choice."

**Reply.** The quadratic structure is not asserted as a full dynamical law. It is established as the unique leading-order form compatible with non-negativity, evenness, locality, and compositional additivity. These constraints are imposed by identity preservation, not by classical analogy. Higher-order terms are not excluded; they are simply subleading in regimes where identity continuity is maintained. The result is a necessity claim, not a sufficiency claim.

### 9.5 "This smuggles in least-action physics through the back door."

**Reply.** No least-action principle is assumed. The analysis stops at the level of admissibility constraints on identity preservation. The observation that quadratic identity strain admits a variational interpretation is explicitly marked as a pointer, not a derivation. The logical direction of explanation runs from identity coherence to structural constraint, not from mechanics to metaphysics.

### 9.6 "The framework overreaches beyond what L₃ alone can justify."

**Reply.** All necessity claims are derived from Determinate Identity, Non-Contradiction, and Excluded Middle applied to multiplicity and persistence. Where additional structure is suggested (metric geometry, variational form), it is clearly flagged as future work. The present results establish only that admissible dynamics must fall within a constrained class. No specific physical laws are claimed to follow without further assumptions.

---

## 10. Conclusion

Determinate Identity has implications for spacetime structure. Temporal ordering emerges from joint inadmissibility; Lorentzian signature encodes the asymmetry between timelike (ordering-required) and spacelike (ordering-optional) separations; CTCs are excluded by identity preservation; singularities cannot destroy information. Identity continuity imposes bounded distinguishability constraints on temporal evolution, forcing a quadratic leading-order structure for identity strain that points toward variational dynamics.

These results are programmatic. Full derivations require:
- Rigorous formalization of the admissibility → signature argument
- Connection to Einstein's field equations
- Treatment of quantum gravity

But the direction is clear: if $L_3$ constrains instantiation, that constraint applies to spacetime itself, not just to configurations within spacetime. The arena of physics is not a neutral backdrop but a structure that must itself satisfy logical admissibility.

This is the ultimate extension of logic realism: not just "physics is logical" but "spacetime is logical."

---

## Acknowledgments

This research was conducted independently. I thank the related online communities for critical feedback on early drafts, particularly regarding circularity concerns and related derivations.

**AI Assistance Disclosure:** This work was developed with assistance from AI language models including Claude (Anthropic), ChatGPT (OpenAI), Gemini (Google), Grok (xAI), and Perplexity. These tools were used for drafting, editing, literature review, and exploring mathematical formulations. All substantive claims, arguments, and errors remain the author's responsibility. Human-Curated, AI-Enabled (HCAE).

---

## References

Gödel, K. (1949). An example of a new type of cosmological solutions of Einstein's field equations of gravitation. *Reviews of Modern Physics*, 21(3), 447–450.

Hawking, S. W. (1975). Particle creation by black holes. *Communications in Mathematical Physics*, 43(3), 199–220.

Hawking, S. W. (1992). Chronology protection conjecture. *Physical Review D*, 46(2), 603–611.

Longmire, J. (2025). Logic Realism Theory: Physical Foundations from Logical Constraints. Position Paper. Zenodo. https://doi.org/10.5281/zenodo.18111736

Malament, D. B. (1977). The class of continuous timelike curves determines the topology of spacetime. *Journal of Mathematical Physics*, 18(7), 1399–1404.

Penrose, R. (1965). Gravitational collapse and space-time singularities. *Physical Review Letters*, 14(3), 57–59.

Rovelli, C. (2004). *Quantum Gravity*. Cambridge University Press.

Sorkin, R. D. (2003). Causal sets: Discrete gravity. In *Lectures on Quantum Gravity* (pp. 305–327). Springer.

Wald, R. M. (1984). *General Relativity*. University of Chicago Press.

