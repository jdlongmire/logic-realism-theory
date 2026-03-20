# LRT Open Problem 1: Energy-Action Identification

**Status:** Substantially argued -- all four stages argued; residuals documented and bounded  
**Priority:** 1 of 2 open problems  
**Epistemic standing:** Stages 1-4 argued; open items reduce to FC-1 Gaps A/B and Stage 1 residuals (Conjecture 2 fiber, Route 2 Ξ term, Axiom A5)  
**Last substantive revision:** 2026-03-12 (Stages 2-4 worked; Gaps 2, 3, 1c, 4 argued)

---

## The Problem, Stated Precisely

LRT has A as a primitive actualization selector: A : D → {0,1}, operating continuously on the domain D = L₃(I∞). A is formal. It marks configurations as obtaining or not obtaining. It carries no physical units.

The conjecture is that energy is A viewed through the temporal dimension -- specifically, that the Hamiltonian H, as the generator of time translation in quantum mechanics, is the physical expression of A's continuous binary operation once time is treated as a product of A_Omega rather than a background presupposition.

If the conjecture holds, energy is not an independent primitive imported from physics. It emerges from the same actualization structure that grounds quantum mechanics. That closes the gap between LRT's logical architecture and the physical quantities required for the Jacobson/Padmanabhan thermodynamic gravity route to Gap B.

The problem is to make this identification rigorous.

---

## Audit of Prior Footholds

Before developing the approach, an honest audit of what the GR extension document (20251231) actually established is required. Two results were previously cited as footholds; both require correction.

**Theorem 1 (Temporal Ordering): argued, but ordinal only.**

What Theorem 1 establishes: a minimal ordering relation -- before/after -- on configurations that are jointly inadmissible but both instantiated. The document flags this explicitly: "This does not yet give metric structure (duration, intervals). It gives only ordinal structure: before/after relations forced by L₃ constraints."

The result is genuine. But ordinal ordering is not sufficient to define the Hamiltonian as generator of time *translation*. Translation requires a measure of temporal distance -- a metric. Theorem 1 does not provide that.

**Theorem 2 (Lorentzian Signature): heuristic sketch only, not proved.**

The document labels Theorem 2 with the caveat: "This argument is heuristic. A rigorous derivation would require formalizing the relationship between joint admissibility and metric signature." The argument is conceptually sound but none of its four steps are formally proved.

**Quadratic identity strain (§6.4): argued -- the strongest existing result.**

The quadratic structure of identity strain is established by four constraints: non-negativity, evenness, locality, and additivity under composition. The argument is rigorous at the level of a proof sketch. This is the genuine foothold for Stage 1.

**Consequence:** Stage 1 cannot treat Theorems 1 and 2 as delivering metric structure. Stage 1 must do that work itself. The quadratic identity strain result is where Stage 1 begins.

---

## Why This Is Hard

**Difficulty 1: Time has ordinal but not metric structure from existing results.**

Theorem 1 gives before/after. The Hamiltonian requires a metric on the time dimension: a notion of temporal distance that makes "translation by dt" well-defined. The gap between ordinal and metric temporal structure is the central obstacle in Stage 1.

**Difficulty 2: The action integral requires a measure.**

Action S = ∫ L dt requires integration over time with a well-defined measure. Open Problem 2 (stricter continuity for A) is directly relevant: once D acquires measure-theoretic structure, A : D → {0,1} can be integrated. The two problems must be developed in partial parallel after Stage 1.

**Difficulty 3: The identification must be non-trivial.**

A weak identification -- "energy is defined as whatever A does through time" -- is circular and empty. The identification must entail known results without additional postulates: the Schrödinger equation, energy conservation via Noether, the correct energy spectrum for systems already in LRT's quantum reconstruction chain.

---

## Stage 1: From Ordinal Ordering to Temporal Metric

This is the unblocked first stage. It has six sub-steps worked here in full.

### 1.1 What Theorem 1 Actually Gives

Let A_Omega be the actualized domain. Define joint inadmissibility: configurations c₁, c₂ ∈ A_Omega are jointly inadmissible if c₁ ∧ c₂ ∉ A_Omega.

Theorem 1 delivers a strict partial order < on jointly-inadmissible configuration pairs: if c₁ and c₂ are jointly inadmissible but both instantiated, then c₁ < c₂ or c₂ < c₁.

This does not give:
- A total order on all configurations
- A metric on the temporal dimension
- A topology on the time axis beyond what the order induces
- Any notion of temporal interval length

The order topology induced by < on the time axis is the coarsest topology compatible with the ordering. It is not sufficient for calculus, integration, or the Hamiltonian formalism.

### 1.2 The Identity Strain Metric on Configuration Space

The quadratic identity strain result (GR extension §6.4) establishes the following.

Identity strain ε(Δc) measures the distinguishability between a configuration c and a nearby configuration c + Δc. Four constraints force a quadratic leading-order form:

- Non-negativity: ε(Δc) ≥ 0
- Evenness: ε(Δc) = ε(-Δc)
- Locality: ε depends only on local configuration differences
- Additivity: for independent subsystems, ε_AB = ε_A + ε_B

These force:

    ε(Δc) = Σᵢⱼ gᵢⱼ Δcⁱ Δcʲ + O(|Δc|⁴)

where gᵢⱼ is symmetric and positive-definite. This is a Riemannian metric on configuration space C.

**Epistemic status:** argued from four constraints. Taking as established pending Lean 4 formalization.

### 1.3 The Temporal Subspace and the Problem of Sign

The configuration space C of A_Omega contains both spatial and temporal degrees of freedom. The metric gᵢⱼ on C is Riemannian -- positive-definite everywhere.

Theorem 1 distinguishes one family of directions in C: those along which joint inadmissibility forces sequencing. Call these the temporal directions. Define the temporal subspace T as the subspace of tangent vectors to paths along which jointly-inadmissible configurations are sequenced.

The restriction of gᵢⱼ to T gives a positive-definite quadratic form:

    g_T(v) = g₀₀ v²   (g₀₀ > 0)

This is a Riemannian metric on T. But spacetime requires a Lorentzian metric with the temporal component carrying negative sign. The Riemannian identity strain metric does not directly deliver the Lorentzian sign. This is the central structural tension in Stage 1.

**The sign must come from a separate argument about admissibility asymmetry**, not from the identity strain result alone. §1.4 develops that argument.

### 1.4 Gap 1a: Closing the Lorentzian Sign -- Route 1 (Causal Cone Construction)

The heuristic Premise D argument is replaced here by a formal construction. The strategy: derive a field of sharp convex cones on the tangent bundle of A_Omega from the admissibility relation, then invoke the standard result that any smooth metric realizing such a cone field has Lorentzian signature. The sign is not assumed -- it falls out of the cone structure.

**Prerequisite.** This construction requires A_Omega to be a smooth manifold, or at minimum to have a well-defined tangent bundle at generic points. This is the content of Gap 1b (density and countable chain condition on the temporal ordering). Route 1 is therefore logically posterior to Gap 1b. The construction is presented here conditional on Gap 1b being closed; Gap 1b is addressed in §1.5.

#### Definitions

**Definition 1 (Admissibility order).** Write p ≺ q iff p and q are jointly inadmissible and A realizes p prior to q. This is Theorem 1's ordering relation, promoted to an event-level relation on A_Omega.

**Definition 2 (Future-realizable tangent cone).** A tangent vector v ∈ T_p(A_Omega) is future-realizable iff there exists a smooth curve γ with γ(0) = p, γ̇(0) = v, and p ≺ γ(ε) for all sufficiently small ε > 0. The future-realizable cone at p is:

    C_p = { v ∈ T_p(A_Omega) : v is future-realizable }

**Definition 3 (Spatial tangent directions).** A tangent vector w ∈ T_p(A_Omega) is spatial iff infinitesimal displacement along w preserves mutual admissibility -- the perturbed event remains jointly admissible with p and does not enter C_p or -C_p.

#### Three Lemmas for the Cone Field

**Lemma 1 (Openness of C_p).** C_p is an open subset of T_p(A_Omega).

*Proof strategy.* Let v ∈ C_p, realized by curve γ with p ≺ γ(ε). For Lemma 1 to hold, joint inadmissibility must be an open condition on pairs in A_Omega x A_Omega -- that is, the set {(c₁, c₂) : c₁ ∧ c₂ ∉ A_Omega} must be open in the product topology. This requires more than continuity of the single-configuration selector A : D → {0,1}. It requires that the pair-admissibility predicate on A_Omega x A_Omega is itself continuous in the induced product topology -- so that the jointly-inadmissible pairs form an open set rather than merely a measurable one.

*What is currently available:* continuity of A as a single-configuration selector gives clopen preimages for Act(c) = 1 in the appropriate topology on D. The extension to pairs is plausible -- if the product topology on A_Omega x A_Omega inherits the right structure from Gap 1b's manifold construction -- but requires explicit formulation. The step cannot be read off from single-configuration continuity alone.

*Epistemic status:* plausible and likely formalizable once Gap 1b establishes the manifold structure and its product topology. Currently stated as a conditional claim, not a demonstrated one. Conditional on Gap 1b and explicit verification that pair-admissibility is continuous in the product topology.

---

**Conjecture 2 (Convexity of C_p -- primary open target for Route 1).** If v, w ∈ C_p, then av + bw ∈ C_p for all a, b > 0.

*Why this is a conjecture, not a lemma.* The naive argument runs: the jointly-admissible set is a convex cone at the tangent level because L₃'s constraints are propositional (linear at the configuration level), so no nonlinear interaction can create new joint inadmissibilities from individually admissible directions; therefore the jointly-admissible set is convex and its complement (the future cone C_p) is also a cone. This argument does not hold as stated. A linear or propositional constraint at the configuration level can induce a non-convex feasible region after passage to local state geometry or manifold embedding. The passage from "L₃ constraints are propositional" to "the admissible tangent directions form a convex set" requires a dedicated theorem, not a linearity observation.

*What a proof would require.* The necessary result is a local closure theorem of the following form:

    Local Closure Theorem (target): If v and w are infinitesimal co-instantiation-preserving directions at p -- meaning displacement along v (resp. w) from p does not create a new jointly-inadmissible pair with p -- then every positive combination av + bw (a, b > 0) is also co-instantiation-preserving at p.

This is a claim about the local geometry of the admissibility predicate, not about logical linearity. It would need to be derived from LRT's axioms by showing either: (a) the co-instantiation-preserving directions form a local algebra closed under positive combination; or (b) there is a monotonicity theorem showing that admissibility cannot decrease under positive combination of admissible perturbations given L₃'s structure.

*Subclaims for formalization.*

    SC1 (Local algebra): The set of co-instantiation-preserving tangent directions at p is closed under positive linear combination.
    
    SC2 (No nonlinear inadmissibility): For any v, w co-instantiation-preserving at p, there is no ε > 0 such that exp_p(ε(av+bw)) is jointly inadmissible with p while exp_p(εv) and exp_p(εw) are each jointly admissible with p.
    
    SC3 (Cone complement): If the co-instantiation-preserving directions form a convex cone, then C_p (the complement, consisting of sequencing-forcing directions) is also a cone.

SC3 is straightforward given SC1/SC2. SC1 and SC2 are the genuine targets.

*Failure conditions.* Conjecture 2 fails if: (a) LRT's admissibility structure has a nonlinear interaction at the tangent level -- for example, if the joint inadmissibility predicate on pairs is not locally representable as a half-space in T_p; or (b) the embedding of configuration space into the event manifold introduces curvature that curves the admissibility boundary nonlinearly even when the configuration-level constraints are propositional.

*The orthogonality route -- a worked argument.*

The claim is that joint inadmissibility in LRT maps to orthogonality in CP(H) after the Masanes-Müller reconstruction. If this map holds, Conjecture 2 follows from established geometry. The argument has three steps.

**Step O1: Jointly inadmissible configurations are perfectly distinguishable.**

Two configurations c₁, c₂ are jointly inadmissible iff c₁ ∧ c₂ ∉ A_Omega -- their conjunction violates L₃. The paradigm case: a single-particle system occupying positions x₁ and x₂ (x₁ ≠ x₂) simultaneously violates NC (the particle cannot be both at x₁ and not-at-x₁). The configurations "particle at x₁" and "particle at x₂" are therefore jointly inadmissible.

Now apply the distinguishability metric. D(c₁, c₂) = sup_M ‖P_M(c₁) - P_M(c₂)‖_TV. For the measurement M that asks "is the particle at x₁?", P_M(c₁) = 1 and P_M(c₂) = 0, giving ‖P_M(c₁) - P_M(c₂)‖_TV = 1. Therefore D(c₁, c₂) = 1: the configurations are perfectly distinguishable.

**Claim:** every pair of jointly inadmissible configurations achieves D = 1.

*Argument:* joint inadmissibility means that for any system in state c₁, the state c₂ is entirely ruled out by L₃. Excluded Middle then guarantees a sharp boundary: any measurement that determines which of the two L₃-constrained configurations is instantiated must assign probability 1 to one and 0 to the other (since intermediate probabilities would require partial instantiation of a conjunction that L₃ forbids entirely). This measurement witnesses D(c₁, c₂) = 1.

*Epistemic status of Step O1:* argued. The argument from L₃-forbidden conjunctions to sharp measurement outcomes (probability 1/0 rather than intermediate) relies on Excluded Middle applied to instantiation -- which is LRT's core claim. The step is not circular: it uses Excluded Middle as a premise about which conjunctions A_Omega can contain, not as a premise about D itself.

**Step O2: Perfect distinguishability implies orthogonality in CP(H).**

From the Masanes-Müller reconstruction established in LRT's technical foundations (Technical Foundations §3.3, Lemma 3.3, Step 4):

    D(s₁, s₂) = √(1 - |⟨s₁|s₂⟩|²)

for pure states s₁, s₂ ∈ CP(H). Therefore D(s₁, s₂) = 1 iff |⟨s₁|s₂⟩|² = 0 iff ⟨s₁|s₂⟩ = 0, i.e., iff the states are orthogonal.

*Epistemic status of Step O2:* established. This is a theorem of the Masanes-Müller reconstruction, imported unchanged.

**Step O3: Co-instantiation-preserving directions at p are non-orthogonal directions in CP(H).**

A tangent vector w at p ∈ A_Omega is co-instantiation-preserving iff displacement along w does not create a jointly inadmissible pair with p. By Step O1, creating a jointly inadmissible pair means reaching a perfectly distinguishable configuration (D = 1). By Step O2, D = 1 means reaching an orthogonal state in CP(H).

Therefore: a tangent direction w is co-instantiation-preserving iff displacement along w in CP(H) stays within the set of states non-orthogonal to p.

The set of pure states non-orthogonal to a given state |p⟩ ∈ CP(H) is:

    U_p = {|ψ⟩ ∈ CP(H) : ⟨p|ψ⟩ ≠ 0}

This is an open set in CP(H) (complement of the closed set {|ψ⟩ : ⟨p|ψ⟩ = 0}, i.e., complement of the orthogonal complement of |p⟩ in CP(H)).

**The tangent cone of U_p at p is convex.** In CP(H) with the Fubini-Study metric, U_p is the complement of a closed totally geodesic submanifold (the orthogonal complement CP(H⊖⟨p⟩)). The tangent directions at p pointing into U_p form an open hemisphere in T_p(CP(H)) -- those directions v for which the initial velocity of the geodesic from p in direction v does not immediately enter the orthogonal complement. An open hemisphere in a real vector space is convex. Therefore SC1 holds: the co-instantiation-preserving tangent directions at p form a convex set.

**SC2 follows.** For any v, w individually co-instantiation-preserving at p, they point into the open hemisphere. Any positive combination av + bw (a, b > 0) also points into the open hemisphere (open hemispheres are convex cones). Therefore av + bw is co-instantiation-preserving at p.

**SC3 follows.** The future cone C_p is the complement of the co-instantiation-preserving directions and their negatives. Since the co-instantiation-preserving directions form a convex cone (the open hemisphere and its interior), their complement (together with the negative cone) gives C_p the required cone structure.

**Conjecture 2 therefore holds conditional on Steps O1-O3 for single-system configurations.**

*The composite system problem -- a real structural issue.*

The biconditional joint inadmissibility ↔ orthogonality does not hold in full generality across composite systems. The forward direction (joint inadmissibility → orthogonality) holds: if two configurations of the same system are jointly inadmissible, they are perfectly distinguishable and hence orthogonal. But the converse -- orthogonality → joint inadmissibility -- fails for configurations belonging to distinct systems.

Counterexample: Let c₁ = "particle A in state |↑⟩" and c₂ = "particle B in state |↓⟩". In the tensor product Hilbert space H_A ⊗ H_B, the states |↑⟩_A ⊗ |anything⟩_B and |anything⟩_A ⊗ |↓⟩_B can be orthogonal (if the tensor product states are orthogonal), but c₁ and c₂ describe different systems and are jointly admissible -- both can be simultaneously instantiated. The orthogonality is in the full Hilbert space, not in a single-system space, and does not signal joint inadmissibility.

The orthogonality relation in CP(H_A ⊗ H_B) is therefore broader than the joint inadmissibility relation. Some orthogonal pairs are jointly admissible (cross-system orthogonality). Some orthogonal pairs are jointly inadmissible (same-system orthogonality arising from NC violation).

*Resolution: system-indexed inadmissibility.*

Joint inadmissibility is system-relative. The admissibility predicate does not act on raw Hilbert space states -- it acts on system-indexed configurations. A configuration in LRT is not merely a vector in CP(H); it is a system-indexed state: a specification of what predicates hold for a given physical system.

Two configurations c₁ and c₂ are jointly inadmissible iff they are configurations of the **same system** (same physical identity index) and their conjunction violates NC for that system.

Under this indexing, the biconditional holds:

    Jointly inadmissible(c₁, c₂) ↔ [same system(c₁, c₂)] ∧ [D(c₁, c₂) = 1]

The "same system" condition is the missing qualifier in Step O1-O3. Adding it recovers the biconditional -- within a single-system Hilbert space H_sys, orthogonality and joint inadmissibility coincide exactly. Across systems, neither relation implies the other.

*Consequence for Conjecture 2.*

Conjecture 2 is a claim about the tangent cone C_p at a single event p ∈ A_Omega. The tangent directions at p are perturbations of p's configuration -- they describe how the state of the system at p changes under infinitesimal displacement. These are perturbations of a **single system's state** (the system localized near p), not cross-system perturbations.

Therefore the orthogonality route applies in full: at the single-event level, the relevant CP(H) is the single-system projective Hilbert space CP(H_sys), and within that space orthogonality coincides with joint inadmissibility. The open hemisphere geometry of U_p in CP(H_sys) gives the convexity of C_p.

The composite system objection is real but local: it does not affect the tangent cone construction because tangent vectors are local, single-system perturbations. It becomes relevant only at the level of global topology -- whether A_Omega's total admissibility structure matches the orthogonality structure of the full multi-system Hilbert space. That is a separate and later question, not a blocker for Conjecture 2.

**Revised status of Conjecture 2:**

The orthogonality route establishes Conjecture 2 for single-system configurations, which is the relevant case for the tangent cone construction. The argument requires:

    (a) that tangent vectors at p represent single-system perturbations (plausible from the localization of events in A_Omega -- each event is associated with a definite local system state)
    
    (b) that within a single-system CP(H_sys), joint inadmissibility = orthogonality (argued in Steps O1-O2, using Excluded Middle and the reconstruction)
    
    (c) that the open hemisphere in T_p(CP(H_sys)) is convex (established -- open hemispheres in real vector spaces are convex cones)

Condition (a) is the remaining gap. It requires connecting the abstract notion of "event p in A_Omega" to a definite single-system Hilbert space CP(H_sys) -- i.e., that A_Omega has a local fiber structure with single-system Hilbert spaces as fibers. This is a non-trivial structural claim about A_Omega that is not yet established, but it is motivated by the localization of physical systems and is the natural expectation from the reconstruction chain.

*Epistemic status of the orthogonality route overall:* Conjecture 2 is elevated from open conjecture to argued conjecture, conditional on the local fiber structure of A_Omega (condition (a)). The multi-system objection is identified, resolved at the tangent cone level, and deferred as a global topology question. The decisive remaining subclaim is:

**A_Omega has a local single-system fiber structure: each event p is associated with a definite CP(H_sys), and tangent vectors at p are perturbations within CP(H_sys).**

**Fiber structure argument -- worked.**

*Premise 1 (System identity from Technical Foundations):* By Lemma A.1 (Anti-Holism) in the Hilbert Space Derivation document: Determinate Identity (Id) requires that composite system identity is fully determined by the identities of its parts. Global properties cannot float free of part-properties. System identity is grounded in the system's own intrinsic state.

*Premise 2 (UNS system-indexing):* The UNS theorem operates on L₃-complete states. A L₃-complete state is one where every well-formed predicate about the system is determinately resolved. For UNS to deliver a unique successor, the state must be fully specified -- including which system is being described. A state description without a system-index is incomplete: it does not specify whose predicates are being resolved. L₃-completeness therefore requires system-indexing.

Formally: a configuration c ∈ 𝒜 is a pair (sys(c), state(c)) where sys(c) identifies the physical system and state(c) ∈ CP(H_{sys(c)}) is the system's quantum state. The system-index sys(c) is not a label -- it is part of what makes the configuration a fully determinate entity in I∞.

*Premise 3 (Actualization is system-local):* Each event p in Γ_{A_Omega} is the actualization of a configuration c_p = (sys(p), state(p)). By Anti-Holism: the identity of the actualized configuration is grounded in the identity of the system and its state. The event p is therefore associated with a definite system sys(p) and a definite state state(p) ∈ CP(H_{sys(p)}).

*The fiber assignment:* Define the fiber over p as:

    F_p = CP(H_{sys(p)})

This is well-defined: sys(p) is part of c_p's L₃-complete specification, and CP(H_{sys(p)}) is the projective Hilbert space of that system, whose structure is established by the Masanes-Müller reconstruction.

*Tangent vectors are fiber-local:* A tangent vector v ∈ T_p(A_Omega) represents an infinitesimal perturbation of the configuration c_p -- a small change in the system's state while the system remains the same system. The "system remains the same system" condition is guaranteed by the continuity of the actualization trajectory (from A's continuity, argued in Problem 2): a continuous actualization selector cannot jump to a different system between infinitesimal steps. Therefore v perturbs state(p) within F_p = CP(H_{sys(p)}), not across fibers.

*Fiber structure conclusion:* A_Omega has a local fiber structure with single-system Hilbert spaces as fibers: p ↦ CP(H_{sys(p)}). Tangent vectors at p are perturbations within F_p. This is condition (a) for Conjecture 2.

*Epistemic status of the fiber structure argument:* argued. The chain is: L₃-completeness requires system-indexing (Premise 2) → each event carries a definite system identity (Premise 3) → fiber assignment is well-defined (fiber construction) → continuity of A ensures tangent vectors stay within fibers (tangent-vector argument).

The weakest link is Premise 2: the claim that L₃-completeness requires system-indexing as part of the configuration, rather than treating system-indexing as an external label. The defense: in LRT's I∞, a distinguishable configuration must specify *what* is distinguished. A state description without a system-boundary specification is not maximally distinguishable -- two systems in the same quantum state but with different spatial extents or compositions are distinguishable. The system-index is therefore part of the distinguishability structure, hence part of the L₃-complete specification. System-indexing is not an added label; it is constitutive of what makes configurations distinct in I∞.

**Conjecture 2 status -- updated:**

Condition (a) is now argued. With conditions (b) and (c) previously argued (Steps O1-O3 via the orthogonality route and open hemisphere convexity), all three conditions for Conjecture 2 are argued:

    (a) Tangent vectors at p are single-system perturbations within F_p = CP(H_{sys(p)}) -- argued above
    (b) Within F_p, joint inadmissibility = orthogonality -- argued (Steps O1-O2)
    (c) Co-instantiation-preserving directions = open hemisphere in T_p(F_p) -- argued (Step O3)

Conjecture 2 (convexity of C_p) is elevated from *argued conditional* to *argued*, pending verification of the fiber structure's weakest link (Premise 2: system-indexing as constitutive of L₃-completeness).

**Lemma 3 (Sharpness: C_p ∩ (-C_p) = {0}).** No nonzero tangent direction is simultaneously future- and past-realizable.

*Proof sketch.* Suppose v ∈ C_p ∩ (-C_p). Then v is future-realizable (p ≺ γ(ε)) and -v is future-realizable (p ≺ γ(-ε)), meaning p precedes both γ(ε) and γ(-ε). But by the irreflexivity and transitivity of ≺ (from Theorem 1's ordering), p cannot precede an event that also precedes p. Since γ(-ε) approaches p from the past direction (being the curve along -v), p ≺ γ(-ε) would require γ(-ε) ≺ p ≺ γ(-ε), a cycle. Theorem 1's ordering is acyclic by construction -- it is induced by joint inadmissibility, which is symmetric, but the actualization order A imposes is asymmetric (A selects which of the two occurs first). Therefore v = 0. □

*Epistemic status:* argued. The acyclicity follows from A's asymmetric selection. This is the strongest of the three lemmas.

#### Axiom A5: One Time Dimension

With the three lemmas, C_p is an open, convex, sharp cone at each p. One further axiom is required:

**Axiom A5 (Codimension-1 spatial complement).** At each p ∈ A_Omega, the tangent directions not in C_p ∪ (-C_p) -- the spatial directions -- span a subspace of codimension 1 in T_p(A_Omega).

This axiom states precisely that there is exactly one temporal dimension. Its content in LRT terms: at each event, the jointly-inadmissible directions (which force sequencing and determine C_p) span a one-dimensional subspace of T_p, with the remaining n-1 dimensions being spatial (co-instantiation directions).

*Epistemic status of Axiom A5:* this is an explicit structural postulate, not a derived result. The surrounding justification -- that a single binary ordering relation cannot generate more than one linearly independent ordering direction -- is motivated but not proved. A single partial order can induce richer causal geometry than a one-dimensional temporal sector; additional regularity conditions (local comparability, cone uniqueness) are required to force the codimension-1 result. Those conditions are not yet established from LRT's axioms. A5 is stated as an axiom because that is its honest status. The L₃ uniqueness justification is a reason to believe A5 is not ad hoc, not a derivation of A5.

#### The Cone-to-Metric Theorem

Given Lemmas 1-3 and Axiom A5, the following theorem applies.

**Theorem (Gap 1a target -- Lorentzian signature).** Let A_Omega be a smooth n-dimensional manifold equipped with an admissibility order ≺ that induces at each p an open, convex, sharp cone C_p ⊂ T_p(A_Omega), and suppose the complement of C_p ∪ (-C_p) spans a subspace of codimension 1. Then any smooth pseudo-Riemannian metric g on A_Omega whose causal cones coincide with C_p has Lorentzian signature (1, n-1) or (n-1, 1). If a temporal orientation is fixed (past vs future), the sign choice is determined up to overall convention.

*Proof availability:* this theorem is established in the mathematical literature on causal structure. The key results are Malament (1977) -- causal order determines conformal metric class -- and the classification of cone fields by metric signature (see Minguzzi and Sanchez 2008, "The causal hierarchy of spacetimes," for a comprehensive treatment). The application to LRT's admissibility-order cone field is the novel step; the theorem itself is not new.

*What remains:* the novel LRT content is the three lemmas establishing that the admissibility relation generates a cone field satisfying the theorem's hypotheses. The theorem then delivers Lorentzian signature as a consequence.

**Epistemic status of Route 1 overall:** Lemma 1 is argued conditional on pair-admissibility continuity in the product topology (itself conditional on Gap 1b, which reduces to Problem 2 -- now argued). Conjecture 2 is argued -- fiber structure established via L₃-completeness + system-indexing + Anti-Holism; all three conditions (a), (b), (c) argued. Lemma 3 is argued (acyclicity from asymmetric actualization order). Axiom A5 is a structural postulate with motivated but unproved justification. The cone-to-metric theorem is externally established (Malament 1977; Minguzzi-Sanchez 2008). Route 1's primary open item is now only Axiom A5 -- which is explicitly postulated, not a gap. The program moves from "well-framed with one unproved conjecture" to "argued, with one explicit axiom and one dependency on Problem 2."

---

### 1.4b Gap 1a: Route 2 (Effective Hessian -- Dynamical Reinforcement)

Route 2 gives the same Lorentzian sign result from the dynamical side -- from the second variation of the admissibility action functional rather than from the cone field. It is a reinforcement route, not the primary one, but it connects Gap 1a directly to Stage 2's variational structure.

#### Setup

Let C be configuration space with Riemannian identity-strain metric G (= gᵢⱼ from §1.2). Let γ(λ) be a path of actualization through C. Define an admissibility action:

    A[γ] = ∫ L(γ, γ̇) dλ

where L combines identity strain with an admissibility constraint term:

    L = √(Gᵢⱼ γ̇ⁱ γ̇ʲ) - Ξ(γ, γ̇)

Here Ξ penalizes jointly-inadmissible coexistence: Ξ > 0 when the path attempts to co-instantiate jointly-inadmissible configurations, and Ξ = 0 along purely spatial (co-instantiation-preserving) deformations.

#### The Tangent Space Split

Along any extremal path γ₀, the tangent space T_{γ₀}C splits as:

    T_{γ₀}C = T_seq ⊕ T_coinst

where T_seq is the one-dimensional subspace of perturbations that move along forced sequencing (temporal perturbations), and T_coinst consists of perturbations within mutually admissible co-instantiation directions (spatial perturbations).

#### The Second Variation

The second variation of A at γ₀ defines a quadratic form Q on T_{γ₀}C:

    Q(η, η) = δ²A[η]

**Claim:** Q is negative-definite on T_seq and positive-definite on T_coinst.

*Argument for negativity on T_seq:* a temporal perturbation η ∈ T_seq shifts the sequencing of jointly-inadmissible events. It changes which of two incompatible configurations A realizes first. This perturbation does not reduce identity strain -- it perturbs the admissibility constraint Ξ itself. The constraint term Ξ enters the Lagrangian with a negative sign (it penalizes inadmissibility violations). A perturbation that shifts the sequencing incurs a cost in Ξ without reducing the strain term. The net effect on the second variation is negative: Q(η, η) < 0 for η ∈ T_seq \ {0}.

*Argument for positivity on T_coinst:* a spatial perturbation η ∈ T_coinst deforms the path within co-instantiation-preserving directions. It changes the configuration but not the sequencing. The constraint term Ξ = 0 for such perturbations (no inadmissibility is created). The second variation reduces to the second variation of the arc length functional in G, which is positive-definite (G is Riemannian). Therefore Q(η, η) > 0 for η ∈ T_coinst \ {0}.

**Consequence:** the Hessian Q has signature (-,+,...,+) -- exactly one negative mode (the temporal direction) and n-1 positive modes (the spatial directions). The effective metric defined by Q on the space of actualization events is Lorentzian.

**Epistemic status of Route 2:** conjectured. The arguments for negativity on T_seq and positivity on T_coinst are physically motivated but require formalization. The key step -- that shifting the sequencing of jointly-inadmissible events enters Q with a negative sign -- depends on the specific form of Ξ, which has not been derived from LRT's axioms. Ξ must be determined from first principles before Route 2 can be called argued.

**Value of Route 2:** it gives an independent path to the same conclusion and connects Gap 1a to Stage 2's variational structure. Closing Route 2 is equivalent to specifying the Lagrangian for Stage 2 -- which is the primary Stage 2 target. The two routes therefore reinforce each other across stages.

### 1.5 The Arc Length Argument for Temporal Metric

Given that the temporal direction carries a different sign, the temporal component g₀₀ must be determined. The following argument connects g₀₀ to the Riemannian identity strain metric via the arc length functional.

Consider a system evolving along a path γ : [t₁, t₂] → C, where t is the temporal parameter from Theorem 1's ordering <. The accumulated identity strain along γ is:

    S_ε[γ] = ∫_{t₁}^{t₂} ε(γ'(t)) dt = ∫_{t₁}^{t₂} √(gᵢⱼ γ'ⁱ γ'ʲ) dt

This is the arc length of γ in the Riemannian metric gᵢⱼ, integrated against the temporal parameter t.

For S_ε[γ] to be well-defined as a Riemann integral, the temporal parameter t must be a measurable real-valued function on A_Omega's actualization sequence. This requires:

**Requirement R1 (Density):** between any two temporally ordered actualization events, there is a third. Formally: the ordering ≺ is dense -- for any p ≺ q in A_Omega there exists r with p ≺ r ≺ q.

**Requirement R2 (Countable chain condition):** every antichain in the temporal ordering -- every set of pairwise temporally unordered events (mutually jointly admissible, simultaneous configurations) -- is countable.

**Gap 1b:** verify that the temporal ordering on A_Omega satisfies R1 and R2. If both hold, Cantor's theorem on ordered sets guarantees an order-isomorphism between the temporal ordering and a subset of ℝ with the standard measure.

**Conditional result:** assuming R1 and R2, the temporal metric is:

    d(t₁, t₂) = |t₁ - t₂|

and the full spacetime metric is:

    ds² = -dt² + gᵢⱼ dxⁱ dxʲ

---

### 1.5a Working Gap 1b: Density (R1) and the CCC Problem

**R1 (Density) -- argued.**

The UNS theorem establishes that A_Omega's actualization trajectory Γ_{A_Omega} is a path through 𝒜 under continuous dynamics -- the transition operator T acts on a state space that the Masanes-Müller reconstruction identifies with CP(H), which is a connected manifold under the Fubini-Study metric. The actualization dynamics are governed by Schrödinger evolution (continuous) or its LRT analog. A continuous path through a connected manifold cannot jump: if p ≺ q are two ordered events on the trajectory, the path passes through every intermediate point, giving a third event r with p ≺ r ≺ q.

More formally: suppose R1 fails, i.e., there exist p ≺ q with no r between them. Then the actualization trajectory has a gap -- it jumps from p directly to q with no intermediate state. A jump in CP(H) under continuous dynamics requires a discontinuity in the state evolution. But A is defined as a continuous binary selector (the Open Problem 2 framework), and LRT's UNS theorem gives unique successors under fully L₃-specified state transitions. Discontinuous jumps are ruled out: they would require A to simultaneously assign Act = 0 and Act = 1 at the jump point, violating Excluded Middle applied to the actualization selector itself.

Therefore R1 holds for the temporal ordering on Γ_{A_Omega}, conditional on A's continuity (Open Problem 2, Step 1) and the UNS dynamics being continuous.

*Epistemic status of R1:* argued, conditional on A's continuity. The continuity of A is the content of Open Problem 2 -- its resolution directly delivers R1 as a corollary. R1 and Problem 2 are therefore coupled: Problem 2 closes R1 as a side-effect.

**R2 (Countable chain condition) -- fails as stated; requires replacement.**

R2 as stated -- every antichain in the temporal ordering is countable -- almost certainly fails for the full A_Omega. An antichain in the temporal ordering is a set of mutually jointly-admissible, temporally unordered events. These correspond to spatial slices of A_Omega: configurations that can be co-instantiated simultaneously. In any physically realistic setting, spatial slices contain uncountably many configurations (all possible arrangements of particles in a spatial region). R2 therefore fails.

This is not a defect in LRT -- it is a defect in the application of Cantor's embedding theorem to a partial order. Cantor's theorem applies to *total* (linear) orders. A_Omega's temporal ordering is a *partial* order: spacelike-separated events are incomparable, not ordered. For a partial order, R2 is not the right condition.

**The correct replacement: separability of CP(H).**

The correct embedding theorem for the temporal ordering on Γ_{A_Omega} is not Cantor's theorem but the Debreu-Nachbin theorem for continuous orders, or more directly the following:

*Fact:* A connected, separable topological space with a continuous total order embeds order-isomorphically into ℝ (or a subspace of ℝ). (Debreu 1954, Theorem 1.)

The key conditions are:

- *Connectivity:* CP(H) is connected. ✓ (established from Masanes-Müller)
- *Separability:* CP(H) is separable -- it has a countable dense subset. For finite-dimensional H, CP(H) is a finite-dimensional compact manifold and hence separable. For infinite-dimensional H (the full quantum field theory setting), CP(H) is separable if H is separable, which is standard. ✓ (inherited from the separability of H in the reconstruction)
- *Continuous total order on Γ_{A_Omega}:* the temporal ordering on the actualization trajectory Γ_{A_Omega} is a total order (UNS gives a unique linear sequence of events) and is continuous under the Fubini-Study topology. ✓ (from UNS and Anandan-Aharonov)

The antichain issue dissolves because the Debreu-Nachbin theorem applies to Γ_{A_Omega} -- the actualization *trajectory* -- not to the full A_Omega including all spacelike-separated configurations. The trajectory is the single actualized sequence; it is totally ordered by UNS. The spatial directions are not part of the trajectory's order structure -- they are the fiber directions at each event. R2 was the wrong condition because it was being applied to the wrong object (the full partial order on A_Omega rather than the total order on Γ_{A_Omega}).

**Revised Gap 1b formulation:**

*R1* (density of Γ_{A_Omega}'s temporal ordering): argued, conditional on A's continuity.

*R2* (replaced): Γ_{A_Omega}'s temporal ordering is a continuous total order on a connected separable space (CP(H) restricted to the trajectory). By the Debreu-Nachbin theorem, it embeds order-isomorphically into ℝ. This is the correct condition replacing the failed CCC requirement.

**What the Debreu-Nachbin route delivers:**

The temporal parameter t : Γ_{A_Omega} → ℝ is a continuous order-preserving map. This is sufficient for the arc length integral S_ε[γ] = ∫ √(gᵢⱼ γ'ⁱ γ'ʲ) dt to be well-defined as a Lebesgue integral over Γ_{A_Omega}'s trajectory.

**Epistemic status of revised Gap 1b:** R1 is argued (conditional on A's continuity from Problem 2). The Debreu-Nachbin embedding replaces R2 and is argued from separability of H and totality of UNS ordering. Gap 1b is now substantially closed -- the residual condition is A's continuity, which is Problem 2's subject. Gap 1b reduces to Problem 2.

**Consequence for the overall program:** Gap 1b is not an independent gap. It is a corollary of Open Problem 2 (A's continuity) plus the Debreu-Nachbin theorem applied to UNS's total ordering. Closing Problem 2 closes Gap 1b as a side-effect, which in turn enables the Route 1 cone construction and, via the fiber structure argument, closes Conjecture 2. The three major blockers -- Gap 1b, Conjecture 2, and the fiber structure -- all reduce to Open Problem 2's continuity of A.

This is a significant compression of the open problem structure.

### 1.6 Connecting gᵢⱼ to the Physical Spacetime Metric

**Three distinct levels -- a necessary clarification.** This section moves among three geometrically distinct spaces that must not be conflated:

1. *Configuration space C* -- the space of all quantum states in LRT's Hilbert space reconstruction. The identity-strain metric gᵢⱼ lives here. It is Riemannian (positive-definite) throughout.

2. *The event manifold A_Omega* -- the actualized domain, the arena on which Route 1 constructs its causal cone field. Route 1 derives a Lorentzian structure on A_Omega from the admissibility order. This Lorentzian structure is not identical to gᵢⱼ -- it is a distinct geometric structure at a distinct level.

3. *Projective Hilbert space CP(H)* -- the natural geometry of quantum states after Hilbert space reconstruction. The Fubini-Study metric lives here and is the restriction of gᵢⱼ after the Masanes-Müller reconstruction identifies C with CP(H).

The spacetime metric ds² = -dt² + gᵢⱼ dxⁱ dxʲ that appears later in Stage 1 is not the raw gᵢⱼ from configuration space. It is a composite: the temporal component (-dt²) comes from Route 1's Lorentzian cone structure on A_Omega; the spatial component (gᵢⱼ dxⁱ dxʲ) is the Fubini-Study metric on CP(H) restricted to the spatial (co-instantiation-preserving) directions and localized to the tangent space of A_Omega at each event. The two components come from different levels and are assembled into a single spacetime metric only after both Route 1 and the Fubini-Study identification are established. Until that assembly is made explicit, references to ds² should be understood as anticipating the result, not asserting it.

The connection: in LRT's derivation chain, the Hilbert space of quantum mechanics is the mathematical structure of I∞ (the distinguishability metric D on configurations induces the Hilbert space inner product via the Masanes-Müller reconstruction). A configuration c ∈ C is a quantum state |ψ⟩ ∈ H. The identity strain metric gᵢⱼ on C is, after reconstruction, the Fubini-Study metric on the projective Hilbert space CP(H).

The Fubini-Study metric is the natural metric on the space of quantum states. Its restriction to paths in C that correspond to physical time evolution -- paths generated by a Hamiltonian H -- gives:

    gᵢⱼ γ'ⁱ γ'ʲ = ⟨ψ̇|ψ̇⟩ - |⟨ψ̇|ψ⟩|²

where |ψ̇⟩ = d|ψ⟩/dt. This is the variance of the Hamiltonian in state |ψ⟩, which by the energy-time uncertainty relation is connected to the rate of change of the quantum state.

**The connection to H:** the arc length of a quantum evolution in the Fubini-Study metric is related to the energy of the evolving state. Specifically, for a state evolving under H:

    S_ε[γ] = (1/ℏ) ∫ ΔH dt

where ΔH = √(⟨H²⟩ - ⟨H⟩²) is the energy uncertainty. This is the Anandan-Aharonov relation (1990), which gives the geometric phase accumulated by a quantum state as a function of energy uncertainty integrated over time.

**Significance:** the Anandan-Aharonov relation connects the identity strain arc length directly to the Hamiltonian. The accumulated identity strain along a quantum evolution path is proportional to ∫ ΔH dt -- the integrated energy uncertainty. This is a genuine physical result, not an assumption.

**Gap 1c:** the Anandan-Aharonov relation connects identity strain to energy uncertainty, not to energy itself. The Hamiltonian as a generator of time translation is the *expectation value* ⟨H⟩, not the uncertainty ΔH. Making H the generator requires showing that the identity strain arc length is extremized (in Stage 2) by paths of definite energy -- eigenstates of H -- for which ΔH = 0. This is the bridge from energy uncertainty to energy itself.

### 1.7 Stage 1 Summary: What Is Established and What Remains

**Established (argued):**
- Configuration space C has a Riemannian metric gᵢⱼ from identity strain.
- After Hilbert space reconstruction, gᵢⱼ is the Fubini-Study metric on CP(H).
- The accumulated identity strain along quantum evolution paths is proportional to ∫ ΔH dt (Anandan-Aharonov).
- The temporal ordering from Theorem 1 is the parameter against which this arc length is integrated.

**Conditionally established (conjectured pending gap closure):**
- Lorentzian signature: one negative eigenvalue in the temporal direction (Gap 1a -- Route 1 program requires Conjecture 2 and Axiom A5; not closed).
- Temporal ordering embeds in ℝ with standard measure (Gap 1b -- R1 argued from A's continuity; R2 replaced by Debreu-Nachbin; reduces to Open Problem 2).
- Identity strain arc length connects to energy via Stage 2's variational argument (Gap 1c).

**Residual gaps within Stage 1:**

| Gap | Description | Status |
|---|---|---|
| Gap 1b | Temporal embedding: R1 (density) argued from A's continuity; R2 replaced by Debreu-Nachbin + UNS totality; reduces to Open Problem 2 | Substantially argued -- residual is A's continuity (Problem 2) |
| Gap 1a: Conjecture 2 | Convexity of C_p: local closure of co-instantiation-preserving directions | Open -- decisive hinge of Route 1 |
| Gap 1a: Axiom A5 | One temporal dimension: codimension-1 spatial complement | Axiomatized -- not derived |
| Gap 1c | Connect ∫ ΔH dt to ⟨H⟩ via eigenstates | Open -- bridges Stage 1 to Stage 2 |

Stage 1 is well-framed and more advanced than the prior formulation. Gap 1b is substantially argued -- it reduces to Open Problem 2's continuity of A via R1 (argued) and the Debreu-Nachbin theorem replacing R2. Conjecture 2 is argued for single-system configurations pending the local fiber structure of A_Omega, which itself reduces to Problem 2 via UNS system-indexing. The decisive remaining blocker is therefore Open Problem 2, not Gap 1b as an independent obstacle. Axiom A5 remains an explicit postulate. Stage 1 closes when Problem 2 closes (carrying Gap 1b and Conjecture 2 with it) and when A5 is either derived or accepted as a structural axiom.

---

## Stage 2: Variational Structure -- Worked Argument

**Target:** show that admissible dynamics on A_Omega extremize the accumulated identity strain S_ε[γ].

**Starting point:** S_ε[γ] = ∫ √(gᵢⱼ γ'ⁱ γ'ʲ) dt is the arc-length functional in the Fubini-Study metric. Extremizing arc length gives geodesics in CP(H). In quantum mechanics, geodesics of the Fubini-Study metric correspond to unitary evolution under a time-independent Hamiltonian (Anandan 1991; Anandan and Aharonov 1990). That is an established external result -- what LRT needs to contribute is the argument that A's actualization criterion selects the geodesic path rather than an arbitrary path through eigenspace sequences.

---

### Gap 2: A's Actualization Criterion = Fubini-Study Geodesic Selection

**2.1 The selection problem stated precisely.**

From Problem 2 (argued): A's actualization regions are projection-lattice elements of P(H). Γ_{A_Omega} is a sequence of definite eigenstates -- a path through the eigenspaces of P(H) indexed by the temporal ordering from Stage 1.

The selection problem: there are many possible sequences of eigenspaces A could in principle trace. A path γ : [t_0, t_1] → CP(H) through the eigenstate domain is any continuous map with γ(t) a definite eigenstate at each t (on the actualized trajectory). The Fubini-Study metric assigns each such path an arc length S_ε[γ]. The geodesic is the path of minimal arc length connecting any two points.

**The Gap 2 claim:** A selects the geodesic. Actualized trajectories Γ_{A_Omega} extremize S_ε.

**2.2 The geodesic selection argument -- fortified.**

The original §2.2 argument invoked Identity minimality (P1) and noted its compatibility with UNS uniqueness (P2). On closer examination, the resolution of the P1/P2 gap was asserted rather than argued: it claimed UNS selects the minimum-strain successor without showing that UNS's logical uniqueness and Identity's strain minimization pick the same successor. This is the vulnerability. The fortification bypasses it.

**Repair: UNS + continuity + G-symmetry → Hamiltonian flow → geodesic.**

*Step R1 (UNS gives a unique discrete sequence):* The UNS theorem establishes that for each L₃-complete state c_n ∈ 𝒜, there is exactly one L₃-admissible successor c_{n+1}. This is a discrete statement: it gives a sequence, not a flow.

*Step R2 (Continuity of A gives a differentiable trajectory):* From Problem 2 (argued): A is continuous on its domain Γ_{A_Omega}. The Debreu-Nachbin embedding (Gap 1b) gives a continuous temporal parameter t : Γ_{A_Omega} → ℝ. Together, these give Γ_{A_Omega} the structure of a continuous curve γ : ℝ → CP(H). Differentiability follows from the Hilbert space structure: CP(H) is a smooth manifold and A's actualization regions are projection-lattice elements, which are smooth submanifolds. A continuous curve through smooth submanifolds of CP(H) is piecewise smooth and, under the UNS uniqueness condition, smooth at every non-exceptional point.

*Step R3 (The curve has a unique tangent vector at each point):* UNS gives uniqueness of successor at each step. In the continuous limit, this means the tangent vector γ̇(t) is uniquely determined at each t by the UNS condition applied to γ(t). Γ_{A_Omega} therefore defines a vector field V on CP(H) such that γ̇(t) = V(γ(t)) for all t on the trajectory.

*Step R4 (G-equivariance from A3b -- CBP):*

The original formulation grounded G-equivariance in "Identity's basis-independence requirement: A cannot single out G-related states since they are operationally indistinguishable." This requires correction on two counts.

First, G-related states are generally not operationally indistinguishable. G acts transitively on pure states (Technical Foundations Lemma 3.2, from A3a + A3b): any pure state can be taken to any other by some g ∈ G. Two states related by g ∈ G have D(s₁, s₂) > 0 in general -- they are fully distinguishable. The "indistinguishable" framing was wrong.

Second, the correct axiom is not Identity but **A3b (CBP -- information preservation)**. A3b requires that reversible transformations preserve the structure of actualized trajectories: if trajectory γ is L₃-admissible, then g·γ must also be L₃-admissible for any g ∈ G, since g is a reversible transformation and CBP requires information preservation under reversible dynamics. The class of actualized trajectories is therefore closed under G.

This closure condition forces V to be G-equivariant:

    V(g·p) = dg_p · V(p)    for all g ∈ G, p ∈ CP(H)

If V were not G-equivariant, then for some g ∈ G the trajectory starting from g·p with tangent dg_p · V(p) would not be the actualized trajectory from g·p -- contradicting closure of actualized trajectories under G.

A G-equivariant smooth vector field on CP(H) is generated by an element of the Lie algebra of G (Technical Foundations Lemma 3.2: G is the compact Lie group U(n) under A3a + A3b + A3c via Masanes-Müller). The Lie algebra of U(n) consists of skew-Hermitian operators iH where H is Hermitian. The corresponding flow is:

    γ(t) = e^{-iHt/ℏ}|ψ_0⟩    projected to CP(H)

This is the Hamiltonian flow. By Anandan (1991), this flow traces Fubini-Study geodesics.

**Axiom grounding for R4:** G-equivariance follows from A3b (CBP) via closure of actualized trajectories under G. The Lie algebra identification follows from Lemma 3.2 (A3a + A3b → compact Lie group G) and the Masanes-Müller reconstruction (A3a + A3b + A3c → G = U(n)). No axiom beyond A1-A5 is required.

*Step R5 (Conclusion):* UNS (uniqueness) + continuity of A (smoothness) + A3b-grounded G-equivariance → Hamiltonian flow → Fubini-Study geodesic.

**What happened to the Identity minimality premise (P1)?**

P1 is not wrong -- it is simply not load-bearing. The UNS-selected trajectory being minimum-strain is a corollary of the Hamiltonian flow being geodesic, not an independent premise. P1 is retained as physical motivation.

*Epistemic status of §2.2 (fortified):* argued. The chain is: UNS uniqueness → unique vector field → A3b (CBP) forces G-equivariance → skew-Hermitian generator → Hamiltonian flow (Anandan 1991) → geodesic. Each link is traced to specific axioms. R4 is grounded in A3b, not in Identity -- a verifiable axiom-level claim rather than a philosophical one.

**Remaining question: does G-equivariance force a single H?**

For time-homogeneous (free) evolution: yes. G-equivariance + time-homogeneity forces a single fixed skew-Hermitian generator. For time-inhomogeneous evolution (H(t)), the generator varies along the trajectory -- this is the cosmological setting of Stage 4, handled there separately.

**2.3 Formalization: the variational condition.**

The condition "change only as much as L₃ forces" can be stated as a variational principle:

    δS_ε[γ] = 0

where S_ε[γ] = ∫_{t_0}^{t_1} √(gᵢⱼ γ'ⁱ γ'ʲ) dt and the variation is over paths γ with fixed endpoints.

The Euler-Lagrange equations for this functional are the geodesic equations in the Fubini-Study metric:

    d²γᵏ/dt² + Γᵏᵢⱼ (dγⁱ/dt)(dγʲ/dt) = 0

where Γᵏᵢⱼ are the Christoffel symbols of the Fubini-Study metric.

By the Anandan (1991) result: solutions to this equation in CP(H) are exactly the orbits of unitary evolution under a time-independent Hamiltonian H. The orbit γ(t) = e^{-iHt/ℏ}|ψ_0⟩ projected to CP(H) is a Fubini-Study geodesic.

**Gap 2 result:** A's actualization criterion, as the UNS-determined sequence of L₃-admissible successors traced by the Identity-minimality condition, selects paths that satisfy the geodesic equation in CP(H). By Anandan (1991), these paths are orbits of Hamiltonian evolution. Therefore:

    Actualized trajectories Γ_{A_Omega} = Fubini-Study geodesics = Hamiltonian orbits on CP(H).

*Epistemic status:* argued (fortified). The chain is: UNS uniqueness → unique vector field → A3b (CBP) forces G-equivariance → skew-Hermitian generator → Hamiltonian flow → Anandan (1991) → geodesic. R4 is now traced to A3b, not to Identity -- an axiom-level grounding that a reviewer can verify against the Technical Foundations document. The Identity minimality/UNS compatibility gap is resolved; the prior G-related-states indistinguishability error is corrected.

**Gap 1c closes here.** Gap 1c asked: how does ∫ΔH dt connect to ⟨H⟩? On a geodesic, the Anandan-Aharonov relation gives S_ε = (1/ℏ)∫ΔH dt. For a Hamiltonian eigenstate, ΔH = 0 and the geodesic is a phase rotation -- zero arc length in CP(H) (it stays at the same point). For a superposition of eigenstates, ΔH > 0 and the geodesic has positive arc length. The expectation value ⟨H⟩ governs the phase accumulation rate along the geodesic: iℏ d|ψ⟩/dt = H|ψ⟩ gives phase rate proportional to ⟨H⟩ for a state evolving under H. Gap 1c closes as a consequence of Gap 2: once the geodesic selection is established, the connection from ΔH to ⟨H⟩ follows from the Schrödinger equation that the geodesic condition entails.

---

### Gap 2 Updated Status

| Sub-claim | Status |
|---|---|
| Fubini-Study geodesics = Schrödinger orbits | Established (Anandan 1991) |
| Fubini-Study metric = identity strain metric | Argued (Technical Foundations §3.3 + quadratic identity strain + Masanes-Müller) |
| UNS → unique tangent vector field on trajectory | Argued (R1-R3) |
| Trajectory vector field is G-equivariant | Argued -- from A3b (CBP): closure of actualized trajectories under reversible transformations forces G-equivariance (R4); axiom-grounded |
| G-equivariant vector field on CP(H) → skew-Hermitian generator | Established (Lie algebra of U(n); homogeneous space structure of CP(H)) |
| Skew-Hermitian generator → Hamiltonian flow → geodesic | Established (Anandan 1991) |
| Identity minimality (P1) | Retained as motivation; now a corollary of geodesic = Hamiltonian, not a premise |
| Gap 2 overall: A = geodesic selector | Argued (fortified) |
| Gap 1c: ∫ΔH dt → ⟨H⟩ | Argued -- closes as consequence of Gap 2 |

---

## Stage 3: A-Hamiltonian Identification -- Worked Argument

**Target:** identify A with H = iℏ ∂/∂t acting as generator of geodesic flow on CP(H).

**Input from Stage 2:** actualized trajectories Γ_{A_Omega} are Fubini-Study geodesics. By the Anandan (1991) result, these geodesics are orbits of Hamiltonian evolution: γ(t) = e^{-iHt/ℏ}|ψ_0⟩ projected to CP(H). Stage 3 asks: what is H in LRT's terms?

---

### The A-H Identification

**3.1 H as generator of A's temporal action.**

A operates through the temporal dimension to produce Γ_{A_Omega}: the sequence of L₃-admissible successors indexed by temporal ordering. At each infinitesimal step dt, A selects the next configuration. The operator that generates this step -- that maps the current configuration to the next one as a function of dt -- is, in the language of quantum mechanics, the Hamiltonian.

More precisely: the geodesic flow on CP(H) is generated by a one-parameter group of unitary operators U(t) = e^{-iHt/ℏ}. A's temporal action is the selector of the trajectory traced by this flow. A does not generate the flow -- H does. A selects which trajectory (which geodesic, starting from which initial condition) is actualized.

The identification: **H is the infinitesimal generator of the unitary flow that A's actualization criterion selects.** A selects a geodesic; H generates the flow along that geodesic. A and H describe different aspects of the same structure:

- A describes selection: which configurations are actualized (binary, at each time step)
- H describes generation: how the actualized trajectory evolves infinitesimally (differential, continuous)

The identification A ≡ H (in the original framing) is therefore imprecise. The correct formulation: A's actualization criterion, applied to the temporal dimension, selects a geodesic whose generator is H. H is A's temporal action expressed as a differential operator.

*Epistemic status of §3.1:* argued. This is a conceptual refinement of the original identification, not a proof that H has a specific spectrum or commutation relations. Those follow from the Hilbert space structure already established (Masanes-Müller reconstruction chain).

**3.2 The Schrödinger equation as consequence.**

From the geodesic condition (Gap 2): Γ_{A_Omega} satisfies the geodesic equations in CP(H). By Anandan (1991): the lift of a Fubini-Study geodesic to H satisfies the Schrödinger equation:

    iℏ d|ψ(t)⟩/dt = H|ψ(t)⟩

where H is the self-adjoint generator of the U(t) group.

This is not an assumption -- it is a consequence of (a) the geodesic selection (Gap 2, argued) and (b) the Hilbert space structure (Masanes-Müller, argued). The Schrödinger equation is the differential form of the geodesic condition, once the geodesic is lifted from CP(H) to H.

**The Schrödinger equation is therefore argued as a consequence of LRT's architecture**, not as an external postulate. Epistemic status: argued, conditional on Gap 2's weakest link (the §2.2 identification of Identity minimality with local geodesic condition).

---

### Gap 3: Path Coherence

**3.3 The path coherence problem.**

Geodesics in CP(H) are not globally unique: two distinct geodesics starting from different initial conditions can intersect. When two geodesics cross, A's actualization criterion must select one consistently -- it cannot jump from the geodesic it was tracing to the intersecting one. If A were to jump, the actualized trajectory would not correspond to evolution under a single consistent Hamiltonian H; it would be a piecewise evolution under different Hamiltonians spliced at the crossing point.

Gap 3 is the requirement that A is path-coherent: it commits to a single geodesic and does not jump at intersections.

**3.4 Path coherence -- fortified.**

The original §3.4 argument invoked tangent-vector inclusion in I∞: two states at the same CP(H) point but different momenta are distinct configurations in I∞, giving distinct UNS successors, preventing geodesic jumping. This argument was flagged as requiring verification against the Technical Foundations axiom set.

On closer examination, the argument has a structural problem. LRT's I∞ is identified with CP(H) via the Masanes-Müller reconstruction -- the configuration space of pure states. The distinguishability metric D is defined on CP(H), not on T(CP(H)) (the tangent bundle). Two states at the same CP(H) point with different tangent vectors are at the *same* point of I∞ as currently defined. They are not distinguishable configurations; they are the same configuration with different velocities. UNS, which operates on configurations, would then give the same successor from both -- which is precisely the crossing-point ambiguity rather than its resolution.

The tangent-vector argument therefore does not close Gap 3 as stated. It implicitly requires that I∞ is T(CP(H)) rather than CP(H). That is a non-trivial upgrade requiring either a new axiom or a derivation not yet in LRT's architecture.

**The correct resolution: path coherence from §2.2 G-equivariance.**

The fortified §2.2 argument already resolves the path-coherence problem, as a consequence rather than an additional result.

§2.2 showed: UNS + continuity of A + G-equivariance → the vector field on CP(H) is generated by a single fixed skew-Hermitian operator iH, where H ∈ Lie(U(n)) is a fixed Hermitian operator. The Hamiltonian flow is:

    γ(t) = e^{-iHt/ℏ}[ψ₀]    for all t

This is a one-parameter group action. One-parameter groups are globally determined by their generator H and their initial condition [ψ₀]. From any point [ψ] on the trajectory, the continuation is:

    γ(t + s) = e^{-iHs/ℏ}[ψ]

The operator H is the same at every point -- it is the fixed generator of the entire flow, not a locally-selected tangent direction. Two geodesics for the *same* H but different initial conditions [ψ₁] and [ψ₂] may intersect at some [χ] ∈ CP(H). At [χ], the continuation of *both* trajectories is e^{-iHs/ℏ}[χ] -- the same trajectory forward. There is no branching: the forward continuation from [χ] is uniquely determined by H, which is fixed by the G-equivariance argument.

The crossing-point ambiguity arises only if different parts of the trajectory could have *different* generators H₁ and H₂. But G-equivariance forces a single fixed generator for the entire trajectory. There is no room for generator-switching. Path coherence is therefore a consequence of §2.2, not an independent requirement.

**What happened to the tangent-vector claim?**

The claim that "L₃-complete state includes tangent vector" is not wrong as a physical statement -- it is a reasonable description of phase space in quantum mechanics. But it is not needed for path coherence. It is also not derivable within the current I∞ = CP(H) architecture without upgrading to a tangent-bundle formulation. The claim is therefore: (a) physically motivated, (b) structurally unsupported by current LRT axioms, (c) not needed for the argument.

It is retained in the document as a pointer toward a possible future development -- if LRT's configuration space is upgraded to the cotangent bundle T*(CP(H)) (the full quantum phase space), the tangent-vector argument would work directly. But that upgrade is not required for the current path-coherence result.

**The actual residual in Gap 3:**

The one remaining question is whether the G-equivariance argument covers the time-inhomogeneous case H(t). For free evolution (Stage 3), H is constant and the one-parameter group argument applies in full. For driven evolution (Stage 4, cosmological H(t)), the generator varies along the trajectory. In that case path coherence must be argued separately. Stage 4 handles the H(t) case explicitly; the Gap 3 path-coherence result is restricted to free evolution.

*Epistemic status of §3.4 (fortified):* argued. Path coherence follows from the G-equivariance argument in §2.2. The tangent-vector claim is demoted from load-bearing to motivational. The I∞ = CP(H) vs T(CP(H)) tension is acknowledged and parked as a potential future development, not a current gap. The residual -- time-inhomogeneous path coherence -- is handled in Stage 4.

**3.5 Hamiltonian uniqueness.**

Given path coherence: A selects a single globally consistent geodesic. The generator of that geodesic is a single self-adjoint operator H on H. H is uniquely determined by the initial data (initial configuration and tangent vector) up to:

(a) Unitary equivalence: H and UHU† generate the same geodesic flow for any unitary U (they correspond to different orthonormal bases for the same evolution).

(b) The addition of multiples of the identity I: H and H + cI generate geodesics that differ only by an overall phase, which does not affect any CP(H) observable.

These are the standard gauge freedoms of quantum mechanics -- the choice of basis and the choice of energy zero-point. They are not indeterminacies in LRT's identification; they are the expected structure.

**Gap 3 result:** A selects a path-coherent geodesic in CP(H). Path coherence follows from the G-equivariance argument (§2.2) applied to the fixed generator H -- not from tangent-vector inclusion in I∞ (which was the prior argument and is now demoted). The generator H is uniquely determined by the initial data and the G-equivariance condition, up to unitary equivalence and energy zero-point. The Schrödinger equation iℏ d|ψ⟩/dt = H|ψ⟩ follows.

*Epistemic status of Gap 3:* argued (fortified). Path coherence derives from §2.2's G-equivariance, not from the tangent-vector claim. The tangent-vector argument was structurally unsupported within I∞ = CP(H); its demotion removes a vulnerability while the path-coherence result is preserved via the stronger §2.2 derivation. The residual -- time-inhomogeneous path coherence for H(t) -- is handled in Stage 4.

**Stage 3 updated status:** A's temporal action = H's geodesic generation, argued. Schrödinger equation derived as consequence, argued. Path coherence argued via §2.2 G-equivariance -- tangent-vector inclusion claim demoted from load-bearing to motivational; I∞ = CP(H) vs T(CP(H)) tension acknowledged, parked as future development. Time-inhomogeneous path coherence deferred to Stage 4.

---

## Stage 4: Energy Conservation via Noether -- Worked Argument

**Target:** derive energy conservation from time-translation symmetry of A_Omega, use as consistency test on Stage 3, and connect the approximate conservation rate to FC-1's dark energy density.

**Input from Stage 3:** actualized trajectories Γ_{A_Omega} are orbits of a self-adjoint Hamiltonian H on H. The Schrödinger equation iℏ d|ψ⟩/dt = H|ψ⟩ holds. H is the generator of geodesic flow on CP(H), identified as A's temporal action.

---

### 4.0 Time-Inhomogeneous Path Coherence

**The deferred problem.** Stage 3's path coherence argument (via §2.2 G-equivariance) was restricted to time-independent H. For cosmological evolution, H varies with time: the Hubble parameter H(t) feeds into A_Omega's temporal metric, breaking time-translation symmetry. Stage 3 explicitly deferred path coherence for H(t) to Stage 4. This section closes that deferral.

**The problem precisely.** For constant H, path coherence followed from G-equivariance (A3b) forcing a single fixed Lie algebra generator. A one-parameter group with fixed generator never branches: from any point, the forward direction is uniquely determined by H. For H(t), the generator varies with t. The evolution operator is the time-ordered exponential T exp(-i∫H(t')dt'/ℏ) -- not a one-parameter group. The G-equivariance argument does not directly give a single fixed generator, so path coherence requires separate treatment.

**The argument.**

G-equivariance (from A3b) applies pointwise at each t: at each instant, the vector field V(t) on CP(H) is G-equivariant and therefore generated by some H(t) ∈ Lie(U(n)). The actualized trajectory satisfies the time-dependent Schrödinger equation:

    iℏ d|ψ(t)⟩/dt = H(t)|ψ(t)⟩

This is an ODE on H with time-varying coefficients. By the Picard-Lindelöf existence and uniqueness theorem: if H(t) is locally Lipschitz in t (equivalently, if H(t) is continuously differentiable in t), then for any initial condition |ψ₀⟩, there exists a unique solution |ψ(t)⟩ on [0, T] for some T > 0. Under the regularity conditions standard for FRW cosmology (H(t) smooth away from the Big Bang singularity), the solution is global.

UNS provides the initial condition |ψ₀⟩. Picard-Lindelöf provides the unique forward continuation. Path coherence holds: A follows the unique integral curve of {H(t)} from |ψ₀⟩. No branching occurs.

**Why branching cannot occur for H(t).** Two trajectories with different initial conditions [ψ₀] and [φ₀] but the same cosmological H(t) are:

    γ_ψ(t) = T exp(-i∫₀ᵗ H(t')dt'/ℏ) |ψ₀⟩
    γ_φ(t) = T exp(-i∫₀ᵗ H(t')dt'/ℏ) |φ₀⟩

These may intersect at some [χ] ∈ CP(H). At the crossing point, both trajectories proceed forward under the same H(t) -- which is determined by the cosmological background, not by the state. The forward direction from [χ] is uniquely H(t)-prescribed. There is no branching ambiguity; the crossing point does not create a choice.

This is structurally simpler than the constant-H case: H(t) is externally prescribed by the cosmological background. A does not select H(t); H(t) is a consequence of A_Omega's temporal metric evolution under the cosmological dynamics. Path coherence for H(t) is the statement that A follows this externally prescribed evolution from its UNS-determined initial condition -- which is immediate from ODE uniqueness.

**Regularity condition.** The argument requires H(t) to be locally Lipschitz in t. For standard FRW cosmology, H(t) is smooth and H_dot is bounded for t > t_Planck (away from the Planck epoch). This is a standard cosmological regularity assumption, not an LRT-specific gap. At the Planck epoch, the semiclassical approximation underlying the FRW metric breaks down independently; LRT makes no claims in that regime.

*Epistemic status of §4.0:* argued. Time-inhomogeneous path coherence follows from G-equivariance applied pointwise (A3b → H(t) ∈ Lie(U(n)) at each t) combined with ODE uniqueness (Picard-Lindelöf). The standard cosmological regularity condition (H(t) smooth for t > t_Planck) is the only residual, and it is not LRT-specific.

---

### 4.1 Noether's Theorem Applied to A_Omega

**The symmetry.** If the Lagrangian L governing Γ_{A_Omega} is invariant under t → t + δt (time translation), Noether's theorem yields a conserved charge. For the arc-length Lagrangian L = √(gᵢⱼ γ'ⁱ γ'ʲ) on CP(H), the conserved charge associated with time-translation symmetry is the energy -- specifically, the expectation value ⟨H⟩ along the geodesic.

This is the standard result in Lagrangian mechanics: time-translation invariance of the Lagrangian → conservation of the Hamiltonian (energy). For the Fubini-Study arc-length Lagrangian, time-translation invariance holds when H is time-independent -- when the geodesic is generated by a constant self-adjoint operator. In that case, ⟨H⟩ is conserved: d⟨H⟩/dt = 0.

*Epistemic status:* established (standard Noether theorem applied to the Fubini-Study geodesic Lagrangian; no new LRT content required here).

**Consistency test.** Stage 3 identifies H as the generator of A's geodesic flow. Stage 4's Noether result says the conserved charge of that flow is ⟨H⟩. This is exactly energy conservation -- ⟨H⟩ is the expectation value of the Hamiltonian, which does not change under Schrödinger evolution with a time-independent H. The consistency test passes: Stage 3's identification is compatible with Noether conservation.

---

### 4.2 The Cosmological Symmetry Breaking

**Why exact conservation fails cosmologically.** In the cosmological setting, A_Omega is not time-translation invariant. The Hubble parameter H(t) -- the expansion rate of the universe -- varies with time: H_dot ≠ 0. The arc-length Lagrangian depends on the metric gᵢⱼ, which in the cosmological setting is a function of both the CP(H) configuration and the cosmological time (through the expanding geometry). Time-translation is broken.

When time-translation symmetry is broken, the Noether charge (energy) is not conserved. The rate of non-conservation is:

    d⟨H⟩/dt = ∂L/∂t |_{explicit}

where the explicit time dependence comes from the cosmological evolution of the background geometry -- specifically, from H(t)'s variation.

**The rate of non-conservation is the dark energy source.** In LRT's FC-1 framework, the dark energy density ρ_act arises from the energy cost of maintaining global logical consistency across A_Omega's horizon identity network as it evolves cosmologically. The non-conservation rate of the Noether charge is exactly this cost: it is the rate at which energy is "injected" into the consistency maintenance of the actualization process by the changing cosmological background.

---

### 4.3 Connection to FC-1 -- Honest Scope

**What Stage 4 establishes and what remains open.**

Stage 4 establishes: (a) exact Noether conservation holds for time-independent H; (b) cosmological time variation of H breaks time-translation symmetry; (c) the rate of Noether charge non-conservation is the explicit time-derivative of the Lagrangian, which is determined by H_dot(t).

The connection to FC-1's specific density formula ρ_act = (β · ℏ · H²) / (l_P² · c³) · ln(c/H·l_P) requires two additional steps that Stage 4 does not close:

*Step I (Gap A in FC-1):* derive β from the topology of the percolated logical-identity network. β is the fraction of horizon nodes requiring global reconciliation per Hubble time. This requires a theorem about consistency-reconciliation statistics in constraint graphs near the percolation threshold. Stage 4's Noether framework gives the energy accounting structure (non-conservation rate = consistency overhead cost), but does not quantify β. Gap A remains open.

*Step II (Gap B in FC-1):* embed the energy non-conservation rate covariantly as a stress-energy tensor component in curved spacetime. Gap B as stated in FC-1 conflates two distinct requirements:

**Claim B1 (FRW covariance -- substantially argued):** ρ_act is a valid covariant energy density in FRW cosmology. ρ_act = β·ℏ·H²/(l_P²·c³) is a scalar under FRW coordinate transformations (H is a well-defined FRW scalar). The continuity equation holds for ρ_act ∝ H² by internal consistency of the Friedmann system. The equation of state w_act(z) follows from Requirements 1-2 plus the standard slow-roll relation. Claim B1 is substantially argued and is sufficient for FC-1's falsifiability criterion.

**Claim B2 (full GR embedding -- genuinely open):** ρ_act is covariantly embeddable in the Einstein equations for arbitrary spacetimes, without new dynamical degrees of freedom. This requires a local definition of the reconciliation flux valid for any causal horizon (not just the global Hubble horizon), and recovery of the logarithmic factor from local scale integration. The Jacobson-Padmanabhan framework targets Claim B2. A dimensional check reveals that the simple insertion of ρ_act into the Clausius relation does not work (ρ_act·c·A_H ≠ δQ/dt from the standard Clausius calculation), so Steps 3-4 of the A.6 program require genuine local reformulation of the reconciliation flux. Claim B2 remains open.

FC-1's falsifiability criterion requires only Claim B1. Claim B2 is a long-range theoretical target. See the Gap B Analysis note for the full argument.

**What Stage 4 does connect:**

The scaling class of ρ_act is established by Stage 4's framework without closing Gaps A or B:

From the Noether non-conservation rate:

    d⟨H⟩/dt ~ H_dot · (⟨H⟩ / H)

The Hubble rate H has dimensions of inverse time; ⟨H⟩ is an energy. The natural energy associated with the Hubble timescale is ℏH (quantum of energy at the Hubble frequency). The natural energy density at the Hubble horizon is:

    ρ ~ ℏH · N_horizon / V_horizon ~ ℏH · (R_H/l_P)² / R_H³ ~ ℏH² / (l_P² · c)

Using l_P² = ℏG/c³:

    ρ ~ H²/G

This is the Tier 1 result of FC-1's Appendix A -- the H²/G scaling class established from horizon area scaling and the Hubble timescale. **Stage 4's Noether framework independently reproduces Tier 1** from the energy non-conservation rate, without invoking the horizon information argument explicitly. The two routes agree on the scaling class, which is a genuine consistency check.

The w(z) prediction w_act(z) = -1 + Ω_m(z) follows from this scaling class alone, independent of β and insensitive to the logarithmic factor (as FC-1 Appendix A.4 establishes). Therefore: **the w(z) prediction is supported by Stage 4's Noether framework to the extent that the H²/G scaling class is correct.**

*Epistemic status of §4.3:* the scaling class connection is argued. The w(z) derivation from that scaling class is established (FC-1 Appendix A.4, via the continuity equation). The specific density formula requires Gaps A and B, which remain open.

---

### 4.4 Stage 4 Result

**What Stage 4 delivers:**

(a) *Consistency test passed:* Noether conservation for time-independent H is consistent with Stage 3's identification. ⟨H⟩ is the conserved charge; this is energy conservation in the standard quantum mechanical sense. ✓

(b) *Cosmological symmetry breaking identified:* H_dot ≠ 0 breaks time-translation symmetry; the Noether charge non-conservation rate is the explicit time derivative of the Lagrangian, determined by H_dot(t). ✓

(c) *Scaling class reproduced:* the Noether non-conservation framework gives ρ ~ H²/G independently of the horizon-information argument, agreeing with FC-1 Tier 1. ✓

(d) *w(z) prediction supported at scaling-class level:* w_act(z) = -1 + Ω_m(z) follows from the H²/G scaling class (FC-1 Appendix A.4 derivation). ✓ (to this level)

(e) *β and covariant embedding remain open:* Gap A (β from network topology) and Gap B (covariant stress-energy embedding) are the residual gaps. ○

**Stage 4 epistemic status:** argued at the scaling class level. The consistency test passes. The w(z) prediction is supported. The density magnitude and covariant embedding require Gaps A and B, which are the two documented open problems in FC-1.

**Gap 4 updated status:** substantially argued. The "approximate Noether conservation = FC-1 dark energy density" connection holds at the scaling class level (H²/G) and gives the w(z) prediction. The precise density formula requires Gaps A and B. Gap 4 is not fully closed but is no longer an independent gap -- it reduces to FC-1's documented Gaps A and B.

---

## Gap Register

| Gap | Description | Stage | Status |
|---|---|---|---|
| Gap 1b | Temporal embedding: R1 from A's continuity (argued); R2 replaced by Debreu-Nachbin + UNS; reduces to Problem 2 | 1 | Substantially argued -- residual is Problem 2 (now argued) |
| Gap 1a R1: Conjecture 2 | Convexity of C_p: co-instantiation closed under positive linear combination | 1 | Argued -- fiber structure established via L₃-completeness + Anti-Holism + system-indexing; all three conditions (a)(b)(c) argued; weakest link is Premise 2 (system-indexing constitutive of L₃-completeness) |
| Gap 1a R1: Axiom A5 | One time dimension from L₃ uniqueness of ordering relation | 1 | Axiomatized with motivated justification -- explicit postulate, not a gap |
| Gap 1a R2 | Ξ constraint term derived from LRT axioms; negativity of Q on T_seq proved | 1 | Open -- Route 2 reinforcement; Gap 2 closed independently so no longer a primary blocker |
| Gap 1c | ∫ ΔH dt → ⟨H⟩ via geodesic extremization | 1-2 bridge | Argued -- closes as consequence of Gap 2 (geodesic condition entails Schrödinger equation; ⟨H⟩ governs phase rate along geodesic) |
| Gap 2 | A's actualization criterion = Fubini-Study geodesic selection | 2 | Argued -- L₃ Identity → minimum strain → local geodesic → Anandan (1991) → Hamiltonian evolution; weakest link identified and defended |
| Gap 3 | A selects path-coherent geodesic in CP(H) | 3 | Argued (fortified) -- path coherence from §2.2 G-equivariance (A3b); tangent-vector claim demoted; time-inhomogeneous case closed in §4.0 via Picard-Lindelöf + pointwise G-equivariance |
| Gap 4 | Approximate Noether conservation = FC-1 dark energy density | 4 | Substantially argued -- H²/G scaling class reproduced; w(z) supported at scaling level; Gap A (β) open; Gap B split: Claim B1 (FRW covariance) substantially argued and sufficient for FC-1; Claim B2 (full GR embedding) genuinely open as long-range target |

---

## Dependency Structure

```
Gap 1b (A_Omega is smooth manifold) ─────────────────────────┐
                                                               │
Theorem 1 (ordinal ordering) ──────────────────────────────── ►──► Route 1: Cone field
Quad. identity strain (gᵢⱼ = Fubini-Study) ────────────────────►   (Lemmas 1-3 + A5)
                                                                        │
                                                              Lorentzian signature theorem
                                                                        │
Route 2: Admissibility action A[γ] ────────────────────────────►──── ds² = -dt² + gᵢⱼdxⁱdxʲ
         Hessian Q has (-,+,...,+) signature ──────────────────►   (dynamical confirmation)
                                                                        │
Anandan-Aharonov: S_ε = (1/ℏ)∫ΔH dt ──────────────────────────────────►
                                                                        │
                                                                   Stage 1 CLOSED
                                                                        │
                                                                        ▼
                                                              Stage 2: variational structure
                                                              Gap 2: A = geodesic selector
                                                              (Ξ from Route 2 feeds here)
                                                                        │
                                                                        ▼
                                                              Stage 3: A = H identification
                                                              Gap 3: path coherence
                                                                        │
                                                                        ▼
                                                              Stage 4: Noether → FC-1
                                                              Gap 4: dark energy density
                                                                        │
                                                                        ▼
                                                              Gap B: Einstein equations
```

Open Problem 2 feeds into Stage 2 at the measure-theoretic level (integration over CP(H) requires the projection-lattice sigma-algebra). Route 2's Ξ term, once derived, becomes the Lagrangian for Stage 2 -- the two gaps reinforce each other.

---

## Connection to Gap B

With all four stages closed, the energy-action identification gives Jacobson's Clausius relation its LRT content: the energy flux δQ is A's actualization operation through the horizon's temporal dimension, measured in units of ℏH. Inserting this into Jacobson's derivation yields Einstein's field equations as a consequence of A's geodesic action on A_Omega's horizon structure. That is the refactoring claim.

---

## What Success Would Not Yet Establish

Completion of all four stages establishes: energy as a derived quantity, the Schrödinger equation as a corollary, energy conservation as a theorem (approximate under cosmological expansion, with the non-conservation rate being the FC-1 dark energy density), and the Gap B route as formally open.

It does not establish: Newton's G, the equivalence principle, the full T_μν, or the complete Einstein field equations. Those require the full Gap B calculation.

---

## Epistemic Status Summary

| Claim | Status |
|---|---|
| Temporal ordering ordinal (Theorem 1) | Argued |
| Lorentzian signature via Theorem 2 | Superseded -- heuristic only; replaced by Routes 1/2 |
| Identity strain metric gᵢⱼ on C is Riemannian | Argued |
| gᵢⱼ = Fubini-Study metric after Hilbert space reconstruction | Argued |
| Accumulated identity strain = (1/ℏ) ∫ ΔH dt (Anandan-Aharonov) | Established -- external theorem applied |
| A_Omega temporal embedding (Gap 1b) | Substantially argued -- R1 from A's continuity (Problem 2, argued); R2 replaced by Debreu-Nachbin |
| Route 1 Lemma 1: openness of C_p | Argued conditional on Gap 1b |
| Route 1 Conjecture 2: convexity of C_p | Argued -- fiber structure via L₃-completeness + Anti-Holism; all three conditions (a)(b)(c) argued; weakest link is Premise 2 |
| Route 1 Lemma 3: sharpness of C_p | Argued -- from acyclicity of admissibility order |
| Route 1 Axiom A5: one time dimension | Explicit postulate with L₃ uniqueness motivation |
| Route 1 cone-to-metric theorem | Established externally (Malament 1977; Minguzzi-Sanchez 2008) |
| Gap 1a overall: Lorentzian signature | Argued -- Route 1 complete except A5 (axiom); Route 2 reinforcement pending Ξ |
| Route 2 Ξ term derived from LRT axioms | Open -- reinforcement target; not a primary blocker |
| Route 2 Hessian has (-,+,...,+) signature | Conjectured -- conditional on Ξ |
| Stage 1 overall: temporal metric established | Argued -- all major gaps argued; A5 explicit axiom; Ξ open reinforcement |
| Admissible dynamics = Fubini-Study geodesics (Gap 2) | Argued -- L₃ Identity → minimum strain → geodesic → Anandan (1991) |
| Gap 1c: ∫ ΔH dt → ⟨H⟩ | Argued -- closes as Gap 2 corollary |
| A's temporal action = H generating geodesic flow (Gap 3) | Argued -- path coherence via UNS + tangent bundle; Schrödinger equation as consequence |
| Approximate Noether conservation = FC-1 dark energy (Gap 4) | Argued at scaling class level -- H²/G reproduced; w(z) supported; magnitude requires FC-1 Gaps A/B |
| Einstein equations via Jacobson from A | Open -- conditional on FC-1 Gap B (covariant embedding) |

---

## Immediate Next Actions

The derivation chain from L₃ to Schrödinger is argued end-to-end. All primary gaps are argued. The remaining open items are:

**Route 2 Ξ term (reinforcement):** the Route 1 geodesic argument (Gap 2) now stands independently. Route 2 is a reinforcement route -- deriving Ξ closes the dynamical confirmation of Lorentzian signature and completes the variational architecture. It is no longer a primary blocker but remains the highest-value open derivation within the energy-action problem.

**Axiom A5 (one time dimension):** explicitly postulated with L₃ uniqueness motivation. An argument that L₃'s ordering relation admits exactly one temporal direction (rather than being an explicit postulate) would upgrade A5 from axiom to theorem. This is a long-range target.

**FC-1 Gap A (β coefficient):** derive the duty-cycle fraction β from the topology of the percolated logical-identity network. Independent of the w(z) prediction, which does not require β.

**FC-1 Gap B (covariant embedding):** embed the Noether non-conservation rate as a covariant stress-energy tensor component in curved spacetime via Jacobson/Padmanabhan. This is the route to Einstein's field equations.

**Tangent-vector inclusion verification:** confirm that LRT's existing Technical Foundations axiom set already entails that tangent vectors are part of the L₃-complete state specification (used in Gap 3's path coherence argument). Literature check against Technical Foundations axioms -- not a new derivation.
