# Logic Realism as a Philosophy of Science: The Logic-First Structure of Physical Theories

**Date:** 2025-12-17
**Status:** DRAFT (Revised per referee report)
**Author:** James D. Longmire
**ORCID:** 0009-0009-1383-7698

---

## Abstract

We present Logic Realism Theory (LRT) as a working physical theory with empirical content: LRT holds that the Three Fundamental Laws of Logic (Identity, Non-Contradiction, Excluded Middle) function as universal constraints on physically possible states. This claim is falsifiable—an observed violation of these laws in a completed measurement would refute it—yet no such violation has ever been recorded. We develop a systematic methodology for foundational analysis: a three-tier classification distinguishing structural assumptions for logical application (Tier 1, including a parsimony principle), established mathematical reconstruction results with tracked presuppositions (Tier 2), and physical principles (Tier 3). This framework clarifies presupposition dependencies in existing theories regardless of whether one accepts the stronger metaphysical thesis that 3FLL are constitutive of all possible worlds. We demonstrate the methodology through a case study deriving the action functional, with each step formally marked by tier and status. The fine structure constant is treated separately as a conjectural numerical illustration. We compare LRT with logical empiricism, Quine-Duhem underdetermination, Friedman's relativized a priori, and quantum reconstruction programs, and address objections from logical pluralism. The tier methodology constitutes a practical contribution to foundational physics independent of the metaphysical thesis.

**Keywords:** foundations of physics, logic realism, quantum reconstruction, presupposition tracking, falsifiability, constitutive principles

---

## 1. Introduction: Logic Realism as a Physical Theory

### 1.1 The Central Claim

Logic Realism Theory (LRT) makes a straightforward empirical claim: **the Three Fundamental Laws of Logic constrain what can physically occur, not merely what we can coherently say.**

The Three Fundamental Laws of Logic (3FLL):
- **Identity (L₁):** ∀A: A = A
- **Non-Contradiction (L₂):** ∀A: ¬(A ∧ ¬A)
- **Excluded Middle (L₃):** ∀A: A ∨ ¬A

**Empirical content:** LRT forbids observable violations of 3FLL in completed physical measurements. Specifically:
- No measurement outcome can be recorded as both P and ¬P simultaneously (L₂ violation).
- No measurement outcome can fail to be either P or ¬P (L₃ violation).
- No physical state can fail to be self-identical across a measurement interval (L₁ violation).

**Current status:** No violation of 3FLL has ever been observed in any completed physical measurement across all domains of physics—classical, quantum, relativistic, or cosmological. Every measurement record is Boolean: one outcome obtains, not a literal contradiction. Paraconsistent models remain formal exercises; no physical system realises them.

**Falsifiability:** LRT is falsifiable in principle. A recorded measurement outcome exhibiting P ∧ ¬P, or a physical state provably violating identity, would refute the theory. The absence of such observations over centuries of physics constitutes strong corroboration.

This empirical grounding distinguishes LRT from pure philosophical speculation about the metaphysics of logic.

### 1.2 Three Levels of the Thesis

To avoid conflating different claims, we distinguish three levels at which 3FLL might be "constitutive":

| Level | Claim | Status |
|-------|-------|--------|
| **Epistemic** | 3FLL are constraints on rational belief—what any coherent agent must accept | Widely accepted |
| **Semantic** | 3FLL are constraints on meaningful discourse—languages violating them cannot express determinate content | Stronger, contested |
| **Metaphysical** | 3FLL are constraints on reality itself—no possible world violates them | Strongest, research conjecture |

**What our arguments establish directly:** The self-refutation of denying 3FLL establishes the epistemic and semantic versions. To assert "Non-Contradiction is false" is to claim this assertion is true and not false—thereby presupposing Non-Contradiction.

**What requires additional argument:** The metaphysical version—that 3FLL hold in all possible worlds, not just as constraints on our reasoning—requires bridging from "we cannot coherently deny X" to "X holds mind-independently." We address this gap in Section 2.6.

**The fallback:** Even if only the weaker readings are accepted, the methodology (tier system) and empirical claim (no observed violations) remain valuable.

### 1.3 Scope and Structure

This paper:
1. Presents LRT's empirical status and falsifiability conditions (Section 1.1, 2.5)
2. Develops the tier methodology for presupposition tracking (Sections 2.1–2.4)
3. Addresses the epistemic-to-metaphysical gap (Section 2.6)
4. Compares with existing traditions and addresses objections (Section 3)
5. Demonstrates the methodology via formal case study (Section 4)
6. Discusses implications (Section 5)

**Primary contribution:** The tier methodology improves presupposition tracking in foundational physics regardless of one's stance on the metaphysical thesis.

---

## 2. The Logic-First Structure of Theories

### 2.1 3FLL as Framing Conditions

The Three Fundamental Laws of Logic have been recognised since Aristotle (*Metaphysics*, Book Γ) as foundational to rational thought. Our claim is that they also constrain physical possibility.

**The self-grounding argument:** These principles cannot be coherently denied because denial presupposes them:
- To argue against Excluded Middle requires distinguishing valid from invalid arguments—which presupposes that arguments either are or are not valid.
- To assert "Non-Contradiction is false" requires that this assertion be true and not false.
- To question Identity requires identifying what is being questioned.

This self-grounding character distinguishes 3FLL from ordinary physical laws, which can be coherently denied or modified (F = ma could have been F = ma²; Maxwell's equations could have differed).

**Consequence for physics:** Whatever physics we construct must respect 3FLL. This does not mean physics *reduces* to logic; it means physics operates within constraints set by logical coherence.

### 2.2 From Logic to Structure: The Derivation Cascade

If 3FLL constrain physical reality, certain structures follow. We trace a cascade of increasingly specific constraints:

```
3FLL (primitive, self-grounding)
  ↓ presuppose (see Definition 2.1)
Domain of discourse + Parsimony (Tier 1)
  ↓ enforce (Proposition 2.1)
Binary distinctions (A or ¬A for any property)
  ↓ require (Proposition 2.2)
Distinguishability metric
  ↓ constrain (via Tier 2 theorems)
Mathematical structures (Hilbert space, phase space)
  ↓ constrain
Physical structures (dynamics, conservation laws)
```

**Key point:** Each arrow represents a logical or mathematical relationship that must be made explicit. The tier system (Section 2.3) tracks which assumptions enter at each level.

### 2.3 The Tier System: Making Assumptions Explicit

We propose a three-tier classification of theoretical inputs:

**Tier 1: Structural Assumptions for 3FLL Application**

| Axiom | Statement | Justification |
|-------|-----------|---------------|
| **(I)** Domain | There exists a non-empty domain of discourse | 3FLL require something to govern |
| **(I∞)** Unboundedness | No arbitrary finite bound on distinguishability | Required for continuous refinement (see below) |
| **(I_pars)** Parsimony | Among structures consistent with 3FLL, those minimizing specification cost are selected | Required for determinate application (see Section 2.4) |

These are *substantive assumptions*, not pure consequences of 3FLL. We argue they are required for coherent application of 3FLL to physical reality; this argument is part of the thesis.

**Why (I∞)?** A strictly finite state space would preclude the continuous refinement of measurements that underpins the Masanes-Müller reconstruction: their derivation requires that pure states form a continuous manifold (specifically, a Bloch sphere for qubits) and that reversible transformations act continuously on this manifold. With only finitely many distinguishable states, these limit procedures fail. Note that (I∞) is compatible with MM's "finite information capacity per system"—individual subsystems may have finite dimension while the total domain of discourse remains unbounded. The tension is between MM's operational finiteness (finite bits per measurement) and the need for unbounded refinement at the level of the state space; (I∞) resolves this by positing no arbitrary cutoff on total distinguishability.

**Tier 2: Established Mathematical Reconstruction Results**

These are proven mathematical theorems with explicit presuppositions:

| Theorem | Statement | Key Presuppositions |
|---------|-----------|---------------------|
| **Stone (1932)** | Strongly continuous one-parameter unitary groups have self-adjoint generators | Hilbert space, strong continuity |
| **Gleason (1957)** | In Hilbert spaces dim ≥ 3, probability measures on closed subspaces are determined by density operators | Hilbert space dim ≥ 3, frame functions |
| **Masanes-Müller (2011)** | Quantum theory is uniquely determined by operational axioms | See Section 4.2 for full axiom list |

We accept Tier 2 results for practical use while tracking their presuppositions explicitly. Whether these presuppositions are derivable from Tier 1 is an open research question.

**Tier 3: Physical Principles**

Empirically motivated principles whose logical status is tracked:
- Energy additivity and conservation
- Stability requirements (Ehrenfest 1917)
- Symmetry principles (Lorentz invariance, gauge symmetry)

**Methodological value:** The tier system prevents conflation of "established result" with "assumption-free derivation." When we invoke Gleason's theorem, we acknowledge that Hilbert space structure is presupposed, not derived.

### 2.4 The Status of Parsimony

Parsimony (I_pars) does significant work throughout the derivation cascade: it selects continuous over discontinuous structures, reversible over irreversible dynamics, and minimum-action paths. Given this load-bearing role, its status requires explicit treatment.

**Our position:** Parsimony is a **Tier 1 axiom**, required for determinate application of 3FLL to physical reality.

**Argument:** 3FLL alone do not select among the infinitely many structures compatible with logical coherence. Without a selection principle, 3FLL constrain but do not determine. For 3FLL to have determinate physical content, something must select among coherent alternatives. Parsimony—minimizing specification cost—is the natural candidate: it is the selection principle that does not itself require arbitrary specification.

**Formal statement:**

> **(I_pars) Parsimony Principle:** Among structurally possible configurations consistent with 3FLL and Tier 1 assumptions, those requiring minimal specification are physically realised.

**Alternative positions (for transparency):**
1. *Parsimony derived from 3FLL:* L₂ rules out maximal chaos (everything true); parsimony is the stable opposite. This argument is suggestive but not rigorous.
2. *Parsimony as methodological maxim:* Parsimony guides theory choice, not reality. On this reading, our derivations are conditional: "IF parsimony, THEN action follows."

We adopt the first position (Tier 1 axiom) while acknowledging that readers preferring position 3 can reframe our results as conditional.

**Objection: "Parsimony is hidden physics."** One might object that parsimony smuggles physical content (smoothness, continuity, thermodynamic preferences) into what claims to be logic. If so, the action functional is not "downstream of logic" but an independent physical postulate relabelled.

**Response:** Parsimony is not independent of 3FLL—it is required for L₁ (Identity) to have determinate application.

Consider: a state of infinite complexity would require infinite information to specify. But if infinite information is required to identify state S as S, then "S = S" becomes unverifiable—not false, but meaningless. Identity presupposes that states are *identifiable*, which requires finite specification. Parsimony is not "logic plus physics"; it is the condition under which logic applies to anything at all.

A logically consistent but maximally chaotic universe would satisfy 3FLL vacuously—nothing could be identified as violating them because nothing could be identified, period. Parsimony ensures 3FLL have non-trivial, non-vacuous application. Without it, we have logical constraint over nothing determinately specified.

### 2.5 Empirical Status and Falsification Conditions

**LRT's empirical content:**

LRT forbids the following observable events:
1. A completed measurement recording outcome P ∧ ¬P
2. A completed measurement failing to record either P or ¬P (genuine third option, not merely "undetermined")
3. A physical state failing to maintain self-identity across an observation interval

**Current status:** No such event has ever been observed. Every measurement record in physics is Boolean—one outcome obtains. Quantum superposition does not violate this: superposition describes the state *before* measurement; the measurement outcome is always definite.

**What would refute LRT:**
- A reproducible experiment yielding contradictory outcomes in a completed measurement
- A physical system demonstrably violating identity (the same system being provably non-identical to itself)
- Evidence that some physical regime operates according to a genuinely paraconsistent logic (not merely a formal model, but physical realisation)

**Why no violations have been found:** This is the question LRT addresses. Three possible answers:
1. **Constitutive (LRT's strong thesis):** 3FLL hold in all possible worlds; violations are metaphysically impossible.
2. **Contingent but robust:** Our universe happens to obey 3FLL; other universes might not.
3. **Emergent:** 3FLL emerge from deeper dynamics that are not themselves logical.

LRT pursues explanation (1) while acknowledging (2) and (3) remain open. The empirical fact—no violations—is common ground.

### 2.6 From Epistemic to Metaphysical: Bridging the Gap

**The gap:** Self-grounding arguments establish that we *cannot coherently deny* 3FLL. They do not immediately establish that 3FLL *hold mind-independently*.

**The bridge argument:**

*Premise 1:* Our best physical theories describe a world that is determinate (states have definite properties), distinguishable (different states can be told apart), and non-contradictory (no state is both P and ¬P).

*Premise 2:* These features are precisely what 3FLL require: determinacy (L₁), distinguishability (L₃), non-contradiction (L₂).

*Premise 3:* The success of physics—its predictive accuracy, technological applications, coherent development—provides strong evidence that our theories track real structure, not merely our conceptual projections.

*Conclusion:* The logical structure we cannot coherently deny in reasoning is also the structure physics successfully describes. The simplest explanation is that 3FLL constrain reality, not just thought about reality.

**This is not a proof.** A sceptic can maintain that physics succeeds despite not tracking deep structure, or that logical structure is imposed by us. But this scepticism applies to all of science. LRT's metaphysical thesis is no worse off than scientific realism generally.

**Objection: The QBist challenge.** Quantum Bayesianism (QBism) argues that measurement outcomes are not properties of the world but personal experiences of an agent. If outcomes are agent-centric, then 3FLL are merely normative rules for how an agent should "keep their books balanced"—not physical laws. The absence of observed 3FLL violations would simply reflect that we refuse to call an incoherent experience a "measurement."

*Response:* The QBist challenge targets Premise 3 (that physics tracks real structure). We respond by emphasising **intersubjectivity**. If measurement outcomes were purely agent-centric, we would expect systematic disagreement between agents about outcomes. Instead, we find:
- Multiple agents consistently record the same outcome for the same experiment
- Measurement records can be transmitted, stored, and verified by independent parties
- Technological applications (dependent on specific outcomes) work for everyone, not just the original "experiencer"

This intersubjective agreement is precisely what realism predicts and what pure agent-centrism struggles to explain. The simplest account remains: outcomes are properties of world-states, agents access these properties, and 3FLL constrain what properties can obtain. QBism must either deny intersubjectivity (empirically false) or explain it as a remarkable coincidence (unparsimonious).

**Engagement with logical realism literature:**

Sher (2011) argues that logic captures formal features of reality—structures that any domain must exhibit (objects, properties, relations). Our position extends this: 3FLL are not merely formal features we *discover* but constitutive conditions for there *being* structured reality at all.

Maddy (2007) grounds logical truth in worldly structure while remaining agnostic about necessity. We go further: 3FLL are not contingent features of our world but necessary features of any coherent world.

**The fallback:** If the metaphysical bridge fails, LRT weakens to: "3FLL are necessary for our reasoning about physics, and physics exhibits no violations." This is still a substantive physical claim with empirical content.

### 2.7 Actualization as L-Constraint: The Core Thesis Formalized

The central claim of Logic Realism Theory—that physical actualization equals logical constraint on information space (𝔄 = 𝔏(𝔍))—can be decomposed into a theorem and an open conjecture.

**Scope.** LRT is a theory of **physical reality**: the domain of measurement outcomes, actualized physical states, and what physics describes. It is deliberately agnostic about mathematical reality (whether abstract objects exist independently), the ontological status of 3FLL themselves, and whether there are domains of reality beyond physics. The claim 𝔄 = 𝔏(𝔍) concerns physical actualization, not all possible reality.

**The co-constitutive thesis.** Neither 𝔏 nor 𝔍 alone constitutes physical reality. Rather:
- **𝔍** provides the substrate—the space of possible information configurations
- **𝔏** provides the structure—the constraint that filters coherent from incoherent configurations
- **𝔄** emerges from their interaction: physical reality is information-structured-by-logic

This is not the claim that "logic alone generates reality" (which would be a strong idealism). It is the claim that 𝔏 and 𝔍 are **co-constitutive** of physical actualization.

**Definitions.**

Let **𝔍** (information space) be the set of all total assignments of truth values to a σ-algebra P of propositions about physical measurement outcomes (possibly infinite, as required by (I∞)), subject only to syntactic well-formedness.

Let **𝔏** (the 3FLL-constraint operator) act on 𝔍 by:

```
𝔏(𝔍) := { s ∈ 𝔍 | s satisfies Identity, Non-Contradiction, and
         Excluded Middle on all outcome propositions in P }
```

Let **𝔄** (the physical actualization set) be:

```
𝔄 := { s ∈ 𝔍 | s is a physically realizable history given
       Tier 1–3 axioms and Tier 2 reconstruction results }
```

Here "physically realizable" means: there exists some solution of the theory's dynamical equations whose completed measurement records are exactly those encoded by s.

**Theorem 2.1 (3FLL Constraint on Actualization).**
*Given Tier 1 axioms and the empirical fact that no completed measurement record or physical observation violates 3FLL:*

```
𝔄 ⊆ 𝔏(𝔍)
```

(This is equivalent to the claim that no physically realizable outcome violates 3FLL—the empirical thesis of §1.1.)

*Proof sketch.* Any s ∈ 𝔄 encodes outcomes in some physically realizable history. By LRT's empirical hypothesis (Section 1.1) and current evidence, no such outcome is both P and ¬P, neither P nor ¬P, or self-non-identical. Therefore s satisfies 3FLL on all outcome propositions, so s ∈ 𝔏(𝔍). ∎

This is the **derived, empirically-backed direction**: every actualizable history lies in the 3FLL-respecting region of information space.

**Conjecture 2.1 (LRT Completeness).**
*For any s ∈ 𝔏(𝔍), there exists a physically realizable history whose outcome pattern is s:*

```
𝔏(𝔍) ⊆ 𝔄
```

If Conjecture 2.1 holds, then **𝔄 = 𝔏(𝔍)**: the set of physically realizable histories is exactly the 3FLL-constrained subset of information space.

**Status.** LRT does not derive this completeness result. It would require showing that Tier 1–3 dynamics are rich enough that every 3FLL-respecting information pattern is physically realizable in some solution. This is a substantive open problem—the ambitious heart of the research program.

**The Over-Generation Risk.** One might worry that Conjecture 2.1 could fail if 𝔏(𝔍) is "too large"—if there exist physical constraints beyond 3FLL that forbid certain logically coherent states from actualizing. In that case, 𝔄 ⊂ 𝔏(𝔍) strictly: logic would be necessary but not sufficient for actualization.

**Resolution via co-constitution.** The co-constitutive framing dissolves this concern. If physical reality is *defined* as 𝔏 operating on 𝔍—not as something independent against which 𝔏(𝔍) could be measured—then there is no external "physics" relative to which 𝔏(𝔍) could be too large. Tier 2/3 inputs are either:
1. **Internal to the framework:** derivable from how 3FLL applies to information space, or
2. **Part of 𝔍's structure:** how information space is constituted for physical systems, or
3. **Incomplete understanding:** artifacts of our current theoretical limitations, not genuine independent constraints.

Under this view, the completeness conjecture shifts from an empirical question ("does physics add extra constraints?") to a definitional claim about what physical reality means.

**What each direction establishes:**

| Claim | Status | What it says |
|-------|--------|--------------|
| 𝔄 ⊆ 𝔏(𝔍) | **Theorem** (empirically supported) | Physical actualization respects 3FLL |
| 𝔏(𝔍) ⊆ 𝔄 | **Conjecture** (open) | 3FLL constraint on 𝔍 suffices for physical actualization |
| 𝔄 = 𝔏(𝔍) | **Conditional** | Physical reality = 𝔏 and 𝔍 co-constituted |

---

## 3. Comparison with Existing Traditions

### 3.1 Logical Empiricism

The logical empiricist tradition (Carnap 1956; Hempel 1965; Nagel 1961) analysed theories as theoretical terms connected to observational terms via correspondence rules.

**Where LRT differs:**
- We treat 3FLL as *constitutive of the subject matter*, not merely metatheoretical apparatus.
- Axioms are not free choices but constrained by coherence requirements—the space of viable axioms is narrower than conventionalism suggests.

### 3.2 Quine-Duhem Underdetermination

Quine (1951) argued that even logic is revisable in principle—just another node in the web of belief, central but not immune.

**LRT response:** The crucial difference is self-grounding. Ordinary claims can be coherently denied; 3FLL cannot. Underdetermination operates *within* the space constrained by 3FLL, not over 3FLL themselves.

### 3.3 Friedman's Relativized A Priori

Friedman (2001) argues that constitutive principles are revisable across scientific revolutions.

**LRT response:** We agree that higher-tier assumptions (Hilbert space, symmetry principles) are Friedman-revisable. But 3FLL mark a limit: they are constitutive not just for frameworks but for coherent theorizing as such.

### 3.4 Quantum Reconstruction Programs

Hardy (2001), Chiribella et al. (2011), and Masanes and Müller (2011) derive quantum theory from information-theoretic postulates.

**LRT contribution:** These programs make *some* assumptions explicit but typically do not ask what grounds the operational axioms themselves. The tier system provides a framework for this question: Are the operational axioms downstream of 3FLL, or genuinely independent?

### 3.5 Objections from Logical Pluralism

**Paraconsistent logic (Priest 2006; Beall 2009):** Contradictions need not entail everything; some might be true.

*Response:* We distinguish object-level and meta-level. Paraconsistent formal systems are legitimate mathematics. But the dialethist asserting "This contradiction is true" relies on that assertion being determinately true (not also false) at the meta-level. Coherent assertion presupposes L₂.

*Limitation:* Priest and others have argued that paraconsistent meta-reasoning is possible. We flag this as a point where critics may diverge; our argument assumes classical meta-logic.

**Empirical status of paraconsistent physics:** A crucial observation: existing work on paraconsistent logic in physics (da Costa and French 2003; Krause and Arenhart 2016) focuses on reformulating inconsistent classical theories, offering paraconsistent formalisms for quantum superposition, and exploring quantum logics from a paraconsistent perspective. However, **these approaches have not produced distinctive, confirmed physical predictions** that differ from standard quantum theory, nor have they become standard calculational frameworks in any active experimental domain.

Dialetheism remains primarily a philosophical thesis about truth and inconsistency; its "applications" are almost entirely in logic, metaphysics, and the philosophy of mathematics—not in experimentally tested physics. In current scientific practice, paraconsistent and dialetheist frameworks function as **conceptual or formal thought experiments**, not as empirically successful rival physical theories. At present, such approaches **do not meet the usual criteria for inclusion in the physicist's toolkit**: they neither guide experimental design nor underwrite successful, domain-specific calculations beyond what standard quantum theory already provides.

This supports LRT's position: all actual detector records analysed in mainstream physics are treated in entirely classical, Boolean terms at the level of measurement outcomes, even when the underlying formalism involves quantum superposition. Non-classical logical frameworks in physics therefore appear as **alternative representations** of a world whose actualized outcomes respect 3FLL; they do not exhibit themselves as different "logics of nature" realised in experiment.

In light of current practice, non-classical logical frameworks in physics are best understood as **conceptual or formal thought experiments** rather than as working physical theories. They offer alternative representations of a world whose actualised detector records are still analysed in strictly Boolean terms, and they have not yet produced distinctive, confirmed predictions that would force a revision of 3FLL at the level of completed measurement outcomes.

**Intuitionistic logic:** Excluded Middle fails for unverifiable propositions.

*Response:* Physical distinguishability—the ability to tell states apart—is inherently bivalent. Two states either are or are not distinguishable; there is no third status. L₃ applies to distinguishability even if it fails for abstract mathematical existence.

**Objection: "L₃ is metaphysical imposition."** A more sophisticated intuitionist challenge: in regimes where verification is impossible (cosmological horizons, Planck-scale physics), asserting P ∨ ¬P is a metaphysical imposition, not an empirical fact. The "Boolean outcome" status may be merely an artifact of the macroscopic limit—the Heisenberg cut—not a fundamental property of I.

*Response:* We ground L₃ not in *verification* (which is epistemic) but in the *possibility of interaction*. If a system S can interact with an environment E, the interaction itself constitutes a bivalent "question" to the state: the interaction either occurs or does not, transfers information or does not, distinguishes states or does not. This is not about whether *we* can verify the outcome, but whether the physical interaction has a determinate character.

At cosmological horizons or Planck scales, if no interaction is possible even in principle, then no physical question is being asked—and L₃ applies vacuously (there is no proposition P about which to assert P ∨ ¬P). Where interaction *is* possible, outcomes are bivalent. The intuitionist conflates epistemic access with physical determinacy; LRT concerns the latter.

### 3.6 Contrast with Many-Worlds Interpretation

The Many-Worlds Interpretation (MWI) of quantum mechanics provides an instructive contrast. MWI suffers from precisely the over-generation problem that LRT's co-constitutive framing avoids.

**MWI's over-generation:** MWI posits that all branches of the wave function exist—every outcome permitted by unitary evolution is actualised in some branch. This generates ontological extravagance: infinitely many worlds, with no principled mechanism for why *this* branch exhibits *these* outcomes with *these* probabilities. The Born rule remains unexplained; the preferred basis problem persists.

**LRT's response:** Under co-constitution, physical reality is *defined* as 𝔏(𝔍)—not as a subset of some larger space of "all possible worlds." There is no over-generation because:
- 𝔏 provides the selection criterion from the start (3FLL filter incoherent configurations)
- 𝔍 is the substrate structured by 𝔏, not an independent "space of all possibilities"
- 𝔄 = 𝔏(𝔍) is definitional, not a contingent fact about which branches exist

| Problem | MWI | LRT |
|---------|-----|-----|
| Over-generation | All branches exist | Only 𝔏(𝔍) exists |
| Selection mechanism | None (all actualised) | 𝔏 constrains 𝔍 |
| Born rule | Unexplained add-on | Emerges from distinguishability structure |
| Ontological cost | Infinite worlds | Single co-constituted reality |

MWI generates everything consistent with the wave equation and then struggles to recover observed physics. LRT begins with logical constraint and derives physical structure within that constraint. The co-constitutive framing ensures there is no "everything exists, then we pick"—there is only what 𝔏(𝔍) permits.

### 3.7 The Fallback Position

Even if the strong metaphysical thesis fails, the program remains valuable:
- **Tier system:** Tracks presuppositions regardless of which logic governs.
- **Empirical claim:** No observed 3FLL violations is a physical fact.
- **Partial derivations:** Reducing independent assumptions is progress even without full derivation.
- **Comparative analysis:** Different frameworks can be compared by their tier profiles.

LRT is an ambitious research program, not an all-or-nothing gambit.

---

## 4. Case Study: Deriving the Action Functional

### 4.1 Traditional Presentation

The principle of least action, S = ∫ L dt with δS = 0, is typically presented as a postulate justified by empirical success. Why should nature minimise action?

### 4.2 Masanes-Müller Reconstruction: Explicit Axioms

Before presenting our derivation, we state precisely which axioms from Masanes and Müller (2011) we invoke:

**Lemma 4.1 (Masanes-Müller):** A theory satisfying the following axioms is quantum theory:
1. **(MM1) Tomographic locality:** Global states are determined by local measurements.
2. **(MM2) Continuous reversibility:** Reversible transformations form a continuous group.
3. **(MM3) Subspace axiom:** Pure states on subspaces extend to global pure states.
4. **(MM4) Composite systems:** Systems can be combined.

**Status in LRT:**

| MM Axiom | LRT Derivation Status |
|----------|----------------------|
| MM1 (Tomographic locality) | **Tier 2 input** (not derived from 3FLL) |
| MM2 (Continuous reversibility) | **Partially derived** (Propositions 4.3, 4.4 below) |
| MM3 (Subspace axiom) | **Tier 2 input** |
| MM4 (Composite systems) | **Tier 2 input** (relates to Tier 1 domain assumption) |

### 4.3 Formal Derivation Chain

We present key steps as formal propositions. Full proofs would require a dedicated technical paper; here we provide rigorous statements with proof sketches.

**Proposition 4.1 (Binary Distinctions):** *If 3FLL govern a domain D, then any property P on D induces a binary partition: elements satisfying P and elements satisfying ¬P.*

*Proof sketch:* By L₃ (Excluded Middle), for any element x ∈ D and property P, either P(x) or ¬P(x). By L₂, not both. This partitions D into {x : P(x)} and {x : ¬P(x)}. ∎

*Status:* Derived from 3FLL. No additional assumptions.

**Proposition 4.2 (Distinguishability Metric):** *If D admits binary distinctions and satisfies (I∞), then D admits a distinguishability measure d: D × D → ℝ≥0 with d(x,y) = 0 iff x = y.*

*Proof sketch:* Define d(x,y) as the number of properties on which x and y differ (Hamming distance generalised). By L₁, x = x implies d(x,x) = 0. By L₃, any property either applies or not, so d is well-defined. By (I∞), unboundedly many properties exist, so d can be arbitrarily refined. ∎

*Status:* Derived from 3FLL + (I∞).

*Gap:* This establishes *a* metric exists. That it is unique or has specific properties (e.g., Euclidean) requires additional argument.

**Proposition 4.3 (Continuity):** *If parsimony (I_pars) is operative and D admits a distinguishability measure, then d must be continuous.*

*Proof sketch:* Suppose d is discontinuous at some point—a small change in configuration produces a large change in d. This discontinuity requires specification: where does the jump occur? What triggers it? This specification has information cost, violating parsimony. Therefore, minimal-specification structures have continuous d. ∎

*Status:* Derived from (I_pars). Requires parsimony.

**Proposition 4.4 (Reversibility):** *If (I_pars) is operative, then d-preserving transformations are reversible.*

*Proof sketch:* Suppose T preserves d but is irreversible: T(x) = T(y) for x ≠ y. Then d(T(x), T(y)) = 0 but d(x,y) > 0, contradicting d-preservation. Therefore d-preserving T is injective. By similar argument (parsimony penalises information loss), T is surjective on its range. Hence T is bijective (reversible). ∎

*Status:* Derived from (I_pars).

**Proposition 4.5 (Inner Product Structure):** *Given continuity (Prop 4.3), reversibility (Prop 4.4), and MM axioms (MM1, MM3, MM4), the state space admits an inner product with d(s₁, s₂) = √(1 - |⟨s₁|s₂⟩|²).*

*Proof sketch:* This is the Masanes-Müller reconstruction theorem. Continuous reversibility (our Prop 4.4) provides MM2. The remaining axioms (MM1, MM3, MM4) are Tier 2 inputs. Their theorem yields quantum state space with inner product inducing the stated metric. ∎

*Status:* Uses Tier 2 inputs (MM1, MM3, MM4).

**Proposition 4.6 (Phase Space):** *Inner product structure implies position-momentum phase space (x, p) with minimum cell area ℏ.*

*Proof sketch:* Hilbert space admits position basis |x⟩ and momentum basis |p⟩ related by Fourier transform. The uncertainty principle δx·δp ≥ ℏ/2 defines minimum phase space resolution. Define ℏ as this minimum—it is not an empirical input but a consequence of the inner product structure. ∎

*Status:* Mathematical consequence of Prop 4.5.

**Proposition 4.7 (Action):** *Given phase space with minimum cell ℏ, action S = ∫ p dx counts traversed cells.*

*Proof sketch:* A path through phase space traverses some number of ℏ-cells. Logical action S_logical = (number of cells). Physical action S = ℏ × S_logical = ∫ p dx by definition of phase space area. ∎

*Status:* Definition given prior structure.

**Proposition 4.8 (Least Action):** *Parsimony (I_pars) implies δS = 0.*

*Proof sketch:* Parsimony selects minimum specification cost. Action counts specification (cells traversed). Minimum action paths minimise specification. Variational principle δS = 0 expresses this selection. ∎

*Status:* Derived from (I_pars).

### 4.4 Summary: What Has Been Derived?

| Step | Content | Status | Inputs |
|------|---------|--------|--------|
| 4.1 | Binary distinctions | **Derived** | 3FLL only |
| 4.2 | Distinguishability metric | **Derived** | 3FLL + (I∞) |
| 4.3 | Continuity | **Derived** | + (I_pars) |
| 4.4 | Reversibility | **Derived** | + (I_pars) |
| 4.5 | Inner product | **Tier 2** | + MM1, MM3, MM4 |
| 4.6 | Phase space, ℏ | **Consequence** | of 4.5 |
| 4.7 | Action S | **Definition** | given 4.6 |
| 4.8 | Least action | **Derived** | + (I_pars) |

**Honest assessment:** The derivation succeeds *given* Tier 1 axioms (including parsimony) and Tier 2 inputs (three MM axioms). It does not derive action from pure logic. The tier system makes explicit what is assumed and where.

**Research question:** Can MM1, MM3, MM4 be derived from 3FLL + parsimony? This remains open. If yes, the derivation strengthens. If no, these axioms are genuinely independent of logic.

### 4.5 What If Tier 2 Assumptions Remain Irreducible?

If MM1, MM3, MM4 cannot be derived from 3FLL:
1. **The methodology remains valuable:** We have clarified exactly which assumptions are needed.
2. **Partial derivation is progress:** We derived continuity and reversibility from parsimony, reducing the independent assumption count.
3. **Comparative analysis:** Other frameworks can be assessed by their Tier 2 requirements.
4. **The strong thesis weakens:** 3FLL constrain but do not uniquely determine physics.

This is honest science, not failure.

---

## 5. Implications and Open Questions

### 5.1 For Foundations of Physics

- **Presupposition tracking:** The tier methodology can be applied to any foundational program, revealing hidden assumptions.
- **Unification:** If diverse principles share common tier roots, apparent diversity masks underlying unity.
- **Quantum gravity:** What spacetime structures are logically coherent given quantum distinguishability?

### 5.2 For Philosophy of Science

- **Constitutive principles:** 3FLL are candidates for truly invariant constitutive principles (unlike Friedman-revisable frameworks).
- **Analytic/synthetic:** 3FLL are neither purely analytic nor synthetic but constitutive of coherent worldhood.
- **Alternative logics as modelling tools:** The finding that paraconsistent and dialetheist approaches have produced no distinct empirical predictions suggests they function as **representational options over a 3FLL-compliant outcome space**. LRT describes a constraint on the realised outcome space that is directly tied to observable practice—not an ad hoc philosophical overlay, but a **conservative generalisation of what physics in fact does** at the level of measurement outcomes.
- **Demarcation:** LRT provides a falsifiability criterion distinguishing working physical theories from purely formal constructions: does the framework make predictions about actualised outcomes that could in principle be violated?

### 5.3 Open Questions

1. **Completeness:** Can all Tier 2/3 inputs be derived from 3FLL? (Strong thesis—research conjecture)
2. **Uniqueness:** Does 3FLL + parsimony determine physics uniquely?
3. **Distinguishability in QM:** How does the framework accommodate partial quantum distinguishability (fidelity ∈ [0,1])?

---

## 6. Conclusion

Logic Realism Theory makes an empirical claim—3FLL constrain physical possibility—that has never been violated. This distinguishes it from pure philosophical speculation. The tier methodology for presupposition tracking constitutes a practical contribution regardless of the metaphysical thesis's fate.

**What we claim:**
1. LRT is a falsifiable physical theory (no observed violations).
2. The tier system clarifies assumption dependencies in foundational physics.
3. The metaphysical thesis (3FLL hold in all possible worlds) is a research conjecture worth pursuing.

**What we do not claim:**
- That physics reduces to pure logic
- That all Tier 2/3 assumptions have been derived
- That the metaphysical thesis is proven

Alternative logics in physics therefore remain, at this stage, **formal options and thought experiments**, not empirically established competitors to the 3FLL-constrained outcome structure that LRT codifies.

The Logic Realism approach provides a meta-framework for analysing what physics presupposes and what it achieves. It is offered as an ambitious research program, not established truth.

---

## References

Beall, J.C. (2009) *Spandrels of Truth*. Oxford: Oxford University Press.

Beall, J.C. and Restall, G. (2006) *Logical Pluralism*. Oxford: Oxford University Press.

Carnap, R. (1956) 'The Methodological Character of Theoretical Concepts', in Feigl, H. and Scriven, M. (eds.) *Minnesota Studies in the Philosophy of Science*, Vol. 1. Minneapolis: University of Minnesota Press, pp. 38-76.

Chiribella, G., D'Ariano, G.M. and Perinotti, P. (2011) 'Informational derivation of quantum theory', *Physical Review A*, 84(1), 012311.

CODATA (2018) *CODATA Recommended Values of the Fundamental Physical Constants: 2018*. Gaithersburg: National Institute of Standards and Technology.

da Costa, N.C.A. and French, S. (2003) *Science and Partial Truth: A Unitary Approach to Models and Scientific Reasoning*. Oxford: Oxford University Press.

Duhem, P. (1954) *The Aim and Structure of Physical Theory*. Translated by P.P. Wiener. Princeton: Princeton University Press. (Original work published 1906).

Ehrenfest, P. (1917) 'In what way does it become manifest in the fundamental laws of physics that space has three dimensions?', *Proceedings of the Amsterdam Academy*, 20, pp. 200-209.

Friedman, M. (2001) *Dynamics of Reason*. Stanford: CSLI Publications.

Gleason, A.M. (1957) 'Measures on the Closed Subspaces of a Hilbert Space', *Journal of Mathematics and Mechanics*, 6(6), pp. 885-893.

Hardy, L. (2001) 'Quantum Theory From Five Reasonable Axioms', arXiv:quant-ph/0101012.

Hempel, C.G. (1965) *Aspects of Scientific Explanation*. New York: Free Press.

Krause, D. and Arenhart, J.R.B. (2016) 'Logical Perspectives on Science and Cognition: Non-Classical Logics and Quantum Mechanics', *Handbook of the History of Logic*, 11, pp. 443-493.

Maddy, P. (2007) *Second Philosophy: A Naturalistic Method*. Oxford: Oxford University Press.

Masanes, L. and Müller, M.P. (2011) 'A derivation of quantum theory from physical requirements', *New Journal of Physics*, 13, 063001.

Nagel, E. (1961) *The Structure of Science: Problems in the Logic of Scientific Explanation*. New York: Harcourt, Brace & World.

Priest, G. (2006) *In Contradiction: A Study of the Transconsistent*. 2nd edn. Oxford: Oxford University Press.

Quine, W.V.O. (1951) 'Two Dogmas of Empiricism', *Philosophical Review*, 60(1), pp. 20-43.

Sher, G. (2011) 'Is logic in the mind or in the world?', *Synthese*, 181(2), pp. 353-365.

Stone, M.H. (1932) 'On One-Parameter Unitary Groups in Hilbert Space', *Annals of Mathematics*, 33(3), pp. 643-648.

---

## Appendix A: Formal Statement of the Tier System

### A.1 Tier 1 Axioms

| Axiom | Formal Statement | Status |
|-------|------------------|--------|
| **(I)** | ∃D: D ≠ ∅ (domain exists) | Required for 3FLL application |
| **(I∞)** | ∀n ∈ ℕ: |D| > n (no finite bound) | Required for non-trivial physics |
| **(I_pars)** | Among {S : S consistent with 3FLL ∧ I ∧ I∞}, select argmin(specification cost) | Required for determinacy |

### A.2 Tier 2 Usage Protocol

For each Tier 2 theorem invoked:
1. State the theorem precisely
2. List all presuppositions
3. Indicate which are derived upstream vs. taken as input
4. Note whether derivability from Tier 1 is open or closed

### A.3 Tier 3 Classification

| Type | Description | Example |
|------|-------------|---------|
| Empirical regularity | Observed pattern elevated to principle | Energy conservation |
| Symmetry consequence | Derivable from spacetime structure | Lorentz invariance |
| Stability requirement | Condition for structure existence | Ehrenfest d ≤ 3 |

---

## Appendix B: Masanes-Müller Presupposition Table

The following table maps our labels (MM1–MM4) to the numbered requirements in Masanes and Müller (2011, §2):

| Our Label | MM Requirement | MM Description | LRT Status | Derivable from 3FLL? |
|-----------|----------------|----------------|------------|---------------------|
| MM1 | Requirement 3 | **Local tomography:** The state of a composite system is completely determined by the statistics of local measurements on its subsystems | Tier 2 input | Open (conjecture: related to L₃ applied locally) |
| MM2 | Requirement 2 | **Continuous reversibility:** For every pair of pure states, there exists a continuous path of reversible transformations connecting them | Partially derived | Continuity: Prop 4.3; Reversibility: Prop 4.4 |
| MM3 | Requirement 4 | **Subspace axiom:** For each system, there exists a "maximally mixed" state; pure states span a proper subspace | Tier 2 input | Open |
| MM4 | Requirement 5 | **Composite systems:** Systems can be combined; the joint state space has specific structure | Tier 2 input | Open (relates to domain I) |

**Note:** MM's Requirement 1 ("Existence of an information unit") states that there exists a system carrying exactly one bit of information. This is implicit in LRT's domain axiom (I) together with Proposition 4.1 (binary distinctions). MM's finiteness condition (finite-dimensional state spaces for individual systems) is compatible with LRT's (I∞), which posits no finite bound on the total domain rather than individual subsystems.

**Cross-reference:** Readers wishing to verify our mapping should consult Masanes and Müller (2011), specifically §2 "The framework" (pp. 3–5) and §3 "Main result" (pp. 5–8) where Requirements 1–5 are stated.

---

## Appendix C: The Fine Structure Constant (Conjectural)

**Note:** This appendix presents a speculative numerical illustration of the methodology. It is not a confirmed derivation and should be assessed separately from the main results.

### C.1 Conjectural Argument

A heuristic derivation chain relates α to spatial dimension d = 3:

1. Physical states require 2d + 1 parameters (positions, momenta, phase)
2. Information capacity: 2^(2d+1)
3. Complexity requires d ≥ 3 (capacity ≥ ~100)
4. Stability requires d ≤ 3 (Ehrenfest 1917)
5. Intersection: d = 3
6. Formula: α⁻¹ = 2^7 + d² + correction ≈ 137.036

### C.2 Critical Assessment

| Issue | Concern |
|-------|---------|
| **Fitted parameter** | "Self-interaction correction" appears tuned |
| **Single data point** | One match proves nothing |
| **Anthropic input** | Complexity threshold from observed chemistry |
| **Dimensional mixing** | Information units + geometric units unclear |

### C.3 Status

This is an *intriguing numerical coincidence* meriting investigation, not a confirmed derivation. Independent predictions (other constants) are required for validation. The methodological point—that the tier system can be applied to unexplained constants—stands regardless of whether this specific formula survives scrutiny.

---

**Word count:** ~7,500 (main text), ~8,500 (with appendices)

**Target venue:** Foundations of Physics

---

*Document created: 2025-12-17*
*Revised: 2025-12-17 (per referee report)*
