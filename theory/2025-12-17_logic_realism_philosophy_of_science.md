# Logic Realism as a Philosophy of Science: The Logic-First Structure of Physical Theories

**Date:** 2025-12-17
**Status:** DRAFT
**Author:** James D. Longmire
**ORCID:** 0009-0009-1383-7698

---

## Abstract

Physical theories are typically presented as mathematical structures with empirical interpretations, but the background assumptions enabling their coherence often remain implicit. We propose the *Logic Realism Thesis*: that the Three Fundamental Laws of Logic (Identity, Non-Contradiction, Excluded Middle) function not merely as rules of valid reasoning but as constitutive constraints on coherent reality itself. This thesis—a research conjecture rather than an established result—generates a systematic methodology for foundational analysis. We introduce a three-tier classification distinguishing structural assumptions required for logical application (Tier 1), established mathematical reconstruction results with tracked presuppositions (Tier 2), and physical principles (Tier 3). This framework is compared with logical empiricism (Carnap 1956; Nagel 1961), Quine-Duhem underdetermination, Friedman's (2001) relativized a priori, and recent quantum reconstruction programs (Hardy 2001; Masanes and Müller 2011). Two case studies demonstrate the methodology: deriving the action functional and the fine structure constant, with explicit tracking of which assumptions enter at each tier. We argue that the Logic Realism approach provides a meta-framework for clarifying what physical theories presuppose and achieve, without claiming that all physics reduces to pure logic.

**Keywords:** philosophy of science, foundations of physics, logical structure, quantum reconstruction, underdetermination, constitutive principles

---

## 1. Introduction: The Hidden Structure of Physical Theories

### 1.1 The Problem of Background Assumptions

Physical theories are typically presented as mathematical structures plus empirical interpretations. A theory specifies differential equations, symmetry groups, or algebraic structures, then connects these to observable phenomena through measurement procedures and correspondence rules. What often remains implicit are the background assumptions that make the mathematics coherent and applicable—assumptions about logic, distinguishability, continuity, and composition.

The logical empiricist tradition recognized this problem. Carnap (1956) distinguished theoretical terms from observational terms, connected by correspondence rules. Nagel (1961) analysed the structure of scientific explanations, noting the role of auxiliary assumptions. Yet even these careful analyses tended to treat logic itself as unproblematic background—a metatheoretical apparatus rather than a substantive constraint on physical content.

The Quine-Duhem thesis (Quine 1951; Duhem 1954) revealed that empirical evidence alone cannot uniquely determine theory choice, since auxiliary hypotheses can always be adjusted to save any core commitment. This underdetermination has been taken to show that theoretical frameworks involve conventional elements not fixed by evidence. But which elements are conventional and which are not?

**Thesis statement:** We propose that the Three Fundamental Laws of Logic (3FLL)—Identity, Non-Contradiction, and Excluded Middle—function as constitutive constraints on any coherent physical theory, and that making this logic-first structure explicit illuminates the otherwise hidden dependencies between theoretical postulates.

### 1.2 The Logic Realism Thesis

**Definition:** The Logic Realism Thesis holds that 3FLL are not merely rules of valid reasoning but constitutive of coherent reality itself. All substantive axioms of mathematics and physics are downstream of this logical foundation—they are theorems of coherent structure, constrained by the requirement that reality be logically coherent.

This thesis has historical resonance. Leibniz held that the principle of contradiction and the principle of sufficient reason constrain all possible worlds. Kant argued that certain principles are constitutive of experience itself. More recently, Friedman (2001) has revived the notion of "relativized a priori" principles that function as constitutive for particular theoretical frameworks while remaining revisable across scientific revolutions.

Our position is related but distinct. We locate the truly invariant constitutive principles at 3FLL themselves, arguing that these cannot be revised without abandoning coherent theorizing entirely. Higher-level principles (mathematical structures, physical laws) are constrained by 3FLL but admit variation—this is where underdetermination genuinely operates.

**Important clarification:** This is a research conjecture and metaphysical thesis, not an established result of standard logic. In standard accounts, the laws of thought constrain reasoning about any subject matter but do not determine that subject matter's content. Our claim is stronger: that 3FLL are *constitutive* of reality, not merely *descriptive* of valid inference. We present this as a thesis to be developed and tested through its consequences, not as a proven result.

**Taxonomy of claims:** To avoid conflating different types of claims, we distinguish three levels at which 3FLL might be "constitutive":

- **Epistemic:** 3FLL are constraints on rational belief—what any coherent agent must accept. This is the weakest reading and is widely accepted.
- **Semantic:** 3FLL are constraints on meaningful discourse—any language or model violating them cannot express determinate content. This is stronger and more contested.
- **Metaphysical:** 3FLL are constraints on reality itself—no possible world violates them. This is the strongest reading and the one Logic Realism defends.

Much of our supporting argument—the self-refutation of denying 3FLL—establishes the epistemic and semantic versions directly. The metaphysical version requires an additional step: arguing that coherent theorizing tracks real structure, not merely our conceptual limitations. We acknowledge this gap and address objections in Section 3.5. The methodology (tier system) remains valuable even if only the weaker readings are accepted.

### 1.3 Scope and Aims

This paper:
1. Articulates the logic-first structure of theories as a methodology (Section 2)
2. Introduces a tiered classification of assumptions (Section 2.3) and addresses parsimony's status (Section 2.4)
3. Compares this approach with existing traditions in philosophy of science (Section 3) and addresses objections from logical pluralism (Section 3.5)
4. Demonstrates the methodology through case studies from Logic Realism Theory (Section 4), including assessment of what happens if Tier 2/3 assumptions remain irreducible (Section 4.4)
5. Discusses implications and open questions (Section 5)

Our aim is not to prove that physics reduces to logic—a claim we do not make—but to show that explicit tracking of logical dependencies clarifies foundational analysis and makes hidden assumptions visible.

---

## 2. The Logic-First Structure of Theories

### 2.1 3FLL as Framing Conditions

The Three Fundamental Laws of Logic have been recognised since Aristotle (Metaphysics, Book Γ) as foundational to rational thought:

- **Identity (L₁):** ∀A: A = A — Every thing is identical to itself.
- **Non-Contradiction (L₂):** ∀A: ¬(A ∧ ¬A) — Nothing can both be and not be.
- **Excluded Middle (L₃):** ∀A: A ∨ ¬A — For any proposition, either it or its negation holds.

**Claim:** These principles are not optional axioms that could be otherwise. They are self-grounding in the following sense: any attempt to deny them presupposes them. To assert "Non-Contradiction is false" is to claim that this assertion is true and not false—thereby presupposing Non-Contradiction. To argue against Excluded Middle requires distinguishing valid from invalid arguments—which presupposes that arguments either are or are not valid.

This self-grounding character distinguishes 3FLL from other theoretical principles. Physical laws (F = ma, Maxwell's equations) can be coherently denied or modified. Mathematical axioms (Euclid's parallel postulate, the axiom of choice) can be replaced with alternatives. But 3FLL cannot be coherently denied because the denial itself relies on them.

**Consequence:** 3FLL function as the deepest constraint on theory construction. They are not among the assumptions to be varied in underdetermination analysis—they are the preconditions for coherent theorizing. This does not mean we can derive all of physics from logic alone; it means that whatever physics we construct must respect these constraints.

### 2.2 From Logic to Structure: The Derivation Cascade

If 3FLL are constitutive of coherent reality, then certain structures must follow. We can trace a cascade of increasingly specific structures, each constrained by what comes before:

```
3FLL (primitive, self-grounding)
  ↓ presuppose
Domain of discourse (something exists to reason about)
  ↓ enforce
Binary distinctions (A or ¬A for any property)
  ↓ require
Distinguishability metric (coherent difference between states)
  ↓ constrain
Mathematical structures (those compatible with 3FLL)
  ↓ constrain
Physical structures (those instantiating coherent mathematics)
```

Consider each step:

**3FLL → Domain:** The laws of logic are about something. L₁ (Identity) requires a domain of entities that can be self-identical. L₃ (Excluded Middle) requires propositions that can be evaluated. Without a domain, 3FLL have nothing to govern.

**Domain → Binary distinctions:** Given L₃, every property either applies or does not. This is the origin of "bits"—binary distinctions that partition the domain. A state either has property P or has ¬P; there is no third option.

**Binary distinctions → Distinguishability:** If states can differ in properties, there must be a notion of distinguishability—a metric or at least an ordering of how much states differ. This need not be unique, but some such structure is required for L₁ to have content (two things are identical iff they are indistinguishable in all respects).

**Distinguishability → Mathematical structures:** Not all conceivable mathematical structures are compatible with 3FLL-based distinguishability. For instance, structures that violate trichotomy or admit true contradictions are excluded. The compatible structures form a constrained space.

**Mathematical → Physical structures:** Physical reality, whatever it is, must be describable by 3FLL-compatible mathematics. This does not uniquely fix physics but constrains it.

This cascade makes explicit what is usually implicit: the logical dependencies between layers of theoretical structure.

### 2.3 The Tier System: Making Assumptions Explicit

To operationalise this framework, we propose a three-tier classification of theoretical inputs:

**Tier 1: Structural Assumptions for 3FLL Application**

These are assumptions about what exists for 3FLL to govern:
- **Domain assumption (I):** There exists a domain of discourse—something rather than nothing.
- **Unboundedness assumption (I∞):** There is no arbitrary finite bound on distinguishability—the domain is rich enough for 3FLL to have non-trivial application.

These are substantive assumptions, not pure consequences of 3FLL. One could imagine 3FLL applying to a trivial domain (a single element, or finitely many indistinguishable states). The assumption that our domain is rich enough to ground physics is an additional commitment. LRT argues these assumptions are *required* for coherent application of 3FLL to reality; this argument is part of the thesis.

**Tier 2: Established Mathematical Reconstruction Results**

These are proven mathematical theorems that constrain what structures are possible given certain inputs:
- **Stone's theorem** (Stone 1932): Strongly continuous one-parameter unitary groups have self-adjoint generators.
- **Gleason's theorem** (Gleason 1957): In Hilbert spaces of dimension ≥ 3, probability measures on closed subspaces are determined by density operators.
- **Masanes-Müller reconstruction** (Masanes and Müller 2011): Quantum theory is the unique theory satisfying certain operational axioms (tomographic locality, continuous reversibility, subspace axiom, composite systems).

Each Tier 2 result has its own presuppositions (see Table 1). These presuppositions are neither arbitrary nor proven from 3FLL—they occupy an intermediate status. We accept Tier 2 results for practical use while tracking their presuppositions explicitly.

**Table 1: Tier 2 Presupposition Tracking**

| Theorem | Key Presuppositions | Derivability from 3FLL |
|---------|---------------------|------------------------|
| Stone (1932) | Hilbert space, strongly continuous unitary group | Open |
| Gleason (1957) | Hilbert space dim ≥ 3, frame functions | Open |
| Masanes-Müller (2011) | Tomographic locality, continuous reversibility, subspace axiom | Open |
| Hardy (2001) | Continuous state space, finite dimensionality, simplicity | Open |
| Chiribella et al. (2011) | Causality, purification principle | Open |

**Tier 3: Physical Principles**

These are empirically motivated principles about how the physical world behaves:
- Energy additivity and conservation
- Locality and causality constraints
- Stability requirements (Ehrenfest 1917)
- Symmetry principles (Lorentz invariance, gauge symmetry)

Tier 3 inputs may be empirical regularities elevated to principles, or they may be derivable from more fundamental considerations. The tier system requires us to track their status rather than treating them as self-evident.

**Key insight:** Every Tier 2/3 input carries presuppositions that can be traced. Making this explicit prevents the conflation of "established result" with "assumption-free derivation." When we use Gleason's theorem, we must acknowledge that Hilbert space structure is presupposed, not derived.

### 2.4 The Status of Parsimony

Throughout the derivation cascade, we invoke *parsimony*—the principle of minimizing specification cost. Parsimony does significant work: it selects continuous over discontinuous distinguishability, reversible over irreversible transformations, and minimum-action paths over alternatives. Given this load-bearing role, its status requires explicit discussion.

**Three possible positions:**

1. **Parsimony as derived from 3FLL:** One argument: L₂ (Non-Contradiction) rules out maximal chaos (every proposition true). The opposite extreme—maximal specification—is equally problematic, requiring infinite information. Parsimony emerges as the stable middle: minimum specification consistent with determinacy. This argument is suggestive but not yet rigorous.

2. **Parsimony as a Tier 1 assumption:** If parsimony cannot be derived from 3FLL, it should be added explicitly to Tier 1. This is honest: the derivation cascade requires 3FLL + parsimony, not 3FLL alone. The cost is admitting an extra-logical principle at the foundation.

3. **Parsimony as methodological maxim:** Parsimony might be a rational preference for simpler theories rather than a constraint on reality. On this reading, parsimony-based derivations show what physics *would be* if parsimony holds, not what it *must be*.

**Our position:** We tentatively adopt position (1) as a research hypothesis, while acknowledging that position (2) may be required. The key point is transparency: wherever parsimony enters a derivation, we mark it explicitly. Readers who reject parsimony as foundational can trace exactly where their disagreement begins.

This is preferable to the alternative—smuggling parsimony in under labels like "naturalness" or "simplicity" without acknowledgment. The tier system's value is precisely that it forces such commitments into the open.

---

## 3. Comparison with Existing Traditions

### 3.1 Logical Empiricism and the Structure of Theories

The logical empiricist tradition, developed by Carnap (1956), Hempel (1965), Nagel (1961), and others, provided the most systematic 20th-century analysis of scientific theory structure. On this view, a theory consists of:

- **Theoretical terms:** Unobservable entities and properties (electrons, fields, entropy)
- **Observational terms:** Directly observable entities and properties
- **Correspondence rules:** Connecting theoretical and observational vocabulary
- **Axioms:** Organizing theoretical structure

This framework illuminated much about scientific explanation and theory confirmation. But it faced persistent difficulties: the theory/observation distinction proved unstable (Hanson 1958); correspondence rules seemed insufficiently constrained; the framework said little about why theories take the forms they do.

**Where Logic Realism differs:**

First, we treat 3FLL not as metatheoretical apparatus but as *constitutive of the subject matter*. Logical empiricists used logic to analyse theories; we propose that logic constrains what theories can coherently describe.

Second, the correspondence problem shifts. If logical structure is not imposed on reality but is reality's coherence condition, then the gap between theoretical structure and world structure narrows. We are not asking how theoretical terms "hook onto" reality; we are asking what structures are coherent at all.

Third, axioms are not free choices. The logical empiricists tended to treat axiom selection as conventional within the bounds of empirical adequacy. On our view, axioms are constrained derivations from coherence requirements—the space of viable axioms is narrower than conventionalism suggests.

### 3.2 Underdetermination and Background Assumptions

The Quine-Duhem thesis (Quine 1951; Duhem 1954) states that empirical evidence alone cannot uniquely determine theory choice. Any observation can be accommodated by adjusting auxiliary hypotheses. This has been taken to establish a robust underdetermination of theory by evidence.

Quine (1951) drew radical conclusions: the boundary between analytic and synthetic truths dissolves; even logic and mathematics are revisable in principle; our web of belief faces experience as a corporate body. On this view, 3FLL are just more nodes in the web—central and resistant to revision, but not absolutely immune.

**Logic Realism response:**

We agree that many theoretical commitments are underdetermined by evidence. But we deny that 3FLL are among them. The crucial difference is self-grounding. Ordinary empirical claims can be coherently denied: "electrons do not exist" is false but meaningful. But "Excluded Middle is false" cannot be coherently asserted without relying on Excluded Middle.

The tier system makes explicit which assumptions *can* be varied (Tier 2/3 presuppositions) and which cannot (3FLL). This does not eliminate underdetermination but clarifies its scope. Underdetermination operates within the space constrained by logical coherence. There may be multiple Tier 2/3 combinations compatible with evidence, but all must respect 3FLL.

**Comparison with Friedman's "relativized a priori":**

Friedman (2001) argues that scientific revolutions involve changes in constitutive principles—not just empirical claims but the framework conditions that make empirical claims meaningful. Newton's absolute space was constitutive for Newtonian mechanics; Einstein revised it. These principles are "a priori" for a framework but revisable across frameworks.

We agree substantially with Friedman's analysis. The difference is where we locate the truly invariant principles. For Friedman, even the deepest constitutive principles are historically revisable. For us, 3FLL mark a limit: they are constitutive not just for a framework but for coherent theorizing as such.

Higher-tier assumptions (Hilbert space structure, tomographic locality, energy conservation) are constitutive for particular frameworks but not absolutely. These are the Friedman-revisable principles. 3FLL are deeper—they constrain what counts as revision versus incoherence.

### 3.3 Reconstruction Programs in Quantum Foundations

A major development in foundations of physics has been the *reconstruction program*: deriving quantum theory from simple, physically motivated postulates rather than accepting Hilbert space structure as primitive.

Hardy (2001) showed that quantum theory follows from five "reasonable" axioms including continuity and simplicity. Chiribella, D'Ariano, and Perinotti (2011) derived quantum theory from information-theoretic principles including causality and purification. Most relevant to our framework, Masanes and Müller (2011) showed that quantum theory is uniquely determined by tomographic locality, continuous reversibility, and the subspace axiom.

These programs make *some* assumptions explicit—a significant advance over treating Hilbert space as given. But they typically do not ask: what grounds the operational axioms themselves? Why should nature satisfy tomographic locality? Why continuous reversibility?

**Logic Realism analysis:**

Our framework provides a place to locate these questions. Tomographic locality—the principle that global states are determined by local measurements—might itself be downstream of 3FLL plus distinguishability requirements. Or it might be an additional assumption at Tier 2 level. The tier system forces us to ask.

Current status: We accept reconstruction results as Tier 2 inputs, tracking their presuppositions (Table 1). Whether these presuppositions are derivable from 3FLL is an open research question. The methodology does not answer this question but makes it precise.

### 3.4 "Assumptions of Physics" Projects

Several research programs share the intuition that physics rests on something more fundamental than its standard axioms.

Wheeler's (1990) "it from bit" proposal suggested that physical reality derives from information-theoretic foundations. The slogan captures something important: physics presupposes distinguishability, measurement, and information. But "bit" itself is not self-explanatory. A bit is a binary distinction—and binary distinctions presuppose L₃ (Excluded Middle). Wheeler's intuition is correct, but "bit" is not the ultimate foundation.

Rovelli's (1996) relational quantum mechanics proposes that quantum states are not absolute but relational—a system has properties only relative to another system. This addresses some interpretive puzzles but does not explain why relational quantum mechanics rather than some other framework. The structural question remains.

Various "physics from information" programs (Zeilinger 1999; Brukner and Zeilinger 2003) derive physical principles from information-theoretic foundations. These programs are valuable but typically take information concepts as primitive without asking what grounds them.

**Where Logic Realism differs:**

First, we do not privilege "information" as primitive. Information is *about* something—it presupposes a domain of discourse. Taking information as fundamental inverts the dependency: distinguishability grounds information, not vice versa.

Second, we explicitly ground the framework in 3FLL rather than taking operational concepts as unexplained primitives. "Measurement," "observer," "system" are all concepts that presuppose logical coherence.

Third, we provide a systematic tier classification rather than ad hoc judgments about what is fundamental. The tier system is a methodology that can be applied to any foundational analysis.

### 3.5 Objections and Alternative Logics

The claim that 3FLL are uniquely constitutive faces serious objections from logical pluralism and alternative logic traditions. We address these directly.

**Paraconsistent logic:** Paraconsistent logicians (Priest 2006; Beall 2009) argue that contradictions need not entail everything—that L₂ (Non-Contradiction) can be weakened without trivialising the logic. On dialethist views, some contradictions are true.

*Response:* We distinguish two claims. First, paraconsistent *formal systems* are mathematically legitimate—one can define consequence relations where contradiction does not entail everything. Second, whether such systems can serve as the *metatheory* in which we reason about theories is different. The dialethist who asserts "This contradiction is true" relies on that assertion being determinately true (not also false) at the meta-level. We contend that coherent assertion presupposes L₂, even if object-level systems can model L₂-violations. This is contested; we flag it as a point where critics may diverge.

**Intuitionistic logic:** Intuitionists (Brouwer, Heyting, Dummett) reject L₃ (Excluded Middle) for domains where verification is impossible. On this view, "P ∨ ¬P" is not universally valid—only propositions with decision procedures satisfy it.

*Response:* Intuitionistic logic is appropriate for constructive mathematics, where existence claims require witness construction. But physical distinguishability—the ability to tell states apart—is inherently bivalent: two states either are or are not distinguishable. There is no "third" status. We suggest that L₃ applies to distinguishability even if it fails for abstract mathematical existence. This position is compatible with using intuitionistic methods in proof theory while maintaining L₃ for physical ontology.

**Logical realism literature:** Contemporary defenders of logical realism include Sher (2011), who argues that logic captures formal features of reality, and Maddy (2007), who grounds logical truth in worldly structure. Our position is closer to Sher's: 3FLL are not merely about language or thought but about the formal conditions for any structured reality.

However, Sher's account focuses on formal features shared across domains (e.g., "some," "all," "not") without claiming these features *constitute* reality. Our thesis is stronger: 3FLL do not merely describe formal features—they are conditions without which there is no coherent "reality" to describe. This is a metaphysical commitment beyond Sher's formal-structural realism.

**The fallback position:** Even if the strong metaphysical thesis fails, the methodology remains valuable:
- The tier system tracks assumptions regardless of which logic governs the metatheory.
- Presupposition tracking prevents pseudo-derivation whether or not 3FLL are metaphysically constitutive.
- The derivation cascade structure clarifies dependencies even if some steps require alternative logical resources.

We offer Logic Realism as a research program to be tested, not a dogma. If paraconsistent or intuitionistic foundations prove more fruitful for physics, the tier methodology can accommodate them—the specific content of Tier 0 (logical foundations) would change, but the structural discipline would remain.

---

## 4. Case Studies: The Methodology in Practice

### 4.1 Case Study 1: Deriving the Action Functional

**Traditional presentation:** The principle of least action, S = ∫ L dt where δS = 0 selects physical trajectories, is typically presented as a postulate. Its remarkable success—unifying Newtonian mechanics, electromagnetism, general relativity, and quantum field theory—justifies it empirically. But why should nature minimize action? The question is usually set aside as metaphysical.

**Logic Realism analysis:**

We sketch a *conjectural derivation chain* from 3FLL plus tracked assumptions. This is not a rigorous proof but a structured argument showing how action *might* emerge from logical constraints. Each step is marked with its tier and status (Longmire 2025a):

1. **3FLL → Binary distinctions:** From L₃ (Excluded Middle), any property either obtains or does not. States are characterised by bit-assignments.

2. **Binary distinctions → Distinguishability metric D:** States differing in more bits are more distinguishable. This defines a metric structure (the Hamming distance generalised).

3. **D → Minimum scale (ℏ defined):** [Parsimony argument] If distinguishability had infinite precision, specifying a state would require infinite information—contradicting parsimony. Therefore a minimum distinguishability scale exists. We *define* ℏ as this minimum unit—it is not an empirical input but a logical necessity given parsimony.

4. **D → Continuity:** [Parsimony argument] Discontinuous D would require specification of where discontinuities occur—additional information cost. Parsimony selects continuous D.

5. **D → Reversibility:** [Parsimony argument] Irreversible D-preserving transformations lose information, requiring specification of what was lost. Parsimony selects reversibility.

6. **Continuity + Reversibility → Inner product structure:** [Tier 2: Masanes-Müller reconstruction] These conditions, plus operational axioms, imply inner product structure.

7. **Inner product → Phase space (x, p):** [Mathematical consequence] Hilbert space admits position and momentum representations related by Fourier transform.

8. **Phase space + ℏ → Action S = ∫ p dx:** Action counts the number of ℏ-cells traversed in phase space.

9. **Action → Lagrangian S = ∫ L dt:** Standard Legendre transform (mathematical identity).

10. **Parsimony → Least action δS = 0:** Parsimony selects paths minimizing total specification cost—which is action.

**What this reveals:**

- Steps 1-5 are explicitly derived from 3FLL plus parsimony.
- Step 6 uses a Tier 2 theorem (Masanes-Müller)—presuppositions acknowledged.
- Steps 7-10 are mathematical consequences given prior structure.

The derivation does not claim that action follows from pure logic. It claims that action follows from 3FLL plus parsimony plus Tier 2 reconstruction inputs. The tier system makes explicit what is being assumed and where.

**Methodological value:** We can now ask precisely: Can the Tier 2 presuppositions (tomographic locality, etc.) be derived from 3FLL? This is a research question, not a gap hidden by "that's just how physics works."

### 4.2 Case Study 2: The Fine Structure Constant

**Traditional view:** The fine structure constant α ≈ 1/137.036 is a dimensionless constant characterising electromagnetic coupling strength. Its value is usually taken as empirical—a "dial setting" of the universe that could have been otherwise. Feynman famously called it "one of the greatest damn mysteries of physics."

**Logic Realism analysis:**

We present a *conjectural argument* relating α to spatial dimension (Longmire 2025b). This is speculative and requires independent verification:

1. **3FLL → Distinguishability → Spatial embedding dimension d:** Physical states require spatial embedding. The number of parameters required is 2d + 1 (positions + momenta + phase). [Status: heuristic argument, not rigorous derivation]

2. **Complexity requirement (Tier 1):** Information processing requires sufficient state capacity: 2^(2d+1) ≥ C_min where C_min ~ 100 (from observed complexity of chemistry, genetics). This requires d ≥ 3. [Status: uses anthropic/observational input]

3. **Stability requirement (Tier 3):** Stable orbits and atoms require d ≤ 3 (Ehrenfest 1917). This is a physical input—orbits are unstable in d > 3 dimensions under inverse-square forces. [Status: established physics, not derived from logic]

4. **Intersection:** d = 3 is uniquely selected.

5. **α from d = 3:** Information capacity 2^7 = 128, plus geometric embedding cost d² = 9, plus self-interaction correction, yields α⁻¹ ≈ 137.036. [Status: formula fit to one data point]

**Numerical result:** The formula gives α⁻¹ ≈ 137.036, compared to CODATA (2018) value 137.035999084—agreement to 8 parts per billion.

**Critical assessment:**

This result requires extreme caution:
- **Input sensitivity:** How does the result change if C_min varies within plausible bounds (50-200)? A full sensitivity analysis is needed.
- **Fitting vs. predicting:** With one free parameter (self-interaction correction) and one target value, agreement proves little. Independent predictions (other constants) are required.
- **Derivation gaps:** Steps 1-2 are heuristic, not rigorous. The phase-space formula is motivated but not proven.

We present this as an *intriguing numerical coincidence* that merits investigation, not as a confirmed derivation. The methodological point stands regardless: the tier system forces us to be explicit about which inputs are logic, which are physics, and which are observation. Whether the specific formula survives scrutiny is a separate question from whether the methodology is sound.

### 4.3 Deductive Risk Assessment

A rigorous methodology requires honest assessment of where derivations are vulnerable:

| Component | Risk Level | Analysis |
|-----------|------------|----------|
| Tier 1 Assumptions (I, I∞) | **Moderate** | Are these truly *required* for logic, or just for our version of physics? This is the primary philosophical pivot point. |
| Muon/Electron Ratio (92 ppm accuracy) | **Higher** | The 92 ppm accuracy (Longmire 2025b) suggests missing second-order corrections. Is this a new logic constraint or a Tier 3 physical detail? |
| Dimension d = 3 | **Critical** | Must verify no circularity: d = 3 must be strictly upstream of α. Verified: d depends on complexity + stability, not α. |
| Stability Constraint | **Moderate** | Uses Tier 3 physics (Ehrenfest 1917). A fully logic-first derivation would need to derive stability from 3FLL. |

**The "Leaked Assumptions" discipline:** Each derivation must explicitly track implicit dependencies. If a step relies on ANY property, structure, or assumption not explicitly in the tier tracking—whether mathematical (topological, measure-theoretic), physical (stability, symmetry), logical (choice axioms), or observational (anthropic bounds)—flag it immediately. This prevents pseudo-derivation.

### 4.4 What If Tier 2/3 Assumptions Remain Irreducible?

The strong Logic Realism Thesis holds that all Tier 2/3 inputs are ultimately derivable from 3FLL. But what if this hope fails? What if some presuppositions (tomographic locality, Hilbert space structure, stability constraints) are genuinely irreducible—not derivable from logic alone?

**The program remains valuable even under this weaker reading:**

1. **Assumption tracking:** The tier system clarifies *which* assumptions are irreducible and *where* they enter. This is progress over treating all assumptions as equally opaque.

2. **Partial derivations:** Even if the full chain fails, partial derivations matter. Showing that continuity follows from parsimony, or that phase space structure follows from reconstruction axioms, reduces the number of independent assumptions—even if the reconstruction axioms themselves remain underived.

3. **Comparative analysis:** Different foundational approaches can be compared by their tier profiles. A framework requiring fewer Tier 2/3 inputs (or weaker ones) is preferable, ceteris paribus.

4. **Research guidance:** Marking assumptions as "Open" identifies research targets. Even if some remain permanently irreducible, the attempt to derive them may yield insights.

**The fallback position:** Logic Realism is compatible with the discovery that some physical structure is genuinely contingent—not fixed by logic. In that case, the thesis would weaken to: "3FLL constrain physical structure, but do not uniquely determine it." The methodology (tier tracking, presupposition analysis) survives this weakening intact.

We present Logic Realism as an ambitious research program, not an all-or-nothing foundational gambit. The strong thesis is worth pursuing because it is falsifiable: if Tier 2/3 inputs demonstrably cannot be derived, we learn something important about the limits of logic-first approaches.

---

## 5. Implications and Open Questions

### 5.1 For Philosophy of Science

**Reconceiving the analytic/synthetic distinction:** Quine (1951) famously attacked the analytic/synthetic distinction as a "dogma of empiricism." Our framework suggests a qualified rehabilitation. 3FLL are neither purely analytic (about meanings) nor synthetic (about the world) in the traditional sense. They are *constitutive of coherent worldhood*—conditions for there being a world describable at all. This is not the old analyticity but something new.

**Naturalism and logic:** A tension exists between naturalism (all truths are empirical/scientific) and the apparent necessity of logical laws. If 3FLL are constitutive of reality, logic is not merely a human invention but a discovery of necessary structure. This has implications for debates over logical pluralism (Beall and Restall 2006). Alternative logics (intuitionistic, paraconsistent) may be useful formal systems but cannot replace 3FLL as constitutive principles without sacrificing coherence.

**The status of mathematics:** On our view, mathematics is the study of structures compatible with 3FLL. This grounds mathematics in something more than convention (pace formalism) but less than a Platonic realm of abstract objects. Mathematical truths are necessary given 3FLL—but 3FLL themselves are not arbitrary postulates; they are self-grounding.

### 5.2 For Foundations of Physics

**Unification:** If diverse physical principles (action, quantum mechanics, spacetime structure) are downstream of 3FLL, apparent diversity may mask underlying unity. The tier system provides a framework for investigating this: show that apparently independent principles have common roots in the derivation cascade.

**Quantum gravity:** Spacetime structure itself may be constrained by 3FLL. The problem of quantum gravity—reconciling general relativistic spacetime with quantum mechanics—may have a new angle: what spacetime structures are logically coherent given quantum distinguishability constraints? The derivation of d = 3 (Section 4.2) is a preliminary result in this direction.

**Constants of nature:** Unexplained constants (α, particle masses, cosmological constant) become research questions with precise form: what is their derivation chain? What tier inputs do they require? The 8 ppb result for α suggests that at least some "free parameters" may be structurally constrained.

### 5.3 Open Questions for the Logic Realism Program

**Completeness:** Can all Tier 2/3 inputs eventually be derived from 3FLL? This is the strong version of the Logic Realism Thesis. We do not claim it is true—we claim it is a well-defined research question. Current status: many gaps remain; the thesis is a guiding conjecture.

**Uniqueness:** Does 3FLL + parsimony uniquely determine physics, or are there multiple coherent realisations? If multiple, what selects among them? This connects to multiverse debates and the anthropic principle.

**The status of parsimony:** We frequently invoke parsimony (minimize specification cost) as a selection principle. Is this derived from 3FLL or an additional assumption? One argument: L₂ (Non-Contradiction) rules out chaos (everything true); parsimony is the limit of non-chaos—minimum specification consistent with determinacy. But this argument needs refinement.

**Empirical tests:** The derivation of α (Section 4.2) makes a precise numerical prediction. Further predictions (particle mass ratios, cosmological parameters) could provide empirical tests. If the theory predicts values that disagree with measurement, it is falsified. This distinguishes Logic Realism from pure philosophy.

---

## 6. Conclusion

The Logic Realism Thesis proposes that 3FLL function as constitutive constraints on coherent reality, not merely on valid reasoning. This generates a methodology—the tiered analysis of theoretical assumptions—that makes explicit what is usually hidden in foundational work.

We do not claim to have proven that all physics derives from pure logic. Such a claim would be premature and probably false. We claim that:

1. **Framing 3FLL as constitutive provides a coherent research program.** The thesis organises foundational questions and suggests derivation strategies.

2. **The tier system clarifies assumption dependencies in existing theories.** Whether or not the Logic Realism Thesis is correct, the practice of tracking which assumptions enter at which level improves foundational analysis.

3. **Concrete derivation chains demonstrate the methodology's value.** The action functional and fine structure constant case studies show how the tier system works in practice.

4. **Open questions are precisely locatable within the framework.** Instead of vague claims about "understanding physics," we have specific questions: Can Tier 2 presuppositions be derived from 3FLL? Is parsimony independent or derived? What predicts mass ratios?

The Logic Realism approach does not compete with physics but provides a meta-framework for analysing what physics presupposes and what it achieves. It is offered not as established truth but as a research program worthy of investigation.

---

## References

Beall, J.C. (2009) *Spandrels of Truth*. Oxford: Oxford University Press.

Beall, J.C. and Restall, G. (2006) *Logical Pluralism*. Oxford: Oxford University Press.

Brukner, Č. and Zeilinger, A. (2003) 'Information and Fundamental Elements of the Structure of Quantum Theory', in Castell, L. and Ischebeck, O. (eds.) *Time, Quantum and Information*. Berlin: Springer, pp. 323-354.

Carnap, R. (1956) 'The Methodological Character of Theoretical Concepts', in Feigl, H. and Scriven, M. (eds.) *Minnesota Studies in the Philosophy of Science*, Vol. 1. Minneapolis: University of Minnesota Press, pp. 38-76.

Chiribella, G., D'Ariano, G.M. and Perinotti, P. (2011) 'Informational derivation of quantum theory', *Physical Review A*, 84(1), 012311.

CODATA (2018) *CODATA Recommended Values of the Fundamental Physical Constants: 2018*. Gaithersburg: National Institute of Standards and Technology.

Duhem, P. (1954) *The Aim and Structure of Physical Theory*. Translated by P.P. Wiener. Princeton: Princeton University Press. (Original work published 1906).

Ehrenfest, P. (1917) 'In what way does it become manifest in the fundamental laws of physics that space has three dimensions?', *Proceedings of the Amsterdam Academy*, 20, pp. 200-209.

Friedman, M. (2001) *Dynamics of Reason*. Stanford: CSLI Publications.

Gleason, A.M. (1957) 'Measures on the Closed Subspaces of a Hilbert Space', *Journal of Mathematics and Mechanics*, 6(6), pp. 885-893.

Hanson, N.R. (1958) *Patterns of Discovery*. Cambridge: Cambridge University Press.

Hardy, L. (2001) 'Quantum Theory From Five Reasonable Axioms', arXiv:quant-ph/0101012.

Hempel, C.G. (1965) *Aspects of Scientific Explanation*. New York: Free Press.

Longmire, J.D. (2025a) 'Issue 013: Derivation of the Logical Action Functional', Logic Realism Theory Technical Report. Available at: https://github.com/jdlongmire/logic-realism-theory

Longmire, J.D. (2025b) 'Issue 012: Derivation of the Fine Structure Constant', Logic Realism Theory Technical Report. Available at: https://github.com/jdlongmire/logic-realism-theory

Maddy, P. (2007) *Second Philosophy: A Naturalistic Method*. Oxford: Oxford University Press.

Masanes, L. and Müller, M.P. (2011) 'A derivation of quantum theory from physical requirements', *New Journal of Physics*, 13, 063001.

Nagel, E. (1961) *The Structure of Science: Problems in the Logic of Scientific Explanation*. New York: Harcourt, Brace & World.

Quine, W.V.O. (1951) 'Two Dogmas of Empiricism', *Philosophical Review*, 60(1), pp. 20-43.

Priest, G. (2006) *In Contradiction: A Study of the Transconsistent*. 2nd edn. Oxford: Oxford University Press.

Rovelli, C. (1996) 'Relational quantum mechanics', *International Journal of Theoretical Physics*, 35(8), pp. 1637-1678.

Sher, G. (2011) 'Is logic in the mind or in the world?', *Synthese*, 181(2), pp. 353-365.

Stone, M.H. (1932) 'On One-Parameter Unitary Groups in Hilbert Space', *Annals of Mathematics*, 33(3), pp. 643-648.

Wheeler, J.A. (1990) 'Information, Physics, Quantum: The Search for Links', in Zurek, W.H. (ed.) *Complexity, Entropy, and the Physics of Information*. Redwood City: Addison-Wesley, pp. 3-28.

Zeilinger, A. (1999) 'A Foundational Principle for Quantum Mechanics', *Foundations of Physics*, 29(4), pp. 631-643.

---

## Appendix A: Formal Statement of the Tier System

### A.1 Tier 1: Structural Assumptions for 3FLL Application

**Definition:** Tier 1 assumptions are structural requirements for 3FLL to have non-trivial application to physical reality.

**Current Tier 1 Assumptions:**

| Axiom | Statement | Justification |
|-------|-----------|---------------|
| I (Domain) | There exists a non-empty domain of discourse | 3FLL require something to govern |
| I∞ (Unboundedness) | The domain has no arbitrary finite cardinality bound | Non-trivial application requires richness |

**Status:** These are substantive assumptions, not pure consequences of 3FLL. They are part of the Logic Realism Thesis.

### A.2 Tier 2: Established Mathematical Reconstruction Results

**Definition:** Tier 2 inputs are established mathematical theorems whose presuppositions are explicitly tracked.

**Usage Protocol:**
1. Identify the theorem being used
2. List its presuppositions
3. Note whether each presupposition is derived from 3FLL, assumed at Tier 1, or open

### A.3 Tier 3: Physical Principles

**Definition:** Tier 3 inputs are empirically motivated physical principles whose logical status is tracked.

**Categories:**
- Empirical regularities (observed patterns elevated to principles)
- Symmetry consequences (derivable from spacetime structure)
- Stability requirements (conditions for existence of stable structures)

---

## Appendix B: Presupposition Tracking Tables

### B.1 Masanes-Müller (2011) Reconstruction

| Presupposition | Description | LRT Status |
|----------------|-------------|------------|
| Tomographic locality | Global states determined by local measurements | Open |
| Continuous reversibility | Reversible transformations form continuous group | Partially derived (Theorem 6.1) |
| Subspace axiom | Pure states on subspaces extend to global states | Open |
| Composite systems | Systems can be combined | Open (relates to Tier 1) |
| Finite information | Finite information per system | Derived (Theorem 4.2) |

### B.2 Gleason (1957) Theorem

| Presupposition | Description | LRT Status |
|----------------|-------------|------------|
| Hilbert space | States form a Hilbert space | From reconstruction |
| Dimension ≥ 3 | At least 3-dimensional | From d = 3 derivation |
| Frame functions | Probability measures on projectors | Derived from distinguishability |

### B.3 Stone (1932) Theorem

| Presupposition | Description | LRT Status |
|----------------|-------------|------------|
| Hilbert space | States form a Hilbert space | From reconstruction |
| Strong continuity | One-parameter group is strongly continuous | From continuity (Theorem 5.1) |
| Unitary group | Transformations are unitary | From reversibility (Theorem 6.1) |

---

**Word count:** ~8,500
**Target venues:** Foundations of Physics, Studies in History and Philosophy of Science Part B, Philosophy of Science, Synthese

---

*Document created: 2025-12-17 (Session 46.0)*
*Last updated: 2025-12-17 (Revised per external review feedback)*
