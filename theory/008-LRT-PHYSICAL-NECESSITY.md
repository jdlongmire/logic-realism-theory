# The Physical Necessity of Fundamental Logic

## Logic Realism Theory, Paper VIII

James D. Longmire
Northrop Grumman Fellow (unaffiliated research)
ORCID: 0009-0009-1383-7698
Correspondence: jdlongmire@outlook.com
Date: April 2026
Status: Draft
Series: LRT Paper 008
Upstream: 000-TRM-FOUNDATIONS, 001-LRT-TAB-PHILOSOPHY

---

## Abstract

This paper develops a single argument: the three fundamental laws of logic (Identity, Non-Contradiction, Excluded Middle) are not instruments applied to physics from outside but constitutive preconditions for the existence of anything physics could describe. The argument proceeds in five stages. First, every physical theory requires determinate states; second, determinacy is equivalent to satisfaction of $L_3$; third, the denial of $L_3$'s physical necessity is self-refuting, deploying $L_3$ in the act of denying it; fourth, this self-refutation is not epistemic but transcendental, establishing that $L_3$ constrains what can obtain, not merely what can be represented; and fifth, the removal of $L_3$ entails a deductive cascade from the absence of distinguishable configurations to the impossibility of states, transitions, time, dynamics, and physics. The argument is named *The Physical Necessity of Fundamental Logic* (PNFL) to distinguish it from weaker claims that logic is methodologically useful or cognitively indispensable. PNFL establishes that the relationship between logic and physics is not one of application but of constitution: physics does not *use* $L_3$; physics *is* the domain of structure that $L_3$ makes possible.

**Keywords:** logical necessity, determinacy, transcendental argument, philosophy of physics, identity conditions, constitutive grounding, logic realism

---

## 1. The Question

Is logic necessary for physics, or merely useful?

The question is rarely posed this sharply. Physicists assume logical consistency in their formalisms without examining whether that assumption reflects something about reality or something about the cognitive requirements of formalism-building. Philosophers of physics, when they address the issue at all, typically treat logic as a background condition too obvious to require defense.

But the question has consequences. If logic is merely useful, then reality might not be logical. A world without determinate identity conditions, without the exclusion of contradiction, without closure under truth-value assignment, would be strange, but not impossible. Physics as we know it would not apply there, but something else might. The space of possible realities would be broader than the space of logically structured ones.

If logic is necessary, this broader space collapses. "A world without $L_3$" is not a strange possibility; it is not a possibility at all. The phrase fails to refer, in the same way that "the largest prime number" fails to refer. The relationship between logic and physics is then not one of application (we apply logical tools to an independently existing reality) but of constitution (reality is the domain of structure that logical constraint makes possible).

The argument developed here defends the second position and names it: *The Physical Necessity of Fundamental Logic* (PNFL).

---

## 2. Definitions

**$L_3$** denotes the three fundamental laws of logic understood as ontological constraints, not inference rules:

| Law | Symbolic | Ontological Content |
|-----|----------|---------------------|
| **Identity** | $A = A$ | Every entity is self-identical; a thing is what it is and not something else |
| **Non-Contradiction** | $\lnot(A \land \lnot A)$ | No entity both possesses and lacks a given property in the same respect at the same time |
| **Excluded Middle** | $A \lor \lnot A$ | For every well-formed predicate and every entity, the predicate either holds or does not |

These laws are here understood prescriptively, not descriptively. They do not summarize observed regularities about how things happen to behave. They specify constraints on what can obtain. The distinction is critical: a descriptive reading allows the possibility that reality might violate these regularities (we just have not observed such a violation yet), whereas a prescriptive reading entails that violation is not merely unobserved but impossible.

**Determinacy** is the property of having well-defined identity conditions. A state is determinate when it is self-identical, when it does not both possess and lack a given property, and when every well-formed predicate about it has a truth value. Determinacy, so defined, is logically equivalent to satisfaction of $L_3$. This equivalence is not a theorem to be proved but a conceptual identity: to say "the state is determinate" and to say "the state satisfies Identity, Non-Contradiction, and Excluded Middle" is to say the same thing in different registers.

**Physics** is any theoretical framework that describes systems with states, transitions between states, and dynamical laws governing those transitions. This definition is deliberately broad. It encompasses classical mechanics, quantum mechanics, general relativity, quantum field theory, statistical mechanics, and any speculative successor theory. The claim of PNFL is that every member of this class presupposes $L_3$.

---

## 3. The Argument

### 3.1 Premise 1: Physics Requires Determinate States

Every physical theory posits systems with states. Classical mechanics assigns phase-space points. Quantum mechanics assigns vectors in Hilbert space. General relativity assigns metric tensors on manifolds. Statistical mechanics assigns probability distributions over microstates. In every case, the state must be determinate: it must be *this* state and not *that* one.

The requirement is not negotiable. Without determinate states:

- There are no initial conditions (nothing is the case at $t_0$)
- There are no dynamical laws (laws map states to states; if there are no states, there is nothing for laws to operate on)
- There are no observables (an observable assigns a value to a state; absent a state, nothing receives a value)
- There are no predictions (a prediction is a statement about which state will obtain; if no state is determinate, the concept of prediction is empty)

Even theories that appear to challenge determinacy in fact presuppose it. Quantum superposition is determinate: $\lvert\psi\rangle = \alpha\lvert 0\rangle + \beta\lvert 1\rangle$ is a perfectly well-defined vector, self-identical, distinguishable from $\lvert\phi\rangle$ when $\langle\psi\lvert\phi\rangle \neq 1$. What is indeterminate is the *outcome* of a measurement, not the *state*. The state is a determinate mathematical object; it describes a physical situation with determinate properties (energy, entanglement entropy, expectation values). The interpretive question of what those properties *mean* is downstream of the formal requirement that the state *be* something.

Stochastic theories are determinate: the probability distribution is a well-defined object, even when individual outcomes are not predetermined. Chaotic systems are determinate: sensitivity to initial conditions presupposes that initial conditions exist and are precise. Quantum field theory is determinate: the vacuum state $\lvert 0 \rangle$ is a specific, unique state of the Fock space.

**Premise 1:** Every physical theory requires that systems have determinate states. No exception exists in the known theoretical landscape, and no exception is conceivable within the definition of physics given above.

### 3.2 Premise 2: Determinacy Requires $L_3$

This premise is the conceptual-identity claim: determinacy *is* satisfaction of $L_3$. The two descriptions pick out the same property.

Consider what would happen to a state $s$ if each component of $L_3$ were individually removed.

**Remove Identity.** $s$ is not self-identical. The state does not equal itself. "State $s$" fails to refer to any one thing, because $s$ is not determinately $s$. There is no difference between $s$ and $s'$, not because they happen to share all properties (Leibniz indiscernibility), but because the concept of "being one thing" has been removed. State spaces require their elements to be self-identical. A Hilbert space whose vectors are not self-identical is not a vector space. A phase space whose points are not self-identical is not a set.

**Remove Non-Contradiction.** $s$ both possesses and lacks property $P$. This is not superposition: a superposition state has determinate expansion coefficients and a determinate norm. This is ontological: the state genuinely has $P$ and genuinely lacks $P$, in the same respect, at the same time. Every predicate collapses: "spin-up" and "not spin-up" are compatible, so "spin-up" carries no information. Measurement outcomes become meaningless: an outcome that both occurred and did not occur is not an outcome. The Born rule assigns probabilities to mutually exclusive events; if events are not exclusive, the probability space is ill-defined.

**Remove Excluded Middle.** For some predicate $P$ and state $s$, $s$ neither has $P$ nor lacks $P$. This is not epistemic uncertainty (we do not *know* whether $s$ has $P$). This is ontological incompleteness: there is no fact of the matter. The state is a partial function over the space of predicates, undefined at $P$. But physics requires total functions: Hamiltonians must be defined everywhere in their domain; wavefunctions must assign amplitudes to every basis state; metrics must be defined at every point of the manifold (or the singularity is itself a determinate feature of the geometry). A state with ontological gaps is not a state any physical theory can use.

**Premise 2:** A state is determinate if and only if it satisfies $L_3$. Determinacy without $L_3$ is a phrase without a referent.

### 3.3 Intermediate Conclusion: $L_3$ Is Necessary for Physics

From Premises 1 and 2:

1. Physics requires determinate states. (Premise 1)
2. Determinacy requires $L_3$. (Premise 2)
3. Therefore, physics requires $L_3$. (Hypothetical syllogism)

This conclusion is logically valid. Its soundness depends entirely on the truth of the premises. Premise 1 is empirically uncontested and conceptually unavoidable. Premise 2 is a conceptual identity claim. The intermediate conclusion follows necessarily.

But "logically valid" is not yet "transcendentally necessary." The argument so far shows that physics, as defined, cannot proceed without $L_3$. It does not yet show that the denial of $L_3$'s necessity is incoherent. A critic might say: "You have shown that *our* physics requires $L_3$. Perhaps there is a physics beyond our conception that does not."

The next stage of the argument closes that escape route.

### 3.4 Premise 3: The Denial Is Self-Refuting

Suppose someone asserts:

$$D: \quad \text{"$L_3$ is not necessary for physics."}$$

Consider what this assertion presupposes.

**$D$ presupposes Identity.** The assertion is self-identical. It says what it says and not something else. If the assertion were not self-identical, it would not be a determinate claim; it could equally well mean its own negation or anything at all. The act of making claim $D$ requires that $D = D$.

**$D$ presupposes Non-Contradiction.** The assertion is not simultaneously true and false. The speaker intends $D$ to be true, which requires that $D$ not also be false. If $D$ could be both true and false, then asserting $D$ would accomplish nothing, because the assertion would be compatible with $\lnot D$. The act of denying $L_3$'s necessity requires that the denial not be self-contradictory.

**$D$ presupposes Excluded Middle.** The assertion has a truth value. $D$ is either true or false. If $D$ were neither true nor false, it would not be a claim at all; it would be a pseudo-proposition occupying no position in logical space. The act of making a truth-valued assertion requires that truth-values exist and are assigned.

The denial of $L_3$'s necessity therefore deploys $L_3$ in the act of denying it. This is not merely pragmatically self-defeating (like saying "I am not speaking English" in English, where the content is false but the utterance is coherent). It is logically self-refuting: the content of $D$ requires the falsity of $D$'s own presuppositions. If $L_3$ is not necessary, then $D$ itself might not be self-identical (Identity failure), might be both true and false (Non-Contradiction failure), or might lack a truth value (Excluded Middle failure). In any of these cases, $D$ fails as an assertion.

**Premise 3:** Any assertion that $L_3$ is not necessary presupposes $L_3$, and therefore refutes itself.

### 3.5 Premise 4: The Self-Refutation Is Transcendental, Not Epistemic

The self-refutation in §3.4 admits two readings.

**Epistemic reading:** We cannot *think* without $L_3$. Our cognitive apparatus requires logical structure. But reality itself might not have it; we simply cannot conceive of such a reality. $L_3$ is a condition on representation, not on being. (This is Kant's position as reconstructed by Stroud [1968].)

**Transcendental reading:** $L_3$ is a condition on being, not merely on our representation of being. A reality without $L_3$ is not merely inconceivable; it is impossible. "Reality without determinacy" fails to refer, because determinacy is constitutive of what it means for anything to be the case.

PNFL defends the transcendental reading. The defense turns on the nature of determinacy.

Determinacy is not a lens through which we view reality. It is the property of having identity conditions. A configuration that is not self-identical does not merely evade our representation; it fails to *be* anything. A predicate that both holds and does not hold of an entity does not merely confuse us; it carries no information about the entity because the entity has no determinate property for the predicate to track. An entity for which some predicate neither holds nor fails to hold is not merely unknown to us; it is ontologically incomplete in a way that precludes its being a physical system.

The gap between "conditions for thinking about $X$" and "conditions for $X$ existing" arises when there is a coherent space between the two. For empirical properties, the gap is real: we cannot think about the interior of a black hole without general relativity, but the interior exists independently of our theory. For determinacy, no such gap exists. To *be* is to be determinate (Quine's dictum, reinterpreted ontologically). The concept of an indeterminate entity is not a concept of a strange entity; it is a concept with no referent.

This argument follows the constitutive-grounding strategy developed by Cassam (1987) and Stern (2000): transcendental arguments establish objective conclusions when the relevant conditions are genuinely constitutive of the domain rather than merely regulative of thought about it. $L_3$ is constitutive of determinate being, not merely regulative of our reasoning about it.

**Premise 4:** The necessity of $L_3$ for physics is transcendental (constitutive of what can obtain) rather than epistemic (a condition on our representation).

### 3.6 The Deductive Cascade

With all four premises established, the full consequence of $L_3$'s removal can be traced as a deductive cascade. Each step follows necessarily from the previous.

**Step 1: No $L_3 \implies$ no distinguishable configurations.**

Without Identity, no configuration is self-identical. Without Non-Contradiction, configurations both possess and lack every property. Without Excluded Middle, the predicate space is incomplete. In each case, the result is the same: configurations cannot be distinguished. And if they cannot be distinguished, they are not configurations. "Configuration" means a specific arrangement of properties; without specificity, the concept is empty.

**Step 2: No configurations $\implies$ no states.**

A state is a configuration of a physical system. If there are no configurations, there are no states. This is not the claim that we cannot determine which state the system is in (epistemic indeterminacy); it is the claim that there is no state for the system to be in (ontological absence).

**Step 3: No states $\implies$ no transitions.**

A transition is a mapping from one state to another. If there are no states, there is nothing for a transition to connect. Dynamical laws, which specify transitions, have an empty domain.

**Step 4: No transitions $\implies$ no time.**

Time, in physics, is the parameter that orders transitions. If there are no transitions, there is nothing for time to order. Time is not an independently existing container waiting to be filled with events; it is the structure of sequential change. Without sequential change, "time" refers to nothing.

**Step 5: No time $\implies$ no dynamics.**

Dynamics is the study of how states evolve in time. Without time, evolution is undefined. The Schrödinger equation, Hamilton's equations, the Einstein field equations, the Boltzmann equation: all describe temporal evolution of states. Without temporal evolution, they are not merely unsolvable; they are syntactically well-formed strings with no physical referent.

**Step 6: No dynamics $\implies$ no physics.**

Physics, by definition, describes systems with states, transitions, and dynamical laws. If none of these exist, physics has no subject matter. Not a different subject matter; no subject matter.

The cascade:

$$\text{No } L_3 \implies \text{no determinacy} \implies \text{no states} \implies \text{no transitions} \implies \text{no time} \implies \text{no dynamics} \implies \text{no physics}$$

Each implication is deductively necessary. The cascade is not a slippery slope (each step might not follow); it is a chain of entailments (each step must follow).

### 3.7 The Argument Complete

The five stages combine:

| Stage | Content | Section |
|-------|---------|---------|
| 1 | Physics requires determinate states | §3.1 |
| 2 | Determinacy requires $L_3$ | §3.2 |
| 3 | The denial of $L_3$'s necessity is self-refuting | §3.4 |
| 4 | The self-refutation is transcendental, not epistemic | §3.5 |
| 5 | Removal of $L_3$ entails the impossibility of physics via deductive cascade | §3.6 |

PNFL concludes: $L_3$ is not an instrument applied to physics from outside. It is a constitutive precondition for the existence of anything physics could describe. Physics does not *use* logic. Physics *is* the domain of structure that logic makes possible.

---

## 4. Objections and Replies

### 4.1 The Dialetheist Objection

**Objection:** Dialetheism (Priest 2006) holds that some contradictions are true. If true contradictions exist, Non-Contradiction fails, and $L_3$ is not necessary.

**Reply:** Dialetheism is a formal system: a logic in which $A \land \lnot A$ can be true for some $A$ without explosion (inference of everything). It is a modification of *inference rules*, not of *ontological constraints*.

The question is not whether a formal system can tolerate contradictions. Formal systems can be defined however one likes. The question is whether reality can contain a genuine ontological contradiction: a state of affairs in which an entity determinately possesses and determinately lacks a property in the same respect at the same time.

Dialetheist proposals invariably involve semantic paradoxes (the Liar), vagueness, or change through time. None of these involve a clear case of an entity possessing and lacking a physical property simultaneously. The Liar sentence is a linguistic construction; vagueness is an epistemic or semantic phenomenon; change through time involves different temporal indices, not the same respect at the same time.

PNFL concerns physical actuality, not formal systems. A physics built on dialetheist logic would require physical systems that genuinely possess and lack the same property at the same time. No such system has been identified, and the concept appears incoherent when pressed: a particle that is genuinely spin-up and genuinely not spin-up (not in superposition, which is a determinate state, but in ontological contradiction) is not a strange particle; it is not a particle.

### 4.2 The Intuitionist Objection

**Objection:** Intuitionistic logic rejects Excluded Middle. If respectable mathematics can proceed without it, perhaps physics can too.

**Reply:** Intuitionistic logic restricts Excluded Middle *epistemically*: a proposition is true only if constructively provable, and $A \lor \lnot A$ is not asserted when neither $A$ nor $\lnot A$ has been proved. This is a standard for *assertion*, not a claim about *being*.

Intuitionism does not deny that mathematical objects have determinate properties. It denies that we can assert those properties absent proof. The ontological question is different. PNFL claims that physical states have determinate properties whether or not anyone has measured them or constructed a proof. This is consistent with the motivations of intuitionism (epistemic caution) while rejecting its extension to ontology.

Moreover, intuitionistic quantum mechanics (Isham, Butterfield) retains local determinacy within each classical context. The topos-theoretic approach does not deny Excluded Middle ontologically; it relativizes it to contexts. Within each context, Excluded Middle holds. PNFL requires only that Excluded Middle hold within the actual world, which every interpretation of quantum mechanics grants.

### 4.3 The Quantum Logic Objection

**Objection:** Quantum logic (Birkhoff and von Neumann 1936) modifies the distributive law. Perhaps the laws of logic are empirical and revisable, not necessary.

**Reply:** Quantum logic modifies the lattice structure of propositions about quantum systems. It replaces the Boolean distributive law with a weaker orthomodular law. But it does not abandon Identity, Non-Contradiction, or Excluded Middle.

In quantum logic, every proposition about a quantum system has a truth value relative to a state. The projection lattice satisfies Non-Contradiction: no projection is both $P$ and $P^\perp$. Excluded Middle holds within the lattice: $P \lor P^\perp = I$ (the identity operator). Identity is trivially satisfied: every projection is self-identical.

Quantum logic modifies the *structure of conjunction and disjunction* (specifically, distribution), not the *fundamental laws*. The three laws PNFL identifies as constitutive survive the transition from classical to quantum logic intact. The revision is real, but it is a revision of *distributivity*, not of $L_3$.

### 4.4 The "Physics Beyond Our Conception" Objection

**Objection:** Perhaps there is a physics radically unlike anything we can conceive, one that does not require determinate states. Our inability to conceive it does not make it impossible.

**Reply:** This objection conflates epistemic limitation with ontological impossibility. The claim is not "we cannot conceive of physics without $L_3$, so there isn't any." The claim is "physics without $L_3$ is a phrase without a referent, because 'physics' means description of systems with determinate states, and 'determinate states' means states satisfying $L_3$."

The objection asks us to imagine a domain of study that describes systems without states, transitions without endpoints, dynamics without time, and regularities without entities to be regular. That is not a more general physics. It is the absence of a subject.

The move from "we cannot conceive $X$" to "$X$ is impossible" is indeed generally suspect (the argument from ignorance). But PNFL does not make this move. It makes the move from "$X$ is self-contradictory" to "$X$ is impossible," which is logically valid. "Physics without $L_3$" is self-contradictory because the definition of physics includes determinate states, and determinate states just are $L_3$-satisfying states.

### 4.5 The "Logic Is Descriptive, Not Prescriptive" Objection

**Objection:** The laws of logic are generalizations from experience. They describe what we have observed about reality, not what reality must be. Future experience might revise them.

**Reply:** This empiricist account of logic (Mill, Quine in some moods) makes logic continuous with natural science. If logic is revisable in light of experience, then $L_3$ could in principle be falsified.

But what would constitute a falsification? An entity that is not self-identical? An observable that both obtains and does not obtain? A predicate that neither holds nor fails to hold of a physical system? None of these are empirically accessible. They are not the sort of thing an experiment could reveal, because every experiment involves determinate outcomes (the detector clicked or it did not; the pointer moved to position $x$ or it did not; the interference pattern appeared or it did not). Empirical revision of $L_3$ requires empirical access to $L_3$-violations, and $L_3$-violations are not the sort of thing that can be empirically accessed, because empirical access presupposes $L_3$.

This is not a dogmatic assertion that $L_3$ cannot be revised. It is the observation that the revisability thesis is internally incoherent: it proposes that experience could teach us that the preconditions for experience do not hold.

---

## 5. The Recursive Structure

PNFL has a feature that distinguishes it from most philosophical arguments: it is recursively self-supporting. The argument for $L_3$'s necessity deploys $L_3$, and this is not a circularity but a confirmation.

Ordinarily, an argument whose conclusion appears in its premises is circular and therefore defective. But PNFL does not assume $L_3$ in its premises. Its premises are:

1. Physics requires determinate states. (Observation about the structure of physical theories)
2. Determinacy is equivalent to $L_3$ satisfaction. (Conceptual identity)
3. The denial of $L_3$'s necessity presupposes $L_3$. (Observation about the structure of denial)
4. The presupposition is constitutive, not merely cognitive. (Argument about the nature of determinacy)

The conclusion is that $L_3$ is physically necessary. The fact that the argument itself is conducted within $L_3$ (each premise is self-identical, the argument does not contradict itself, each premise has a truth value) is not a smuggled assumption. It is a consequence of the conclusion, manifested in the act of arguing. The argument works precisely because $L_3$ is inescapable: any attempt to reason, including any attempt to reason against $L_3$, operates within $L_3$.

This recursive structure is the hallmark of transcendental arguments about truly fundamental conditions. The argument for the existence of truth is conducted in a language that presupposes truth. The argument for the existence of meaning is itself meaningful. These arguments are not circular; they are reflexively confirmed. The conclusion is demonstrated by the possibility of the demonstration itself.

The recursive structure also explains why PNFL cannot be formalized as a simple syllogism and then "accepted or rejected." Rejecting it requires conducting a counter-argument, which presupposes what is being denied. The argument does not merely have force; it has force that increases under opposition, because opposition deploys the very thing it contests.

The recursive confirmation extends beyond formal inference to every act of evaluation. To assess whether an argument is strong or weak, whether a premise is defensible or exposed, whether a reply succeeds or fails, requires that "strong" and "weak" be determinate predicates, that an argument cannot simultaneously succeed and fail in the same respect, and that every argument occupies some position in the evaluative space between sound and unsound. Critical judgment is $L_3$-governed. This means the scope of PNFL's recursive confirmation is not limited to the logician constructing proofs or the physicist deriving equations. It encompasses the referee assessing this paper, the experimentalist deciding whether a result confirms a hypothesis, and the philosopher judging whether an objection lands. No evaluative act escapes $L_3$'s jurisdiction, because no evaluative act can be conducted without determinate predicates, exclusive alternatives, and truth-valued verdicts. The demonstration of PNFL is therefore not merely confirmed by the act of arguing for it. It is confirmed equally by every act of arguing against it, every act of judging it, and every act of reading it with the intent to assess whether it is true.

### 5.1 Objections as Instances, Not Counters

Every articulated objection to PNFL aims to be a determinate, truth-evaluable claim that is not trivially self-contradictory. In doing so, it instantiates precisely the structure PNFL identifies as fundamental: the objection must be self-identical (Identity), must not both affirm and deny its own content in the same respect at the same time (Non-Contradiction), and must occupy a position in a space of truth and falsity (Excluded Middle). An "objection" that abandons these conditions ceases to be an objection in the relevant sense; it is not a defective counter-argument but a withdrawal from the practice of giving reasons. Hence objections to PNFL cannot undercut its claim that $L_3$ is constitutive of physical intelligibility; at best, they *instantiate* that claim in the very act of trying to deny it.

A common response is to treat this dependence as merely *local*: perhaps objections to PNFL must observe $L_3$ within the contingent practice of argumentation, but this does not show that $L_3$ is constitutive of reality or of physics. This reply mislocates the point. The relevant practice is not an optional discourse game but the very activity of making determinate, truth-evaluable claims about what can obtain. If there is a "logic of reality" distinct from the logic of such claims, it must still allow determinate states of affairs that can be truly described, on pain of collapsing the notion of a physical fact; and PNFL's contention is that this determinacy *just is* $L_3$-structure. Thus the dependence is not parochial to a particular inferential practice but tracks the minimal conditions for there being objective states for physics, or any theory, to be about at all.

Put differently: rhetorical ingenuity cannot overturn constitutive structure. Once we see that $L_3$ fixes the minimal conditions for physical intelligibility, sophistical maneuvers that trade on ambiguity or partial suspension of those conditions do not reveal "deeper possibilities"; they simply step outside the space where assertions can be true or false at all.

---

## 6. Constitutive vs. Instrumental: Why the Distinction Matters

The central claim of PNFL is that the relationship between logic and physics is constitutive, not instrumental. The distinction requires elaboration.

### 6.1 The Instrumental Picture

On the instrumental picture, logic is a tool. Physicists use logical inference to derive consequences from axioms, check consistency of theories, and structure arguments. Logic is indispensable for *doing* physics, but it is not part of *what physics describes*. Reality is one thing; our logical tools for describing it are another.

This picture permits a gap between reality and logic. Reality might, in principle, be alogical: a domain where our tools do not apply. We would be unable to describe or understand such a domain, but it could exist. Logic constrains us, not the world.

Most working physicists operate within the instrumental picture without examining it. It is the default assumption of methodological naturalism: the world is what it is, and our theories (including our logic) are our best attempts to describe it.

### 6.2 The Constitutive Picture

On the constitutive picture, logic is not a tool applied to an independently existing reality. It is part of what constitutes reality. The laws of logic are not generalizations about how things happen to behave; they are conditions for there being things at all.

On this picture, the gap between reality and logic closes. "Alogical reality" is not a possible reality we cannot access; it is a phrase with no referent. Just as "the married bachelor" is not a possible person we cannot find but a contradictory description that fails to pick out anything, "reality without $L_3$" is a contradictory description that fails to pick out a possible world.

### 6.3 Why It Matters for Physics

If the instrumental picture is correct, then the axioms of a physical theory (Hardy's axioms, the postulates of quantum mechanics, the Einstein field equations) have no deeper ground. They are starting points, chosen for empirical adequacy, that could in principle be replaced by radically different starting points, including ones that abandon logical structure. Foundations of physics is then a matter of selecting axioms that work, not of discovering constraints that must hold.

If the constitutive picture is correct, then the axioms of physics are not arbitrary starting points. They are downstream consequences of $L_3$ operating on the domain of possible configurations. The project of quantum reconstruction (Hardy 2001, Chiribella et al. 2011, Masanes and Müller 2011) then has a deeper interpretation: these programs are not merely showing that quantum mechanics can be derived from "reasonable" axioms; they are, when properly grounded, showing that quantum mechanics follows from the constitutive conditions for physical reality.

This is the position of Logic Realism Theory. LRT derives what other programs assume: local tomography, Boolean measurement structure, projection-valued measures, the Born rule, Schrödinger dynamics. The derivations are possible because $L_3$ is constitutive, not instrumental. If $L_3$ were merely a tool, these derivations would be formal exercises with no explanatory force. Because $L_3$ is constitutive, they explain *why* quantum mechanics has the structure it does: because that structure is the unique structure compatible with $L_3$ operating on the informational domain $I_\infty$ through the actualization principle $A$.

---

## 7. Relation to the LRT Corpus

PNFL is not a new addition to Logic Realism Theory. It is the explicit statement of what TAB (Paper I) demonstrates and what every subsequent paper presupposes. Its relationship to the other papers is:

| Paper | How PNFL Functions |
|-------|-------------------|
| **001 (TAB)** | PNFL is the core of §2. TAB develops the transcendental argument for $\chi \equiv [L_3 : I_\infty : A]$; PNFL is the sub-argument establishing $L_3$'s necessity. |
| **002 (Core Physics)** | PNFL underwrites the bridge equation $A_\Omega = L_3(I_\infty)$. Without $L_3$'s constitutive necessity, the bridge is a stipulation. With it, the bridge is a consequence. |
| **004 (How Come the Quantum)** | PNFL answers Wheeler's question at the deepest level: the quantum exists because $L_3$ constrains the informational domain, and Boolean actualization under that constraint yields projection structure. |
| **005 (Measurement)** | PNFL establishes that PVM structure is not postulated but derived from the Boolean character of $L_3$-governed actualization. Measurement outcomes are determinate because $L_3$ is constitutive. |
| **006 (Entanglement)** | PNFL grounds the Non-Decomposability Theorem: entangled systems have non-decomposable identity precisely because $L_3$ operates on composite configurations as wholes. |
| **007 (Resolution)** | PNFL explains why the measurement problem is a category error: it asks for a dynamical mechanism behind what is a logical requirement. PNFL shows that the requirement is not cognitive but constitutive. |

Extracting PNFL as a standalone paper serves two purposes: it makes the argument available to philosophers who are not working through the full LRT reconstruction, and it clarifies that the argument is independent of the specific physics derived in Papers II through VII. PNFL holds even if the physics reconstruction fails. The constitutive necessity of $L_3$ for physics is prior to any particular physical derivation.

---

## 8. The Strongest Form

The argument admits a compressed formulation that captures its recursive, self-supporting character.

**PNFL (compressed):**

> 1. Physics requires determinate states.
> 2. Determinacy is $L_3$ satisfaction.
> 3. Therefore physics requires $L_3$.
> 4. The denial of (3) deploys $L_3$, refuting itself.
> 5. This self-refutation is not cognitive but constitutive: determinacy *is* logical structure, not merely a way of representing it.
> 6. Therefore $L_3$ is physically necessary: not an instrument applied to physics, but a precondition for the existence of anything physics could describe.

The argument is deductively valid. Its premises are defensible against the known objections (dialetheism, intuitionism, quantum logic, radical empiricism, inconceivability arguments). Its conclusion is strong: not that $L_3$ is useful for physics, or that physics as we know it happens to use $L_3$, but that no coherent conception of physics is possible without $L_3$.

If the argument is sound, the relationship between logic and physics is settled. Logic is not a framework we chose. It is not one formal system among many that happens to work. It is the constitutive structure of determinacy, and determinacy is the constitutive structure of physical reality. Remove it and you do not get an alternative physics. You get the impossibility of physics.

Any attempt to coherently deny PNFL must already exemplify the $L_3$-governed determinacy it contests, so objections do not escape its scope; they are further evidence that $L_3$ is constitutive of physical intelligibility rather than a tool contingently applied to it.

---

## References

Birkhoff, G. and von Neumann, J. (1936). The logic of quantum mechanics. *Annals of Mathematics*, 37(4), 823--843.

Cassam, Q. (1987). Transcendental arguments, transcendental synthesis and transcendental idealism. *The Philosophical Quarterly*, 37(149), 355--378.

Chiribella, G., D'Ariano, G.M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Fine, K. (2012). Guide to ground. In F. Correia and B. Schnieder (eds.), *Metaphysical Grounding: Understanding the Structure of Reality*. Cambridge University Press, 37--80.

Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.

Masanes, L. and Müller, M.P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13, 063001.

Priest, G. (2006). *In Contradiction: A Study of the Transconsistent*. 2nd edition. Oxford University Press.

Stern, R. (2000). *Transcendental Arguments: Problems and Prospects*. Oxford University Press.

Stroud, B. (1968). Transcendental arguments. *The Journal of Philosophy*, 65(9), 241--256.
