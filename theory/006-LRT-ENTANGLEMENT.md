# Nonlocality, Nonseparability, and Shared Actualization

## Logic Realism Theory, Paper VI

James D. Longmire
Northrop Grumman Fellow (unaffiliated research)
ORCID: 0009-0009-1383-7698
Correspondence: jdlongmire@outlook.com
Date: April 2026
Status: Draft
Series: LRT Paper 006
Upstream: 000-TRM-FOUNDATIONS, 001-LRT-TAB-PHILOSOPHY, 002-LRT-CORE-PHYSICS, 005-LRT-MEASUREMENT

---

## Abstract

Quantum entanglement generates correlations between spatially separated systems that violate Bell inequalities, resist explanation by local hidden variables, and yet permit no faster-than-light signaling. The tension between nonlocality and no-signaling has driven sixty years of interpretive debate without resolution. This paper argues that the tension is rendered intelligible within Logic Realism Theory (LRT). The primitive ontology $\chi \equiv [L_3 : I_\infty : A]$ distinguishes two domains: the information space $I_\infty$, where configurations evolve unitarily and where entangled states are non-decomposable structures, and the actualized domain $A_\Omega$, where the action primitive $A$ selects determinate, Boolean outcomes subject to $L_3$. Entanglement is neither a causal connection between distant subsystems nor a merely epistemic correlation. It is a structural feature of $I_\infty$: entangled configurations possess a composite identity that cannot be decomposed into the product of subsystem identities. This non-decomposability is derived from Determinate Identity and the tensor product structure of complex Hilbert space (Paper II, Steps 2-4). Bell inequality violations follow as a downstream consequence of non-decomposable structure within the Hilbert space formalism; the Tsirelson bound $2\sqrt{2}$ is the upper limit on correlations that the established Hilbert space structure admits. No-signaling is structural: $A$'s Boolean selection at one location does not alter the reduced state of the distant subsystem in $I_\infty$, because the partial trace is invariant under local projections on maximally entangled states. LRT locates nonlocality in $I_\infty$ and locality in $A_\Omega$, rendering the apparent contradiction intelligible by distributing the two features across distinct ontological levels. This paper develops the full account: the Non-Decomposability Theorem, the derivation of Bell violations and Tsirelson's bound, the structural no-signaling proof, applications to GHZ, Hardy, and quantum teleportation scenarios, and a comparison with Bohmian, Everettian, and retrocausal treatments of nonlocality.

**Keywords:** entanglement, nonlocality, nonseparability, Bell inequalities, Tsirelson bound, quantum foundations, information ontology, logic realism, actualization, non-decomposability

---

## 1. The Problem of Nonlocality

### 1.1 What Bell Established

In 1964, John Bell demonstrated that no theory satisfying two assumptions can reproduce the statistical predictions of quantum mechanics for entangled pairs:

1. **Locality.** The outcome of a measurement on one particle does not depend on the measurement setting chosen for the distant particle.
2. **Separability (factorizability).** The joint probability for outcomes at two locations factors into the product of local probabilities conditioned on a shared hidden variable:

$$P(a, b \mid x, y) = \int d\lambda \, \rho(\lambda) \, P(a \mid x, \lambda) \, P(b \mid y, \lambda)$$

where $a, b$ are outcomes, $x, y$ are measurement settings, and $\lambda$ is a shared hidden variable distributed according to $\rho(\lambda)$.

Any theory satisfying both conditions obeys the CHSH inequality:

$$\lvert S \rvert \leq 2$$

where $S = E(x_1, y_1) - E(x_1, y_2) + E(x_2, y_1) + E(x_2, y_2)$ and $E(x, y) = \sum_{a,b} (-1)^{a+b} P(a, b \mid x, y)$.

Quantum mechanics predicts, and experiment confirms (Aspect, Dalibard, and Roger, 1982; Hensen *et al.*, 2015; Giustina *et al.*, 2015; Shalm *et al.*, 2015), that entangled states violate this inequality. For the singlet state

$$\lvert \Psi^- \rangle = \frac{1}{\sqrt{2}} \bigl( \lvert 01 \rangle - \lvert 10 \rangle \bigr)$$

the maximum quantum violation reaches $\lvert S \rvert = 2\sqrt{2}$, the Tsirelson bound.

### 1.2 The Interpretive Impasse

Bell's result eliminates the conjunction of locality and separability. The question is which to surrender and what to put in its place. Each major interpretation makes a different trade:

| Interpretation | Surrenders | Retains | Cost |
|---|---|---|---|
| Bohmian mechanics | Locality | Separability (implicitly) | Primitive nonlocality via pilot wave; preferred basis (position) |
| Many-Worlds | Separability (at the branch level) | Locality (no collapse) | All branches real; probability problem; preferred basis problem |
| GRW/CSL | Locality (collapse is nonlocal) | Separability (post-collapse) | Modified dynamics; free parameters |
| QBism | Neither (correlations are agent-relative) | No-signaling | No objective ontology of correlations |
| Retrocausal | Temporal locality | Separability (via future-past influence) | Retrocausation as primitive; fine-tuning concerns |

The impasse persists because each interpretation places the burden of nonlocality within the quantum formalism and then attempts to manage the consequences. LRT takes a different path: it distributes nonlocality and locality across two ontological levels.

### 1.3 LRT's Thesis

Entanglement is a structural feature of configurations in $I_\infty$. Non-decomposable configurations possess composite identity that is not reducible to the product of subsystem identities. This nonseparability is ontological: it concerns the identity structure of configurations, not our knowledge of hidden variables.

Locality is a feature of $A_\Omega$. Boolean actualization at one location does not causally influence Boolean actualization at a distant location. No signal passes. The reduced state of the distant subsystem, as a configuration in $I_\infty$, is invariant under local actualization of the near subsystem.

The apparent contradiction between nonlocality and locality is rendered intelligible once the two features are recognized as applying at different ontological levels:

- **Nonseparability in $I_\infty$:** The entangled configuration is a single, non-decomposable structure.
- **Locality in $A_\Omega$:** Actualization at each location is governed by the local interaction Hamiltonian and produces a Boolean outcome without causal influence on the distant site.
- **Correlation:** The correlation between distant outcomes is a consequence of the non-decomposable identity of the configuration in $I_\infty$, not of any signal between the sites. The outcomes are correlated because they are actualizations of a single configuration, not because one outcome produces the other.

This paper develops this account in full formal detail.

---

## 2. Non-Decomposability in $I_\infty$

### 2.1 Composite Systems and Tensor Product Structure

The tensor product structure for composite systems is established at Step 4 of the derivation chain (Paper II, §3.2). Local tomography (Step 3) together with the Masanes-Muller reconstruction theorem entails that the state space of a composite system $AB$ is the tensor product $\mathcal{H}_A \otimes \mathcal{H}_B$ of the subsystem Hilbert spaces.

A composite configuration $c_{AB} \in I_\infty$ is therefore represented by a state vector $\lvert \Psi \rangle_{AB} \in \mathcal{H}_A \otimes \mathcal{H}_B$ (pure case) or a density operator $\rho_{AB}$ on $\mathcal{H}_A \otimes \mathcal{H}_B$ (mixed case).

*[Epistemic status: ESTABLISHED, imported from Masanes and Muller (2011) via Step 4.]*

### 2.2 Decomposable and Non-Decomposable Configurations

**Definition 1 (Decomposable Configuration).** A pure composite configuration $\lvert \Psi \rangle_{AB}$ is *decomposable* (separable) if and only if it can be written as:

$$\lvert \Psi \rangle_{AB} = \lvert \alpha \rangle_A \otimes \lvert \beta \rangle_B$$

for some $\lvert \alpha \rangle_A \in \mathcal{H}_A$ and $\lvert \beta \rangle_B \in \mathcal{H}_B$. A mixed state $\rho_{AB}$ is decomposable if it admits a convex decomposition:

$$\rho_{AB} = \sum_i p_i \, \rho_A^{(i)} \otimes \rho_B^{(i)}$$

with $p_i \geq 0$, $\sum_i p_i = 1$.

**Definition 2 (Non-Decomposable Configuration).** A composite configuration is *non-decomposable* (entangled) if it is not decomposable. Its identity in $I_\infty$ cannot be expressed as the product of subsystem identities.

*[Epistemic status: ESTABLISHED, standard definition within the Hilbert space framework of Step 4.]*

### 2.3 The Non-Decomposability Theorem

**Theorem 1 (Non-Decomposability).** Let $\mathcal{H}_A$ and $\mathcal{H}_B$ each have dimension $d \geq 2$. Then $\mathcal{H}_A \otimes \mathcal{H}_B$ contains non-decomposable configurations. The set of decomposable (product) states is a measure-zero subset of the pure state space.

**Proof.** Consider $\mathcal{H}_A = \mathcal{H}_B = \mathbb{C}^2$. The state

$$\lvert \Psi^- \rangle = \frac{1}{\sqrt{2}} \bigl( \lvert 0 \rangle_A \otimes \lvert 1 \rangle_B - \lvert 1 \rangle_A \otimes \lvert 0 \rangle_B \bigr)$$

is non-decomposable. Suppose for contradiction that $\lvert \Psi^- \rangle = \lvert \alpha \rangle \otimes \lvert \beta \rangle$ for some $\lvert \alpha \rangle = a_0 \lvert 0 \rangle + a_1 \lvert 1 \rangle$ and $\lvert \beta \rangle = b_0 \lvert 0 \rangle + b_1 \lvert 1 \rangle$. Then the coefficients satisfy $a_0 b_0 = 0$, $a_0 b_1 = 1/\sqrt{2}$, $a_1 b_0 = -1/\sqrt{2}$, $a_1 b_1 = 0$. From $a_0 b_1 \neq 0$, both $a_0 \neq 0$ and $b_1 \neq 0$. From $a_1 b_0 \neq 0$, both $a_1 \neq 0$ and $b_0 \neq 0$. But $a_0 b_0 = 0$ requires $a_0 = 0$ or $b_0 = 0$, contradicting the previous. Therefore $\lvert \Psi^- \rangle$ is non-decomposable.

The measure-zero claim follows from the dimension count: the product states form a submanifold of real dimension $2(2d - 2)$ within the pure state space of real dimension $2(d^2 - 1)$. For $d \geq 2$, $2(2d - 2) < 2(d^2 - 1)$. The product states are therefore a proper submanifold of lower dimension, hence measure zero. $\square$

*[Epistemic status: ESTABLISHED, standard result in quantum information theory.]*

### 2.4 Non-Decomposability as Ontological Nonseparability

The Non-Decomposability Theorem is a mathematical result about the tensor product structure. Within LRT's framework, it acquires ontological significance through the following argument.

**Claim.** Non-decomposable configurations possess irreducibly composite identity: the composite's identity in $I_\infty$ is not constituted by the identities of its subsystems alone.

*[Epistemic status: ARGUED.]*

**Argument.** Determinate Identity (Paper II, Step 2) requires that every configuration $c \in A_\Omega$ be self-identical and possess determinate properties. For a decomposable configuration $\lvert \alpha \rangle \otimes \lvert \beta \rangle$, the composite's identity supervenes on the subsystem identities: knowing $\lvert \alpha \rangle$ and $\lvert \beta \rangle$ suffices to determine $\lvert \Psi \rangle_{AB}$ completely. Every property of the composite reduces to properties of or correlations between the subsystems, and those correlations are themselves products.

For a non-decomposable configuration, this reduction fails. The composite $\lvert \Psi^- \rangle$ is determinate as a whole: it is self-identical, non-contradictory, and every well-defined property has a truth value. But the subsystems $A$ and $B$ individually lack determinate pure states. The reduced state of $A$ is:

$$\rho_A = \text{Tr}_B \bigl( \lvert \Psi^- \rangle \langle \Psi^- \rvert \bigr) = \frac{1}{2} \mathbb{I}_A$$

which is maximally mixed. The subsystem has no pure-state identity of its own. Its identity is constituted only through its participation in the composite configuration.

This is ontological nonseparability: the composite's identity is irreducibly composite. The subsystems do not have independent identities that jointly compose the whole. The whole is prior to the parts in the order of identity constitution.

**Clarification on L₃ compliance.** Non-decomposability does not violate $L_3$. The composite configuration $\lvert \Psi^- \rangle$ satisfies Identity (it is what it is), Non-Contradiction (it does not both possess and lack any property in the same respect), and Excluded Middle (every well-formed proposition about the composite has a determinate truth value). What the composite's properties include is correlational structure that cannot be captured by subsystem properties alone. The subsystems, considered individually, are in maximally mixed states in $I_\infty$; they are partially actualized (in the sense of Paper V, §3) with respect to some properties and indeterminate with respect to others. $L_3$ governs the composite's identity as a whole, and that identity is determinate.

### 2.5 The Schmidt Decomposition and Entanglement Quantification

Every pure bipartite state admits a Schmidt decomposition:

$$\lvert \Psi \rangle_{AB} = \sum_{k=1}^{r} \lambda_k \lvert e_k \rangle_A \otimes \lvert f_k \rangle_B$$

where $\lambda_k > 0$, $\sum_k \lambda_k^2 = 1$, and $r = \text{rank}(\rho_A)$ is the Schmidt rank. The state is decomposable if and only if $r = 1$. The degree of non-decomposability is quantified by the entanglement entropy:

$$S(\rho_A) = -\sum_k \lambda_k^2 \log \lambda_k^2$$

which vanishes for product states and reaches $\log d$ for maximally entangled states in $\mathbb{C}^d \otimes \mathbb{C}^d$.

Within LRT, the Schmidt decomposition reveals the structure of the non-decomposable configuration: the Schmidt basis identifies the subsystem degrees of freedom that are correlated in the composite, and the Schmidt coefficients $\lambda_k$ determine the dispositional structure of the configuration with respect to actualization. The Born rule (Paper II, Step 6) assigns probability $\lambda_k^2$ to each correlated outcome pair.

*[Epistemic status: ESTABLISHED, standard quantum information theory applied within the Step 4 Hilbert space.]*

---

## 3. Bell Inequality Violations from Non-Decomposability

### 3.1 The CHSH Inequality Derived

Consider a bipartite experiment. Alice chooses measurement setting $x \in \{x_1, x_2\}$ and obtains outcome $a \in \{+1, -1\}$. Bob chooses $y \in \{y_1, y_2\}$ and obtains $b \in \{+1, -1\}$. The correlation function is:

$$E(x, y) = \sum_{a,b \in \{+1,-1\}} a \cdot b \cdot P(a, b \mid x, y)$$

The CHSH parameter is:

$$S = E(x_1, y_1) - E(x_1, y_2) + E(x_2, y_1) + E(x_2, y_2)$$

**Bell's theorem (CHSH form).** If the joint probabilities admit a local hidden variable decomposition

$$P(a, b \mid x, y) = \int d\lambda \, \rho(\lambda) \, P(a \mid x, \lambda) \, P(b \mid y, \lambda)$$

then $\lvert S \rvert \leq 2$.

*[Epistemic status: ESTABLISHED, Clauser, Horne, Shimony, and Holt (1969); Bell (1964).]*

### 3.2 Quantum Violation via Non-Decomposable States

For the singlet state $\lvert \Psi^- \rangle$ and spin measurements along directions $\hat{a}$ and $\hat{b}$, the quantum correlation function is:

$$E(\hat{a}, \hat{b}) = \langle \Psi^- \rvert (\hat{a} \cdot \vec{\sigma}) \otimes (\hat{b} \cdot \vec{\sigma}) \lvert \Psi^- \rangle = -\hat{a} \cdot \hat{b}$$

Choosing $x_1 = 0°$, $x_2 = 90°$, $y_1 = 45°$, $y_2 = 135°$:

$$S = E(0°, 45°) - E(0°, 135°) + E(90°, 45°) + E(90°, 135°)$$

$$= -\cos 45° + \cos 135° - \cos 45° - \cos 135°$$

$$= -\frac{\sqrt{2}}{2} - \frac{\sqrt{2}}{2} - \frac{\sqrt{2}}{2} + \frac{\sqrt{2}}{2} = -2\sqrt{2}$$

so $\lvert S \rvert = 2\sqrt{2} > 2$. The CHSH inequality is violated.

*[Epistemic status: ESTABLISHED, standard calculation within the Hilbert space of Step 4.]*

### 3.3 LRT's Diagnosis: Why Local Hidden Variables Fail

Bell's factorizability condition requires:

$$P(a, b \mid x, y) = \int d\lambda \, \rho(\lambda) \, P(a \mid x, \lambda) \, P(b \mid y, \lambda)$$

This condition presupposes separability: the hidden variable $\lambda$ carries all correlations, and once $\lambda$ is fixed, the local outcomes are independent. The decomposable structure of the probability is a direct consequence of the decomposable structure of the presumed ontological state.

LRT's response is precise. The factorizability condition fails because the entangled configuration $\lvert \Psi^- \rangle$ is non-decomposable. Its identity in $I_\infty$ is not the product of subsystem identities, and therefore no assignment of hidden variables to the individual subsystems can capture the full correlational content of the composite configuration.

The violation is structural, given the Hilbert space formalism: it follows from the geometry of non-decomposable vectors in a tensor product Hilbert space. It does not require any causal influence between the measurement sites. The correlations are written into the identity of the configuration in $I_\infty$ prior to any actualization event.

*[Epistemic status: ARGUED. The claim that non-decomposability is sufficient to explain Bell violations without nonlocal causation is an LRT-specific interpretation of the established mathematical result. The mathematical fact that entangled states violate Bell inequalities is ESTABLISHED. The ontological reading of this fact as nonseparability rather than nonlocal causation is the contribution of LRT's two-level ontology.]*

### 3.4 The Tsirelson Bound

**Theorem (Tsirelson, 1980).** For any quantum state $\rho$ and any choice of local observables $A_1, A_2$ (Alice) and $B_1, B_2$ (Bob) with eigenvalues in $\{+1, -1\}$:

$$\lvert S \rvert \leq 2\sqrt{2}$$

The bound is tight: the singlet state with the optimal angle choices achieves it.

Within LRT, the Tsirelson bound is the upper limit on correlations that the Hilbert space structure of $I_\infty$ admits. It is tighter than the algebraic maximum $\lvert S \rvert = 4$ (achievable by no-signaling but supra-quantum theories, such as the Popescu-Rohrlich box) because the Hilbert space structure imposes additional constraints beyond mere no-signaling.

The Tsirelson bound is a consequence of the mathematical structure established at Step 4 of the derivation chain. LRT does not independently derive it from $\chi$; it follows from the complex Hilbert space that local tomography and the Masanes-Muller theorem select. The bound is the ceiling on quantum correlations, and LRT inherits it from the formalism it reconstructs.

*[Epistemic status: ESTABLISHED, Tsirelson (1980), imported via the Hilbert space structure of Step 4.]*

### 3.5 Why Not Supra-Quantum Correlations?

A natural question arises: why does nature obey the Tsirelson bound rather than allowing stronger correlations up to the algebraic maximum $\lvert S \rvert = 4$? Supra-quantum correlations would satisfy no-signaling while exceeding the quantum bound.

LRT's answer is structural. The Tsirelson bound follows from the complex Hilbert space structure of $I_\infty$, which is in turn selected by local tomography (Step 3) and the Masanes-Muller reconstruction (Step 4). Supra-quantum correlations would require a state space other than complex Hilbert space. Since LRT derives the Hilbert space structure from the constitutive requirements of $L_3$ (via local tomography from Determinate Identity), supra-quantum correlations are excluded by the same grounding argument that selects the quantum formalism.

The question "why not supra-quantum?" reduces, within LRT, to the question "why complex Hilbert space?" And that question is answered by the derivation chain: because Determinate Identity requires local tomography, and local tomography with the reconstruction axioms uniquely selects $\mathbb{C}\mathcal{H}$.

*[Epistemic status: ARGUED. The grounding argument for why the Tsirelson bound holds is an LRT-specific contribution. The mathematical fact that the bound follows from the Hilbert space structure is ESTABLISHED.]*

---

## 4. Shared Actualization

### 4.1 The Concept

When a non-decomposable configuration in $I_\infty$ undergoes actualization, the actualization is *shared*: the Boolean selection at one subsystem's location determines a correlated outcome at the distant subsystem's location, because both outcomes are actualizations of a single non-decomposable configuration.

**Definition 3 (Shared Actualization).** Let $\lvert \Psi \rangle_{AB}$ be a non-decomposable configuration in $I_\infty$, and let $P_a^A$ be a projection operator corresponding to outcome $a$ for a measurement on subsystem $A$. Shared actualization is the process by which $A$ selects a determinate outcome for the composite:

$$A(E_{a,b}, c) = 1 \quad \text{for some pair } (a, b)$$

where $E_{a,b}$ is the joint event "outcome $a$ at $A$ and outcome $b$ at $B$." The joint probability is:

$$p(a, b) = \langle \Psi \rvert P_a^A \otimes P_b^B \lvert \Psi \rangle$$

Shared actualization is distinguished from three alternatives:

1. **Signal-mediated correlation:** One outcome causally produces the other via a physical signal. LRT denies this: no signal propagates.
2. **Pre-established harmony:** The outcomes were determined by a shared hidden variable at the source. Bell's theorem excludes this for non-decomposable states.
3. **Branching:** Both outcomes occur in different branches. LRT denies this: $A$ selects one outcome in $A_\Omega$.

Shared actualization is a fourth option: the correlation is grounded in the non-decomposable identity of the configuration in $I_\infty$, and the joint outcome is a single actualization event applied to the composite, not two independent actualization events applied to the subsystems.

Why does this count as explanatory progress rather than ontology-flavored relabeling? The answer is structural. A relabeling would rename the correlation without changing any inferential relationship. Shared actualization does more: it unifies a range of otherwise disparate phenomena (Bell violations, GHZ all-or-nothing outcomes, monogamy constraints, teleportation's classical bottleneck) under a single mechanism, non-decomposable identity in $I_\infty$ actualized as a whole. It predicts the Tsirelson bound as a consequence of the selected Hilbert structure rather than treating it as an unexplained empirical ceiling. And it entails no-signaling as a structural theorem rather than requiring a contingent equilibrium condition (contrast Bohmian mechanics). A redescription that generates novel unifications, constrains correlations quantitatively, and eliminates contingent assumptions does explanatory work that mere relabeling cannot.

### 4.2 Temporal Structure of Shared Actualization

A question arises about the temporal ordering of the two outcomes. In special relativity, spacelike-separated events have no invariant temporal ordering: one observer may see Alice's outcome first, another may see Bob's first, and a third may see them as simultaneous.

LRT's response is that shared actualization is not a temporal process. It is an ontological transition: the non-decomposable configuration transitions from $I_\infty$ to $A_\Omega$ as a whole. The "order" in which the subsystem outcomes become determinate is not a physical fact because $A$ operates on the composite configuration, not on the subsystems sequentially.

This is consistent with the no-signaling theorem (§5): if $A$ operated on the subsystems sequentially, with the first actualization influencing the second, then the order of actualization would be a physical fact, and the reduced state of the distant subsystem would depend on the local measurement setting. The no-signaling theorem guarantees that this does not occur. Shared actualization is non-sequential: it lacks invariant temporal ordering and has no temporal extension. The composite configuration is non-decomposable in $I_\infty$ and then it is actualized in $A_\Omega$, with correlated outcomes at both sites. No intermediate stage intervenes, and no frame-dependent "first" or "second" actualization occurs.

*[Epistemic status: ARGUED. The claim that actualization operates on the composite rather than sequentially on subsystems is an LRT-specific ontological commitment. The consistency with no-signaling (§5) supports the claim but does not compel it independently of LRT's framework.]*

### 4.3 Partial Actualization and Entanglement

Paper V (§3) introduced partial actualization: a configuration may be actualized with respect to some degrees of freedom while remaining in $I_\infty$ with respect to others. Entanglement interacts with partial actualization in a specific way.

Consider a composite system $AB$ in the non-decomposable state $\lvert \Psi^- \rangle$. Before any measurement, both subsystems' spin degrees of freedom remain in $I_\infty$. The composite has a determinate identity as a whole (it is the singlet), but neither subsystem has a determinate spin state.

When Alice measures spin along $\hat{z}$ and obtains $+\hbar/2$, shared actualization simultaneously determines:

$$A(\text{spin}_A = +z, c) = 1 \quad \text{and} \quad A(\text{spin}_B = -z, c) = 1$$

Bob's spin is now actualized along $\hat{z}$, regardless of whether Bob has yet performed a measurement. If Bob subsequently measures along $\hat{z}$, he obtains $-\hbar/2$ with certainty. If Bob measures along a different axis $\hat{n}$, the outcome probabilities follow from the Born rule applied to the state $\lvert -z \rangle_B$ projected onto the $\hat{n}$ eigenstates.

A clarification on Bob's actualization status is needed here. After Alice's measurement, is Bob's spin "actualized" even though Bob has not interacted with a measuring apparatus? Within LRT, the answer is: the composite configuration has been fully actualized in $A_\Omega$, so the individual subsystem states are determinate. Bob's spin is determinate because it is constituted by the composite's actualized identity, not because Bob's local apparatus has brought it into the scope of $A$. The distinction between "actualized via local interaction" and "actualized via shared actualization of a non-decomposable composite" is real: both produce determinate states in $A_\Omega$, but the mechanism differs. Local interaction operates through the interaction Hamiltonian; shared actualization operates through the non-decomposable identity of the composite.

*[Epistemic status: ARGUED. The extension of partial actualization to the entanglement case is natural within LRT's framework but constitutes a substantive ontological commitment about how $A$ operates on composite configurations.]*

---

## 5. The No-Signaling Theorem

### 5.1 Statement

**Theorem 2 (No-Signaling).** Let $\lvert \Psi \rangle_{AB}$ be any composite configuration in $I_\infty$, and let $P_a^A$ be any projection operator on $\mathcal{H}_A$. The reduced state of subsystem $B$ after actualization of outcome $a$ at subsystem $A$ is independent of Alice's measurement setting.

### 5.2 Proof

Let Alice's measurement be described by a PVM $\{P_a^A\}$ on $\mathcal{H}_A$. After Alice obtains outcome $a$, the (unnormalized) post-measurement state of $B$ is:

$$\tilde{\rho}_B^{(a)} = \text{Tr}_A \bigl[ (P_a^A \otimes \mathbb{I}_B) \lvert \Psi \rangle \langle \Psi \rvert (P_a^A \otimes \mathbb{I}_B) \bigr]$$

The probability of outcome $a$ is $p(a) = \text{Tr}(\tilde{\rho}_B^{(a)})$. The reduced state of $B$ averaged over Alice's outcomes is:

$$\rho_B = \sum_a \tilde{\rho}_B^{(a)} = \sum_a \text{Tr}_A \bigl[ (P_a^A \otimes \mathbb{I}_B) \lvert \Psi \rangle \langle \Psi \rvert (P_a^A \otimes \mathbb{I}_B) \bigr]$$

Since $\{P_a^A\}$ is a PVM, $\sum_a P_a^A = \mathbb{I}_A$. Therefore:

$$\rho_B = \text{Tr}_A \bigl[ (\mathbb{I}_A \otimes \mathbb{I}_B) \lvert \Psi \rangle \langle \Psi \rvert (\mathbb{I}_A \otimes \mathbb{I}_B) \bigr] = \text{Tr}_A \bigl( \lvert \Psi \rangle \langle \Psi \rvert \bigr)$$

which is independent of Alice's measurement choice $\{P_a^A\}$. $\square$

*[Epistemic status: ESTABLISHED, standard result in quantum information theory, applied within the Hilbert space of Step 4.]*

### 5.3 LRT Interpretation of No-Signaling

The no-signaling theorem has a precise ontological reading within LRT. The reduced state $\rho_B = \text{Tr}_A(\lvert \Psi \rangle \langle \Psi \rvert)$ is the description of subsystem $B$'s configuration in $I_\infty$ as it appears to any observer with access only to $B$. This description is invariant under Alice's measurement choice. Alice's actualization event determines a correlated outcome at $B$, but it does not alter $B$'s description in $I_\infty$ from the perspective of any agent lacking information about Alice's outcome.

The physical content is: no experiment that Bob can perform on $B$ alone will reveal whether Alice has performed a measurement, or which measurement she performed. Bob's local statistics are invariant. The correlation between $A$ and $B$ outcomes is accessible only through comparison of records: that is, through classical communication.

LRT distributes the story cleanly:

- **In $I_\infty$:** The non-decomposable configuration contains all correlational structure. Alice's measurement choice determines which PVM enters the scope of $A$. The configuration's non-decomposable identity determines the joint outcome probabilities.
- **In $A_\Omega$:** Each site has a Boolean outcome. The outcomes are correlated. The correlation is accessible only through classical comparison.
- **Between $I_\infty$ and $A_\Omega$:** Shared actualization produces the joint outcome. No causal signal propagates.

This distribution renders Einstein locality and quantum nonseparability simultaneously tenable. Einstein was right that there is no "spooky action at a distance": no physical signal travels from Alice to Bob. The EPR argument was wrong only in assuming separability: that the composite's state must be a product of subsystem states. The failure of separability is a feature of $I_\infty$'s configuration structure, not a modification of causal structure in $A_\Omega$.

---

## 6. Applications

### 6.1 GHZ States and Mermin's Inequality

The Greenberger-Horne-Zeilinger (GHZ) state extends entanglement to three or more parties:

$$\lvert \text{GHZ} \rangle = \frac{1}{\sqrt{2}} \bigl( \lvert 000 \rangle + \lvert 111 \rangle \bigr)$$

This state is non-decomposable with respect to any bipartition: tracing out any one subsystem yields a separable (classically correlated) mixed state for the remaining two. The entanglement is genuinely tripartite.

Mermin (1990) showed that GHZ correlations produce an all-or-nothing conflict with local hidden variables: certain joint measurement outcomes that local hidden variable theories predict to be deterministic are exactly reversed by quantum mechanics. No statistical accumulation is needed; a single round of the experiment can distinguish quantum from classical predictions (up to experimental imperfections).

**LRT analysis.** The GHZ configuration is non-decomposable in $I_\infty$ across all three subsystems. Its identity is irreducibly tripartite: no subsystem or pair of subsystems has a determinate pure state independently of the third. Shared actualization operates on the tripartite composite as a whole, producing correlated Boolean outcomes at all three locations simultaneously.

The Mermin inequality violation follows from the same structural source as the CHSH violation: the non-decomposable identity of the configuration in $I_\infty$ generates correlations that no assignment of pre-existing values to the individual subsystems can reproduce. The GHZ case is more dramatic because the conflict is logical (deterministic predictions are reversed) rather than statistical (inequality bounds are exceeded).

### 6.2 Hardy's Paradox

Hardy (1993) constructed a scenario in which entangled particles produce outcomes that are individually consistent with local realism but jointly impossible under any local hidden variable model. The paradox requires no inequalities: it is a direct logical contradiction between local realism and quantum predictions.

Consider two particles in a specific non-maximally entangled state. Hardy showed that there exist measurement settings under which:

1. If Alice obtains result $a_1$ and Bob obtains $b_1$, both results can occur jointly (quantum mechanics predicts nonzero probability).
2. Local realism requires that certain individual results cannot occur, given the joint constraint.
3. Quantum mechanics predicts that these individual results do occur with nonzero probability.

**LRT analysis.** The non-maximally entangled state is non-decomposable in $I_\infty$. The paradox arises from attempting to assign pre-existing Boolean values to all measurements simultaneously. LRT's partial actualization framework explains why this assignment fails: before measurement, the relevant properties are not actualized. There are no pre-existing values to assign. The outcomes become determinate only through shared actualization, and the joint outcome probabilities follow from the Born rule applied to the non-decomposable configuration.

Hardy's paradox, within LRT, is a demonstration that the identity structure of non-decomposable configurations in $I_\infty$ resists decomposition into independent subsystem facts. The "paradox" arises only if one presupposes separability. Without that presupposition, the quantum predictions follow straightforwardly from the non-decomposable identity and the Born rule.

### 6.3 Quantum Teleportation

Quantum teleportation (Bennett *et al.*, 1993) transfers a quantum state from Alice to Bob using shared entanglement and classical communication. The protocol requires:

1. A shared entangled pair in the Bell state $\lvert \Phi^+ \rangle_{23} = \frac{1}{\sqrt{2}}(\lvert 00 \rangle + \lvert 11 \rangle)$.
2. An unknown state $\lvert \phi \rangle_1 = \alpha \lvert 0 \rangle + \beta \lvert 1 \rangle$ that Alice wishes to transfer.
3. Alice performs a Bell-basis measurement on particles 1 and 2.
4. Alice communicates her result (two classical bits) to Bob.
5. Bob applies a local unitary correction to particle 3, recovering $\lvert \phi \rangle$.

**LRT analysis.** The three-particle state $\lvert \phi \rangle_1 \otimes \lvert \Phi^+ \rangle_{23}$ is initially decomposable between particle 1 and the entangled pair (2,3). After rewriting in the Bell basis for particles (1,2), the composite becomes:

$$\lvert \Psi \rangle_{123} = \frac{1}{2} \sum_{k=0}^{3} \lvert \beta_k \rangle_{12} \otimes U_k \lvert \phi \rangle_3$$

where $\lvert \beta_k \rangle$ are the four Bell states and $U_k$ are the corresponding Pauli corrections.

Alice's Bell measurement on (1,2) is an actualization event: $A$ selects one of four outcomes $k$. This is shared actualization applied to the (1,2) subsystem, which is now non-decomposable. The outcome determines which unitary $U_k$ Bob must apply.

The state $\lvert \phi \rangle$ is not transmitted through space. The information required to reconstruct it travels in two channels: the correlational structure travels via the non-decomposable identity of the (2,3) pair in $I_\infty$; the outcome label $k$ travels as classical communication. Neither channel alone suffices. The no-signaling theorem guarantees that Bob's particle 3, prior to receiving Alice's classical message, is in the maximally mixed state $\frac{1}{2}\mathbb{I}$, which carries no information about $\lvert \phi \rangle$.

Teleportation, within LRT, is not the transmission of a physical object or a violation of locality. It is the coordinated actualization of a non-decomposable configuration, mediated by classical communication. The quantum "channel" is the pre-existing non-decomposable structure of the (2,3) pair in $I_\infty$; the classical channel supplies the label needed to complete the reconstruction.

### 6.4 Entanglement Swapping

Entanglement swapping extends teleportation to create entanglement between particles that have never interacted. Consider four particles: (1,2) share a Bell state, and (3,4) share a Bell state. Particles 2 and 3 are brought together and measured in the Bell basis. After this measurement, particles 1 and 4 (which have never interacted) are entangled.

**LRT analysis.** Before the Bell measurement on (2,3), the four-particle state is:

$$\lvert \Phi^+ \rangle_{12} \otimes \lvert \Phi^+ \rangle_{34}$$

This is decomposable between (1,2) and (3,4). The Bell measurement on (2,3) produces shared actualization of the (2,3) subsystem, projecting the (2,3) pair onto a Bell state. The resulting state of (1,4) is non-decomposable: particles 1 and 4 are now entangled, despite never having been in causal contact.

This result is intelligible within LRT because entanglement is a structural feature of configurations in $I_\infty$, not a causal connection. The Bell measurement on (2,3) restructures the composite configuration in $I_\infty$, producing a new non-decomposable configuration for (1,4). The restructuring is lawful: it follows from the linear algebra of tensor products and the Born rule. No signal passes from (2,3) to (1,4). The non-decomposable identity of (1,4) is a structural consequence of the measurement-induced reconfiguration, mediated by the prior non-decomposable structures of (1,2) and (3,4).

---

## 7. Contrasts with Other Treatments of Nonlocality

### 7.1 Bohmian Mechanics

Bohmian mechanics treats nonlocality as primitive. The guidance equation

$$\dot{q}_k = \frac{\hbar}{m_k} \text{Im} \frac{\nabla_k \Psi(q_1, \ldots, q_N)}{\Psi(q_1, \ldots, q_N)}$$

is holistic: the velocity of each particle depends on the positions of all particles simultaneously, regardless of spatial separation. Bell inequality violations are explained by the explicitly nonlocal character of the pilot wave.

**LRT's contrast.** LRT agrees that the correlations are real and that local hidden variables fail. It disagrees about the mechanism. Bohmian nonlocality is causal: the wave function acts on all particles simultaneously, and the velocity of a distant particle changes instantaneously when a nearby measurement is performed. LRT's nonseparability is structural: the non-decomposable identity of the configuration in $I_\infty$ encodes the correlations without any causal signal propagating between sites.

The contrast is sharpest on the no-signaling theorem. In Bohmian mechanics, no-signaling is a contingent consequence of quantum equilibrium: if the particle distribution happens to be $\lvert \Psi \rvert^2$, then the nonlocal causal influences average out to produce no observable signal. If quantum equilibrium were violated, superluminal signaling would be possible. In LRT, no-signaling is structural: it follows from the PVM resolution of identity ($\sum_a P_a = \mathbb{I}$) and the linearity of the partial trace. No special distribution is required. No-signaling holds necessarily within the formalism, not contingently.

### 7.2 Many-Worlds Interpretation

In the Everettian picture, both outcomes of a Bell experiment occur in different branches. The correlations between Alice and Bob are correlations between branches: in the branch where Alice obtains $+1$, Bob obtains $-1$, and vice versa. Nonlocality is eliminated because there is no single outcome to be nonlocally correlated with a distant single outcome.

**LRT's contrast.** LRT agrees that unitary evolution produces no collapse and that the branching structure in $I_\infty$ is real (as structures in $I_\infty$). It disagrees about actualization: only one branch is actualized in $A_\Omega$. The correlations between Alice and Bob are real correlations between actual outcomes, not merely intra-branch structural features. The advantage is ontological parsimony: LRT does not multiply worlds. The cost is the actualization primitive $A$, which is defended in Papers 0 and I as transcendentally necessary.

### 7.3 Retrocausal Approaches

Retrocausal interpretations (Price, 1996; Wharton, 2014; Adlam, 2022) explain Bell correlations by allowing causal influences to propagate backward in time. The future measurement setting at Bob's location causally influences the hidden variable at the source, producing the observed correlations without faster-than-light signaling.

**LRT's contrast.** Retrocausal approaches preserve temporal locality (no faster-than-light influences at any given time) by introducing causal structure that runs backward in time. LRT preserves both temporal locality and the standard temporal direction of causation. The correlations are explained by nonseparability in $I_\infty$: the non-decomposable identity of the composite configuration encodes the correlations structurally, without causal influence in either temporal direction.

LRT's position is more parsimonious: it introduces nonseparability in $I_\infty$ (which is required independently for the tensor product structure of composite systems) rather than retrocausation (which is a novel causal primitive with no independent motivation). The retrocausal approach also faces fine-tuning concerns: the backward influences must be precisely calibrated to produce quantum correlations and no more. LRT faces no analogous fine-tuning because the Tsirelson bound follows directly from the Hilbert space structure.

### 7.4 Relational Quantum Mechanics

Rovelli's relational interpretation (1996) holds that quantum states are relational: a system has properties only relative to another system. Entanglement correlations are stable relations between subsystems, established through interaction, that constrain future observations.

**LRT's contrast.** LRT agrees that the correlations are grounded in relational structure. It disagrees about the observer-dependence. In RQM, states are relative to observers; in LRT, configurations in $I_\infty$ and $A_\Omega$ are observer-independent. The non-decomposable identity of an entangled configuration is a structural feature of $I_\infty$ that obtains regardless of whether any observer exists. $A$'s Boolean selection in $A_\Omega$ is objective, not relative to an agent or reference system.

### 7.5 Summary Comparison

| Feature | Bohm | MWI | Retrocausal | RQM | **LRT** |
|---|---|---|---|---|---|
| Nonlocality type | Causal (pilot wave) | None (all branches) | Causal (backward) | Relational | Structural ($I_\infty$) |
| No-signaling status | Contingent (quantum equil.) | Structural | By construction | Structural | Structural |
| Ontological cost | Pilot wave + position privilege | Branch multiplication | Retrocausation | Observer-relativity | Non-decomposability in $I_\infty$ |
| Number of outcomes | One | All | One | Relative | One |
| Bell violation source | Nonlocal guidance eq. | Branching correlations | Future boundary conditions | Relational correlations | Non-decomposable identity |
| Tsirelson bound | From Hilbert space | From Hilbert space | From Hilbert space (+ tuning) | From Hilbert space | From Hilbert space (grounded) |

---

## 8. Kochen-Specker Contextuality

### 8.1 The Kochen-Specker Theorem

**Theorem (Kochen and Specker, 1967).** In a Hilbert space of dimension $d \geq 3$, there is no assignment of values $v : \mathcal{P}(\mathcal{H}) \to \{0, 1\}$ to all projection operators such that:

1. $v$ respects orthogonality: if $P_1 + P_2 + \cdots + P_d = \mathbb{I}$, then exactly one $v(P_k) = 1$.
2. $v$ is non-contextual: $v(P)$ depends only on $P$, not on which resolution of the identity $P$ appears in.

No such global value assignment exists for $d \geq 3$.

*[Epistemic status: ESTABLISHED, Kochen and Specker (1967).]*

### 8.2 LRT's Account of Contextuality

The Kochen-Specker theorem is a natural consequence of LRT's measurement account. $A$'s Boolean selection always occurs relative to a specific PVM, which is determined by the physical interaction Hamiltonian (Paper V, §3). The PVM specifies the context: the set of mutually exclusive and jointly exhaustive events among which $A$ selects.

There is no global value assignment because values are not pre-existing properties waiting to be revealed. They are actualized through the interaction of $A$ with the configuration in $I_\infty$, and the interaction determines which PVM is relevant. Different PVMs correspond to different physical interactions, and the same projection operator $P$ may appear in multiple PVMs. Its actualization value depends on the specific PVM because $A$ selects from the complete set of outcomes in that PVM, not from individual projections in isolation.

Contextuality, in LRT, is the observation that actualization is always *contextual actualization*: it operates on a complete PVM, not on individual projections. The impossibility of a non-contextual global value assignment is a structural consequence of the PVM framework that $A$'s Boolean character produces (Paper II, Steps 4-5).

This account distinguishes LRT from hidden variable interpretations that treat contextuality as a surprising constraint on otherwise pre-existing values. In LRT, the absence of pre-existing values is the default: properties are actualized, not revealed. Contextuality is expected rather than anomalous.

*[Epistemic status: ARGUED. The reading of contextuality as a natural consequence of actualization-relative-to-PVM is LRT-specific. The Kochen-Specker theorem itself is ESTABLISHED.]*

---

## 9. Monogamy of Entanglement

### 9.1 The Monogamy Constraint

Quantum entanglement obeys a monogamy constraint: if two qubits $A$ and $B$ are maximally entangled, neither can be entangled with a third qubit $C$. Formally, for qubits:

$$C_{A:B}^2 + C_{A:C}^2 \leq C_{A:BC}^2$$

where $C$ is the concurrence (Coffman, Kundu, and Wootters, 2000). For the tangle $\tau = C^2$:

$$\tau_{A:B} + \tau_{A:C} \leq \tau_{A:BC}$$

This is the Coffman-Kundu-Wootters (CKW) inequality.

*[Epistemic status: ESTABLISHED, Coffman, Kundu, and Wootters (2000).]*

### 9.2 LRT Interpretation

Within LRT, monogamy of entanglement reflects a structural constraint on non-decomposable identity in $I_\infty$. A configuration's non-decomposable identity can be distributed across subsystems, but the total non-decomposable content is bounded by the Hilbert space dimension.

The interpretation is precise: if $A$ and $B$ share a maximally non-decomposable configuration (maximal entanglement), then the composite $AB$ has exhausted the identity content available for non-decomposable relations. No additional non-decomposable identity can be established between $A$ and $C$ because $A$'s identity is already fully constituted through its relation to $B$.

Monogamy is therefore a consequence of the finite-dimensional Hilbert space structure together with the constitutive role of non-decomposable identity. It is not an additional postulate but a downstream constraint from the formalism established at Step 4.

---

## 10. Open Problems

### 10.1 Relativistic Covariance

The present account is formulated within non-relativistic quantum mechanics. Extending it to relativistic quantum field theory requires addressing the following:

1. **Spacelike separation and the actualization primitive.** Shared actualization operates on the composite configuration as a whole, without temporal ordering. In a relativistic setting, the absence of a preferred simultaneity surface must be reconciled with the composite's actualization. The no-signaling theorem guarantees consistency with Lorentz covariance at the level of observable statistics. Whether $A$'s operation can be given a manifestly Lorentz-covariant formulation is an open question.

2. **Algebraic quantum field theory.** The tensor product structure of finite-dimensional Hilbert spaces is replaced by the type III factor structure of local algebras in AQFT. Non-decomposability must be reformulated in terms of entanglement across local algebras rather than tensor product factors. The Reeh-Schlieder theorem guarantees that entanglement is generic in the vacuum state, which is consistent with LRT's prediction that non-decomposable configurations are the typical case (§2.3, measure-zero claim).

*[Epistemic status: OPEN. The non-relativistic account is complete. The relativistic extension is identified as a research direction, not claimed.]*

### 10.2 Entanglement Dynamics

The present paper treats entanglement statically: given a non-decomposable configuration, what are its properties and consequences? The dynamics of entanglement creation, propagation, and destruction under unitary evolution remain to be developed within LRT's framework.

Entanglement is created by interactions that couple previously independent subsystems. In LRT, this means that an initially decomposable configuration in $I_\infty$ becomes non-decomposable through unitary evolution governed by an interaction Hamiltonian. The creation of non-decomposable identity is a structural reconfiguration in $I_\infty$, lawfully governed by the Schrodinger equation (Paper II, Step 13). Decoherence, the effective loss of entanglement through interaction with an environment, is the process by which non-decomposable identity is distributed across an increasingly large composite, rendering the original subsystem pair effectively decomposable when the environment is traced out.

A full account of entanglement dynamics within LRT requires connecting the entanglement entropy evolution to the actualization threshold discussed in Paper V, §9.1. This connection remains open.

### 10.3 Multipartite Entanglement Classification

Multipartite entanglement exhibits a richer structure than bipartite entanglement. For three qubits, there are two inequivalent classes of genuine tripartite entanglement: GHZ-type and W-type (Dur, Vidal, and Cirac, 2000). For four or more qubits, the classification becomes increasingly complex.

LRT's non-decomposability framework provides a natural language for this classification: different types of non-decomposable identity in $I_\infty$ correspond to different entanglement classes. The Schmidt decomposition captures bipartite non-decomposability; multipartite generalizations require the full apparatus of entanglement witnesses, measures, and SLOCC (stochastic local operations and classical communication) equivalence classes.

Developing this classification within LRT's ontological framework, and determining whether LRT's grounding argument constrains the classification beyond what the Hilbert space structure alone provides, is an open problem.

---

## 11. Conclusion

The entanglement problem, as debated in quantum foundations for sixty years, takes the form of a dilemma: either accept nonlocal causation (violating the spirit of relativity) or deny the reality of correlations (violating scientific realism). LRT reframes the dilemma by distributing the phenomena across two ontological levels.

In $I_\infty$, entangled configurations possess non-decomposable identity: their composite identity is irreducibly relational, not reducible to the product of subsystem identities. This is ontological nonseparability, and it is the source of all entanglement phenomena: Bell violations, GHZ correlations, Hardy's paradox, teleportation, and entanglement swapping. Non-decomposability is a structural feature of the tensor product Hilbert space, derived at Step 4 of the reconstruction chain from Determinate Identity and local tomography.

In $A_\Omega$, each measurement produces a Boolean outcome through the action primitive $A$. Shared actualization produces correlated outcomes at spacelike-separated locations without causal signaling between them. The no-signaling theorem is structural: it follows from the resolution of identity for PVMs and the linearity of the partial trace. No contingent distribution (quantum equilibrium) is required.

The Tsirelson bound $2\sqrt{2}$ is not an unexplained empirical fact. It is a structural consequence of the complex Hilbert space that LRT's derivation chain selects. Supra-quantum correlations are excluded by the same grounding argument that selects the quantum formalism over its competitors.

Three features distinguish LRT's account from its alternatives. First, nonlocality and locality are not in tension because they apply at different ontological levels. Second, no-signaling is necessary rather than contingent. Third, the Tsirelson bound is grounded rather than postulated. These features come at the cost of the actualization primitive $A$ and the two-level ontology of $I_\infty$ and $A_\Omega$, which are defended as transcendentally necessary in Papers 0 and I.

The principal open problems are the relativistic extension (§10.1), entanglement dynamics (§10.2), and multipartite classification within LRT's framework (§10.3). These are extensions of a complete non-relativistic account, not gaps in the current argument.

---

## References

Adlam, E. (2022). Is there causation in fundamental physics? *New Directions in the Philosophy of Science*. Routledge.

Aspect, A., Dalibard, J., and Roger, G. (1982). Experimental realization of Einstein-Podolsky-Rosen-Bohm Gedankenexperiment: A new violation of Bell's inequalities. *Physical Review Letters*, 49(25), 1804-1807.

Bell, J. S. (1964). On the Einstein Podolsky Rosen paradox. *Physics Physique Fizika*, 1(3), 195-200.

Bennett, C. H., Brassard, G., Crepeau, C., Jozsa, R., Peres, A., and Wootters, W. K. (1993). Teleporting an unknown quantum state via dual classical and Einstein-Podolsky-Rosen channels. *Physical Review Letters*, 70(13), 1895-1899.

Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Clauser, J. F., Horne, M. A., Shimony, A., and Holt, R. A. (1969). Proposed experiment to test local hidden-variable theories. *Physical Review Letters*, 23(15), 880-884.

Coffman, V., Kundu, J., and Wootters, W. K. (2000). Distributed entanglement. *Physical Review A*, 61(5), 052306.

Dur, W., Vidal, G., and Cirac, J. I. (2000). Three qubits can be entangled in two inequivalent ways. *Physical Review A*, 62(6), 062314.

Giustina, M., *et al.* (2015). Significant-loophole-free test of Bell's theorem with entangled photons. *Physical Review Letters*, 115(25), 250401.

Hardy, L. (1993). Nonlocality for two particles without inequalities for almost all entangled states. *Physical Review Letters*, 71(11), 1665-1668.

Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.

Hensen, B., *et al.* (2015). Loophole-free Bell inequality violation using electron spins separated by 1.3 kilometres. *Nature*, 526, 682-686.

Kochen, S. and Specker, E. P. (1967). The problem of hidden variables in quantum mechanics. *Journal of Mathematics and Mechanics*, 17(1), 59-87.

Longmire, J. D. (2026a). The Transcendental Argument for Being: Foundations of Logic Realism Theory. Zenodo. https://doi.org/10.5281/zenodo.19226396

Longmire, J. D. (2026b). Logic Realism Theory: Grounding Reality as Logical, Informational, and Dynamic (Paper II). Pre-print.

Longmire, J. D. (2026c). The Measurement Problem Reframed: Actualization and the Quantum-Classical Interface (Paper V). Pre-print.

Masanes, L. and Muller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Mermin, N. D. (1990). Extreme quantum entanglement in a superposition of macroscopically distinct states. *Physical Review Letters*, 65(15), 1838-1840.

Price, H. (1996). *Time's Arrow and Archimedes' Point: New Directions for the Physics of Time*. Oxford University Press.

Rovelli, C. (1996). Relational quantum mechanics. *International Journal of Theoretical Physics*, 35(8), 1637-1678.

Shalm, L. K., *et al.* (2015). Strong loophole-free test of local realism. *Physical Review Letters*, 115(25), 250402.

Tsirelson, B. S. (1980). Quantum generalizations of Bell's inequality. *Letters in Mathematical Physics*, 4(2), 93-100.

Wharton, K. (2014). Quantum states as ordinary information. *Information*, 5(1), 190-208.

---

## Appendix A: Notation Summary

| Symbol | Name | Definition |
|---|---|---|
| $\chi$ | Primitive ontology | $[L_3 : I_\infty : A]$ |
| $L_3$ | Three Laws of Logic | Identity, Non-Contradiction, Excluded Middle |
| $I_\infty$ | Information Space | Domain of all $L_3$-admissible configurations |
| $A$ | Action primitive | Boolean: $\{$actual, non-actual$\}$ |
| $A_\Omega$ | Actualized domain | $L_3(I_\infty)$; the domain of physically manifest configurations |
| $\mathcal{H}$ | Hilbert space | Complex Hilbert space (Step 4) |
| PVM | Projection-valued measure | Complete set of orthogonal projections (Step 5) |
| $D(s_1, s_2)$ | Distinguishability metric | $\sup_M \lvert P_M(s_1) - P_M(s_2) \rvert_{\text{TV}}$ |
| $S(\rho)$ | Entanglement entropy | $-\text{Tr}(\rho \log \rho)$ |
| $C$ | Concurrence | Entanglement measure for qubits |
| $\tau$ | Tangle | $C^2$; appears in CKW inequality |

## Appendix B: Epistemic Status Index

| Claim | Section | Status |
|---|---|---|
| Tensor product structure for composites | §2.1 | ESTABLISHED |
| Non-Decomposability Theorem | §2.3 | ESTABLISHED |
| Non-decomposability as ontological nonseparability | §2.4 | ARGUED |
| CHSH inequality | §3.1 | ESTABLISHED |
| Quantum violation of CHSH | §3.2 | ESTABLISHED |
| Non-decomposability explains Bell violations without nonlocal causation | §3.3 | ARGUED |
| Tsirelson bound | §3.4 | ESTABLISHED |
| Supra-quantum correlations excluded by LRT grounding | §3.5 | ARGUED |
| Shared actualization concept | §4.1 | ARGUED |
| Temporal structure of shared actualization | §4.2 | ARGUED |
| No-signaling theorem | §5.2 | ESTABLISHED |
| LRT interpretation of no-signaling | §5.3 | ARGUED |
| Kochen-Specker theorem | §8.1 | ESTABLISHED |
| Contextuality as natural consequence of actualization | §8.2 | ARGUED |
| Monogamy constraint (CKW) | §9.1 | ESTABLISHED |
| Relativistic extension | §10.1 | OPEN |
| Entanglement dynamics | §10.2 | OPEN |
| Multipartite classification | §10.3 | OPEN |

---

*HCAE: Honest, Comprehensive, Accurate, Epistemic*

*Logic Realism Theory Project | Paper VI | April 2026*
