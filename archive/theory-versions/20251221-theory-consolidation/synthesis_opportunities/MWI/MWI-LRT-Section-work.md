# Section 4: Solving the Preferred Basis Problem

**Final Revised Version**

**Author:** James (JD) Longmire  
ORCID: 0009-0009-1383-7698  
Northrop Grumman Fellow (unaffiliated research)

---

## 4. Solving the Preferred Basis Problem

### 4.1 The Problem Stated Precisely

Consider a quantum system S measured by apparatus A. After interaction, the composite state is:

$$|\Psi\rangle_{SA} = \sum_i c_i |s_i\rangle_S \otimes |a_i\rangle_A$$

where $\{|s_i\rangle_S\}$ and $\{|a_i\rangle_A\}$ are orthonormal bases.

**MWI's branching claim:** The terms $|s_i\rangle_S |a_i\rangle_A$ represent distinct "worlds" or "branches" of reality. Each is an actual universe containing definite measurement outcome.

**The problem:** This decomposition is not unique. The same state admits infinitely many decompositions:

$$|\Psi\rangle_{SA} = \sum_j d_j |s'_j\rangle_S \otimes |a'_j\rangle_A$$

in different bases $\{|s'_j\rangle\}$, $\{|a'_j\rangle\}$ related by unitary transformation.

**Example (spin-½):**

$$|\Psi\rangle = \frac{1}{\sqrt{2}}(|\uparrow_z\rangle_S|\text{up}_z\rangle_A + |\downarrow_z\rangle_S|\text{down}_z\rangle_A)$$

This can equally be written:

$$|\Psi\rangle = \frac{1}{\sqrt{2}}(|\uparrow_x\rangle_S|\text{up}_x\rangle_A + |\downarrow_x\rangle_S|\text{down}_x\rangle_A)$$

**Which decomposition defines worlds?** In the z-basis, there are two worlds (↑ measured and ↓ measured). In the x-basis, there are two different worlds (→ measured and ← measured). Both decompositions are mathematically valid.

Nothing in the wavefunction itself picks out one basis as "the" basis for branching. Yet MWI claims branches are physically real. If reality is basis-dependent, we have a serious problem.

### 4.2 Standard MWI Response: Decoherence

The standard MWI answer invokes **environmental decoherence** (Zurek 1981, 2003; Wallace 2012).

**The decoherence argument:**

1. Real measurement devices interact with environments (air molecules, photons, thermal radiation).

2. Environment E entangles with system-apparatus composite:
$$|\Psi\rangle_{SAE} = \sum_i c_i |s_i\rangle_S |a_i\rangle_A |e_i\rangle_E$$

3. Environmental states $\{|e_i\rangle_E\}$ corresponding to different pointer positions become rapidly orthogonal: $\langle e_i | e_j \rangle \approx \delta_{ij}$ for $i \neq j$.

4. The reduced density matrix for SA becomes effectively diagonal:
$$\rho_{SA} = \text{Tr}_E(|\Psi\rangle\langle\Psi|) \approx \sum_i |c_i|^2 |s_i\rangle\langle s_i|_S \otimes |a_i\rangle\langle a_i|_A$$

5. Off-diagonal terms (coherences) vanish exponentially: $\langle s_i a_i|_{SA} \rho_{SA} |s_j a_j\rangle_{SA} \approx 0$ for $i \neq j$.

6. **Conclusion:** The **pointer basis** (states distinguishable to environment) is selected dynamically. Branches are defined by eigenstates of the interaction Hamiltonian with environment.

**Why this is progress:** Decoherence explains why we don't observe macroscopic superpositions. The pointer basis is not arbitrary—it's the basis most robust under environmental monitoring (Zurek's "einselection"). For position measurements, position eigenstates decohere fastest. For momentum measurements, momentum eigenstates.

### 4.3 Why Decoherence Alone Is Insufficient

Despite its power, decoherence does not fully solve the preferred basis problem for MWI:

**Objection 1 (Ontological vs. Dynamical):**

Decoherence is a **dynamical** process depending on:
- Environment details (which degrees of freedom couple, how strongly)
- Timescales (decoherence time τ_D ~ ℏ/(kT λ²) for spatial separation λ)
- Initial conditions (what the environment was doing)

But branching, according to MWI, should be **ontological**—it's about what worlds exist, not about dynamics. Tying world-existence to environmental dynamics makes reality contingent on accidental features (Kent 2010).

**Example:** In an isolated universe with no environment, decoherence wouldn't occur. Does this mean no worlds exist? MWI defenders might say "yes, branching requires environment," but this seems to make fundamental ontology depend on whether dust particles happen to be around.

**Objection 2 (Perfect Decoherence Never Achieved):**

Decoherence makes off-diagonal terms exponentially small, not exactly zero:
$$|\langle s_i a_i e_i | s_j a_j e_j \rangle| = \exp(-\Gamma t)$$

They approach zero but never reach it. So coherence is never perfectly destroyed.

If branches are defined by "effectively diagonal" density matrices, then branching is approximate, not fundamental. But MWI claims branches are actual entities. Approximate entities are suspect ontology.

**Objection 3 (Basis Ambiguity Remains):**

Even with decoherence, multiple bases can be simultaneously "decohered" to good approximation (Schlosshauer 2007). For a particle in Gaussian wavepacket, both position and momentum are approximately diagonal in their respective bases if the wavepacket is broad enough. Which basis defines worlds?

Decoherence narrows the choices but doesn't uniquely determine a basis unless we add a criterion like "fastest decoherence" or "most robust." But these are external principles, not derivable from MWI alone.

**Objection 4 (Wallace's Response and Its Limitation):**

Wallace (2012) argues that "world" is an emergent, quasi-classical concept, not fundamental. We shouldn't expect perfect precision in where one world ends and another begins. Approximate branching is fine for emergent structure.

**Reply:** This concedes too much. If worlds are merely emergent patterns in the wavefunction, why take them as ontologically serious? And if they are ontologically serious (as MWI claims), approximate definitions are inadequate. You can't be "approximately real."

### 4.4 The LRT Solution: Context Determines Basis

LRT resolves the preferred basis problem by recognizing that basis selection is not a feature of IIS dynamics but of the **interface context**.

**Key insight:** The basis is not "in" the wavefunction. It's specified by the measurement interaction—the physical coupling that determines which observable's eigenstates become correlated with distinguishable apparatus states. This is not a "choice" in any subjective sense but an objective feature of the interaction Hamiltonian.

**The mechanism:**

1. **In IIS:** The state $|\Psi\rangle_{SA}$ exists without preferred basis. All decompositions are simultaneously present as structural features of the state.

2. **Measurement interaction:** The physical setup couples system observable $\hat{O}_S$ to apparatus pointer states. This specifies the eigenbasis $\{|s_i\rangle\}$ of $\hat{O}_S$.

3. **Interface operation:** The measurement context defines the Boolean partition—the set of mutually exclusive, exhaustive outcomes corresponding to $\hat{O}_S$ eigenvalues.

4. **Actualization:** One term from the $\{|s_i\rangle\}$ decomposition actualizes with Born rule probability $P_i = |c_i|^2$.

5. **Result:** The actualized outcome is in the measurement basis because that's the basis the physical interaction specified.

**Formal statement:**

**Definition 4.1 (Measurement Context).** A measurement context $M$ is the informational specification of an interface transition, comprising:

- Observable $\hat{O}_S$ (Hermitian operator on system S)
- Eigenbasis $\{|s_i\rangle : \hat{O}_S |s_i\rangle = o_i |s_i\rangle\}$
- Boolean partition $\{o_i\}$ (distinct eigenvalues as mutually exclusive outcomes)

Crucially, the context is not a prior condition that must be "set" before measurement occurs. Rather, the context is *constituted by* the physical coupling between system, apparatus, and environment at the moment the interface threshold is crossed. What observable is measured is determined by which degrees of freedom are coupled and how—this is a physical fact about the interaction Hamiltonian, not a choice requiring prior actualization.

**Remark:** The context $M$ and the interface threshold $\tau$ are logically distinct:
- The **threshold** $\tau$ determines *that* an actualization occurs (when branch distinguishability becomes irreversible)
- The **context** $M$ determines *what* actualizes (which observable's eigenbasis partitions the outcome space)

Both are objective physical features, not observer-dependent choices.

The interface operation $\Phi_M: \mathcal{I} \to \mathcal{A}$ relative to context $M$ produces outcome $o_i$ with probability:
$$P(o_i | |\psi\rangle, M) = |\langle s_i | \psi \rangle|^2$$

**Theorem 4.1 (Contextual Basis Selection).** For any IIS state $|\Psi\rangle_{SA}$ and measurement context $M$ specifying basis $\{|s_i\rangle\}$, the actualized outcome is in the $\{|s_i\rangle\}$ basis with probability given by Born rule.

*Proof:* Gleason's theorem (Gleason 1957) establishes that *given* a projection lattice on Hilbert space (dim ≥ 3), the Born rule $P_i = |\langle s_i|\psi\rangle|^2$ is the unique probability measure satisfying non-contextuality, normalization, and finite additivity. Gleason fixes the *form* of any probability assignment once the lattice structure is specified.

LRT's distinctive move: the physical measurement interaction selects *which* projection lattice applies. The context $M$—constituted by the interaction Hamiltonian coupling system to apparatus—determines the eigenbasis $\{|s_i\rangle\}$, thereby fixing the relevant sublattice of projectors $\{|s_i\rangle\langle s_i|\}$. Gleason then delivers the Born probabilities on that sublattice.

Thus "which basis" and "which probability measure" are not independent choices but jointly determined by a single interface structure: the physical context selects the lattice, Gleason determines the measure. Different contexts $M'$ select different lattices $\{|s'_j\rangle\langle s'_j|\}$ and yield correspondingly different Born distributions. □

**Why this solves the problem:**

**No preferred basis in IIS:** The state $|\Psi\rangle$ doesn't carry a preferred decomposition. All bases are present simultaneously as potential decompositions. The state is basis-neutral.

**Basis emerges at interface:** When a measurement occurs (interface transition), the context specifies which basis. Different measurements specify different bases.

**Not arbitrary:** The basis isn't chosen by human convention or subjective decision. It's determined by the physical measurement setup—what observable couples to what detector, which Hamiltonian describes the interaction.

**Example:** 
- **Stern-Gerlach z-measurement:** $\hat{O} = \sigma_z$, basis $\{|\uparrow_z\rangle, |\downarrow_z\rangle\}$
- **Stern-Gerlach x-measurement:** $\hat{O} = \sigma_x$, basis $\{|\uparrow_x\rangle, |\downarrow_x\rangle\}$

Different experimental setups (magnet orientation) specify different bases. The basis is not "discovered" in the quantum state but imposed by the measurement interaction.

### 4.5 The Role of Decoherence in LRT

Decoherence is important but plays a different role than in standard MWI:

**In MWI:** Decoherence *defines* branches by selecting pointer basis.

**In LRT:** Decoherence *prepares* the state for interface transition by making branches distinguishable.

**The mechanism:**

1. **Before decoherence:** Superposition state $|\psi\rangle = \sum_i c_i |i\rangle$ has off-diagonal density matrix elements $\rho_{ij} = c_i c_j^*$ for $i \neq j$. The branches $|i\rangle$ are distinguishable but not yet independent—they can interfere.

2. **During decoherence:** Environment entangles: $|\Psi\rangle = \sum_i c_i |i\rangle_S |e_i\rangle_E$. Off-diagonal terms $\langle i | \rho_S | j \rangle$ vanish as $\langle e_i | e_j \rangle \to 0$.

3. **Effect:** Branches become **effectively independent**—they no longer interfere, cannot be recombined, are distinguishable to environment. The state approaches the **interface threshold**.

4. **Interface transition:** One branch actualizes. Decoherence determined which branches are distinguishable (hence candidates for actualization) but didn't determine which one actualizes (that's stochastic, Born rule).

**Analogy:** 

Decoherence is like separating cream from milk. It makes components distinguishable. But it doesn't determine which component you drink.

Interface transition is the selection: which component actualizes to Boolean outcome.

**Why decoherence helps:**

- **Fast decoherence** means branches become distinguishable quickly, making measurement reliable (no interference washing out differences).
- **Robust pointer states** are those that decohere slowest, making them good measurement outcomes (stable records).
- **Einselection** (environment-induced superselection) identifies which observables are naturally "classical" (position, energy, etc.).

But decoherence doesn't replace context-specification. Even after decoherence, you still need to measure something—the physical setup specifies an observable. Decoherence makes that specification effective by eliminating interference, but it doesn't make the specification itself.

### 4.5.1 Interface Threshold vs. Measurement Context: Blocking the Regress

A persistent objection to context-dependent basis selection is the **von Neumann chain regress**: if the measurement apparatus is itself a quantum system, what determines *its* state? If the apparatus must be in a definite configuration to "set" the context, doesn't that require a prior measurement of the apparatus, which requires a meta-apparatus, ad infinitum?

This objection would be fatal if LRT claimed that context must be actualized *before* the system is measured. But LRT claims no such thing.

**The Interface Threshold**

The interface threshold $\tau$ is an objective physical condition: the point at which branch distinguishability becomes effectively irreversible. This occurs when environmental entanglement has made branches mutually orthogonal ($\langle e_i | e_j \rangle \approx 0$) and recombination would require thermodynamically prohibitive operations.

The threshold is crossed when physical conditions obtain, not when observation occurs—analogous to a phase transition that proceeds regardless of whether anyone watches.

**Remark (Operational Criterion).** While "irreversible distinguishability" is the conceptual criterion, operational proxies are available: the threshold is approached when the trace distance $D(\rho_i, \rho_j) = \frac{1}{2}\text{Tr}|\rho_i - \rho_j|$ between branch-conditional reduced states approaches unity, and reversal would require thermodynamic work exceeding practical bounds. Whether the threshold is sharp (as in objective collapse models such as Penrose-Diósi or GRW) or effectively gradual (as in standard decoherence) is an empirical question that LRT does not prejudge. What LRT requires is that *some* physical condition marks the transition from IIS superposition to Boolean actuality; the framework is compatible with multiple candidate mechanisms.

**The Measurement Context**

The context $M$ specifies *which observable* is measured—equivalently, which basis partitions the Boolean outcome space. This is fixed by the interaction Hamiltonian: which system degrees of freedom couple to which apparatus degrees of freedom.

**Joint Actualization**

The apparatus state and system outcome are determined together at threshold, not sequentially. Consider:

$$|\Psi\rangle_{SAE} = \sum_i c_i |s_i\rangle_S |a_i\rangle_A |e_i\rangle_E$$

When this state crosses threshold, one entire branch actualizes—system, apparatus, and environment together. The apparatus doesn't need prior actualization to set context; the apparatus configuration is part of what actualizes.

The von Neumann chain assumes definiteness propagates stepwise: apparatus becomes definite, then measures system. LRT rejects this: prior to threshold, the full composite exists in IIS as superposition; at threshold, one complete branch actualizes; after threshold, Boolean actuality contains both definite apparatus and definite outcome as components of a single actualized branch.

**The Apparatus Superposition Case**

Consider apparatus A in superposition of measuring different observables:

$$|\Psi\rangle = \alpha |z\text{-config}\rangle_A |s\rangle_S + \beta |x\text{-config}\rangle_A |s\rangle_S$$

After interaction and decoherence, this yields a complex branching structure. The resolution is unchanged: at threshold, one complete branch actualizes, containing a definite apparatus configuration and a definite outcome in the corresponding basis. No regress arises because apparatus definiteness is not a precondition but a component of the actualized branch.

**Theorem 4.2 (Regress Blocking).** Let $|\Psi\rangle_{SAE}$ be an entangled system-apparatus-environment state with branches indexed by $(a, s, e)$. At interface threshold, actualization selects one complete tuple $(a_j, s_j, e_j)$ with probability $P(a_j, s_j, e_j) = |c_{(a_j, s_j, e_j)}|^2$. The apparatus configuration $a_j$ and system outcome $s_j$ are jointly actualized; no prior actualization of $a_j$ is required. □

**Remark.** This reflects actual physics: the apparatus *is* a quantum system until decoherence, and "the apparatus being in a definite configuration" is itself an actualized outcome. Standard MWI faces this regress more acutely—if all branches are actual, "which observable was measured" becomes world-relative, and the notion of a measurement result becomes problematic. LRT avoids this by actualizing one complete branch while others remain as IIS structure.

### 4.6 Comparison: Standard MWI vs. LRT

| Aspect | Standard MWI | LRT |
|--------|-------------|-----|
| **Basis in wavefunction?** | Yes (via decoherence) | No (context-specified) |
| **Decoherence role** | Defines branches | Makes branches distinguishable |
| **Branching occurs when** | Decoherence complete | Interface transition |
| **Basis selection** | Dynamical (fastest decoherence) | Contextual (interaction specifies) |
| **Multiple bases?** | Problem (ambiguous) | Not a problem (different contexts) |
| **Isolated systems** | No branching (no decoherence) | Basis still specified by measurement |
| **Worlds status** | Actual (all branches) | Possible (all branches in IIS); one actual |
| **Regress vulnerability** | High (world-relative observables) | Blocked (joint actualization) |

**Key advantage of LRT:** Decouples basis selection (interface context) from decoherence dynamics. This avoids making ontology contingent on environment while still explaining why certain bases are experimentally natural (decoherence-identified).

### 4.7 Concrete Example: Spin Measurement

**Setup:** Electron in superposition $|\psi\rangle_S = \frac{1}{\sqrt{2}}(|\uparrow_z\rangle + |\downarrow_z\rangle)$ enters Stern-Gerlach apparatus oriented along z-axis.

**Step 1 (Interaction):** Electron interacts with magnetic field gradient, entangling with apparatus position:
$$|\Psi\rangle_{SA} = \frac{1}{\sqrt{2}}(|\uparrow_z\rangle_S |\text{up path}\rangle_A + |\downarrow_z\rangle_S |\text{down path}\rangle_A)$$

**In IIS:** This state exists as single point in $\mathcal{H}_S \otimes \mathcal{H}_A$. Both branches present, no preferred basis yet.

**Step 2 (Decoherence):** Environment (lab air, photons) entangles with apparatus:
$$|\Psi\rangle_{SAE} = \frac{1}{\sqrt{2}}(|\uparrow_z\rangle_S |\text{up}\rangle_A |e_\uparrow\rangle_E + |\downarrow_z\rangle_S |\text{down}\rangle_A |e_\downarrow\rangle_E)$$

Environmental states $|e_\uparrow\rangle$ and $|e_\downarrow\rangle$ rapidly become orthogonal ($\langle e_\uparrow | e_\downarrow \rangle \approx 0$) as environment "records" which path.

**Status:** Branches are now distinguishable and approaching interface threshold. Off-diagonal coherences $\langle \uparrow | \rho_S | \downarrow \rangle$ have vanished. But the state still exists fully in IIS.

**Step 3 (Interface Threshold Crossed):** The physical coupling (magnetic field gradient → spatial separation → environmental entanglement) has constituted a measurement context: $\hat{O} = \sigma_z$, with Boolean partition {up, down}.

**Step 4 (Actualization):** One branch actualizes:
- With probability 1/2: $|\uparrow_z\rangle_S |\text{up}\rangle_A |e_\uparrow\rangle_E$ becomes actual
- With probability 1/2: $|\downarrow_z\rangle_S |\text{down}\rangle_A |e_\downarrow\rangle_E$ becomes actual

**Observer sees:** One definite outcome (electron went up, or electron went down). Not both. Not a superposition.

**Different context:** If instead observer measured electron spin in x-basis *after* the paths recombine (counterfactual):
- Context would specify $\{|\uparrow_x\rangle, |\downarrow_x\rangle\}$ basis
- State would be written: $|\Psi\rangle = \frac{1}{\sqrt{2}}(|\uparrow_x\rangle_S |a_x^+\rangle_A + |\downarrow_x\rangle_S |a_x^-\rangle_A)$
- Different actualization, different basis

**The point:** Basis is not discovered in the state but specified by the physical interaction. Decoherence prepared the state (made z-basis branches distinguishable) but didn't force z-basis measurement. You could still measure x (though decoherence would make this impractical for macroscopic apparatus—that's why decoherence matters for observation, not for ontology).

### 4.8 Objections and Replies

**Objection 1:** "Isn't 'measurement context' just a fancy name for 'choice of basis'? You've relocated the arbitrariness, not eliminated it."

**Reply:** No. The measurement context is not arbitrary choice but physical fact about the experimental setup:
- Stern-Gerlach z-magnet vs. x-magnet (different interactions)
- Position detector vs. momentum detector (different coupling)
- Photon polarizer oriented H/V vs. +45°/-45° (different apparatus)

These are different physical situations, not different "choices." Each setup specifies a different observable, hence different basis. The basis is determined by physics, not by human decision.

**Objection 2:** "What if no measurement occurs? Does the state lack a basis?"

**Reply:** Correct. In IIS, the state has no unique basis decomposition. All bases are equally valid structural features. This is not a problem—it's a feature. The state is basis-neutral until interface transition requires basis selection.

For systems not undergoing measurement, no actualization occurs, so no basis is needed. The state evolves unitarily in IIS according to Schrödinger equation, basis-free.

**Objection 3:** "Doesn't this make reality measurement-dependent? Isn't that instrumentalism?"

**Reply:** No. Two clarifications:

1. **IIS reality is measurement-independent.** The full quantum state exists in IIS regardless of whether anyone measures it. All branches are present.

2. **Boolean actuality is measurement-dependent** in the sense that actualization requires interface transition, which requires measurement context. But this is not instrumentalism—it's recognizing that actuality and possibility are distinct ontological categories.

**Analogy:** In classical statistical mechanics, phase space is measurement-independent (all microstates exist as possibilities). But only one microstate is actual. Which one is actual depends on initial conditions—not measurement-dependent but state-dependent. Similarly, in LRT, which branch actualizes depends on measurement context—not subjective choice but physical specification.

**Objection 4:** "This makes human observers special—they 'choose' the basis by choosing what to measure."

**Reply:** Human observers are not special. Any physical interaction requiring Boolean outcomes constitutes a measurement context:
- Cosmic ray hitting detector (no human involved)
- Molecule binding to enzyme (no humans existed yet)
- Rock absorbing photon (no life in the universe)

These all specify contexts (what couples to what) and produce actualizations. Human "choice" is just one type of physical setup specification, no more special than rock orientation.

**Objection 5 (von Neumann Chain Regress):** "Your solution requires the measurement context to be definite before measurement occurs. But the apparatus is itself a quantum system. What determines *its* state? You need a meta-measurement to actualize the apparatus configuration, which requires a meta-apparatus, ad infinitum. You've just relocated von Neumann's infinite regress from 'collapse' to 'context'."

**Reply:** This objection rests on a misunderstanding of LRT's claim. We do *not* require the apparatus to be actualized before the system is measured. The apparatus configuration and system outcome are actualized *simultaneously* as aspects of the same branch crossing the interface threshold.

The von Neumann chain arises in collapse interpretations because collapse is conceived as propagating sequentially along the measurement chain: first the microscopic system collapses, then the apparatus pointer, then the observer's brain, etc. Each step seems to require the next, generating regress.

LRT's interface mechanism is not sequential. When branch distinguishability crosses the irreversibility threshold, the entire entangled state $|s_i\rangle_S |a_i\rangle_A |e_i\rangle_E$ actualizes as a unit. The apparatus state $|a_i\rangle_A$ is not a precondition for actualization but part of what actualizes.

To put it differently: the context is not "set" and then "used." The context is *constituted by* the structure of the actualized branch. Asking "what actualized the apparatus?" is like asking "what caused the cause?" The interface threshold is the fundamental transition; both apparatus and outcome emerge from it together.

See Section 4.5.1 for formal development and Theorem 4.2.

### 4.9 Summary: How LRT Solves the Preferred Basis Problem

**The solution in four points:**

1. **No preferred basis in IIS.** All decompositions are simultaneously present as structural features of the quantum state. Basis-neutrality is not a bug but correct description of pre-actualization reality.

2. **Context specifies basis.** The physical measurement interaction specifies which observable is measured, determining the eigenbasis for that observable. Different physical setups specify different bases.

3. **Decoherence makes effective.** Environmental entanglement makes branches distinguishable and robust, ensuring measurement is reliable. But decoherence prepares rather than determines—it identifies which bases are practically measurable, not which basis must be used.

4. **Joint actualization blocks regress.** The apparatus configuration and system outcome are actualized together, not sequentially. No prior actualization of the apparatus is required, so the von Neumann chain cannot get started.

**Result:** The preferred basis problem dissolves. There's no unique preferred basis in IIS (nor should there be), and the basis for actualization is determined by physical context (as it should be). MWI's problem was demanding that IIS alone determine the basis; LRT recognizes that interface structure is required—and that this structure is constituted at the threshold, not presupposed before it.

---

**END OF SECTION 4**

---

## Revision Summary

This final version integrates:

1. **Original Section 4 structure** from the first complete revision
2. **Refined Theorem 4.1** - Clarifies Gleason provides the *form* of probability measure; LRT provides *lattice selection* via physical context
3. **Trimmed Section 4.5.1** - ~170 words net reduction, removing redundant "simultaneously" and "aspects of the same branch"
4. **Standalone Operational Criterion** - No companion paper dependency; references Penrose-Diósi and GRW as candidate mechanisms while leaving threshold sharpness as empirical question
5. **New Objection 5** - Explicit treatment of von Neumann chain regress

**Word count:** ~4,200 words (down from ~4,500 in first revision)