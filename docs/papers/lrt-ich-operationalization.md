---
layout: paper
permalink: /papers/lrt-ich-operationalization/
title: "Operationalizing Information Circulation: From Horizon Constraints to Cosmological Dynamics"
short_title: "ICH Operationalization"
author: "James (JD) Longmire"
orcid: "0009-0009-1383-7698"
email: "jdlongmire@outlook.com"
date_published: 2026-02-25
abstract: "The Information Circulation Hypothesis (ICH) proposes a closed dynamical loop: information flows from the abstract space of logical possibilities (I∞) into physical instantiation (A_Ω), then returns to I∞ via black hole singularities. Unlike the standard breakdown narrative—which treats singularities as gaps in description—ICH treats them as transition points where L₃ constraints can no longer be satisfied within spacetime, forcing information back to abstract structure. This paper closes the foundational gap identified in prior work: the derivation of the admissibility predicate Adm from L₃. Horizon physics provides exactly this connection. The boundary distinguishability constraint—proven in the companion horizon paper—instantiates L₃ at gravitational boundaries, generating Adm(x) = 1 iff records exist in accessible algebras. When horizons saturate, information routes to radiation (island mechanism) or singularity (de-actualization). The cosmological constant Λ emerges as the fixed-point cost of maintaining this circulation."
keywords:
  - information circulation
  - black hole de-actualization
  - cosmological constant
  - admissibility predicate
  - L₃ constraints
  - Logic Realism Theory
zenodo_url: "https://zenodo.org/communities/logic-realism-theory"
github_url: "https://github.com/jdlongmire/logic-realism-theory"
---

## 1. Introduction

### 1.1 The Central Claim

The Information Circulation Hypothesis (ICH) proposes a **closed dynamical loop** between abstract and physical domains:

$$I_\infty \xrightarrow{\text{instantiation}} A_\Omega \xrightarrow{\text{de-actualization}} I_\infty$$

Information cycles: drawn from the space of logical possibilities ($I_\infty$) into physical instantiation ($A_\Omega$), then returned to $I_\infty$ via black hole singularities. The universe is not a one-way process toward heat death but a circulation—with the cosmological constant $\Lambda$ emerging as the cost of maintaining this cycle.

This is not a relabeling of "classical physics breaks down at singularities." The standard breakdown narrative treats singularities as gaps in our description. ICH treats them as *transition points* in a dynamical mechanism: the phase where L₃ constraints can no longer be satisfied within spacetime, forcing information back to abstract structure.

### 1.2 The Gap in Prior Work

Logic Realism Theory derives quantum mechanics from logical constraints: the three laws of classical logic (L₃)—Identity, Non-Contradiction, Excluded Middle—treated as ontological constraints on physical instantiation rather than merely rules of inference [1]. The derivation proceeds:

$$L_3 \rightarrow \text{Distinguishability} \rightarrow \text{Hilbert Space} \rightarrow \text{Born Rule}$$

ICH extends this framework to cosmology [2, 3], but prior work identified a critical gap:

The companion "Admissibility Dynamics" paper [3] formalized the physics but identified a critical gap:

> **Missing:** Logical operator $L_3 \rightarrow$ Admissibility predicate $\mathsf{Adm}$

That paper operates *downstream* of this step, showing how physics would behave *if* such a filter exists. The present paper closes the gap by showing that **horizon physics provides the concrete instantiation of L₃ → Adm**.

### 1.3 Paper Structure

- **§2:** Importing results from the horizon channel paper
- **§3:** The L₃ → Adm derivation at horizons
- **§4:** De-actualization: what happens at saturation
- **§5:** Cosmological circulation and the Λ fixed point
- **§6:** The complete ICH picture
- **§7:** Falsifiable consequences

### 1.4 Scope of L₃ Constraints

A potential confusion must be addressed at the outset: L₃ does not govern $I_\infty$ itself.

**What L₃ constrains:** The *instantiation* of configurations from $I_\infty$ into $A_\Omega$. L₃ acts as a filter at the boundary between abstract possibility and physical actuality.

**What L₃ does not constrain:** The internal structure of $I_\infty$. The space of logical possibilities contains all coherent configurations, including many that can never instantiate physically. $I_\infty$ is not "made of" L₃-compliant things—it contains the full logical space, and L₃ filters what can cross into physical instantiation.

**Analogy:** A mesh filter doesn't determine what exists upstream—it determines what can pass through. L₃ is the mesh between $I_\infty$ and $A_\Omega$.

This clarification matters because de-actualization (return to $I_\infty$) does not mean information becomes "logically incoherent." It means information loses its physical address while remaining in the space of logical possibilities. L₃ constraints cease to *apply* (because there is no instantiation to constrain), not that they are *violated*.

### 1.5 Framework Assumptions

The derivation proceeds from five core assumptions, stated explicitly:

**A1. Ontological L₃:** The three laws of classical logic (Identity, Non-Contradiction, Excluded Middle) are constraints on physical instantiation, not merely rules of inference.

**A2. Distinguishability Requirement:** For any configuration $x$ to be physically instantiated, it must be distinguishable from all alternative configurations in some accessible algebra.

**A3. Causal Localization:** During causal disconnection, "accessible algebra" means the exterior/boundary algebra—records in causally inaccessible regions do not satisfy the distinguishability requirement.

**A4. Finite Capacity:** Physical systems have finite information capacity bounded by entropy (Bekenstein bound for horizons).

**A5. Circulation Closure:** Information that exits $A_\Omega$ via de-actualization returns to $I_\infty$, maintaining conservation across both domains.

A1 is the core LRT postulate. A2-A4 are physical postulates motivated by L₃ but not derivable from pure logic. A5 is the ICH extension that connects horizon physics to cosmology.

**Note on A3.** Assumption A3 (Causal Localization) is specific to the ICH framework; alternative proposals could relax or modify it, and doing so would change or remove the L₃ → Adm link at horizons. We do not claim A3 is a necessity of nature—it is a physical postulate that makes ICH's predictions possible.

### 1.6 LRT as QFT/GR Bridge

A referee might ask: why should L₃ constraints—operating at the logical level—have anything to say about the GR/QFT interface?

The answer lies in LRT's structural position:

**LRT provides a common substrate.** Both QFT and GR presuppose distinguishability of states. QFT requires orthogonal states for measurement; GR requires distinguishable spacetime points for metric structure. L₃ provides the logical foundation for this shared presupposition.

**Horizons are where the substrate shows.** In ordinary physics, distinguishability is automatic—we don't think about L₃ because it's always satisfied. At horizons, finite capacity and causal structure make the constraint *operative*. The boundary must maintain distinguishability with limited resources under causal constraints.

**LRT does not derive GR from QFT or vice versa.** Rather, it identifies the logical preconditions both theories assume. When those preconditions become constraining (at horizons, at singularities), L₃ determines what can physically occur.

This is why the L₃ → Adm derivation is possible: horizons are exactly where the logical substrate becomes physically relevant.

### 1.7 The Key Move: Horizons as L₃ Instantiation Sites

The horizon channel constraint paper [4] establishes:

**Admissibility Postulate.** For any distinguishable input states with $D(\rho_1, \rho_2) = d > 0$, the boundary marginals after horizon crossing must satisfy:

$$D(\rho_{B,1}, \rho_{B,2}) \geq g_{\min}(d, S_{BH}) > 0$$

This constraint forbids isometries that would erase boundary distinguishability while storing records only in causally inaccessible interior regions.

**The insight:** This constraint *is* L₃ operating at horizons.

- **Identity:** Distinct states must remain distinct in some accessible algebra
- **Non-Contradiction:** The boundary cannot encode both "state 1" and "state 2" for the same subsystem
- **Excluded Middle:** Every distinguishable pair must have a definite record—in the boundary or radiation, not nowhere

The horizon is where L₃ becomes operationally constraining because:
1. The interior is causally disconnected during the pre-emission epoch
2. The boundary is finite-capacity
3. Information must eventually couple to radiation

---

## 2. Horizon Constraints: Established Results

This section summarizes the core results from [4] that serve as inputs to the ICH operationalization.

### 2.1 The Packing Theorem

**Theorem 2.1 (from [4]).** Let $V: H_{in} \rightarrow B \otimes R$ satisfy the record-existence constraint at level $\delta > 0$. Then:

$$M \leq \frac{2 S_{BH}}{\delta^2}$$

where $M$ is the number of mutually distinguishable states and $S_{BH}$ is the Bekenstein-Hawking entropy.

**Corollary.** For finite $S_{BH}$ and $M$ distinguishable inputs:

$$\delta \geq \sqrt{\frac{2M}{S_{BH}}}$$

The distinguishability floor $\delta$ cannot vanish for finite capacity.

### 2.2 The Boundary Algebra Requirement

The constraint specifies *where* records must exist during the pre-emission epoch $t \in [t_{\text{cross}}, t_{\text{emit}}]$:

- **$A_B(t)$:** The boundary/exterior-accessible algebra. Records here can mediate correlations with radiation.
- **$A_{\text{int}}(t)$:** The interior algebra. Causally disconnected from the exterior until emission.

**Admissibility requires records in $A_B(t)$, not merely $A_{\text{int}}(t)$.**

Interior-only storage fails because:
1. Interior DOF are inaccessible during the pre-emission window
2. If interior storage satisfied admissibility, the constraint would reduce to global unitarity
3. The physical content is that *boundary* must maintain records, forcing capacity accounting

### 2.3 The Island Mechanism

At **boundary saturation**—when $S_{\text{reserved}} > S_{BH}^{\text{eff}}$—the boundary can no longer hold all required distinguishability records. Information must transfer to radiation. The quantum extremal surface (QES) marks this overflow boundary.

**Key result:** The island formula emerges as a consequence of boundary saturation under admissibility, not as an independent postulate.

### 2.4 What the Horizon Paper Does Not Address

The horizon paper [4] treats admissibility as either:
- A phenomenological hypothesis, or
- Motivated by LRT but not derived from L₃

It does not:
1. Show the explicit L₃ → Adm mechanism
2. Address what happens to information at the singularity (only at the QES)
3. Connect to the cosmological circulation

These are exactly what the present paper provides.

---

## 3. The L₃ → Adm Derivation at Horizons

### 3.1 The Core Argument

L₃ makes three demands on physical reality:

| L₃ Principle | Ontological Demand | Horizon Expression |
|--------------|-------------------|-------------------|
| **Identity** | A = A | Distinguishable states preserve distinguishability |
| **Non-Contradiction** | ¬(A ∧ ¬A) | Boundary cannot encode contradictory records |
| **Excluded Middle** | A ∨ ¬A | Every distinction has definite record location |

At horizons, these translate to:

**Identity at horizons:** If input states $\rho_1, \rho_2$ satisfy $D(\rho_1, \rho_2) = d > 0$, there must exist some subsystem where this distinction is registered. If the boundary were permitted to erase the distinction entirely (ρ_{B,1} = ρ_{B,2}) while the interior is inaccessible, the *identity* of the input—its distinctness from alternatives—would have no physical instantiation during the pre-emission epoch.

**Non-Contradiction at horizons:** The boundary algebra cannot simultaneously register "input was ρ₁" and "input was ρ₂" for the same crossing event. This is automatic for quantum states but becomes constraining when we ask: can the boundary *fail to register either*? Non-Contradiction forbids contradictory records, but combined with Excluded Middle, it also forbids *no* record.

**Excluded Middle at horizons:** For each distinguishable pair, the record must be *somewhere accessible*. Not "perhaps in the interior, perhaps in the boundary, perhaps nowhere"—somewhere definite in the accessible algebra.

### 3.2 Admissibility Localization

Before deriving the admissibility predicate, we must state explicitly a physical postulate that connects logical necessity ("record must exist *somewhere*") to causal constraint ("record must exist in the *accessible* algebra").

**Lemma 3.0 (Admissibility Localization).** Let $x$ be a physically instantiated configuration during interval $t \in [t_{\text{cross}}, t_{\text{emit}}]$. If:
1. L₃ requires that distinctions between $x$ and alternatives be registered in some definite location, and
2. The interior algebra $A_{\text{int}}(t)$ is causally disconnected from the exterior during this interval,

then the required record must reside in the accessible algebra $A_B(t)$.

**Justification.** This lemma makes explicit what might appear as a gap: the move from "somewhere" to "somewhere accessible." The justification is not pure logic but the **Causal Localization postulate (A3)**: records in causally inaccessible regions do not satisfy the distinguishability requirement for physical instantiation *within* the accessible domain.

Here is the key physical content: L₃ demands that $x$ be distinguished from alternatives *for any observer who can interact with $x$*. During $[t_{\text{cross}}, t_{\text{emit}}]$, the only observers who can interact with boundary information are exterior observers. If the distinction record exists only in the interior, exterior observers cannot—even in principle—distinguish $x$ from alternatives.

This is not a logical necessity but a physical postulate about how L₃ applies to causally structured spacetimes. The postulate is falsifiable: if some mechanism allowed interior records to satisfy L₃ constraints for exterior observers, Lemma 3.0 would fail.

**Relation to Assumption A3.** Lemma 3.0 is an instance of assumption A3 (Causal Localization) applied to horizon geometry. A3 is a physical postulate, not a logical derivation—we state this explicitly to avoid the appearance of deriving physics from pure logic.

### 3.3 Deriving the Admissibility Predicate

Define the admissibility predicate:

$$\mathsf{Adm}(x, t) = \begin{cases}
1 & \text{if } \exists \text{ POVM } \{E_k\} \text{ on } A_B(t) : D(\rho_{B,x}, \rho_{B,y}) \geq \delta \text{ for all } y \neq x \\
0 & \text{otherwise}
\end{cases}$$

**Theorem 3.1 (L₃ → Adm).** Let $x$ be a physically instantiated configuration at time $t$. If L₃ holds as ontological constraint and Causal Localization (A3) holds, then $\mathsf{Adm}(x, t) = 1$.

**Proof.**

*Step 1.* By Identity, $x$ must be self-identical: its properties are definite, not indeterminate.

*Step 2.* By Excluded Middle, for any property $P$ that distinguishes $x$ from alternatives, either $x$ has $P$ or $x$ lacks $P$—there is no third option where $P$-status is undefined.

*Step 3.* By Non-Contradiction, $x$ cannot both have and lack $P$.

*Step 4.* Together, these require that any distinction between $x$ and alternative $y$ be registered in *some* definite location. (This is pure L₃.)

*Step 5.* By Lemma 3.0 (Admissibility Localization), for horizon crossings during $t \in [t_{\text{cross}}, t_{\text{emit}}]$, "definite location" must be the accessible algebra $A_B(t)$. (This invokes A3, not pure logic.)

*Step 6.* Therefore, distinguishability must reside in $A_B(t)$, which is exactly the record-existence constraint.

*Step 7.* By the packing theorem (2.1), this implies $\mathsf{Adm}(x, t) = 1$ with $\delta \geq \sqrt{2M/S_{BH}}$.  ∎

**Note on the derivation structure:** Steps 1-4 are pure L₃. Step 5 invokes a physical postulate (A3). The theorem thus derives Adm from L₃ + A3, not from L₃ alone. This is honest: the causal structure of spacetime is physics, not logic.

### 3.4 Why Horizons Are Special

Horizons are the canonical sites for L₃ → Adm because:

1. **Finite capacity:** $S_{BH}$ bounds how much distinguishability the boundary can encode
2. **Causal structure:** The interior is definitively inaccessible, not merely difficult to access
3. **Forced accounting:** Information must go *somewhere*—boundary, radiation, or...?

In generic quantum systems, "interior-only encoding" is unproblematic because the interior is eventually accessible. At horizons, causal structure makes the pre-emission interval special: L₃ cannot be satisfied by interior records alone during this window.

### 3.5 The Gap Is Closed

The Admissibility Dynamics paper [3] required:

$$L_3 \Rightarrow \mathsf{Adm}$$

We have now shown:

$$L_3 \xrightarrow{\text{horizon structure}} \text{record-existence constraint} \xrightarrow{\text{packing theorem}} \mathsf{Adm}$$

This is not abstract assertion. It is concrete physics: L₃ at horizons forces admissibility predicates on physically instantiated states.

---

## 4. De-Actualization: The Quantum–Classical–Quantum Cycle

### 4.1 The Core Claim: A Closed Dynamic Loop

ICH does not merely label the singularity problem. It proposes a **dynamic mechanism** connecting quantum and classical regimes:

$$\text{quantum instantiation} \xrightarrow{L_3 \text{ filter}} \text{classical emergence} \xrightarrow{\text{horizon saturation}} \text{de-actualization} \xrightarrow{\text{singularity}} \text{return to } I_\infty$$

And the cycle closes: $I_\infty$ is the reservoir from which new instantiations arise.

**What this is not:** A relabeling of "GR breaks down here." The standard narrative treats singularity breakdown as a *failure* of physics—incomplete description awaiting quantum gravity. ICH treats it as the *mechanism* by which actualized information transitions back to abstract structure.

**What this is:** A dynamical loop between:
- **I∞** (abstract, logically possible configurations)
- **A_Ω** (physically instantiated, spacetime-located states)

The loop has two phase transitions:
1. **Instantiation** (I∞ → A_Ω): at Planck scale, filtered by L₃
2. **De-actualization** (A_Ω → I∞): at singularities, forced by L₃ constraint failure

### 4.2 Why "Classical Breakdown" Is the Wrong Frame

Standard narrative: "Classical physics fails at singularities. We need quantum gravity to say what happens there."

This frames the singularity as a *gap in our knowledge*—a domain where existing physics gives no answer.

ICH reframes: The breakdown *is* the transition mechanism. What happens at the singularity is not unknown; it is the switch from Adm(x) = 1 (instantiated, L₃-compliant) to Adm(x) = 0 (no longer physically instantiable under L₃ constraints).

Consider: curvature divergence means the metric structure that *defines* spatial distinguishability ceases to function. Under L₃, states that cannot be distinguished cannot remain co-instantiated. They don't "vanish"—they transition to a domain where distinguishability is not spatially grounded.

That domain is $I_\infty$: logical possibility without physical address.

### 4.3 The Phase Transition: A_Ω → I∞

At the singularity, physical constraints that define instantiation reach a critical point:

- Curvature diverges → metric distinguishability fails
- Spacetime location becomes undefined → "where" loses meaning
- L₃ demands on distinguishability cannot be satisfied in spacetime

ICH proposes that information does not vanish but undergoes a **phase transition**:

$$A_\Omega \xrightarrow{\text{singularity}} I_\infty$$

The information is **de-actualized**: stripped of its physical address and properties, it returns to the space of logical possibilities.

**Key distinction:** This is not information *destruction* but information *de-instantiation*. The logical content persists in $I_\infty$; it ceases to be *physically present* in $A_\Omega$.

**Compatibility with singularity resolution.** If quantum gravity resolves singularities into a non-singular core or bounce, ICH interprets the *effective limit surface*—where spacetime locality breaks down—as the de-actualization site. The mechanism does not require literal classical divergence; it requires a regime where metric-based distinguishability fails and L₃ constraints can no longer be satisfied within spacetime structure. Whether this occurs at a classical singularity or a quantum-resolved near-singular region, the transition logic is the same.

### 4.4 The Closed Loop

The dynamic completes:

| Phase | Domain | What Governs |
|-------|--------|--------------|
| Instantiation | I∞ → A_Ω | L₃ filter at Planck scale |
| Classical emergence | A_Ω internal | QM (derived from L₃) |
| Horizon crossing | A_Ω boundary | Admissibility constraint |
| De-actualization | A_Ω → I∞ | L₃ constraint failure at singularity |

The universe is not a one-way process from Big Bang to heat death. Under ICH, information circulates: instantiated at one scale, de-actualized at another, cycling through physical and abstract domains.

This is what "classical physics breaks down" misses: the breakdown is not a gap but a *transition point* in a dynamical loop.

### 4.5 Connecting to Horizon Saturation

The horizon mechanism and de-actualization are complementary stages in the outflux process:

| Condition | Mechanism | Destination |
|-----------|-----------|-------------|
| Boundary can encode | Standard evolution | Boundary records |
| Boundary saturates | Island mechanism | Radiation |
| Singularity reached | De-actualization | $I_\infty$ |

The admissibility constraint forces information into the boundary until saturation, then into radiation. What reaches the singularity has exhausted both channels—it can no longer satisfy L₃ constraints within A_Ω.

### 4.6 What This Means for Information Conservation

**Standard unitarity:** Total information in $A_\Omega$ is conserved.

**ICH unitarity:** Total information across $I_\infty \cup A_\Omega$ is conserved.

These are compatible if de-actualization is a *transfer*, not destruction. Unitarity in the standard sense applies within $A_\Omega$ (enforced by quantum mechanics). ICH extends this: information that exits $A_\Omega$ via singularity doesn't vanish—it transitions to $I_\infty$.

### 4.7 The Hawking Radiation Question

Does Hawking radiation represent:
1. **Boundary overflow:** Information that couldn't fit (island mechanism)
2. **Partial de-actualization:** Information transitioning via evaporation
3. **Neither:** Thermal noise, not carrying structured information

Under ICH, option (1) applies pre-Page-time; the situation post-Page-time is more complex. The radiation carries correlations established at the boundary—these are *not* de-actualized but remain in $A_\Omega$ as the radiation subsystem.

De-actualization proper occurs at the singularity, for information that doesn't escape via radiation.

---

## 5. Cosmological Circulation and the Λ Fixed Point

### 5.1 The Complete Circulation

We can now state the full ICH picture:

**Influx (I∞ → A_Ω):**
- At the Planck scale, configurations from $I_\infty$ transition to physical instantiation
- L₃ acts as the filter: only configurations satisfying Identity, Non-Contradiction, Excluded Middle can instantiate
- This is the "creation" of space-time, particles, and physical structure

**Outflux (A_Ω → I∞):**
- Black hole singularities de-actualize information
- Configurations that reach the singularity lose their physical "address"
- Information returns to $I_\infty$—not destroyed but de-instantiated

**Circulation equation:**

$$Q(t) = F_{\text{in}}(t) - F_{\text{out}}(t)$$

where:
- $F_{\text{in}}$: instantiation rate from $I_\infty$
- $F_{\text{out}}$: de-actualization rate through black holes
- $Q(t)$: net circulation imbalance

### 5.2 The Λ Fixed Point

From [3], treat the circulation sector as an effective cosmological component:

$$\dot{\rho}_{\text{ICH}} + 3H(\rho_{\text{ICH}} + p_{\text{ICH}}) = Q(t)$$

**Key Proposition (from [3]).** If feedback drives $\rho_{\text{ICH}}$ toward a late-time attractor $\rho_* = \text{const}$, then:

1. $\dot{\rho}_* = 0$
2. With $Q(t) \rightarrow 0$ at late times: $p_* \approx -\rho_*$
3. Therefore $w_* \approx -1$

This produces $\Lambda$-like behavior.

### 5.3 The Horizon Constraint Contribution

The horizon dynamics we've established feed directly into this:

**Boundary saturation rate** → determines outflux capacity
**Packing bound** → limits how much information the universe's black hole population can de-actualize
**Island mechanism** → routes some information to radiation instead of singularity

The detailed dynamics depend on:
- Black hole formation rate (cosmological structure formation)
- Horizon saturation timescales (scrambling dynamics)
- Singularity rates vs. evaporation rates

### 5.4 Why This Explains Λ

Standard $\Lambda$CDM treats the cosmological constant as a primitive: a vacuum energy density with no explanation for its value.

ICH derives $\Lambda$-like behavior from:
1. **L₃ constraints** → admissibility filter
2. **Finite capacity** → horizon saturation
3. **Circulation dynamics** → influx/outflux imbalance
4. **Attractor behavior** → $w \approx -1$ fixed point

$\Lambda$ is not a primitive. It is the *cost of maintaining admissible reality* while information circulates.

### 5.5 Phenomenological Scaling Ansatz: w(z) and Black Hole Demographics

The ICH framework predicts that deviations from $w = -1$ should track the global outflux rate through black holes. We adopt the following phenomenological scaling ansatz as a first-pass, order-of-magnitude linkage, to be refined with detailed structure formation and black hole growth models.

**Outflux Rate.** Define the global de-actualization rate:

$$F_{\text{out}}(z) = \int dM \, n(M, z) \cdot \dot{S}_{\text{BH}}(M)$$

where $n(M, z)$ is the comoving number density of black holes with mass $M$ at redshift $z$, and $\dot{S}_{\text{BH}}(M)$ is the entropy accretion rate per black hole.

**Scaling Ansatz.** The deviation from $w = -1$ scales with the outflux rate relative to the Hubble rate:

$$w(z) + 1 \approx \alpha \cdot \frac{F_{\text{out}}(z)}{H(z) \cdot \rho_{\Lambda}}$$

where $\alpha$ is a dimensionless coupling constant and $\rho_\Lambda$ is the effective dark energy density.

**Physical Interpretation.** When black hole formation and accretion increase, the outflux rate rises, the circulation imbalance $Q(t)$ increases, and $w$ deviates slightly above $-1$. Conversely, when black hole activity decreases (late universe), the system approaches the fixed-point attractor with $w \to -1$.

**Observational Signature.** The ansatz predicts:

$$\frac{dw}{dz}\bigg|_{z \sim 0} \sim \alpha \cdot \frac{d}{dz}\left[\frac{F_{\text{out}}}{H \rho_\Lambda}\right]_{z=0}$$

Since black hole demographics are independently measurable (gravitational wave mergers, X-ray surveys, quasar luminosity functions), this provides a cross-check: ICH predicts a specific correlation between $w(z)$ evolution and global black hole activity.

**Current Constraints.** With $\lvert w + 1 \rvert < 0.06$ at 2σ and estimated $F_{\text{out}}$ from LIGO/Virgo merger rates, the constraint $\alpha \lesssim 0.1$ is consistent with, but does not yet test, the framework. DESI and Euclid will improve $w(z)$ constraints by an order of magnitude; LISA will improve black hole merger demographics by two orders of magnitude. The combination should provide a genuine test by ~2035.

### 5.6 The Observational Mapping

From [3], the framework predicts:

1. **$\Lambda$ behaves as dynamical attractor** with small deviations from $w = -1$
2. **Deviations track global entropy sinks** (black hole demographics) via the scaling ansatz (§5.5)
3. **Phase transitions in admissibility** appear as cosmological phase transitions

Current observational bounds constrain $\lvert w + 1 \rvert < 0.06$ at 2σ. Next-generation surveys (DESI, Euclid, Roman) achieving sub-percent precision could detect or rule out ICH-specific signatures.

---

## 6. The Complete ICH Picture

### 6.1 The Chain

We have now established the complete derivation:

$$L_3 \xrightarrow{\S3} \mathsf{Adm} \xrightarrow{\S4} \text{de-actualization} \xrightarrow{\S5} \Lambda$$

More explicitly:

1. **L₃ at horizons** forces record-existence in accessible algebras (§3)
2. **Packing theorem** converts this to the admissibility predicate (§3.2)
3. **Boundary saturation** routes information to radiation (island) or singularity (de-actualization) (§4)
4. **Circulation dynamics** produce an effective dark energy sector (§5)
5. **Attractor behavior** yields $w \approx -1$ (§5.2)

### 6.2 Relation to Other LRT Papers

The LRT paper series now has three components:

| Paper | Focus | Key Result |
|-------|-------|------------|
| **Flagship** [1] | L₃ → QM | Hilbert space, Born rule from logic |
| **Horizon Channels** [4] | Admissibility at horizons | Packing bounds, island mechanism |
| **ICH Operationalization** (this) | L₃ → Adm → Λ | Cosmological constant as fixed point |

The flagship derives quantum mechanics from logic.
The horizon paper derives gravitational information dynamics from admissibility.
This paper closes the loop, deriving admissibility from L₃ and connecting to cosmology.

### 6.3 What's New Here

The Admissibility Dynamics paper [3] was a *translation layer*: if Adm exists, here's how physics looks.

This paper provides the *operationalization*: Adm is *derived* from L₃ via horizon physics.

The horizon paper [4] was *agnostic* about L₃: treat admissibility as phenomenological hypothesis.

This paper *commits*: the horizon constraint is L₃ instantiated at gravitational boundaries.

---

## 7. Falsifiable Consequences

### 7.1 From Horizons

From [4], the horizon constraint predicts:

- **Page time shift:** $\Delta t / t \sim -0.82\varepsilon$ (earlier Page time)
- **QES location:** $(φ_H - φ_{\text{QES}})/4G \sim S_{\text{rad}} \cdot h(\bar{d})$
- **Scrambling bound:** $t^* \geq kM$ (weaker than Hayden-Preskill)

### 7.2 From Circulation

The cosmological predictions:

- **$w(z)$ evolution:** Small deviations from $-1$, tracking black hole demographics
- **Correlation with entropy production:** $w$ variations should correlate with large-scale structure formation
- **Phase transitions:** Possible signatures at recombination or other cosmological epochs

### 7.3 Joint Constraints

The two prediction families connect:

- Horizon saturation dynamics → determine $F_{\text{out}}$
- Black hole formation → determine circulation budget
- Aggregate behavior → constrain $w_{\text{eff}}$

This is testable in principle, though current precision is insufficient.

### 7.4 What Would Falsify ICH

1. **L₃ violation at horizons:** If distinguishability can be erased without boundary record (even temporarily), the L₃ → Adm step fails
2. **Perfect $w = -1$:** If $\Lambda$ is exactly constant with zero deviations, attractor behavior is indistinguishable from primitive constant
3. **Anti-correlation with black holes:** If $w$ variations correlate *negatively* with black hole demographics, circulation direction is wrong

---

## 8. Discussion

### 8.1 What This Paper Achieves

The central result: **the L₃ → Adm step is operationalized through horizon physics.**

This was the missing link in the ICH chain. Without it, ICH was conceptually motivated but formally incomplete. With it, the derivation proceeds:

$$L_3 \rightarrow \text{(horizon constraint)} \rightarrow \mathsf{Adm} \rightarrow \text{(circulation dynamics)} \rightarrow \Lambda$$

Every step now has formal content.

### 8.2 What Remains Open

1. **Planck-scale instantiation:** The influx mechanism ($I_\infty \rightarrow A_\Omega$) is posited, not derived
2. **Singularity dynamics:** De-actualization is proposed, not calculated from quantum gravity
3. **Quantitative circulation:** The $F_{\text{in}}, F_{\text{out}}$ rates are not computed from first principles

These are the next frontiers.

### 8.3 Relation to Standard Approaches

ICH does not contradict unitarity—it extends it. Standard unitarity conserves information within $A_\Omega$. ICH conserves information across $I_\infty \cup A_\Omega$.

ICH does not contradict the island formula—it provides a mechanism. The island formula is a consistency condition. Boundary saturation under admissibility is why it holds.

ICH does not contradict $\Lambda$CDM observationally (yet). It predicts $w \approx -1$ with small deviations. Current observations are consistent with this.

### 8.4 Philosophical Implications

If ICH is correct:

- **Reality is a circulation,** not a one-way process
- **Logic constrains physics** at the deepest level
- **Information is conserved** across instantiation/de-instantiation phases
- **The cosmological constant** is not arbitrary but emerges from logical necessity

These are strong claims. They stand or fall with the physics.

---

## 9. Conclusion

This paper operationalizes the Information Circulation Hypothesis by deriving the admissibility predicate from L₃ constraints at horizons.

The key results:

1. **L₃ → Adm (§3):** Logical constraints at horizons force record-existence in accessible algebras, generating the admissibility predicate.

2. **De-actualization (§4):** At boundary saturation, information routes to radiation (islands) or singularity (return to $I_\infty$).

3. **Λ as fixed point (§5):** Circulation dynamics drive toward an attractor with $w \approx -1$, explaining the cosmological constant as the cost of maintaining admissible reality.

4. **Closed chain (§6):** The complete derivation $L_3 \rightarrow \mathsf{Adm} \rightarrow \Lambda$ is now formally established.

The framework is falsifiable via horizon physics (QES location, Page time shift) and cosmological observations ($w(z)$ evolution, black hole correlations).

Whether one accepts the metaphysical framework or treats ICH as phenomenological hypothesis, the physics generates testable predictions. The hypothesis stands ready for observational confrontation.

---

## Acknowledgments

This research was conducted independently. AI tools (Claude/Anthropic, GPT/OpenAI) assisted with drafting under HCAE protocol. All claims remain the author's responsibility.

---

## References

[1] Longmire, J.D. (2025). Logic Realism Theory: Physical Foundations from Logical Constraints. Zenodo. https://doi.org/10.5281/zenodo.17831912

[2] Longmire, J.D. (2026). The Information Circulation Hypothesis. LRT Articles. https://jdlongmire.github.io/logic-realism-theory/articles/information-circulation/

[3] Longmire, J.D. (2026). Admissibility Dynamics, Noether Charges, and the Λ Fixed Point. Working Paper.

[4] Longmire, J.D. (2026). Horizon Channel Constraints and the Island Formula: A Boundary Saturation Mechanism. Submitted to JHEP.

Almheiri, A., Engelhardt, N., Marolf, D., & Maxfield, H. (2019). The entropy of bulk quantum fields and the entanglement wedge of an evaporating black hole. *JHEP* 2019(12), 63.

Bekenstein, J.D. (1973). Black holes and entropy. *Phys. Rev. D* 7(8), 2333-2346.

Engelhardt, N., & Wall, A.C. (2015). Quantum extremal surfaces: holographic entanglement entropy beyond the classical regime. *JHEP* 2015(1), 73.

Hawking, S.W. (1975). Particle creation by black holes. *Commun. Math. Phys.* 43(3), 199-220.

Landauer, R. (1961). Irreversibility and heat generation in the computing process. *IBM J. Res. Dev.* 5(3), 183-191.

Page, D.N. (1993). Information in black hole radiation. *Phys. Rev. Lett.* 71(23), 3743-3746.

Penington, G. (2020). Entanglement wedge reconstruction and the information paradox. *JHEP* 2020(09), 002.

---

*End of Paper*
