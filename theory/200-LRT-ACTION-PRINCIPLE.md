---
title: "The Action Principle in Logic Realism Theory: Distinguishability, Geometric Potential, and the Path to Quantum Field Theory"
author: "James D. Longmire"
affiliation: "Northrop Grumman Fellow (unaffiliated research)"
orcid: "0009-0009-1383-7698"
date: "April 2026"
status: "Draft"
series: "LRT Paper 005"
upstream: "001-TRM-FOUNDATIONS, 002-LRT-TAB-PHILOSOPHY, 100-LRT-CORE-PHYSICS"
abstract: |
  Logic Realism Theory (LRT) derives non-relativistic quantum mechanics from the primitive ontology
  χ ≡ [L₃ : I∞ : A] — the Three Laws of Logic as constitutive constraints, an infinite informational
  possibility space, and a binary actualization primitive. The companion paper (100-LRT-CORE-PHYSICS)
  reconstructs the Schrödinger equation and notes, in §5.7, that the quantum action principle is
  available as a consequence. The present paper expands that compressed treatment into a full
  argument. We give careful proofs that the Wootters (1981) statistical distance identifies with the
  Fubini-Study metric, that the Kibble (1979) geometrization of quantum mechanics follows from the
  information geometry of I∞, and that the Anandan-Aharonov (1990) relation — energy uncertainty as
  speed through I∞ — is a theorem rather than an observation. We then articulate the central novel
  principle: the Principle of Least Distinguishability, which provides an ontological grounding for
  δS = 0 in terms of X rather than a brute variational postulate. We examine what additional
  representational input is needed to recover the configuration-space action, assess whether L₃
  symmetry constrains that input, and sketch the forward-looking connection to Fock space and quantum
  field theory via the extension of I∞ to field configurations. Open problems are enumerated with
  precise scope statements.
---

-----

<!-- LRT-200 draft: April 2026. Upstream: 001, 002, 100. Downstream: 006 (gauge), cosmology companion. -->

## 1. Introduction and Motivation

### 1.1 What §5.7 of 002 Establishes and What Remains

The companion paper (Longmire, 2026c; hereafter **002**) reconstructs non-relativistic quantum
mechanics from the primitive ontology

$$\chi \equiv [L_3 : I_\infty : \mathbf{A}]$$

along a thirteen-step chain. At Step 13, the Schrödinger equation is obtained as a consequence of
Stone's theorem applied to the continuous unitary group that Determinate Identity and G-equivariance
require. Section §5.7 of 002 then establishes the dual Lagrangian/path-integral formulation:

- The Legendre transform from H to L is a standard mathematical result that requires nothing beyond
  the self-adjoint Hamiltonian from Stone's theorem (§5.7.1 of 002).
- The path integral admits an exact ontological reading in terms of X: I∞ is the path space, L₃
  governs the action weighting, and A performs the actualization (§5.7.2 of 002).
- The quantum action on projective Hilbert space ℂP(ℋ) is fully determined by two quantities already
  in the reconstruction — the Fubini-Study connection A_FS from the distinguishability metric D on
  I∞, and the Hamiltonian expectation ⟨H⟩ from Stone's theorem — so that OPN-007 (Action Principle
  from X) is resolved for the quantum action (§5.7.3 of 002).
- The Anandan-Aharonov relation v_D = ΔE/ℏ is noted as a consequence, dissolving OPN-001
  (Energy-Action) as a corollary (§5.7.3 of 002).

This is a substantial result, but §5.7 treats it at a density appropriate for an already long
reconstruction paper. Key lemmas are asserted rather than proved. The central interpretive claim —
that the variational principle has an ontological grounding, not just a structural analogy — is
gestured at rather than argued. The scope limitations are noted but not fully analyzed. And the
forward-looking extension to quantum field theory is absent.

The present paper addresses each of these gaps. It is a standalone document; readers should have
familiarity with LRT's primitive ontology (§1 of 002) but the paper is self-contained on the action
principle.

### 1.2 The Central Thesis

The quantum action principle in LRT is not "nature extremizes action" as a postulate imported from
classical mechanics and extended by analogy into quantum theory. It is a consequence of the geometry
of I∞ together with the binary character of A. More precisely:

**The Principle of Least Distinguishability (PLD).** Actualization follows paths through I∞ where
the accumulated geometric potential — the Fubini-Study connection integrated along the path — is
stationary with respect to the competition between traversal of I∞ and the energy cost of sustaining
actualization. The variational condition δS = 0 is not an independent postulate; it is the condition
that a path is extremal with respect to the geometry of distinguishable configurations, where that
geometry is already fixed by the information-theoretic structure of I∞.

The argument for this thesis proceeds in three stages: (1) establishing that the geometry of I∞ is
the Fubini-Study geometry via Wootters' theorem; (2) establishing the Anandan-Aharonov relation as
a theorem connecting energy uncertainty to the rate of traversal through I∞; and (3) showing that the
action functional is the integral of the geometric potential minus the energy cost, so that δS = 0 is
the stationarity condition on this competition. At no stage is an additional postulate introduced
beyond what 002 already establishes.

### 1.3 Epistemic Status Conventions

Following 002's conventions, every claim in this paper is tagged:

- **ESTABLISHED** — imported from a peer-reviewed theorem or follows by standard mathematics from
  established claims. No LRT-specific philosophical argument is required.
- **ARGUED** — defended by LRT-specific grounding arguments. The argument is given and is intended
  to be compelling, but a critic retaining different background assumptions can contest it.
- **CONJECTURED** — presented as a plausible extension with supporting considerations, but not yet
  argued to LRT standards.
- **OPEN** — identified as a problem the theory has not resolved, with scope statement.

-----

## 2. The Information Geometry of I∞: Wootters' Theorem

### 2.1 The Distinguishability Metric D on I∞

The primitive ontology X equips I∞ with a distinguishability structure. As established in §1.3.1 of
002, the metric D on I∞ is:

$$D(s_1, s_2) = \sup_M \lvert P_M(s_1) - P_M(s_2)\rvert_{\mathrm{TV}}$$

where M ranges over all L₃-admissible measurements and the supremum is the total variation distance
between the probability distributions over outcomes. Configurations are distinct (D > 0) if and only
if some idealized physical interaction yields different probability distributions for them;
indistinguishable (D = 0) configurations violate L₃'s Identity requirement and are not distinct
elements of I∞.

This metric is not imposed on I∞ from outside. It is constitutive: what it means for two
configurations in I∞ to be different configurations is precisely that they are distinguishable by
some measurement. The Physical Proposition Criterion (PPC, §1.3 of 002) licenses this identification.

*[Epistemic status: ARGUED — the identification of D with operational distinguishability follows from
the constitutive reading of L₃, as defended in §1.3.1 of 002. The PPC is the governing bridge
principle.]*

### 2.2 Statistical Distance and the Fubini-Study Metric

Once the Born rule is established (Step 6 of 002, from Gleason's theorem), the probability
distributions P_M(s) for a quantum state |ψ⟩ are determined by the Born rule:

$$P_M(\psi) = \{|\langle m_k | \psi \rangle|^2\}_{k}$$

where {|m_k⟩} are the eigenstates of the measurement M. The statistical distance between two quantum
states |ψ₁⟩ and |ψ₂⟩ under all such Born-rule measurements is the supremum of the total variation
distance over all PVMs.

**Lemma 1 (Wootters, 1981).** *The statistical distance between quantum states |ψ₁⟩ and |ψ₂⟩,
defined as the supremum over all PVM measurements of the total variation distance between the
resulting Born-rule probability distributions, equals the Fubini-Study distance:*

$$D_{stat}(\psi_1, \psi_2) = \arccos\lvert\langle\psi_1|\psi_2\rangle\rvert = d_{FS}(\psi_1, \psi_2)$$

**Proof sketch.** The total variation distance between probability distributions {p_k} and {q_k} is
(1/2)Σ_k |p_k − q_k|. For quantum states and PVM measurements, the optimal measurement that
maximizes this distance is the one that projects onto eigenstates most closely aligned with the
difference |ψ₁⟩ − |ψ₂⟩. By the Cauchy-Schwarz inequality applied to the inner product structure of
ℋ, the supremum over all PVMs of the total variation distance is achieved by a two-outcome
measurement, and the supremum equals arccos|⟨ψ₁|ψ₂⟩|. This is precisely the Fubini-Study angle
between the rays in ℂP(ℋ) corresponding to |ψ₁⟩ and |ψ₂⟩. Full proof: Wootters (1981, §II). □

**Corollary 1.** *The distinguishability metric D on I∞, restricted to quantum states (elements of
ℂP(ℋ)), is the Fubini-Study metric d_FS.*

This corollary is the structural cornerstone of the action derivation. The geometry of I∞ — insofar
as I∞ is parameterized by quantum states — is not an independently chosen Riemannian structure. It
is the unique geometry forced by the distinguishability structure of L₃-admissible configurations
together with the Born rule. The Fubini-Study metric is the metric D, restricted and computed.

*[Epistemic status: ESTABLISHED — Corollary 1 follows from Lemma 1 (Wootters, 1981) and the
identification of D with statistical distance, which is ARGUED via the PPC.]*

### 2.3 The Kibble Geometrization

Given the Fubini-Study metric on ℂP(ℋ), Kibble (1979) showed that quantum mechanics admits a
complete geometric formulation on this manifold. The key structures are:

1. **Riemannian metric g_FS:** The Fubini-Study metric, inherited from the round metric on the unit
   sphere in ℋ projected to the ray space ℂP(ℋ).

2. **Symplectic form ω_FS:** The imaginary part of the Hermitian inner product restricted to
   ℂP(ℋ). Together with g_FS, it forms a Kähler structure.

3. **Symplectic potential (connection 1-form) A_FS:** The 1-form satisfying dA_FS = ω_FS, given in
   local coordinates by A_FS = Im⟨ψ|dψ⟩.

4. **Hamiltonian vector fields:** Every self-adjoint operator H on ℋ generates a Hamiltonian vector
   field on ℂP(ℋ) via the symplectic structure. The resulting flow is the projective action of the
   unitary group U(H).

**Theorem 1 (Kibble, 1979).** *Quantum evolution under the Schrödinger equation iℏ∂_t|ψ⟩ = H|ψ⟩
is equivalent to Hamiltonian flow on (ℂP(ℋ), ω_FS) generated by the classical Hamiltonian function
h([ψ]) = ⟨ψ|H|ψ⟩. The Schrödinger equation is the Hamiltonian equation of motion on this Kähler
manifold.*

**LRT reading.** In LRT terms, Kibble's theorem says that the dynamics forced by Stone's theorem
(continuous unitarity under L₃ and G-equivariance) is precisely Hamiltonian flow on the space of
distinguishable configurations I∞, equipped with the metric D = d_FS. The dynamics lives on the
information geometry. Quantum evolution is traversal of I∞ along Hamiltonian trajectories.

*[Epistemic status: ESTABLISHED — Kibble (1979) is imported. The LRT reading is ARGUED via the
identification D = d_FS.]*

-----

## 3. The Anandan-Aharonov Relation as a Theorem

### 3.1 Statement

The Anandan-Aharonov relation connects energy uncertainty to the rate of change of distinguishability.
In 002, §5.7.3, it is cited as a result; here we give the argument in full because it is the key
theorem from which the Principle of Least Distinguishability will be derived.

**Theorem 2 (Anandan and Aharonov, 1990).** *Let |ψ(t)⟩ be a state evolving under the Schrödinger
equation with self-adjoint Hamiltonian H. The instantaneous speed of the state under the Fubini-Study
metric on ℂP(ℋ) is:*

$$v_D(t) \;\equiv\; \frac{d s_{FS}}{d t} \;=\; \frac{\Delta E(t)}{\hbar}$$

*where ΔE(t) = √(⟨H²⟩ − ⟨H⟩²) is the instantaneous energy uncertainty.*

**Proof.** The Fubini-Study distance between |ψ(t)⟩ and |ψ(t + dt)⟩ for an infinitesimal time step dt is:

$$ds_{FS}^2 = \langle d\psi | d\psi \rangle - |\langle \psi | d\psi \rangle|^2$$

where |dψ⟩ = |ψ(t+dt)⟩ − |ψ(t)⟩. From the Schrödinger equation, |ψ̇⟩ = −(i/ℏ)H|ψ⟩, so
|dψ⟩ = (dt)|ψ̇⟩ = −(idt/ℏ)H|ψ⟩. Substituting:

$$\langle d\psi | d\psi \rangle = \frac{dt^2}{\hbar^2}\langle\psi|H^2|\psi\rangle = \frac{dt^2}{\hbar^2}\langle H^2\rangle$$

$$|\langle\psi|d\psi\rangle|^2 = \frac{dt^2}{\hbar^2}|\langle\psi|H|\psi\rangle|^2 = \frac{dt^2}{\hbar^2}\langle H\rangle^2$$

Therefore:

$$ds_{FS}^2 = \frac{dt^2}{\hbar^2}\bigl(\langle H^2\rangle - \langle H\rangle^2\bigr) = \frac{dt^2}{\hbar^2}(\Delta E)^2$$

Taking the square root: $ds_{FS}/dt = \Delta E / \hbar$. □

### 3.2 The LRT Interpretation

Theorem 2 has a precise meaning in LRT's ontological vocabulary. The Fubini-Study metric d_FS is the
distinguishability metric D on I∞ restricted to quantum states (Corollary 1). The quantity v_D(t) is
therefore the rate at which the actualized configuration changes distinguishable position in I∞. The
Anandan-Aharonov relation states:

> *The rate at which an actualized state traverses the space of distinguishable configurations is
> determined entirely by the energy uncertainty of that state.*

Several consequences follow immediately.

**Consequence 1 (Geometric invariant).** The total distinguishability traversed by an evolution
γ: [t_i, t_f] → ℂP(ℋ) is:

$$\ell_D[\gamma] = \int_{t_i}^{t_f} v_D(t)\,dt = \frac{1}{\hbar}\int_{t_i}^{t_f} \Delta E(t)\,dt$$

This is a purely geometric quantity — the arc length of γ in I∞ under D. It is unitary-invariant and
independent of the choice of phase convention for |ψ(t)⟩.

**Consequence 2 (Energy-time uncertainty).** The Mandelstam-Tamm inequality ΔE · Δt ≥ ℏ/2 follows
directly: the minimum time to traverse a Fubini-Study arc length θ = d_FS is Δt ≥ ℏθ/ΔE ≥
ℏπ/(2ΔE). The energy-time uncertainty relation is a statement about the geometry of I∞, not an
independent postulate.

**Consequence 3 (OPN-001 dissolved).** The energy-action relationship OPN-001, listed as an open
problem prior to §5.7.3 of 002, is now a corollary: energy is the rate of distinguishability change
(ΔE/ℏ = v_D), and the action integrates the symplectic potential A_FS along the path. The
relationship is geometric, grounded in D.

*[Epistemic status of Theorem 2: ESTABLISHED — the proof follows from the Fubini-Study metric
definition and the Schrödinger equation, both of which are established in the reconstruction. The
LRT interpretation (Consequences 1-3) is ARGUED via the identification D = d_FS.]*

### 3.3 The Geometric Phase Connection

A further consequence of the Fubini-Study structure is the geometric (Berry) phase. When a state
|ψ(t)⟩ evolves adiabatically around a closed loop γ in ℂP(ℋ), it acquires a geometric phase:

$$\phi_B = \oint_\gamma \mathcal{A}_{FS} = \int_\Sigma \omega_{FS}$$

where ω_FS is the Fubini-Study symplectic form and Σ is any surface bounded by γ (Stokes' theorem).
This is not a dynamical phase — it depends only on the geometry of the path in I∞, not on the
parametrization. In LRT terms, the Berry phase is the holonomy of a closed loop through the
distinguishability geometry of I∞: it measures how much I∞'s curvature has been enclosed by the
actualization trajectory.

*[Epistemic status: ESTABLISHED — Berry (1984) geometric phase is a standard result; the LRT
reading follows from D = d_FS.]*

-----

## 4. The Quantum Action Principle

### 4.1 The Action Functional on ℂP(ℋ)

Given the Kibble geometrization (Theorem 1) and the identification D = d_FS (Corollary 1), the
action functional on ℂP(ℋ) follows from the structure of the Kähler manifold. The Dirac-Frenkel
variational principle states that the Schrödinger equation is equivalent to stationarity of the
functional:

$$S[\gamma] = \hbar\int_\gamma \mathcal{A}_{FS} - \int_{t_i}^{t_f}\langle H\rangle\,dt$$

where γ: [t_i, t_f] → ℂP(ℋ) is a smooth curve, A_FS = Im⟨ψ|dψ⟩ is the symplectic potential (Berry
connection), and ⟨H⟩ = ⟨ψ(t)|H|ψ(t)⟩ is the Hamiltonian expectation along γ. Hamilton's principle
δS = 0 (variation with fixed endpoints in ℂP(ℋ)) recovers the Schrödinger equation.

**Both terms are already in the reconstruction:**

- **Term 1** is the integral of A_FS. As established in §2.2-2.3 above (following Wootters, 1981
  and Kibble, 1979), A_FS is the symplectic potential of the Fubini-Study metric, which is the
  distinguishability metric D restricted to quantum states. A_FS is determined by the information
  geometry of I∞.

- **Term 2** is the integral of ⟨H⟩. The self-adjoint operator H is the generator obtained from
  Stone's theorem (Step 10 of 002). Its expectation value on the evolving state is a function of the
  state and H, both already in the reconstruction.

No third term exists. No additional postulate is required.

*[Epistemic status: ESTABLISHED — the quantum action on ℂP(ℋ) is fully determined by two quantities
already present in 002's reconstruction. The Dirac-Frenkel principle, Kibble's theorem, and the
Wootters identification are all imported peer-reviewed results. OPN-007 is resolved for the quantum
action on state space.]*

### 4.2 Acyclicity of the Dependency Graph

The Schrödinger equation appears in the reconstruction twice: first as a consequence of Stone's
theorem (Steps 7-13 of 002), and second as a consequence of δS = 0. The dependency graph is:

```
D (Step 4) → d_FS → A_FS      ──┐
                                  ├─→ S[γ] → δS=0 → Schrödinger (2nd route)
Stone (Step 10) → H → ⟨H⟩    ──┘

Steps 7-13 (independent) → Schrödinger (1st route, no S[γ] invoked)
```

The two routes are independent derivations of the same equation. Stone's theorem does not invoke S[γ];
the action principle does not invoke Stone's theorem. The convergence is a consistency check: both
approaches to the dynamics of X yield the same evolution equation. The chain is acyclic.

### 4.3 The Legendre Transform and Configuration Space

Given H on ℋ, the classical Lagrangian is available via the Legendre transform:

$$L(q,\dot{q}) = p\dot{q} - H(q,p), \qquad p = \frac{\partial L}{\partial \dot{q}}$$

and the configuration-space action is:

$$S_{cl}[\gamma] = \int_{t_i}^{t_f} L(q(t),\dot{q}(t))\,dt$$

The Legendre transform is a standard mathematical construction. Given H, L follows without new
assumptions. *[Epistemic status: ESTABLISHED.]*

The transition from the state-space action S[γ] on ℂP(ℋ) to the configuration-space action S_cl[γ]
on configuration space Q requires a representation: a choice of basis, or equivalently a choice of
physical observables to treat as coordinates. This is discussed in §6 below.

-----

## 5. The Principle of Least Distinguishability

### 5.1 Motivation: Why δS = 0 Needs Ontological Grounding

Classical mechanics inherits the action principle from Hamilton (1834) as a variational postulate
calibrated to reproduce Newton's laws. Its extension to quantum mechanics via Feynman (1965) is
productive but analogical — "nature chooses the path of least action" is a useful summary but not
an explanation. The question that LRT's program poses is sharper: *given X, why does actualization
follow paths that satisfy δS = 0 rather than some other selection criterion?*

The answer is not that "LRT postulates δS = 0 for ontological reasons." It is that δS = 0 is not
an independent postulate at all in LRT. It is the stationarity condition on the competition between
two quantities that are already defined by X. Once the geometry of I∞ is fixed (Corollary 1) and the
energy cost of actualization is fixed (Stone's theorem via Kibble), the action functional S[γ] is
determined. Its stationarity condition is determined. The principle is derived, not assumed.

### 5.2 The Principle Stated Precisely

**Principle of Least Distinguishability (PLD).** *Let γ: [t_i, t_f] → ℂP(ℋ) be a smooth path with
fixed endpoints [ψ_i] and [ψ_f] in I∞. Actualization follows paths γ that are stationary with
respect to:*

$$S[\gamma] = \underbrace{\hbar\int_\gamma \mathcal{A}_{FS}}_{\text{geometric potential through }I_\infty} - \underbrace{\int_{t_i}^{t_f}\langle H\rangle\,dt}_{\text{energy cost of actualization}}$$

*The condition δS = 0 selects trajectories that are extremal with respect to the competition between
the accumulated geometric potential (traversal of I∞) and the accumulated energy cost of sustaining
the actualized configuration.*

The two terms have distinct ontological sources:

- **The geometric term ℏ∫A_FS** measures the symplectic area swept by the actualization path through
  I∞. It is an intrinsic geometric quantity — the line integral of the information-geometric potential.
  Its integrand A_FS is determined entirely by D on I∞. A larger geometric term corresponds to a path
  that traverses more of I∞'s distinguishability structure.

- **The energy term ∫⟨H⟩dt** is the accumulated cost of maintaining the actualized state against the
  dynamical constraint imposed by H. It is not a geometric quantity; it depends on the specific
  Hamiltonian of the system. For a free particle it vanishes in the zero-energy frame; for a particle
  in a potential it is nonzero.

The stationary paths balance these two contributions. Paths that maximize traversal of I∞ without
incurring excessive energy cost are preferred. Paths that are energetically cheap but geometrically
trivial (staying in one place in I∞) are also selected when H = 0. The variational condition is the
condition of geometric balance in the information space.

### 5.3 The PLD as Grounding for Hamilton's Principle

Hamilton's principle in classical mechanics, δS_cl = 0, follows from the PLD as a semiclassical
limit. In the ℏ → 0 limit (where quantum interference is suppressed), the path integral

$$\langle q_f, t_f | q_i, t_i\rangle = \int \mathcal{D}[\gamma]\,e^{iS[\gamma]/\hbar}$$

is dominated by the stationary-phase trajectory — the single path γ_cl for which δS = 0. This is
the classical trajectory. The classical action principle is the limiting case of the PLD when
actualization probability is concentrated on a single history.

In the full quantum case, the path integral sums over all of I∞ (all histories consistent with the
boundary conditions). Each history receives a phase weight e^{iS[γ]/ℏ} determined by the action.
Histories near the stationary point contribute constructively (their phases are aligned); histories
far from it contribute destructively (their phases are random and cancel). The PLD does not select
a single path; it specifies the interference weighting on all paths in I∞.

*[Epistemic status: ARGUED — the PLD is not a new postulate but an ontological articulation of the
action functional already derived from X. Its grounding is: the geometric term comes from D = d_FS
on I∞ (ESTABLISHED via Wootters, ARGUED via the PPC); the energy term comes from Stone (ESTABLISHED
given Steps 7-10 of 002). The PLD statement is ARGUED insofar as it depends on the identification
D = d_FS, which in turn depends on the ARGUED identification of D with statistical distance via the
PPC.]*

### 5.4 The Information-Geometric Reading

The PLD has a natural information-geometric reading. The Fisher information metric on the space of
probability distributions induced by Born-rule measurements is, by Wootters' theorem, the Fubini-Study
metric on ℂP(ℋ). A path γ in I∞ accumulates arc length ℓ_D[γ] = ∫(ΔE/ℏ)dt — the total
distinguishability traversed.

The stationary paths under δS = 0 are those where the first variation of the accumulated
distinguishability, weighted by the symplectic potential, balances the first variation of the energy
integral. This is a condition on the relationship between the information-geometric curvature of I∞
and the energy landscape defined by H.

Stated differently: the PLD selects paths that are "efficient" in the information-geometric sense —
paths that traverse distinguishability at the rate imposed by H, neither more nor less. Deviations
from this rate cause phase decoherence in the path integral (destructive interference), suppressing
contributions from inefficient paths.

-----

## 6. The Configuration-Space Action: Representation and Scope

### 6.1 What LRT Provides Universally

The foregoing sections establish the quantum action on state space ℂP(ℋ). This is the fully general,
representation-independent result. It holds for any quantum system whose Hilbert space ℋ is
constructed from I∞ via the reconstruction chain of 002. The content is:

1. ℂP(ℋ) is equipped with the Fubini-Study metric d_FS = D|_{states} (Corollary 1).
2. Evolution is Hamiltonian flow on (ℂP(ℋ), ω_FS) generated by h([ψ]) = ⟨H⟩ (Theorem 1).
3. The action S[γ] = ℏ∫A_FS − ∫⟨H⟩dt is determined by D and H (§4.1).
4. The PLD (δS = 0) selects the dynamically allowed paths (§5.2).

This is universal across all physical systems within LRT's reconstruction scope: the particle in a
box, the harmonic oscillator, the hydrogen atom, spin systems — any system whose Hilbert space is
the ℂH of 002.

### 6.2 What Representation Choice Adds

The configuration-space action S_cl = ∫L(q,q̇)dt requires, beyond the above, a choice of
representation: a specification of what physical observables are treated as coordinates q and what
the corresponding kinetic and potential structure of L is.

This representational input has two components:

**Component 1: Kinetic structure.** The kinetic term T = (m/2)q̇² in L(q,q̇) = T − V requires
specifying a mass parameter m and treating position q as the coordinate. Neither m nor the choice of
position as a coordinate is derivable from X alone. The mass appears in the Hamiltonian as the
coefficient of p²/2m; LRT inherits it as an empirical parameter. The choice of position versus
momentum (or angle, or field amplitude) as the fundamental variable is a representation choice that
different physical systems make differently.

**Component 2: Potential structure.** The potential V(q) is a function on configuration space whose
form encodes the specific physical interactions present in the system. It is an empirical input for
every particular system. LRT's reconstruction provides the framework (self-adjoint H with real
spectrum, Schrödinger equation) but not the content.

The Legendre transform (§4.3) provides the formal bridge: given H(q,p) for a specific system with
specific kinetic and potential terms, L(q,q̇) follows by change of variables, and S_cl = ∫Ldt
follows immediately. The transform requires nothing beyond H.

*[Epistemic status: ARGUED — the scope limitation is clear and non-trivial. LRT provides the
framework; the representation provides the physics of specific systems. This is a feature, not a
gap: it is the structural analogue of LRT's non-derivation of specific Hamiltonians (noted in §5 of
002). Particular Hamiltonians are empirical inputs; particular representations are choices made
relative to empirical facts about specific physical domains.]*

### 6.3 Does L₃ Constrain the Representation?

The most interesting question in this vicinity is whether the constitutive role of L₃ in I∞ places
any constraints on which representations are admissible — that is, whether the information geometry
of I∞ "prefers" certain kinetic structures or potential forms.

Several observations can be made:

**Observation 1: Minimal representations.** L₃'s identity requirement (via the PPC) demands that
configurations be operationally distinguishable. A representation that makes physically distinct
configurations indistinguishable in the configuration variable violates the PPC. This rules out
overcomplete or degenerate coordinate choices. Among L₃-admissible representations, those that make
the distinguishability metric D most directly legible are structurally preferred. This suggests, but
does not prove, that representations in which the kinetic term is (proportional to) the metric on
configuration space are preferred.

**Observation 2: The Wigner-Eckart constraint.** L₃ requires that the dynamics be equivariant under
the symmetry group G that the reconstruction identifies (Step 11 of 002). Any representation must
respect G-equivariance. This rules out kinetic terms that are not G-invariant, which in the case of
spatial symmetry groups constrains the mass tensor (isotropy requires scalar m, anisotropy requires
a tensor).

**Observation 3: The information-geometric kinetic term.** The Fubini-Study metric on ℂP(ℋ) induces,
via the Wootters identification, a metric on the parameter space of pure quantum states. For wave
functions ψ(q) in the position representation, the induced metric on function space has the form
proportional to ∫|∂_q ψ|² dq, which after integration by parts is proportional to the kinetic
energy expectation ⟨p²⟩/(2m). This suggests that the standard quadratic kinetic term is the one
that most faithfully represents the information metric D in configuration space.

None of these observations constitutes a derivation of the kinetic term from X. They suggest that
among the possible kinetic structures, the quadratic (Riemannian) form is selected by the information
geometry of I∞ as the "natural" one. Whether this can be made into a rigorous constraint is an open
problem (OPN-A, §9).

*[Epistemic status: CONJECTURED — Observations 1-3 support but do not establish the claim that L₃
selects the quadratic kinetic term. The argument has suggestive force; a fully rigorous version would
require showing that the only L₃-admissible kinetic terms compatible with the distinguishability
geometry are of the form g^{ij}p_ip_j/2m for some Riemannian metric g.]*

### 6.4 Feynman's Path Integral in Configuration Space

The Feynman path integral in configuration space

$$\langle q_f, t_f | q_i, t_i\rangle = \int \mathcal{D}[q]\,e^{iS_{cl}[q]/\hbar}$$

follows from the time-slicing construction: divide [t_i, t_f] into N intervals, insert a complete set
of position eigenstates at each intermediate time, evaluate the resulting matrix elements using the
kernel of e^{-iHdt/ℏ}, and take the continuum limit. Given H, this is a standard construction.

The LRT reading of the Feynman path integral (§5.7.2 of 002) carries over with the representation
specified: the paths are now trajectories in configuration space Q (a subspace of I∞ specified by the
representation choice), the action weighting e^{iS_cl/ℏ} implements the PLD in configuration-space
language, and A selects definite outcomes from the resulting amplitudes.

The path space in configuration space is not all of I∞ — it is the subset of I∞ parameterized by
position configurations in the chosen representation. The full I∞ contains all possible
representations simultaneously; a specific path integral fixes one. This is consistent: I∞ is not
a configuration space but the space of all distinguishable configurations, of which position-space
histories are one coordinatization.

-----

## 7. The QFT Bridge: Fock Space from A

*[This section is speculative. All claims are marked CONJECTURED or OPEN unless noted.]*

### 7.1 Motivation: From Particle Mechanics to Fields

The reconstruction in 002 targets non-relativistic quantum mechanics: a fixed, finite-dimensional
(or separable infinite-dimensional) Hilbert space ℋ with a fixed particle number. Quantum field
theory (QFT) requires extending this to variable particle number, Lorentz covariance, and locality
constraints. The question this section addresses is not whether LRT derives the Standard Model — it
does not, and cannot without additional physical input — but whether the structural extension from
quantum mechanics to QFT is natural within LRT's ontological framework.

The answer, we argue, is that the extension is natural in outline, with specific content requiring
additional input beyond X.

### 7.2 I∞ as Field Configuration Space

In QFT, the path integral sums over field configurations φ(x,t) rather than particle trajectories
q(t). A field configuration is a function from spacetime (or space, in the Hamiltonian formulation)
to field values. The path integral is:

$$Z = \int \mathcal{D}[\phi]\,e^{iS[\phi]/\hbar}$$

where S[φ] = ∫d⁴x L(φ, ∂_μφ) is the field action.

Within LRT's ontology, field configurations are elements of I∞: they are configurations that are
admissible under L₃ and equipped with distinguishability structure D. The extension from particle
mechanics to field theory is, from I∞'s perspective, an extension of the domain of configurations
being summed over — from finite-dimensional trajectories q(t) to infinite-dimensional field
histories φ(x,t). I∞ already contains all L₃-admissible configurations; field configurations are
simply a larger class of elements in I∞ than particle trajectories.

*[Epistemic status: CONJECTURED — the structural claim (field configurations are elements of I∞) is
natural given I∞'s definition as the totality of all L₃-admissible configurations. But the move from
"I∞ contains field configurations" to "the QFT path integral is the restriction of the LRT path
integral to field configurations" requires identifying the appropriate kinematic structure on I∞ for
field configurations, which is not established by the current reconstruction.]*

### 7.3 Variable Particle Number and the Actualization Primitive A

The most structurally interesting aspect of the QFT extension is variable particle number. In
quantum mechanics, ℋ has a fixed particle number n; particle creation and annihilation require the
Fock space:

$$\mathcal{F}(\mathcal{H}_1) = \mathbb{C} \oplus \mathcal{H}_1 \oplus (\mathcal{H}_1 \otimes_s \mathcal{H}_1) \oplus \cdots$$

where ℋ_1 is the single-particle Hilbert space and ⊗_s denotes the appropriate symmetric or
antisymmetric tensor product (for bosons or fermions respectively).

In LRT terms, the existence of a Fock structure is naturally accounted for by A's binary character.
The actualization primitive A selects which configurations in I∞ obtain. In the fixed-particle-number
case, A selects from configurations in a fixed-n sector of I∞. In the variable-particle-number case,
A selects from configurations across all sectors — it can actualize a zero-particle configuration (the
vacuum), a one-particle configuration, a two-particle configuration, and so on.

This maps naturally:

$$I_\infty \;\supset\; \bigsqcup_{n=0}^\infty I_\infty^{(n)}$$

where $I_\infty^{(n)}$ is the n-particle sector of I∞. The Fock space is the Hilbert space
corresponding to this direct-sum structure:

$$\mathcal{F} \;\leftrightarrow\; \bigoplus_{n=0}^\infty \mathcal{H}^{(n)}$$

The actualization primitive A operating on $I_\infty^{(n)}$ for varying n is the ontological
correlate of creation and annihilation operators. A actualizes an (n+1)-particle configuration from
an n-particle state by selecting a configuration in $I_\infty^{(n+1)}$; it de-actualizes a particle
by selecting from $I_\infty^{(n-1)}$.

*[Epistemic status: CONJECTURED — the mapping is structurally natural. The claim is that the Fock
space direct-sum structure is what I∞'s sector decomposition plus A's variable actualization looks
like in the Hilbert space representation. The specific statistics (Bose-Einstein vs. Fermi-Dirac) and
the specific single-particle space ℋ_1 are not derivable from this argument alone.]*

### 7.4 What LRT Constrains Without Additional Input

Even at the CONJECTURED level, the structural argument identifies what LRT can and cannot constrain
in the QFT extension:

**What LRT constrains:**

1. *The existence of a sector decomposition.* If I∞ decomposes into sectors by some conserved
   quantity Q (e.g., particle number), the Fock structure follows. LRT does not derive the specific
   Q, but it is consistent with a sector decomposition whenever the physical system has one.

2. *The binary character of actualization.* A is binary (actual/non-actual). This forces outcomes to
   be definite at the actualization event, which in QFT corresponds to a definite particle number
   being observed (even if the underlying state is a superposition of Fock sectors). The measurement
   problem for QFT has the same LRT resolution as for quantum mechanics: definite outcomes are not
   mysterious given A.

3. *The information geometry of state space.* The Fubini-Study metric D = d_FS extends to Fock
   space: the statistical distance between Fock states is still given by Wootters' formula, now with
   inner products computed in ℱ. The PLD extends to Fock space with the same action formula, now
   with H replaced by the QFT Hamiltonian.

**What LRT does not constrain without additional input:**

1. *The vacuum state.* The Fock vacuum |0⟩ requires specification. LRT does not derive the vacuum
   structure from X; it is an empirical input characterizing the ground state of a specific QFT.

2. *Normal ordering and renormalization.* The ultraviolet divergences of QFT, their regulation, and
   the renormalization group structure are not accessible from X alone. These are features of the
   specific dynamics of QFT, not of the abstract logical-informational-dynamic ontology.

3. *Specific interactions.* The Standard Model Lagrangian, its gauge symmetries, coupling constants,
   and particle content are empirical facts. LRT no more derives the Yukawa coupling than it derives
   the mass of the electron.

4. *Lorentz covariance.* The reconstruction in 002 is non-relativistic. Extending to a
   Lorentz-covariant formulation requires that the causal structure of I∞ be compatible with the
   Lorentz group. Whether L₃ constraints on the ordering structure of actualization events enforce
   Lorentz covariance is a separate, open question (OPN-D, §9).

*[Epistemic status: CONJECTURED for the mapping; OPEN for the derivation of specific QFT content.]*

### 7.5 The Statistics Question: Bosons and Fermions

The division of Fock space into symmetric and antisymmetric sectors corresponds to bosonic and
fermionic statistics. The spin-statistics theorem (in relativistic QFT) connects the statistics
to the spin: integer spin → Bose-Einstein, half-integer spin → Fermi-Dirac.

In LRT terms, the relevant question is: does L₃'s identity requirement constrain the symmetry of
multi-particle configurations in I∞?

The argument for a constraint is the following. L₃ requires that configurations have determinate
identity. For a two-particle system, the configuration (particle 1 at x, particle 2 at y) and the
configuration (particle 1 at y, particle 2 at x) are either the same configuration or different
configurations. If the particles are truly identical (a feature of the quantum formalism), then
swapping them yields no operationally distinguishable difference — D = 0 for the two swapped
configurations. L₃'s Identity requirement then forces them to be the same configuration. This implies
that multi-particle states must be either fully symmetric (D = 0 for any odd-permutation swap,
identifying all permuted configurations) or fully antisymmetric (D = 0 for even-permutation swaps).
Mixed symmetry would yield configurations that are partially identical, which violates Identity.

This is suggestive of the symmetrization postulate of quantum statistics, but it does not constitute
a derivation: the argument above establishes that configurations of identical particles must be
permutation-symmetric or permutation-antisymmetric, but it does not determine which particles are
symmetric (bosons) and which are antisymmetric (fermions) without the spin-statistics connection.

*[Epistemic status: CONJECTURED — the symmetrization argument is suggestive but not rigorous. The
full spin-statistics theorem requires relativistic QFT; LRT's non-relativistic reconstruction does
not reach it.]*

-----

## 8. Consistency Checks

### 8.1 Independence of the Two Derivation Routes

The Schrödinger equation is obtained in 002 via Stone's theorem (Steps 7-13, first route). It is
also obtained here via δS = 0 (second route). The two routes are independent by construction: the
first invokes continuous unitarity and G-equivariance; the second invokes D = d_FS and the Kibble
geometrization. Neither invokes the other. Their agreement is not a tautology.

The convergence constitutes a structural consistency check on LRT: two distinct aspects of X — the
binary actualization structure (via unitarity) and the information geometry of I∞ (via D = d_FS) —
independently yield the same dynamical equation. This is evidence that X has the right internal
coherence to support the full reconstruction.

### 8.2 The Classical Limit

In the ℏ → 0 limit, the PLD reduces to Hamilton's principle for the classical action. This is the
standard stationary-phase result. The LRT reading of the classical limit is: as ℏ → 0, the
information geometry of I∞ becomes irrelevant to the path selection (the geometric term ℏ∫A_FS → 0),
and actualization follows the path that minimizes the energy cost ∫⟨H⟩dt subject to fixed endpoints.
This is the classical trajectory. The classical limit of LRT is classical mechanics with a variational
action principle. *[Epistemic status: ESTABLISHED.]*

### 8.3 The Aharonov-Bohm Effect

The geometric term ℏ∫A_FS has a non-trivial consequence when the underlying space I∞ has non-trivial
topology. In the Aharonov-Bohm effect, a charged particle traversing a region where B = 0 (but
A ≠ 0) acquires a phase proportional to ∮A·dl. In LRT terms, this is the holonomy of the
actualization path through I∞ in the presence of a non-trivial electromagnetic potential. The
potential A (electromagnetic) is the representative, in configuration space, of the curvature of I∞
induced by the electromagnetic field. The Aharonov-Bohm phase is the geometric phase (§3.3) for a
loop in I∞.

This is not a new result but a consistency check: LRT's geometric action functional correctly
reproduces the electromagnetic phase structure as a geometric consequence of A_FS. *[Epistemic
status: ARGUED.]*

-----

## 9. Open Problems

The action principle derivation resolves several problems from 002's open list (OPN-001, OPN-007)
and establishes new questions of its own. This section enumerates the open problems with precise
scope statements.

### OPN-A: Kinetic Term from the Information Geometry of I∞

**Problem.** Can the quadratic kinetic term T = (m/2)q̇² in the configuration-space Lagrangian be
derived from the information geometry of I∞, rather than being imported as representational input?

**What is known.** §6.3 presents three observations suggesting that the quadratic form is the
"natural" kinetic structure compatible with D. The Fubini-Study metric induces a metric on
configuration space that, in the position representation, is proportional to the kinetic energy
expectation. This is suggestive.

**What is needed.** A rigorous argument that (a) the only L₃-admissible kinetic terms compatible
with the distinguishability geometry D are of the form g^{ij}p_ip_j/2m, and (b) the mass parameter
m can be read off from D or from the representation structure.

**Epistemic status: OPEN.** The suggestive evidence in §6.3 is not an argument. Whether the result
holds is unknown.

### OPN-B: Gauge Structure from L₃ Symmetry on I∞

**Problem.** Does L₃ symmetry enforcement on the configurations of I∞ constrain which gauge groups
are admissible? In particular, does the requirement that all configurations in I∞ satisfy L₃ restrict
the internal symmetry structure of admissible field configurations?

**Context.** Gauge symmetries in QFT are local symmetries of the Lagrangian density. They correspond
to redundancies in the field description — physically equivalent configurations related by a gauge
transformation. In LRT terms, physically equivalent configurations are the same element of I∞ (by
L₃'s Identity requirement). Gauge transformations are then equivalence relations on I∞, and the
gauge-invariant configurations are the orbits.

**Conjecture.** L₃'s requirement that physically distinct configurations be distinguishable (PPC)
may constrain the admissible gauge groups to those for which the orbit structure is consistent with
operational distinguishability. A gauge group that makes operationally distinct configurations
equivalent would violate the PPC and would not be L₃-admissible.

**Epistemic status: OPEN.** The conjecture is natural but has not been argued to LRT standards. The
connection between the PPC and gauge equivalence classes requires careful treatment of the
distinction between mathematical redundancy and physical indistinguishability.

### OPN-C: Relativistic Extension and Lorentz Covariance

**Problem.** Does the path integral formulation of LRT extend to a Lorentz-covariant form? Does the
causal ordering structure of actualization events in I∞ enforce Lorentz covariance, or is Lorentz
covariance an additional input?

**Context.** The reconstruction in 002 is non-relativistic. The Schrödinger equation is
non-relativistic. The action principle derived here is for the non-relativistic quantum action. The
relativistic generalization (Klein-Gordon, Dirac, QED) requires that the path integral be
Lorentz-invariant, which imposes constraints on the spacetime structure of I∞ that are not addressed
in the current reconstruction.

**What might be gained.** If the causal structure of I∞ — the ordering of actualization events under
A — is shown to be consistent with Lorentz covariance, that would be a significant structural result.
L₃'s Excluded Middle requirement (every actualization event is either actual or not) is a binary
structure that may or may not be compatible with all Lorentz frames having the same structure.

**Epistemic status: OPEN.** This is the central open problem for the relativistic extension of LRT.

### OPN-D: Specific Hamiltonians

**Problem.** LRT does not derive the Hamiltonian of any specific system. The Schrödinger equation is
reconstructed with H as a formal self-adjoint generator. The specific form — H = p²/2m + V(q) for
a particle in a potential, H = ℏωa†a for a harmonic oscillator, H_QED for quantum electrodynamics —
is an empirical input.

**Scope statement.** This is not an open problem in the sense that LRT needs to solve it — it is a
structural limitation that is intended. Particular Hamiltonians describe particular physical systems.
LRT derives the framework within which all such Hamiltonians operate; it does not claim to derive
the specific content of any particular one. The scope of LRT's reconstruction is the universal
framework, not its specific instantiations.

**What would change this.** A derivation of specific interaction terms from L₃ constraints on I∞
would be extraordinary but would require showing that L₃ selects specific interaction Lagrangians
from among all possible ones. Current understanding does not support this.

### OPN-E: Path Integral Measure in QFT

**Problem.** In the configuration-space path integral for QFT, the functional measure D[φ] requires
careful definition (regularization, discretization, or zeta-function regularization). The ultraviolet
divergences of QFT arise precisely from the definition of this measure. In LRT terms, the "sum over
all field configurations in I∞" requires a well-defined measure on the infinite-dimensional space of
field configurations.

**What LRT provides.** I∞ has a distinguishability structure D that, restricted to quantum states,
gives d_FS. For field configurations, the analogous structure would be a distance on field space.
Whether this distance can serve as the measure-determining structure for the path integral measure is
unknown.

**Epistemic status: OPEN.** The ultraviolet problem is not touched by the current reconstruction.

-----

## 10. Summary

The action principle in Logic Realism Theory is not an independent postulate added to the
reconstruction of quantum mechanics. It is a consequence of two structures already present in X's
primitive ontology: the information geometry of I∞ (which, by Wootters' theorem, is the Fubini-Study
geometry) and the self-adjoint Hamiltonian from Stone's theorem (which, by Kibble's geometrization,
generates Hamiltonian flow on ℂP(ℋ)).

The central result — the Principle of Least Distinguishability — states that δS = 0 is the
stationarity condition on the competition between the geometric potential accumulated through I∞
(proportional to the symplectic potential A_FS of the Fubini-Study structure) and the energy cost
of sustaining actualization (∫⟨H⟩dt). Both terms are grounded in X: the first in D = d_FS on I∞,
the second in the generator H from Stone's theorem. The principle is derived, not assumed.

The Anandan-Aharonov relation — energy uncertainty equals the rate of traversal through I∞ — is
proved as Theorem 2 from the Fubini-Study metric and the Schrödinger equation. It connects the
dynamical quantity ΔE to the geometric quantity v_D = ds_FS/dt, making the energy-action
relationship a theorem about the information geometry of I∞.

The configuration-space action requires representation-specific input (kinetic structure and potential
form) beyond what X provides. The form of this input is constrained by L₃ in the directions outlined
in §6.3, but whether those constraints suffice to derive the standard kinetic term is an open problem.

The QFT extension is natural in outline: field configurations are elements of I∞, variable particle
number corresponds to A operating across sectors of I∞, and the Fock structure corresponds to the
direct-sum decomposition of I∞ by particle number. The specific content of any QFT (vacuum, spectrum,
interactions, renormalization) requires additional input that X does not provide.

Five open problems are identified with precise scope: the kinetic term from D (OPN-A), gauge
structure from L₃ (OPN-B), Lorentz covariance (OPN-C), specific Hamiltonians (OPN-D), and the
path integral measure in QFT (OPN-E).

**Summary table:**

| Result | Epistemic Status | Basis |
|--------|-----------------|-------|
| D = d_FS on ℂP(ℋ) (Corollary 1) | ESTABLISHED (ARGUED via PPC) | Wootters (1981) + PPC |
| Kibble geometrization (Theorem 1) | ESTABLISHED | Kibble (1979) |
| Anandan-Aharonov relation (Theorem 2) | ESTABLISHED | Proof from d_FS + Schrödinger |
| Quantum action on ℂP(ℋ) | ESTABLISHED | D + Stone, OPN-007 resolved |
| Principle of Least Distinguishability | ARGUED | Geometric reading of δS=0 |
| Configuration-space action | ARGUED (scope limited) | Legendre transform + representation choice |
| L₃ constrains kinetic term | CONJECTURED | Observations 1-3 of §6.3 |
| Fock space from I∞ sectors + A | CONJECTURED | Structural mapping in §7.3 |
| QFT specific content from X | OPEN | Not derivable without additional input |
| Lorentz covariance from X | OPEN | Relativistic extension outstanding |

-----

## References

Anandan, J., & Aharonov, Y. (1990). Geometry of quantum evolution. *Physical Review Letters*,
65(14), 1697–1700. https://doi.org/10.1103/PhysRevLett.65.1697

Berry, M. V. (1984). Quantal phase factors accompanying adiabatic changes. *Proceedings of the
Royal Society A*, 392(1802), 45–57. https://doi.org/10.1098/rspa.1984.0023

Feynman, R. P., & Hibbs, A. R. (1965). *Quantum Mechanics and Path Integrals*. McGraw-Hill.

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics
and Mechanics*, 6(6), 885–893. https://doi.org/10.1512/iumj.1957.6.56050

Kibble, T. W. B. (1979). Geometrization of quantum mechanics. *Communications in Mathematical
Physics*, 65(2), 189–201. https://doi.org/10.1007/BF01225149

Longmire, J. D. (2026a). *Logic Realism Theory: Transcendental Realist Metaphysics*
(001-TRM-FOUNDATIONS). Zenodo. https://doi.org/10.5281/zenodo.19226396

Longmire, J. D. (2026b). *The Transcendental Argument for Being: Philosophical Foundations of LRT*
(002-LRT-TAB-PHILOSOPHY). Zenodo. https://doi.org/10.5281/zenodo.19226396

Longmire, J. D. (2026c). *Logic Realism Theory: Grounding Reality as Logical, Informational, and
Dynamic — Part II: Physics Reconstruction* (100-LRT-CORE-PHYSICS). Zenodo.
https://doi.org/10.5281/zenodo.19226396

Masanes, L., & Müller, M. P. (2011). A derivation of quantum theory from physical requirements.
*New Journal of Physics*, 13(6), 063001. https://doi.org/10.1088/1367-2630/13/6/063001

Renou, M.-O., Trillo, D., Weilenmann, M., Le, T. P., Tavakoli, A., Gisin, N., Acín, A., &
Navascués, M. (2021). Quantum theory based on real numbers can be experimentally falsified.
*Nature*, 600(7890), 625–629. https://doi.org/10.1038/s41586-021-04160-4

Stone, M. H. (1930). Linear transformations in Hilbert space: III. Operational methods and group
theory. *Proceedings of the National Academy of Sciences*, 16(2), 172–175.
https://doi.org/10.1073/pnas.16.2.172

Wootters, W. K. (1981). Statistical distance and Hilbert space. *Physical Review D*, 23(2), 357–362.
https://doi.org/10.1103/PhysRevD.23.357

-----

<!-- End of 200-LRT-ACTION-PRINCIPLE.md — April 2026 draft -->
