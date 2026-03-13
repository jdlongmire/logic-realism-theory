# Admissibility Dynamics, Noether Charges, and the Λ Fixed Point

**A Translation Layer from LRT Information Circulation to Cosmological Dynamics**

**James (JD) Longmire**\
ORCID: 0009-0009-1383-7698\
Correspondence: jdlongmire@outlook.com

**Version 1.0 — February 2026**

---

## Abstract

This note provides a formal bridge between Logic Realism Theory (LRT) and standard cosmological dynamics. We show how the LRT framework—where physical evolution is constrained to admissible states—maps onto variational mechanics via Noether's theorem, and how the Information Circulation Hypothesis (ICH) maps onto interacting dark energy models. The central result: if information circulation dynamics drive toward a late-time attractor with constant energy density, the resulting equation of state approaches $w \approx -1$, reproducing $\Lambda$-like behavior.

This formalization assumes the existence of an admissibility filter $\mathsf{Adm}$ selecting physically instantiable states from the larger representable space $I_\infty$. The derivation of $\mathsf{Adm}$ from the LRT logical operator $L_3$ remains an open problem. This note operates downstream of that derivation, showing how standard physics would behave if such a filter exists.

**Keywords:** cosmological constant, dark energy, Noether theorem, admissibility, Logic Realism Theory, information circulation, equation of state

---

## 1. Definitions and Framework

Let $I_\infty$ denote the space of representable configurations (logical possibility space), and $A_\Omega \subseteq I_\infty$ the subset of physically instantiable states.

Define an admissibility predicate:

$$\mathsf{Adm}: I_\infty \rightarrow \{0,1\}, \qquad A_\Omega = \{x \in I_\infty : \mathsf{Adm}(x) = 1\}$$

Physical evolution is a flow restricted to admissible states:

$$\Phi_t: A_\Omega \rightarrow A_\Omega, \qquad \Phi_{t+s} = \Phi_t \circ \Phi_s$$

**Axiom L (Admissibility Preservation).** If $x \in A_\Omega$ then $\Phi_t(x) \in A_\Omega$ for all $t$.

This encodes the LRT claim that logical admissibility constrains physical evolution.

---

## 2. Admissibility Invariance and Noether Charges

Introduce an action on admissible histories:

$$S[x] = \int L(x, \dot{x}, t) \, dt$$

**Axiom T (Time Admissibility Invariance).** Admissible evolution is independent of the time origin:

$$\frac{\partial L}{\partial t} = 0$$

By Noether's theorem, time-translation invariance implies a conserved quantity:

$$H = \frac{\partial L}{\partial \dot{x}} \cdot \dot{x} - L$$

This Hamiltonian generates evolution:

$$\dot{x} = \{x, H\} \quad \text{(classical)} \qquad \text{or} \qquad i\hbar \partial_t \lvert\psi\rangle = \hat{H} \lvert\psi\rangle \quad \text{(quantum)}$$

**Interpretation.** Energy is the Noether charge associated with admissible time evolution. Logical admissibility supplies the invariance condition; physics registers the conserved scalar.

**Theorem Schema (Energy from Admissibility Invariance).** If admissible evolution is invariant under time translation, a conserved generator of evolution exists. This generator is energy.

This reframes energy as the invariant measure of logically permitted change.

---

## 3. Information Circulation and the Effective Action

The Information Circulation Hypothesis posits two fluxes:
- Instantiation influx $F_{\text{in}}$
- De-actualization outflux $F_{\text{out}}$

Define net circulation:

$$Q(t) = F_{\text{in}}(t) - F_{\text{out}}(t)$$

Treat the circulation sector as an effective cosmological component with density $\rho_{\text{ICH}}$ and pressure $p_{\text{ICH}}$:

$$\dot{\rho}_{\text{ICH}} + 3H(\rho_{\text{ICH}} + p_{\text{ICH}}) = Q(t)$$

This is the standard continuity equation for interacting dark-energy sectors.

**Key Proposition (Λ Fixed Point).** If feedback drives $\rho_{\text{ICH}}$ toward a late-time attractor $\rho_{\text{ICH}} \rightarrow \rho_* = \text{const}$, then:
1. The left-hand side of the continuity equation vanishes: $\dot{\rho}_* = 0$
2. With $Q(t) \rightarrow 0$ at late times, this requires $p_* \approx -\rho_*$
3. Therefore $w_* = p_*/\rho_* \approx -1$

This produces $\Lambda$-like behavior.

**Interpretation.** $\Lambda$ emerges as the stabilization term required to maintain bounded admissibility invariants under ongoing circulation.

In LRT language:

$$\Lambda = \text{ground-state enforcement of admissible reality}$$

**Note on premises.** The proposition requires that $Q(t) \rightarrow 0$ at late times. If $Q$ remains nonzero, $\rho$ can be constant only if $Q$ exactly balances the expansion dilution term $3H(\rho + p)$. This would correspond to a finely-tuned steady state rather than a natural attractor.

---

## 4. Physical Bridge: Logical Operations and Energetic Cost

Landauer's principle establishes that logical irreversibility carries thermodynamic cost. Erasing one bit dissipates at least:

$$k_B T \ln 2$$

This licenses a bidirectional explanatory link:

- **Forward direction (established):** Logical operations $\rightarrow$ energetic footprint
- **LRT extension:** Energetic structure $\rightarrow$ enforcement of logical admissibility

Energy becomes the persistence bookkeeping of admissible transformations.

---

## 5. Observational Mapping

The circulation framework predicts an effective dark-energy sector characterized by:
- Present-day density parameter $\Omega_{\text{ICH}}$
- Equation-of-state evolution $w(z)$
- Coupling term $Q(t)$

### 5.1 Minimal Observable Constraints

**(i) Type Ia Supernova Distance Modulus $\mu(z)$**

Constrains late-time expansion history and fixed-point behavior. Current constraints: $w = -1.03 \pm 0.03$ (Planck + BAO + SNe).

**(ii) Baryon Acoustic Oscillations (BAO)**

Provide geometric distances that bound deviations from constant $\Lambda$.

**(iii) CMB Distance Priors**

Anchor early-universe geometry and total energy budget.

**(iv) Structure and Black-Hole Demographics**

If outflux is sink-mediated, small deviations in $w(z)$ should correlate with large-scale entropy production and black-hole growth history.

### 5.2 Expected Deviation Magnitude

Current observational bounds constrain $\lvert w + 1 \rvert < 0.06$ at $2\sigma$. Detectable deviations require either:
- Next-generation surveys (DESI, Euclid, Roman) achieving sub-percent precision
- Correlated signatures linking $w(z)$ evolution to entropy production proxies

This distinguishes stabilization-based $\Lambda$ from a strictly constant vacuum parameter.

---

## 6. Programmatic Predictions

If $\Lambda$ is an admissibility fixed point rather than a primitive constant, the framework implies:

1. **$\Lambda$ behaves as a dynamical attractor** with small deviations from $w = -1$
2. **Deviations track global entropy sinks** and circulation imbalance
3. **Conservation laws correspond to admissibility invariants**
4. **Phase transitions in admissibility** appear as cosmological phase transitions

These are falsifiable.

---

## 7. Foundational Gap

This note assumes the admissibility filter $\mathsf{Adm}$.

**Core LRT claim:** $L_3 \Rightarrow \mathsf{Adm}$

That derivation remains open.

The present formalization therefore sits at the level:

$$\text{Logical admissibility} \rightarrow \text{Physical invariants} \rightarrow \text{Cosmological dynamics}$$

The missing step is:

$$\text{Logical operator } L_3 \rightarrow \text{Admissibility predicate } \mathsf{Adm}$$

More precisely: the derivation must show that $L_3$ generates *this specific* $\mathsf{Adm}$—one that produces time-translation invariance rather than some other symmetry class.

Closing that step would move the framework from translation layer to foundational derivation.

---

## 8. Summary

- Energy arises as the Noether charge of admissible time evolution
- Information circulation introduces a regulated source term in cosmological dynamics
- The late-time attractor of this system reproduces $\Lambda$ behavior (when $Q(t) \rightarrow 0$)
- $\Lambda$ can therefore be interpreted as the stabilization term required for persistent distinguishability of admissible states
- The decisive task is deriving the admissibility filter from $L_3$

**Concise statement:**

> Physics measures persistence.\
> Admissibility defines what may persist.\
> $\Lambda$ is the global cost of keeping admissible reality stable while it evolves.

---

## Acknowledgments

This note emerged from collaborative refinement with AI assistants (OpenAI GPT-4.5, Anthropic Claude). The translation from LRT concepts to cosmological formalism was developed through iterative dialogue. All theoretical claims, errors, and interpretive commitments are the author's responsibility.

---

## Citation

Longmire, J.D. (2026). Admissibility Dynamics, Noether Charges, and the Λ Fixed Point: A Translation Layer from LRT Information Circulation to Cosmological Dynamics. Working Paper.

---

**Status:** Conceptual formalization. Companion note to the Information Circulation Hypothesis paper.

**Last Updated:** 2026-02-24
