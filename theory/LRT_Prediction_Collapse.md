# Collapse Rate Constraints from Logic Realism Theory

**James D. Longmire**
ORCID: 0009-0009-1383-7698

---

## Abstract

We derive constraints on objective collapse rates from Logic Realism Theory's Global Parsimony principle. If objective collapse occurs, Global Parsimony requires that collapse parameters be derivable from existing physical structure rather than introduced as free parameters. Combined with dimensional analysis and gravitational self-energy considerations, this uniquely selects the Diósi-Penrose formula τ ~ ℏR/(Gm²) over phenomenological models like GRW. The key distinguishing prediction is that LRT's "logical actualization" preserves exact unitarity and energy conservation, unlike physical collapse models which predict anomalous heating. We identify experimental platforms capable of discriminating between these scenarios within the next decade.

---

## 1. Introduction

### 1.1 The Collapse Parameter Problem

Objective collapse models introduce modifications to quantum mechanics to explain definite measurement outcomes. The GRW model (Ghirardi et al. 1986) and its continuous variant CSL (Pearle 1989) introduce collapse parameters—a rate λ₀ and localization width a—that are adjusted phenomenologically to avoid observable violations while producing definite outcomes at macroscopic scales.

This parameter freedom raises a foundational question: Are collapse parameters fundamental constants of nature, or should they be derivable from more basic structure?

### 1.2 The LRT Approach

Logic Realism Theory (LRT) provides a principled answer through its Global Parsimony axiom: physical structure contains no surplus elements beyond what is required by logical consistency and initial conditions. Applied to collapse, this means:

1. If collapse occurs, its parameters must be functions of existing quantities
2. No new free parameters are permitted
3. The collapse rate must be derivable from available structure: mass m, size R, and fundamental constants G, ℏ

This paper develops the consequences of this constraint, showing that Global Parsimony uniquely selects the Diósi-Penrose form for collapse rates and makes specific, falsifiable predictions.

### 1.3 Scope and Structure

**Conditional nature of predictions:** LRT does not predict that objective collapse occurs. It predicts what collapse must look like if it exists:

> IF objective collapse exists (superposition lifetime bounded beyond environmental decoherence), THEN:
> - Collapse rate λ = α·Gm²/(ℏR), with α derivable from geometry
> - Energy strictly conserved (no anomalous heating)
> - Mass scaling λ ∝ m² (not λ ∝ m)
>
> IF no objective collapse exists (all apparent collapse is environmental decoherence), THEN:
> - LRT is consistent with standard quantum mechanics
> - Global Parsimony is satisfied (no collapse parameters needed)

The paper proceeds as follows: §2 reviews the Diósi-Penrose formula and existing collapse models; §3 develops the derivation from Global Parsimony; §4 presents predictions distinguishing LRT from other approaches; §5 discusses experimental tests; §6 assesses the current status and limitations.

---

## 2. Background: Collapse Models

### 2.1 The Diósi-Penrose Formula

Penrose (1996) and Diósi (1987) independently proposed that gravitational self-energy provides a natural collapse timescale. The heuristic derivation proceeds as follows:

**Step 1: Gravitational self-energy.** For a mass m in superposition of locations separated by Δx > R (characteristic size):
$$E_G \sim \frac{Gm^2}{R}$$

**Step 2: Energy-time uncertainty.** Quantum mechanics provides: ΔE · Δt ~ ℏ

**Step 3: Collapse timescale.** If the "energy cost" of maintaining superposition is E_G:
$$\tau \sim \frac{\hbar}{E_G} = \frac{\hbar R}{Gm^2}$$

The collapse rate is therefore:
$$\lambda = \frac{1}{\tau} \sim \frac{Gm^2}{\hbar R}$$

### 2.2 Numerical Estimates

| System | Mass | Size R | τ_collapse | Experimentally Accessible? |
|--------|------|--------|------------|---------------------------|
| Electron | 10⁻³⁰ kg | 10⁻¹⁵ m | ~10⁴⁵ s | No |
| C₆₀ molecule | 10⁻²⁴ kg | 10⁻⁹ m | ~10²⁷ s | No |
| Nanosphere (10⁶ amu) | 10⁻²¹ kg | 10⁻⁷ m | ~10¹⁵ s | No |
| Microparticle (10¹² amu) | 10⁻¹⁵ kg | 10⁻⁵ m | ~10³ s | Yes |
| Dust grain (10¹⁵ amu) | 10⁻¹² kg | 10⁻⁴ m | ~1 s | Yes |

*Values are order-of-magnitude estimates for uniform spheres following Diósi (1987) and Penrose (1996). See Bassi et al. (2013) Table I for refined estimates.*

### 2.3 Comparison with Phenomenological Models

| Model | Collapse Rate | Parameters | Derivable from Geometry? |
|-------|--------------|------------|-------------------------|
| GRW | λ ~ 10⁻¹⁶ s⁻¹ per nucleon | λ₀, a (localization width) | No (free parameters) |
| CSL | Similar to GRW | λ₀, r_c (correlation length) | No (free parameters) |
| Diósi-Penrose | λ ~ Gm²/(ℏR) | None beyond G, ℏ | Yes |

The key distinction: GRW/CSL parameters are adjusted to match phenomenological requirements, while Diósi-Penrose uses only fundamental constants.

---

## 3. Derivation from Global Parsimony

### 3.1 The Global Parsimony Constraint

Global Parsimony states that actuality contains exactly the structure required by logical consistency and initial conditions—no surplus elements exist. Applied to collapse:

1. If collapse occurs, it must be described by existing structure
2. "Existing structure" comprises {logical laws, geometry, fundamental constants}
3. No new free parameters are permitted
4. The collapse rate must be a function of available quantities

### 3.2 Available Quantities and Dimensional Analysis

For a localized mass m with characteristic size R, the available quantities are:

| Quantity | Symbol | Dimensions | Source |
|----------|--------|------------|--------|
| Mass | m | M | System property |
| Size | R | L | System property |
| Gravitational constant | G | L³ M⁻¹ T⁻² | Spacetime geometry |
| Planck constant | ℏ | L² M T⁻¹ | Quantum structure |
| Speed of light | c | L T⁻¹ | Spacetime structure |

The collapse rate λ has dimensions [T⁻¹]. From {G, m, R, ℏ}, the unique combination (excluding c) is:

$$\lambda = \alpha \frac{Gm^2}{\hbar R}$$

where α is a dimensionless coefficient. Dimensional analysis determines the form; the coefficient requires physical argument.

### 3.3 Why Gravitational Self-Energy is Unique

Consider a mass m in superposition |x₁⟩ + |x₂⟩. What provides the "energy cost" of this superposition?

**Excluded mechanisms:**
- Electromagnetic: neutral masses can superpose without EM cost
- Nuclear: irrelevant for spatial localization
- Kinetic: superposition of positions, not momenta

**The gravitational argument:** Each branch creates a gravitational field. The superposition creates "superposed geometry" with self-energy difference ΔE ~ Gm²/R between localized and delocalized configurations.

**Assumptions for gravity uniqueness:**

| Coupling | Why Excluded | Required Assumption |
|----------|-------------|---------------------|
| Electromagnetic | Charged objects have EM self-energy | Neutral test masses |
| Scalar fields | Would contribute additional self-energy | No universal scalar coupling to mass |
| Fifth force | Would modify scaling | Equivalence principle |

These are standard assumptions in collapse model literature (Bassi et al. 2013). Violations would constitute independently detectable new physics.

### 3.4 The Coefficient

Dimensional analysis gives λ = α·Gm²/(ℏR). What determines α?

Diósi (1987, equation 12) derived the collapse rate from the gravitational self-energy integral:
$$\lambda = \frac{G}{\hbar} \int \frac{[\rho(\mathbf{x}) - \rho'(\mathbf{x})][\rho(\mathbf{y}) - \rho'(\mathbf{y})]}{|\mathbf{x}-\mathbf{y}|} d^3x \, d^3y$$

For a uniform sphere, this evaluates to **α = 6/5**.

Different geometric configurations yield different order-unity coefficients:
- Uniform sphere: α = 6/5
- Other shapes (ellipsoids, rods): different α, all O(1)

The key constraint from Global Parsimony: the coefficient must be derivable from geometry. No arbitrary scaling is permitted.

### 3.5 The Methodological Distinction

LRT's claim concerns the logical status of physical structure, not new physics.

**The geometry analogy:** Euclidean geometry is not derived from logic alone (it requires the parallel postulate), but every theorem is logically derived from axioms. LRT has the same structure:

| Axioms (Inputs) | Theorems (Derived by Logic) |
|----------------|---------------------------|
| Three Laws of Logic | Distinguishability metric |
| Continuity | Inner product via Hardy kernel |
| Local tomography | Complex Hilbert space |
| Reversibility | Unitary dynamics, Born rule |
| Global Parsimony | No free parameters |
| Gravity exists | τ ~ ℏR/(Gm²) |

**Key distinction:**
- "Not derived from logic alone" → TRUE (requires physics inputs)
- "Every derived component IS derived from logic" → ALSO TRUE (every step is logical entailment)

| Aspect | Phenomenological (GRW/CSL) | Logical Derivation (LRT) |
|--------|---------------------------|-------------------------|
| Method | Fit parameters to avoid violations | Derive from constraints |
| Parameters | Free (adjusted empirically) | Determined by {G, ℏ, m, R} |
| Coefficient | Arbitrary scaling allowed | Must be O(1), geometry-dependent |

---

## 4. Predictions and Falsifiability

### 4.1 Distinguishing Predictions

| Prediction | LRT | GRW | Experimentally Distinguishable? |
|------------|-----|-----|--------------------------------|
| Mass scaling | λ ∝ m² | λ ∝ m (nucleon count) | Yes |
| Size dependence | λ ∝ 1/R | R-independent | Yes |
| Geometry dependence | Shape matters | No shape dependence | Yes |
| Absolute rate | Derivable from G, ℏ | Free parameter | Yes |

### 4.2 The Energy Conservation Signature

LRT's "logical actualization" differs fundamentally from physical collapse:

| Aspect | Physical Collapse (GRW/DP-as-collapse) | LRT (Logical Actualization) |
|--------|---------------------------------------|----------------------------|
| Process | Wavefunction physically modified | Category transition |
| Schrödinger equation | Modified (collapse terms added) | Exact (no modification) |
| Energy | Not conserved | Strictly conserved |

**Physical collapse models** predict anomalous heating of isolated systems because collapse violates unitarity. The heating rate scales as dE/dt ≈ N·λ·ℏ/τ where N is nucleon count.

**LRT** predicts no anomalous heating because actualization is a logical/ontological transition, not a physical process modifying the wavefunction.

### 4.3 Comprehensive Model Comparison

| Model | Free Parameters | Schrödinger Eq. | Energy | Mass Scaling | Heating |
|-------|-----------------|-----------------|--------|--------------|---------|
| Standard QM | None | Exact | Conserved | N/A | None |
| GRW/CSL | λ₀, r_c | Modified | Violated | λ ∝ m | Yes |
| DP (bare) | None | Exact* | Conserved* | λ ∝ m² | None* |
| DP (as collapse) | None | Modified | Violated | λ ∝ m² | Yes |
| LRT | None | Exact | Conserved | λ ∝ m² | No |

*Bare DP model is ambiguous on dynamics; DP interpreted as physical collapse modifies Schrödinger equation.

**The discriminant:** LRT uniquely predicts (1) DP timescale, (2) no heating, (3) no free parameters.

### 4.4 Falsification Conditions

**LRT is falsified if:**
1. Collapse rate scales as m (not m²)
2. Collapse rate is size-independent
3. Anomalous heating is observed
4. Different materials (same m, R) require different λ
5. Coefficient must be adjusted beyond geometric factors

**LRT is supported if:**
1. Collapse rate scales as m²
2. Collapse rate scales as 1/R
3. No anomalous heating detected
4. Shape-dependence follows self-energy integral predictions

### 4.5 The Critical Experimental Signature

| Observation | Interpretation |
|-------------|----------------|
| τ ∝ m⁻¹ + heating | GRW confirmed; LRT falsified |
| τ ∝ m⁻² + heating | DP-as-collapse confirmed; LRT falsified |
| τ ∝ m⁻² + no heating | LRT confirmed; physical collapse falsified |
| No superposition limit | Standard QM (no objective collapse) |

---

## 5. Experimental Tests

### 5.1 Near-term Experiments (2025-2030)

| Platform | Mass Range | What It Tests | LRT Prediction |
|----------|-----------|---------------|----------------|
| Levitated nanoparticles | 10⁶–10⁸ amu | Superposition lifetime | τ > 10⁶ s (decoherence-limited) |
| Anomalous heating searches | 10⁶–10⁹ amu | Energy conservation | No heating beyond known sources |
| Large-molecule interferometry | 10⁵–10⁶ amu | Visibility decay | Environmental decoherence dominates |

### 5.2 Medium-term Experiments (2030-2040)

| Platform | Mass Range | What It Tests | LRT Prediction |
|----------|-----------|---------------|----------------|
| MAQRO-type missions | 10⁹–10¹² amu | Absolute collapse timescale | Collapse visible if τ < mission duration |
| Ground-based microparticles | 10¹²–10¹⁵ amu | Macroscopic superposition | τ ~ 10³ s |

### 5.3 Decisive Experimental Platforms

| Platform | Tests m² Scaling? | Tests No-Heating? | Decisive for LRT? |
|----------|------------------|-------------------|-------------------|
| Optical levitation | Yes (vary m at fixed R) | Yes (temperature monitoring) | Yes |
| MAQRO | Yes (absolute timescale) | Limited | Partial |
| Needle Paul traps | Yes | Yes (sensitive heating) | Yes |
| Cryogenic cantilevers | Limited | Yes (sub-K bounds) | Partial |

**The critical test:** Measure collapse rate as function of mass at fixed R.
- LRT prediction: λ ∝ m² (factor of 10 in mass → 100× rate change)
- GRW prediction: λ ∝ m (factor of 10 in mass → 10× rate change)

This is experimentally distinguishable with current technology.

---

## 6. Discussion

### 6.1 Logical Status of Inputs

| Input | Status | Source |
|-------|--------|--------|
| Global Parsimony | Derived | LRT axiom |
| Three Laws of Logic | Foundational | Constitutive of distinguishability |
| Hilbert space structure | Derived | From logic (Technical paper §3) |
| Energy-time uncertainty | Derived | From Hilbert space |
| Gravity exists | Imported | Empirical physics |
| G, ℏ values | Imported | Measured constants |
| Equivalence principle | Imported | Standard physics |

The form of the collapse rate (λ ∝ Gm²/ℏR) follows from LRT plus imported physics. The claim that collapse must follow this form is LRT-specific: Global Parsimony forbids free parameters.

### 6.2 Current Status Assessment

| Component | Status | Notes |
|-----------|--------|-------|
| Parsimony constraint | Strong | Direct from LRT axioms |
| Dimensional form | Strong | Unique without free parameters |
| Physical interpretation | Moderate | Requires gravity as input |
| Exact coefficient | Moderate | Derivable from geometry (Diósi 1987) |
| QM uncertainty derivation | Moderate | Derivable from logic; chain needs explicit work |

### 6.3 Limitations

1. **Gravity as input:** The derivation requires that gravity exists. This is an empirical input, not derived from logic alone.

2. **Coefficient from Diósi:** The α = 6/5 coefficient comes from Diósi's integral, not from the full LRT derivation chain.

3. **Continuous vs. discrete:** LRT does not clearly distinguish continuous collapse (DP-style) from discrete hits (GRW-style).

4. **Dependence on standard QM:** The energy-time uncertainty relation is derivable from Hilbert space structure, which LRT derives from logic—but the explicit chain requires demonstration.

### 6.4 The Honest Claim

LRT's Global Parsimony constrains collapse mechanisms to have geometry-derivable parameters. Combined with gravity (universal coupling to mass) and quantum uncertainty (derivable from logical structure), this uniquely selects the Diósi-Penrose formula:

$$\lambda = \frac{6}{5} \frac{Gm^2}{\hbar R}$$

This is a conditional prediction: IF objective collapse occurs, THEN it must follow this form with no free parameters and no anomalous heating.

---

## 7. Conclusion

Global Parsimony provides a principled constraint on objective collapse: if collapse exists, its parameters must be derivable from existing structure rather than introduced as free parameters. This uniquely selects the Diósi-Penrose formula over phenomenological models like GRW.

The key distinguishing predictions are:
1. **Mass scaling:** λ ∝ m² (not λ ∝ m)
2. **Energy conservation:** No anomalous heating (exact unitarity preserved)
3. **No free parameters:** Rate determined by {G, ℏ, m, R} alone

These predictions are testable with existing and near-term experimental platforms. Observation of m² scaling with no anomalous heating would support LRT; observation of m scaling or anomalous heating would falsify it.

The methodological contribution is the demonstration that collapse rates can be constrained by logical principles rather than fitted phenomenologically—a distinction testable by experiment.

---

## References

- Bassi, A. et al. (2013). "Models of wave-function collapse." Rev. Mod. Phys. 85, 471.
- Diósi, L. (1987). "A universal master equation for the gravitational violation of quantum mechanics." Phys. Lett. A 120, 377.
- Ghirardi, G.C., Rimini, A., Weber, T. (1986). "Unified dynamics for microscopic and macroscopic systems." Phys. Rev. D 34, 470.
- Kaltenbaek, R. et al. (2016). "Macroscopic quantum resonators (MAQRO)." EPJ Quantum Tech. 3, 5.
- Millen, J. et al. (2020). "Optomechanics with levitated particles." Rep. Prog. Phys. 83, 026401.
- Pearle, P. (1989). "Combining stochastic dynamical state-vector reduction with spontaneous localization." Phys. Rev. A 39, 2277.
- Penrose, R. (1996). "On Gravity's Role in Quantum State Reduction." Gen. Rel. Grav. 28, 581.
- Vinante, A. et al. (2017). "Upper bounds on spontaneous wave-function collapse models." Phys. Rev. Lett. 119, 110401.
- Vinante, A. et al. (2020). "Narrowing the parameter space of collapse models." Phys. Rev. Lett. 125, 100404.
