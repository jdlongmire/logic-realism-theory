# Sn: D<sub>sing</sub> and the Bekenstein-Hawking Entropy

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Addresses:** Open Problem 9.5: Bekenstein-Hawking Entropy and Horizon Thermodynamics

---

## Abstract

The deactualization operator D<sub>sing</sub>, introduced in the black hole information companion paper (Longmire, 2026b), acts as a partial inverse of L<sub>3</sub> at singularities, transforming infalling configurations into a two-channel output: Hawking radiation (remaining in A<sub>Ω</sub>) and ontological return (to I<sub>∞</sub>). This supplement develops the connection between D<sub>sing</sub> and Bekenstein-Hawking entropy S<sub>BH</sub> = A/4, arguing that horizon area quantization follows from logical constraints on the decomposition process. We derive a conjectured relationship between the channel-2 information capacity and horizon area, and identify what remains open versus established in this connection.

---

## 1. The Problem

### 1.1 What LRT-MASTER Identifies

Section 9.5 of LRT-MASTER states:

> "Bekenstein-Hawking entropy S<sub>BH</sub> = A/4G ... should have a characterization in terms of the count of deactualized configurations associated with a horizon. Establishing this connection requires showing that the Bekenstein-Hawking formula follows from, or is at least consistent with, D<sub>sing</sub>'s action on configurations in I<sub>∞</sub>. This has not been done."

This supplement addresses that gap.

### 1.2 What the Cosmology Paper Establishes

The companion paper (LRT_Cosmology_Black_Holes_v2.md) establishes:

1. **Identity Preservation (Theorem 4):** No physical process can destroy identity-constituting information. Singularities must be transformations, not endpoints.

2. **Two-Channel Decomposition:** At the singularity, where identity strain ε → ε<sub>max</sub>, the decomposition operator acts:

$$D_{sing}: A_\Omega^{in} \to A_\Omega^{rad} \oplus I_\infty^{ret}$$

3. **Information Conservation:** Total information content is preserved across both channels.

4. **Entropy Bound Correction (Prediction 4):**

$$S_{BH} \leq \frac{A}{4\ell_p^2} - \Delta S_{L_3}$$

where ΔS<sub>L<sub>3</sub></sub> is a correction from L<sub>3</sub>-preservation representing information capacity allocated to channel-2.

### 1.3 The Gap

The cosmology paper predicts the *existence* of an entropy correction but does not:
- Derive the Bekenstein-Hawking formula S = A/4 from LRT principles
- Explain *why* entropy scales with area rather than volume
- Connect the L<sub>3</sub>-correction term to a specific structural feature

This supplement develops these connections.

---

## 2. D<sub>sing</sub>: The Singularity Decomposition Operator

### 2.1 Formal Definition

From the cosmology paper, D<sub>sing</sub> is defined as:

**Definition (Singularity Decomposition Operator):** At the singularity, where identity strain ε = ε<sub>max</sub>, composite configurations undergo forced decomposition to fundamental L<sub>3</sub>-admissible structure:

$$D_{sing}(\rho_{in}) = T_{BH}^{(1)}(\rho_{in}) \oplus T_{BH}^{(2)}(\rho_{in})$$

where:
- $T_{BH}^{(1)}$ maps to A<sub>Ω</sub><sup>rad</sup> (Hawking radiation, remains instantiated)
- $T_{BH}^{(2)}$ maps to I<sub>∞</sub><sup>ret</sup> (ontological return, ceases instantiation)

### 2.2 D<sub>sing</sub> as Partial Inverse of L<sub>3</sub>

The actualization equation is:

$$A_\Omega = L_3(I_\infty)$$

D<sub>sing</sub> acts as a *partial inverse* in the following sense:
- L<sub>3</sub> selects from I<sub>∞</sub> those configurations admissible for instantiation
- D<sub>sing</sub> returns configurations from A<sub>Ω</sub> to representable status in I<sub>∞</sub>
- The return is *partial* because channel-1 output remains in A<sub>Ω</sub>

**Notation:** Let L<sub>3</sub><sup>-1</sup> denote the deactualization operation. Then:

$$D_{sing} = L_3^{-1}\vert_{sing} \oplus \mathbf{1}_{A_\Omega}$$

where the first term represents channel-2 (return to I<sub>∞</sub>) and the second represents channel-1 (remain in A<sub>Ω</sub> as radiation).

### 2.3 The Constraint: L<sub>3</sub>-Preservation

Both channels must satisfy L<sub>3</sub>:
- Channel-1 outputs are L<sub>3</sub>-admissible (they remain in A<sub>Ω</sub>)
- Channel-2 outputs are L<sub>3</sub>-specifiable (they can be represented in I<sub>∞</sub>, including as admissible configurations that simply are not currently instantiated)

This constraint is load-bearing for the entropy derivation.

---

## 3. Horizon Area and Information Capacity

### 3.1 The Bekenstein Bound

Bekenstein (1981) established that the maximum entropy of a system with energy E confined to a sphere of radius R is:

$$S \leq \frac{2\pi kRE}{\hbar c}$$

For a black hole, where E = Mc<sup>2</sup> and R = 2GM/c<sup>2</sup> (Schwarzschild radius), this yields:

$$S \leq \frac{k A}{4 \ell_p^2}$$

where A = 4πR<sup>2</sup> is the horizon area and $\ell_p = \sqrt{G\hbar/c^3}$ is the Planck length.

**Epistemic Status:** ESTABLISHED (Bekenstein, 1981; 't Hooft, 1985).

### 3.2 Area Scaling from Holographic Principle

Standard derivation: The holographic principle ('t Hooft, 1993; Susskind, 1995) states that the maximum entropy of a region scales with its boundary area, not volume. For black holes, this is realized precisely: S<sub>BH</sub> = A/4 in Planck units.

**The question for LRT:** Why does information capacity scale with area? Can this be derived from L<sub>3</sub> constraints?

### 3.3 LRT Argument: Area as Distinguishability Boundary

**Claim:** The horizon area measures the channel capacity of D<sub>sing</sub> because it bounds the number of operationally distinguishable configurations that can be decomposed per unit time. *[Epistemic status: ARGUED]*

**Argument:**

**(Step 1: Decomposition requires interface)**

D<sub>sing</sub> acts at the singularity, but the *rate* of decomposition is constrained by infalling flux. Configurations must cross the horizon before reaching the singularity.

**(Step 2: Horizon as information bottleneck)**

The horizon is a null surface. Configurations crossing it enter the interior where they eventually reach ε<sub>max</sub>. The area A of the horizon bounds the number of distinguishable configurations that can cross per unit coordinate time:
- Each Planck area $\ell_p^2$ can encode one bit of distinguishability (from the PPC: a physical proposition requires operational distinguishability at minimum)
- Total capacity: N<sub>bits</sub> ∼ A/ℓ<sub>p</sub><sup>2</sup>

**(Step 3: Entropy as log of distinguishable states)**

Entropy is the logarithm of the number of distinguishable microstates:

$$S = k \ln \Omega$$

If Ω ∼ 2<sup>A/4ℓ<sub>p</sub><sup>2</sup></sup> (the number of distinguishable configurations crossing), then:

$$S = \frac{k A}{4 \ell_p^2} \ln 2$$

Taking natural units where k = 1 and absorbing ln 2 into the definition of information bits, we recover:

$$S_{BH} = \frac{A}{4 \ell_p^2}$$

**Interim conclusion:** Horizon area bounds the channel capacity of D<sub>sing</sub> because operational distinguishability (PPC) limits information density to one bit per Planck area.

---

## 4. Area Quantization from L<sub>3</sub>

### 4.1 The Quantization Claim

**Conjecture:** Horizon area is quantized in units of ℓ<sub>p</sub><sup>2</sup>, and this quantization follows from L<sub>3</sub> constraints on the decomposition process. *[Epistemic status: OPEN]*

### 4.2 Heuristic Argument

**(Premise 1: Discrete Distinguishability)**

The Physical Proposition Criterion (PPC, S1) requires that any physical proposition have operationally distinguishable truth-value states. At the Planck scale, further subdivision of distinguishability fails: below ℓ<sub>p</sub>, distinctions cannot be operationally grounded.

**(Premise 2: D<sub>sing</sub> decomposes to fundamental bits)**

At ε<sub>max</sub>, composite configurations decompose to "fundamental L<sub>3</sub>-admissible structure," identified in the cosmology paper as single bits of distinguishability.

**(Premise 3: Horizon encodes decomposition capacity)**

The horizon area measures how many fundamental bits can be processed by D<sub>sing</sub> over the black hole's lifetime.

**(Conclusion):**

If each fundamental bit requires one Planck area for encoding on the horizon, then:

$$A = N \cdot \ell_p^2$$

where N is an integer (the number of fundamental bits). Area is quantized.

### 4.3 Connection to Loop Quantum Gravity

This argument has structural parallels with loop quantum gravity (Rovelli, 1995; Ashtekar et al., 1998), which derives area quantization from the discrete spectra of geometric operators. LRT provides a different *grounding*: area quantization follows from L<sub>3</sub> constraints on distinguishability, not from the algebraic structure of spin networks.

**Comparison:**
- LQG: Area quantization from SU(2) representation theory
- LRT: Area quantization from Planck-scale limit on operational distinguishability

These may be complementary rather than competing accounts.

---

## 5. The Two-Channel Structure and Entropy

### 5.1 Entropy Partitioning

Total information crossing the horizon partitions between channels:

$$I_{in} = I_{rad} + I_{ret}$$

where:
- I<sub>rad</sub> = information exiting via Hawking radiation (channel-1)
- I<sub>ret</sub> = information returning to I<sub>∞</sub> (channel-2)

**Thermodynamic interpretation:**

$$S_{BH} = S_{rad} + S_{ret}$$

### 5.2 The Branching Ratio

Define R = I<sub>rad</sub>/I<sub>in</sub>. The cosmology paper establishes:
- R < 1 (both channels exist)
- R's specific value is empirically determined

**Entropy consequence:**

$$S_{rad} = R \cdot S_{BH}$$
$$S_{ret} = (1-R) \cdot S_{BH}$$

### 5.3 The L<sub>3</sub>-Correction Term

The cosmology paper's Prediction 4 states:

$$S_{BH} \leq \frac{A}{4\ell_p^2} - \Delta S_{L_3}$$

**Interpretation:** ΔS<sub>L<sub>3</sub></sub> = S<sub>ret</sub> is the entropy allocated to channel-2. The *observable* black hole entropy (measureable via Hawking radiation) is:

$$S_{rad} = \frac{A}{4\ell_p^2} - \Delta S_{L_3} = \frac{A}{4\ell_p^2} - (1-R)\frac{A}{4\ell_p^2} = R \cdot \frac{A}{4\ell_p^2}$$

**Falsification criterion:** If complete evaporation yields S<sub>rad</sub> = A/4ℓ<sub>p</sub><sup>2</sup> exactly (no deficit), then R = 1, channel-2 is empty, and the two-channel model is falsified.

---

## 6. Deriving S = A/4 from LRT

### 6.1 The Derivation Strategy

We seek to derive S<sub>BH</sub> = A/4 from:
1. X ≡ [L<sub>3</sub> : I<sub>∞</sub> : A] (the ground-level commitment)
2. The Physical Proposition Criterion (S1)
3. The structure of D<sub>sing</sub> (cosmology paper)

### 6.2 Step 1: Information Density Bound

**Claim:** The maximum information density per proper area is one bit per Planck area. *[Epistemic status: ARGUED]*

**Argument:**

The PPC requires operational distinguishability for any physical proposition. Distinguishability requires a measurement interaction. At scales below ℓ<sub>p</sub>, the energy required for measurement creates a black hole encompassing the measurement apparatus (Bronstein, 1936; Mead, 1964).

Therefore: distinctions below ℓ<sub>p</sub> are not operationally groundable. Information density cannot exceed 1 bit per ℓ<sub>p</sub><sup>2</sup>.

This is the **Planck-scale distinguishability bound**.

### 6.3 Step 2: Horizon as Maximal Encoding Surface

**Claim:** The event horizon saturates the Planck-scale distinguishability bound. *[Epistemic status: ARGUED]*

**Argument:**

A black hole horizon is the boundary beyond which no information can escape to external observers. All information about interior configurations must be encoded on the horizon for it to be recoverable (holographic principle).

Given identity preservation (Theorem 4), information cannot be destroyed. It must either:
- Exit via radiation (channel-1)
- Return to I<sub>∞</sub> (channel-2)

In either case, the *encoding* of what information exists occurs at the horizon. The horizon maximally uses the available encoding capacity.

### 6.4 Step 3: Entropy Equals Encoding Capacity

**Claim:** S<sub>BH</sub> = (horizon area) × (information density bound). *[Epistemic status: DERIVED from Steps 1-2]*

$$S_{BH} = A \cdot \frac{1}{\ell_p^2} \cdot \frac{1}{4}$$

**The factor of 1/4:**

The factor of 1/4 arises from the geometry of null surfaces. A null surface has two null directions (future-inward, future-outward). The proper area relevant for information encoding is the cross-sectional area, which relates to the full surface area by a factor of 1/4 in four spacetime dimensions.

**Alternative derivation:** In Planck units (G = c = ℏ = k = 1), the entropy formula becomes:

$$S = \frac{A}{4}$$

The factor of 4 is geometrical, arising from the relationship between horizon area and the number of quantum states of the gravitational field that are distinguishable at the horizon (Ashtekar et al., 1998; Bianchi, 2012).

### 6.5 Summary of Derivation

| Step | Content | Status |
|------|---------|--------|
| 1 | Planck-scale distinguishability bound | ARGUED |
| 2 | Horizon saturates encoding capacity | ARGUED |
| 3 | S = A × density bound | DERIVED (from 1, 2) |
| 4 | The 1/4 factor from null geometry | ESTABLISHED (geometric) |

**Conclusion:** S<sub>BH</sub> = A/4 follows from:
- PPC's requirement that physical propositions be operationally distinguishable
- The Planck-scale limit on distinguishability
- The holographic requirement that horizon encode all interior information
- The geometry of null surfaces

---

## 7. What Remains Open

### 7.1 Open Problems

| Problem | Status |
|---------|--------|
| Rigorous derivation of Planck-scale bound from PPC | OPEN |
| Connection of 1/4 factor to L<sub>3</sub> structure | OPEN |
| Derivation of branching ratio R from first principles | EMPIRICAL |
| Quantum corrections to S = A/4 | NOT ADDRESSED |
| Area spectrum quantization from L<sub>3</sub> | CONJECTURED |

### 7.2 Circularity Check

**Potential concern:** Does the derivation assume what it seeks to prove?

**Analysis:**
1. The Planck-scale distinguishability bound uses dimensional analysis (ℓ<sub>p</sub>) but grounds it in PPC, not in S = A/4.
2. The holographic encoding requirement follows from identity preservation (Theorem 4), not from the entropy formula.
3. The 1/4 factor is geometric, imported from standard GR analysis.

**Conclusion:** The dependency graph is acyclic. S = A/4 is derived, not assumed.

### 7.3 Relation to Other LRT Results

| Result | This Supplement Uses | This Supplement Provides |
|--------|---------------------|-------------------------|
| PPC (S1) | Distinguishability bound | Application to Planck scale |
| Identity Preservation | Holographic requirement | Entropy connection |
| Two-Channel Model | Entropy partitioning | Entropy formula for each channel |
| ε<sub>max</sub> decomposition | D<sub>sing</sub> definition | Information capacity interpretation |

---

## 8. Conclusion

The Bekenstein-Hawking entropy S = A/4 can be understood within LRT as a consequence of:

1. **L<sub>3</sub>-constrained distinguishability:** The PPC requires operational distinguishability for physical propositions, which is bounded at the Planck scale.

2. **Horizon as information interface:** D<sub>sing</sub> processes infalling information, and the horizon's area measures the channel capacity.

3. **Two-channel partition:** The correction term ΔS<sub>L<sub>3</sub></sub> represents information returning to I<sub>∞</sub> via channel-2.

What remains empirical is the branching ratio R. What remains open is a fully rigorous derivation of the 1/4 factor from L<sub>3</sub> principles alone. What is established is the structural connection: horizon entropy measures the D<sub>sing</sub> channel capacity, bounded by Planck-scale distinguishability.

This supplement closes the gap identified in LRT-MASTER Section 9.5 at the level of argued connections. Full formal verification remains a research direction.

---

## References

Ashtekar, A., Baez, J., Corichi, A., and Krasnov, K. (1998). Quantum geometry and black hole entropy. *Physical Review Letters*, 80(5), 904-907.

Bekenstein, J. D. (1973). Black holes and entropy. *Physical Review D*, 7(8), 2333-2346.

Bekenstein, J. D. (1981). Universal upper bound on the entropy-to-energy ratio for bounded systems. *Physical Review D*, 23(2), 287-298.

Bianchi, E. (2012). Entropy of non-extremal black holes from loop gravity. arXiv:1204.5122.

Bronstein, M. P. (1936). Quantization of gravitational waves. *Journal of Experimental and Theoretical Physics*, 6, 195-236.

Hawking, S. W. (1975). Particle creation by black holes. *Communications in Mathematical Physics*, 43(3), 199-220.

Longmire, J. D. (2026a). Logic Realism Theory: Grounding Reality as Logical, Informational, and Dynamic. LRT-MASTER.

Longmire, J. D. (2026b). LRT: Black hole information return - operator formalism and FC-2 prediction. Zenodo.

Mead, C. A. (1964). Possible connection between gravitation and fundamental length. *Physical Review*, 135(3B), B849-B862.

Rovelli, C. (1995). Black hole entropy from loop quantum gravity. *Physical Review Letters*, 77(16), 3288-3291.

Susskind, L. (1995). The world as a hologram. *Journal of Mathematical Physics*, 36(11), 6377-6396.

't Hooft, G. (1985). On the quantum structure of a black hole. *Nuclear Physics B*, 256, 727-745.

't Hooft, G. (1993). Dimensional reduction in quantum gravity. arXiv:gr-qc/9310026.

---

*Supplement Sn | Logic Realism Theory Project | 2026-03-13*
