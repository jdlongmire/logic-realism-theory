# S10: Lorentz Covariance from L<sub>3</sub> Symmetry Structure

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Addresses:** Section 9.2 Open Problem (Relativistic Extension / Lorentz Covariance)

---

## Abstract

This supplement investigates whether Lorentz group structure can be derived from L<sub>3</sub> constraints on $I_\infty$. The central question: does the distinguishability structure of $A_\Omega$ under boost transformations constrain or determine the form of spacetime symmetries? We examine three candidate derivation strategies: (1) deriving Lorentz structure from homogeneity and isotropy of the distinguishability metric, (2) deriving it from causality constraints on distinguishability, and (3) deriving it from the automorphism group of $I_\infty$'s Boolean-metric structure. We find that LRT's framework constrains but does not uniquely determine Lorentz covariance: the structure of spacetime symmetries requires an additional physical input (the principle of relativity or equivalently, the invariance of the speed of information propagation). The supplement classifies the Lorentz covariance requirement as ARGUED given this input, and identifies what would be needed to elevate it to ESTABLISHED.

---

## 1. The Problem

### 1.1 What the Master Document States

Section 9.2 of LRT-MASTER identifies the relativistic extension as an open problem:

> "Whether the Lorentz group can be derived from X or must be specified as a physical input is an open question. The Poincaré group's structure – including the role of mass as a Casimir invariant – may have a natural home in the distinguishability structure of $I_\infty$, but this has not been developed."

The G-equivariance derivation in S7 establishes that time evolution must commute with whatever symmetry group $G$ the physical system has. But S7 explicitly notes that the *specific content* of $G$ is not derived from L<sub>3</sub>:

> "LRT does not derive that $G = U(\mathcal{H})$ from pure logic; it derives that whatever symmetry group $G$ the physical system has, time evolution must be equivariant with respect to $G$."

### 1.2 The Specific Question

Can LRT derive the Lorentz group $SO(3,1)$ (or its covering group $SL(2,\mathbb{C})$) as the symmetry group of $A_\Omega$ for relativistic systems, or must this be introduced as a physical axiom?

### 1.3 What Success Would Mean

**If derivable:** The Lorentz group emerges from L<sub>3</sub> constraints on distinguishability structure, without additional physical postulates. This would be a significant extension of LRT's derivation program.

**If not derivable:** Lorentz covariance must be introduced as a Tier 3 (physical principle) axiom, alongside other empirical inputs like specific Hamiltonians. This is not a failure – it correctly identifies the boundary between logical-informational structure and contingent physical law.

---

## 2. Strategy 1: Homogeneity and Isotropy

### 2.1 The Approach

The Lorentz group is the maximal group of transformations that preserves the Minkowski metric:

$$ds^2 = c^2 dt^2 - dx^2 - dy^2 - dz^2$$

One derivation strategy: show that L<sub>3</sub> constraints on $I_\infty$ require the distinguishability metric $D$ to be homogeneous (translation-invariant) and isotropic (rotation-invariant), then derive the Lorentz group from these requirements.

### 2.2 What L<sub>3</sub> Requires

**Claim 1 (Homogeneity):** The distinguishability metric $D$ must be translation-invariant.

**Argument:**
- By Identity, a configuration $c$ has the same identity regardless of where it is "located" in $I_\infty$.
- Location is not an intrinsic property of configurations; it is a relational property determined by distinguishability from other configurations.
- If $D$ varied with position (non-homogeneous), configurations at different positions would have different distinguishability structures, implying their identity depends on position.
- But L<sub>3</sub> requires identity to be intrinsic: $c = c$ regardless of context.
- Therefore, $D$ must be translation-invariant.

**Epistemic status:** ARGUED. The inference from "intrinsic identity" to "translation-invariance" requires that position is not itself an identity-determining property. This is plausible but not logically necessary.

**Claim 2 (Isotropy):** The distinguishability metric $D$ must be rotation-invariant.

**Argument:**
- By the same reasoning: if $D$ varied with direction (anisotropic), configurations would have direction-dependent identities.
- But there is no privileged direction in $I_\infty$ absent external structure.
- Therefore, $D$ must be isotropic.

**Epistemic status:** ARGUED. The claim "no privileged direction in $I_\infty$" is a physical assertion about the structure of the configuration space.

### 2.3 The Gap

Homogeneity + isotropy implies the symmetry group includes $\mathbb{R}^3$ (translations) and $SO(3)$ (rotations). This gives the Euclidean group $E(3)$, not the Lorentz group.

To get Lorentz structure, we need an additional constraint relating space and time transformations. The Lorentz group emerges when:

1. Space and time translations form a connected structure (not separately invariant)
2. There exists a finite invariant speed $c$

Neither of these follows from homogeneity and isotropy alone.

**Verdict:** Strategy 1 constrains the symmetry group to include $E(3)$ but does not derive Lorentz structure.

---

## 3. Strategy 2: Causality Constraints

### 3.1 The Approach

The Lorentz group is uniquely characterized by causality preservation: it is the group of linear transformations that maps the light cone to itself, preserving the causal order of events.

Strategy: derive causality constraints from L<sub>3</sub>, then show these constraints determine Lorentz structure.

### 3.2 Distinguishability and Causal Structure

**Claim 3 (Causal Ordering from Distinguishability):** Configurations in $A_\Omega$ are ordered by a causal relation: $c_1 \preceq c_2$ iff $c_2$ can be reached from $c_1$ by a physically admissible evolution.

**Argument:**
- By UNS (Step 8), each configuration has a unique successor under time evolution.
- The successor relation generates a partial order on $A_\Omega$.
- This partial order is the causal structure: $c_1$ causally precedes $c_2$ iff there is a chain of successor relations from $c_1$ to $c_2$.

**Epistemic status:** ESTABLISHED (follows from UNS and transitivity).

**Claim 4 (Causal Preservation by Symmetries):** Any symmetry $g \in G$ must preserve the causal order: if $c_1 \preceq c_2$, then $g(c_1) \preceq g(c_2)$.

**Argument:**
- Causal order is part of the distinguishability structure: causally related configurations have $D > 0$ (they are distinct and connected by evolution).
- Symmetries preserve distinguishability (definition of $G$).
- Therefore, symmetries preserve causal connectedness.
- Causal order (the direction from past to future) is preserved if the symmetry commutes with time evolution (G-equivariance from S7).

**Epistemic status:** ARGUED. The identification of causal order with distinguishability structure requires that "causally connected" is operationally definable.

### 3.3 The Causality-to-Lorentz Inference

**Known result (Alexandrov, 1967; Zeeman, 1964):** The group of bijections of Minkowski space that preserve the causal order is the Poincaré group (Lorentz transformations plus translations) up to scaling.

**Application:** If $A_\Omega$ has the causal structure of Minkowski space, and $G$ preserves causal order, then $G$ is (isomorphic to a subgroup of) the Poincaré group.

### 3.4 The Gap

The inference requires:

1. **That $A_\Omega$ has Minkowski causal structure** – a 4-dimensional spacetime with light-cone causality.
2. **That causality is determined by a finite maximal signal speed** – the existence of $c$.

Neither of these is derived from L<sub>3</sub>. They are physical facts about the world we inhabit.

**Claim 5 (Finite Signal Speed from Distinguishability):** The distinguishability metric imposes a finite maximal speed of information propagation.

**Attempted argument:**
- For two configurations $c_1$ and $c_2$ to be distinguishable, there must be a measurement protocol that distinguishes them.
- Measurements require physical interactions, which propagate at finite speed.
- Therefore, distinguishability between spacelike-separated configurations requires a finite interaction time.
- This suggests a finite maximal speed $c$.

**Analysis:** This argument is suggestive but circular: it assumes "spacelike-separated" which presupposes Lorentz structure. The concept of "finite speed" requires a metric relating space and time, which is what we're trying to derive.

**Verdict:** Strategy 2 shows that *given* Minkowski causal structure, the symmetry group is constrained to the Poincaré group. But the Minkowski structure itself is not derived from L<sub>3</sub>.

---

## 4. Strategy 3: Automorphism Group of Boolean-Metric Structure

### 4.1 The Approach

$A_\Omega$ carries two structures:
1. **Boolean structure:** From the projection-valued measures (Step 5), events form a Boolean algebra.
2. **Metric structure:** The distinguishability metric $D$ on states.

Strategy: determine the automorphism group of this combined structure and check whether it is the Lorentz group.

### 4.2 What the Boolean-Metric Structure Determines

**Theorem (Wigner, extended):** The automorphisms of the Boolean algebra of projection operators on a Hilbert space, combined with preservation of the transition probability metric, are unitary or anti-unitary transformations.

This gives $G = U(\mathcal{H}) \cup \overline{U}(\mathcal{H})$ (unitaries and anti-unitaries).

**For relativistic systems:** The Hilbert space carries a representation of the Poincaré group. The question is whether the Poincaré structure is determined by the Boolean-metric structure alone.

### 4.3 The Representation Theory Perspective

**Wigner's classification (1939):** Irreducible unitary representations of the Poincaré group are classified by mass $m$ and spin $s$ (the Casimir invariants).

**Observation:** The Poincaré group acts on the Hilbert space via a unitary representation. But the *existence* of the Poincaré group as a symmetry is not determined by the Hilbert space structure alone – many groups can act unitarily on a given Hilbert space.

### 4.4 The Gap

The Boolean-metric structure determines:
- That symmetries are unitary (or anti-unitary)
- That time evolution is strongly continuous and unitary

It does not determine:
- The specific group that acts (Poincaré vs. Galilean vs. other)
- The dimensionality of spacetime
- The signature of the spacetime metric

**Verdict:** Strategy 3 gives the unitary structure of symmetries but does not single out the Lorentz group.

---

## 5. What Would Be Needed for Derivation

### 5.1 The Missing Ingredient

All three strategies converge on the same gap: L<sub>3</sub> constraints determine that symmetries must:
- Preserve distinguishability (from DI)
- Preserve causal order (from UNS)
- Be unitary/anti-unitary (from Wigner's theorem)

But they do not determine the *specific* group that satisfies these constraints. The Lorentz group is one possibility; the Galilean group is another; higher-dimensional generalizations are others.

### 5.2 The Physical Input Required

To select the Lorentz group, one of the following physical inputs is needed:

**Option A (Principle of Relativity):** The laws of physics are the same in all inertial frames. Combined with homogeneity and isotropy, this determines the Lorentz group (up to the value of $c$).

**Option B (Finite Maximal Speed):** There exists a finite invariant speed $c$. Combined with homogeneity and isotropy, this determines the Lorentz group (with $c$ as parameter).

**Option C (Causality Structure):** Spacelike-separated regions are causally independent. Combined with 4-dimensional spacetime, this determines Minkowski structure.

Each of these is an empirical statement about the physical world, not derivable from logic alone.

### 5.3 LRT's Honest Position

**Claim (Lorentz Covariance Classification):** Within LRT, Lorentz covariance is a **Tier 3 physical principle**, not a Tier 1 logical consequence.

**Argument:**
- Tier 1 (structural assumptions): I, $I_\infty$ – derivable from L<sub>3</sub>
- Tier 2 (established mathematics): Stone, Gleason, Masanes-Müller – standard theorems
- Tier 3 (physical principles): Conservation laws, the principle of relativity, the value of $c$

Lorentz covariance belongs to Tier 3: it is a physical symmetry principle that constrains which configurations are actualizable, not a logical consequence of L<sub>3</sub>.

---

## 6. The Positive Result

### 6.1 What LRT Does Derive

Although LRT does not derive Lorentz covariance, it provides a framework for incorporating it:

**Result 1 (Equivariance Constraint):** Given that $G$ includes Lorentz transformations (physical input), time evolution must be Lorentz-equivariant (S7).

**Result 2 (Unitary Representation):** The Lorentz group acts on $A_\Omega$ via unitary (or projective unitary) representations (from DI-preservation and Wigner's theorem).

**Result 3 (Distinguishability Preservation):** Lorentz transformations preserve the distinguishability metric $D$: two states that are distinguishable in one frame are distinguishable in all frames.

### 6.2 The Consistency Requirement

LRT imposes a consistency constraint on Lorentz covariance:

**Constraint:** If Lorentz transformations are symmetries of $A_\Omega$, they must:
1. Preserve the Boolean algebra of projections (PVM structure)
2. Preserve the distinguishability metric $D$
3. Commute with time evolution operators
4. Form a group that acts unitarily on $\mathcal{H}$

These constraints are automatically satisfied by the standard Lorentz group action on quantum states, confirming that Lorentz covariance is *consistent* with LRT even though it is not *derived* from LRT.

### 6.3 The Invariance of Distinguishability Under Boosts

**Claim 6 (Boost-Invariance of $D$):** The distinguishability metric $D(s_1, s_2)$ is invariant under Lorentz boosts.

**Argument:**
- Distinguishability is defined operationally: $D(s_1, s_2) = \sup_M \lvert P_M(s_1) - P_M(s_2) \rvert_{TV}$.
- The supremum is over all physically admissible measurements.
- In a boosted frame, the same states $s_1, s_2$ are described by boosted state vectors, and the same measurement $M$ is described by a boosted operator.
- By the unitarity of Lorentz transformations: $P_{L(M)}(L(s)) = P_M(s)$ for any Lorentz transformation $L$.
- Therefore, the supremum over measurements is frame-independent.
- Hence $D$ is Lorentz-invariant.

**Epistemic status:** ESTABLISHED (given that Lorentz transformations are unitary).

This result confirms that L<sub>3</sub>'s identity constraints (via $D$) are compatible with Lorentz covariance: identity is absolute, not frame-dependent.

---

## 7. Comparison with Historical Derivations

### 7.1 Einstein's 1905 Derivation

Einstein derived the Lorentz transformations from:
1. The principle of relativity (laws are the same in all inertial frames)
2. The constancy of the speed of light

LRT cannot reproduce this derivation because (1) and (2) are physical postulates, not logical necessities.

### 7.2 Ignatowski's 1910 Derivation

Ignatowski showed that the Lorentz transformations follow from:
1. Homogeneity of space and time
2. Isotropy of space
3. Principle of relativity
4. Group structure of inertial transformations

This eliminates the need for light's constancy as an independent postulate. But (3) remains a physical input.

### 7.3 LRT's Position

LRT can derive (1), (2), and (4) from L<sub>3</sub> constraints (homogeneity and isotropy from intrinsic identity; group structure from composition of symmetries). But (3) – the principle of relativity – cannot be derived.

**The principle of relativity** states that no inertial frame is privileged. This is an assertion about the physical world, not about logical structure. A universe with a preferred frame (Lorentz ether theory) is logically coherent even if empirically falsified.

---

## 8. Open Questions

### 8.1 Can the Principle of Relativity Be Grounded?

**Question:** Is there an argument from L<sub>3</sub> or $I_\infty$ structure that privileges the principle of relativity over frame-privileged alternatives?

**Possible approach:** If a privileged frame introduces distinguishability without operational signature (the frame is "real" but undetectable), this violates the PPC. Therefore, detectable privileged frames are required if any exist, and their non-detection supports relativity.

**Analysis:** This argument establishes compatibility with relativity, not derivation of it. The non-existence of a privileged frame is an empirical fact, not a logical necessity.

### 8.2 Can Spacetime Dimensionality Be Derived?

**Question:** Does L<sub>3</sub> constrain the dimensionality of spacetime?

**Observation:** The Masanes-Müller reconstruction gives complex Hilbert spaces in any dimension. The 3+1 dimensionality of spacetime is not derived.

**Possible direction:** Some have argued (Tegmark, 1997) that 3+1 is the unique dimensionality supporting stable atoms and complex structures. If so, 3+1 might follow from the requirement that $A_\Omega$ support complex distinguishable structures. This is speculative.

### 8.3 Quantum Gravity Implications

**Question:** Does the L<sub>3</sub>/distinguishability framework constrain approaches to quantum gravity?

**Observation:** Approaches that treat spacetime as emergent (e.g., causal sets, loop quantum gravity) may align well with LRT: spacetime structure emerges from more fundamental distinguishability relations. The Lorentz group would then be an effective symmetry, not fundamental.

This is a research direction, not a current result.

---

## 9. Formal Summary

### 9.1 Derivation Attempt: Results

| Strategy | What It Derives | What It Cannot Derive |
|----------|-----------------|----------------------|
| Homogeneity/Isotropy | Euclidean symmetry $E(3)$ | Space-time mixing; finite $c$ |
| Causality Constraints | Poincaré group *given* Minkowski structure | Minkowski structure itself |
| Boolean-Metric Automorphisms | Unitary/anti-unitary symmetries | Specific symmetry group |

### 9.2 Classification

**Lorentz Covariance Status:** OPEN → ARGUED (given physical input)

**Physical Input Required:** The principle of relativity, or equivalently, the existence of a finite invariant speed $c$.

**Tier Classification:** Tier 3 (physical principle, not logical consequence)

### 9.3 The Positive Contribution

LRT provides:
1. **Framework for incorporating Lorentz covariance:** G-equivariance + unitary action
2. **Consistency verification:** Lorentz transformations preserve $D$, PVMs, and DI
3. **Honest classification:** Distinguishing what is derived from what is assumed

---

## 10. Relation to Other Supplements

### 10.1 Dependency on S7

S10 presupposes the G-equivariance framework of S7. The question addressed here is the *content* of $G$ for relativistic systems, while S7 established the *requirement* of equivariance for whatever $G$ obtains.

### 10.2 Connection to LRT-MASTER Section 9

S10 directly addresses the Open Problem identified in Section 9.2. The conclusion – that Lorentz covariance is a Tier 3 physical principle – resolves the question posed in the master document.

### 10.3 Implications for Future Work

If quantum gravity research suggests that Lorentz symmetry is emergent (from causal structure or distinguishability relations at the Planck scale), S10's framework may need revision. Currently, Lorentz covariance is treated as exact; future supplements may address approximate or emergent Lorentz symmetry.

---

## 11. Epistemic Status Summary

**Previous status (LRT-MASTER):** OPEN (not addressed)

**Current status:** ARGUED (given Tier 3 physical input)

**Classification:**
- Lorentz covariance is *consistent with* L<sub>3</sub> constraints: ESTABLISHED
- Lorentz covariance is *required by* L<sub>3</sub> constraints: NOT ESTABLISHED
- Lorentz covariance as Tier 3 physical principle: ARGUED

**What would elevate to ESTABLISHED:**
- An argument deriving the principle of relativity from L<sub>3</sub> (not currently available)
- Alternatively: formal acceptance that Tier 3 principles are part of LRT's input structure (this is the current position)

---

## References

Alexandrov, A. D. (1967). A contribution to chronogeometry. *Canadian Journal of Mathematics*, 19, 1119-1128.

Einstein, A. (1905). Zur Elektrodynamik bewegter Körper. *Annalen der Physik*, 17, 891-921.

Ignatowski, W. (1910). Einige allgemeine Bemerkungen zum Relativitätsprinzip. *Physikalische Zeitschrift*, 11, 972-976.

Tegmark, M. (1997). On the dimensionality of spacetime. *Classical and Quantum Gravity*, 14, L69.

Wigner, E. P. (1939). On unitary representations of the inhomogeneous Lorentz group. *Annals of Mathematics*, 40, 149-204.

Zeeman, E. C. (1964). Causality implies the Lorentz group. *Journal of Mathematical Physics*, 5, 490-493.

---

*Supplement S10 | Logic Realism Theory Project | 2026-03-13*
