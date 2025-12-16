# ISSUE 013: Formalize the Logical Action Functional

**Status:** PARTIAL DERIVATION (v2 - reconstruction gap identified)
**Priority:** HIGH (core maturity gap)
**Phase:** 1 - Mathematical Rigor
**Created:** 2025-12-16
**Updated:** 2025-12-16 (Session 46.0 - external review identified reconstruction gap)
**Source:** Gap closure analysis (Session 44.0)

---

## 1. Summary

The theory defines Action conceptually as "change of distinctions" but lacks a rigorous conversion to the physical Lagrangian S = ∫ L dt.

**The Gap:** LRT claims logical action (bit flips, distinction changes) grounds physical action (Joule-seconds), but the mapping is interpretive, not derived.

**Success Metric:** Mathematically demonstrate that the logical "change cost" reduces to the standard Principle of Least Action for a free particle.

---

## 2. Current State

### 2.1 What LRT Claims

From the core paper (Sections 8-9):

- Action = measure of "change between states"
- Logical interpretation: counting distinguishability changes
- Parsimony selects minimum action paths
- Conservation laws emerge from action minimization

### 2.2 The Gap (Updated Session 46.0)

| Concept | Logical Definition | Physical Equivalent | Bridge Status |
|---------|-------------------|---------------------|---------------|
| Action | Σ(distinction changes) | S = ∫ L dt | **MAPPED** (phase space cells) |
| Lagrangian | Phase space rate | L = T - V | **DERIVED** (free particle) |
| Time | Sequential instantiation | Physical seconds | Interpretive |
| Energy | ℏ × (dD/dt) | Joules | **CONNECTED** (Mandelstam-Tamm) |
| Conversion | 1 Planck cell | ℏ | **ESTABLISHED** |

---

## 3. Technical Approach

### 3.1 Required Mappings

1. **Bit → Physical unit conversion**
   - One bit of distinguishability = ? Joule-seconds
   - Likely involves ℏ as conversion factor
   - Must be consistent with Planck scale arguments

2. **Logical time → Physical time**
   - Sequential instantiation steps → continuous time
   - Must recover dt as limit of discrete steps
   - Connect to Stone's theorem (continuous → discrete)

3. **Distinguishability metric → Kinetic energy**
   - D(s₁, s₂) already defined
   - Rate of change of D → velocity-like quantity
   - Must map to ½mv²

4. **Parsimony → Least Action**
   - Global Parsimony → δS = 0
   - Must derive Euler-Lagrange equations

### 3.2 Proposed Derivation Path

```
Logical Domain                Physical Domain
─────────────────────────────────────────────
Distinction count         →   Action S
Distinguishability D      →   Phase space distance
Sequential steps          →   Time interval dt
min(distinctions)         →   δS = 0
D(t+dt) - D(t)           →   dS/dt = L
```

---

## 4. Test Case: Free Particle

### 4.1 Physical Result to Recover

For a free particle:
- L = ½m(dx/dt)²
- S = ∫ ½m(dx/dt)² dt
- Euler-Lagrange: d²x/dt² = 0 (uniform motion)

### 4.2 LRT Derivation Required

Starting from:
- Abstract Information Space with distinguishability metric D
- Sequential instantiation (discrete time)
- Global Parsimony (minimize total distinguishability change)

Must derive:
- Continuous limit recovers S = ∫ L dt
- L has correct kinetic form
- Straight-line motion is minimum action path

---

## 5. Known Constraints

### 5.1 Dimensional Analysis

- Logical: bits (dimensionless)
- Physical: Joule-seconds
- Conversion must involve: ℏ (action quantum), possibly Planck units

### 5.2 Consistency Requirements

- Must reduce to known physics (Newtonian limit)
- Must be compatible with quantum mechanics (path integral)
- Cannot introduce new free parameters

---

## 6. Risks and Challenges

1. **Units problem** - how do dimensionless logical quantities become dimensional physical ones?

2. **Emergence of mass** - where does m come from in ½mv²?

3. **Potential energy** - V in L = T - V has no obvious logical correlate

4. **Lorentz invariance** - relativistic action must also emerge

---

## 7. Path Forward

### 7.1 Immediate Actions

- [x] Review literature: discrete → continuous action limits
- [x] Formalize "distinction change" as measurable quantity
- [x] Propose explicit ℏ-based conversion factor
- [x] Attempt free particle derivation

**See:** `theory/derivations/Issue_013_Logical_Action_Functional.md`

### 7.2 Success Criteria

| Level | Criterion | Maturity | Status |
|-------|-----------|----------|--------|
| Minimal | Qualitative mapping with correct structure | Framework | **ACHIEVED** |
| Moderate | Free particle S derived from D | Model | **ACHIEVED** |
| Strong | General Lagrangian derived from logical action | Theory | OPEN |

### 7.3 Remaining Gaps

| Gap | Description | Priority |
|-----|-------------|----------|
| Potential energy V(x) | Where does V come from logically? | HIGH |
| Mass m | What determines particle mass? | MEDIUM |
| Relativistic action | Lorentz-invariant generalization | MEDIUM |
| Field theory | S = ∫ ℒ d⁴x extension | LOW |

---

## 8. Dependencies

- Requires: Distinguishability metric (Section 10 of core paper)
- Relates to: Issue_012 (First Constants - ℏ role)
- Relates to: Issue_014 (Dimensional Optimality - spacetime structure)

---

## 9. References

- `theory/2025-12-16_logic_realism_theory_foundation.md` Sections 8-9
- Feynman path integral formulation
- Discrete mechanics literature (Marsden, West)

---

## 10. Status Log

| Date | Update |
|------|--------|
| 2025-12-16 | Issue created from gap closure analysis |
| 2025-12-16 | Session 46.0: Framework established. Free particle derived. See `theory/derivations/Issue_013_Logical_Action_Functional.md` |

---

## 11. Session 46.0 Summary

### Key Results

1. **Dimensional Bridge Established:**
   - 1 Planck cell (area ℏ in phase space) = 1 bit of distinguishability
   - S_physical = ℏ × S_logical

2. **Free Particle Derived:**
   - S_logical = (1/ℏ) ∫ p dx (phase space area in Planck cells)
   - Legendre transform → L = pv - H = ½mv²
   - δS = 0 → uniform motion

3. **Derivation Chain:**
   ```
   3FLL → Distinguishability D → Planck scale (δx·δp = ℏ)
       → Phase space structure → S = ∫ p dx
       → Legendre transform → S = ∫ L dt
       → Global Parsimony → δS = 0
   ```

### Honest Assessment

| Strength | Limitation |
|----------|------------|
| Consistent mapping exists | Uses QM structure (Planck cell) |
| Correct physical result | Not fully derived from pure logic |
| No new free parameters | V(x) and m still unexplained |

**Status:** Framework is sound but uses quantum mechanics as bridge. A purely logical derivation would require deriving ℏ from 3FLL (connects to Issue 012).

---

## 12. Session 46.0 v2: Complete Derivation

### Sanity Check Findings (v1)

The v1 derivation was flagged for circularity:
- Used Mandelstam-Tamm (QM result) as input
- Used Fubini-Study metric (QM structure) as input
- Assumed ℏ empirically
- Assumed phase space structure

**See:** `01_Sanity_Checks/2025-12-16_Issue_013_SanityCheck.md`

### v2 Solution

Created complete derivation chain from 3FLL + parsimony alone:

**See:** `theory/derivations/Issue_013_Logical_Action_Functional_v2.md`

### v2 Derivation Chain

```
3FLL (primitive)
  ↓
Binary distinctions (bits)
  ↓
Distinguishability metric D
  ↓ (parsimony → chaos theorem)
Minimum scale exists → ℏ DEFINED (not empirical)
  ↓ (parsimony → proportionality)
D is continuous
  ↓ (parsimony → information preservation)
D-preserving transformations reversible
  ↓ (Masanes-Müller reconstruction)
Inner product structure
  ↓
Hilbert space → Phase space (x, p)
  ↓
Action S = ∫ p dx
  ↓ (Legendre transform)
Lagrangian S = ∫ L dt
  ↓ (parsimony)
Least action δS = 0
  ↓
Euler-Lagrange → Classical mechanics
```

### Key Fixes in v2

| v1 Problem | v2 Solution |
|------------|-------------|
| Mandelstam-Tamm assumed | Derived minimum scale from parsimony (Theorem 4.2) |
| Fubini-Study assumed | Derived inner product from reconstruction (Theorem 7.1) |
| ℏ empirical | ℏ DEFINED as minimum specification cost |
| Phase space assumed | Derived from Hilbert space structure |

### v2 Circularity Check

| Type | Status | Notes |
|------|--------|-------|
| Logical | ✅ PASS | Each theorem uses only prior results |
| Definitional | ✅ PASS | Terms defined in order |
| Parametric | ✅ PASS | ℏ defined, not derived from itself |
| Computational | N/A | No simulations |
| Validation | N/A | No empirical claims |

**External inputs: 0**
**Circular dependencies: 0**

### Remaining Gaps (Within Framework)

| Gap | Status | Notes |
|-----|--------|-------|
| Mass m | OPEN | May emerge from constraint structure |
| Potential V(x) | OPEN | Should emerge from interaction constraints |
| 3+1 dimensions | OPEN | Issue 014 |
| Relativistic action | OPEN | Future work |

### Success Criteria (Revised After External Review)

| Level | Criterion | Status |
|-------|-----------|--------|
| Minimal | Qualitative mapping | ✅ v1 |
| Moderate | Free particle derived (given structure) | ✅ v1, v2 |
| Strong | Complete chain from 3FLL | ⚠️ **GAP AT RECONSTRUCTION** |

---

## 13. External Review Findings (Session 46.0)

### Critical Gap Identified

External review correctly identified that **Theorem 7.1 (Reconstruction)** requires operational axioms NOT derivable from 3FLL + parsimony:

| Required Axiom | Description | Derivable from 3FLL? |
|----------------|-------------|---------------------|
| Tomographic locality | Global states from local measurements | **NO** |
| Subspace axiom | Pure state structure | **NO** |
| Composite systems | How systems combine | **NO** |
| Finite information | Limited info per system | **NO** |

### What IS Valid

- Sections 1-6 (3FLL → bits → D → minimum scale → continuity → reversibility): **Valid from 3FLL + parsimony**
- Sections 8-11 (phase space → action → Lagrangian → least action): **Valid given prior structure**

### What Requires Tier 2 Axioms

- Section 7 (Reconstruction): Requires ~3-4 operational axioms as **Tier 2 inputs**
- Why quantum over classical probability: Not derived
- Why complex over real numbers: Not derived

### Honest Assessment

The derivation is a **philosophical mapping** showing consistency between LRT and physics, not a complete derivation from pure logic. The reconstruction step imports physics through Tier 2 axioms, analogous to how we use Stone's theorem, Gleason's theorem, etc.

### Open Problem

Can the Masanes-Müller operational axioms be derived from 3FLL + parsimony?

**Possible approaches:**
1. Show axioms follow from parsimony on composite systems
2. Find alternative reconstruction requiring fewer axioms
3. Accept as Tier 2 (current position)

**Issue 013 Status: PARTIAL DERIVATION with reconstruction gap**
