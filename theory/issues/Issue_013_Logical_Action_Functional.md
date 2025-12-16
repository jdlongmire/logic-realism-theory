# ISSUE 013: Formalize the Logical Action Functional

**Status:** OPEN
**Priority:** HIGH (core maturity gap)
**Phase:** 1 - Mathematical Rigor
**Created:** 2025-12-16
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

### 2.2 The Gap

| Concept | Logical Definition | Physical Equivalent | Bridge Status |
|---------|-------------------|---------------------|---------------|
| Action | Σ(distinction changes) | S = ∫ L dt | Claimed, not proven |
| Lagrangian | ? | L = T - V | No mapping |
| Time | Sequential instantiation | Physical seconds | Interpretive |
| Energy | ? | Joules | No derivation |

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

- [ ] Review literature: discrete → continuous action limits
- [ ] Formalize "distinction change" as measurable quantity
- [ ] Propose explicit ℏ-based conversion factor
- [ ] Attempt free particle derivation

### 7.2 Success Criteria

| Level | Criterion | Maturity |
|-------|-----------|----------|
| Minimal | Qualitative mapping with correct structure | Framework |
| Moderate | Free particle S derived from D | Model |
| Strong | General Lagrangian derived from logical action | Theory |

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
