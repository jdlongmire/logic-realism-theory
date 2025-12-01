# LRT Paper Restructuring Strategy

**Created**: 2025-11-29 (Session 30.0)
**Status**: ACTIVE
**Last Updated**: 2025-11-29 (Gaps 1-4 complete)

---

## Executive Summary

Restructuring from 4-paper series to **2 Physics Papers + 1 Philosophy Paper** based on post-review feedback. Bridging paper deprecated; content absorbed into Main and Technical.

**Goal**: Close critical gaps to produce rigorous, publishable work with no timeline pressure.

---

## Final Paper Structure

### Paper 1: "Quantum Mechanics from Logical Constraints on Distinguishability"

| Attribute | Value |
|-----------|-------|
| **Base** | Current `Logic_Realism_Theory_Main.md` |
| **Target Venue** | Foundations of Physics (primary) or Physical Review A |
| **Length** | 40-45 pages |
| **Audience** | Physics community (foundational physicists, quantum foundations) |
| **Role** | Flagship paper - complete argument with physical interpretation |

**Content**:
- Introduction with puzzle clearly stated
- Framework (3FLL as constitutive, IIS, Boolean actuality)
- Derivation chain with physical interpretation
- Physical implications (measurement, entanglement with worked examples)
- Falsifiability and predictions
- Comparison with alternatives
- Discussion

### Paper 2: "Technical Foundations of Logic Realism Theory"

| Attribute | Value |
|-----------|-------|
| **Base** | Current `Logic_Realism_Theory_Technical.md` |
| **Target Venue** | Foundations of Physics or Studies in HPS |
| **Length** | 30-35 pages |
| **Audience** | Specialists who want full proofs |
| **Role** | Rigorous companion - complete proofs, not sketches |

**Content**:
- Distinguishability as primitive (with Hardy verification)
- IIS physical interpretation (detailed)
- From D to inner product (rigorous)
- LRT → MM1-MM4 (complete proofs)
- Stability selection (with Real QM explicit proof)
- MM5 derivation (rigorous or honest about status)
- Ontic Booleanity (Theorem 7.1)
- Conclusions

### Paper 3: "Logic Realism and Quantum Foundations"

| Attribute | Value |
|-----------|-------|
| **Base** | Current `Logic_Realism_Theory_Philosophy.md` |
| **Target Venue** | British Journal for the Philosophy of Science |
| **Length** | 25-30 pages |
| **Audience** | Philosophers of science/physics |
| **Role** | Philosophical defense and implications |

**Content**:
- Constitutive vs descriptive argument (deepened)
- Conceivability vs observability
- Comparison to Kant, structural realism
- Implications for philosophy of logic
- Forward references to Papers 1-2

### Deprecated: Bridging Paper

`Logic_Realism_Theory_Bridging.md` - No longer a standalone publication.

**Content disposition**:
| Section | Destination |
|---------|-------------|
| §1 (puzzle framing) | Main introduction |
| §3 (abductive argument) | Philosophy paper |
| §5 (philosophical payoffs) | Philosophy paper |
| §6 (technical preview) | Deleted (redundant) |
| §7 (comparison) | Main paper |

---

## Critical Gaps to Close

### Priority Order (Revised)

Based on risk/value analysis, we proceed in this order:

| Priority | Gap | Risk | Value | Time Est. | Status |
|----------|-----|------|-------|-----------|--------|
| 1 | IIS Physical Interpretation | Low | High | 2-3 weeks | COMPLETE |
| 2 | Bell State Worked Calculation | Low | High | 1-2 weeks | COMPLETE |
| 3 | Real QM Local Tomography Proof | Low | Medium | 1 week | COMPLETE |
| 4 | Hardy Kernel Verification | Medium | Medium | 1-2 weeks | COMPLETE |
| 5 | Constitutive vs Descriptive | Low | Medium | 1 week | COMPLETE |
| 6 | MM5 Rigorous Derivation | Medium | High | 1-2 weeks | COMPLETE |
| 7 | Figures and Diagrams | Low | Medium | 2 weeks | NOT STARTED |

**Rationale**: Start with low-risk/high-value gaps to build momentum and strengthen papers regardless of MM5 outcome. Tackle MM5 last with clearer framework established.

---

## Gap Specifications

### Gap 1: IIS Physical Interpretation

**Location**: Technical §3.4 (new), Main §3 (summary)

**Deliverables**:
- [x] Example 1: Single qubit / Bloch sphere
- [x] Example 2: Two-slit experiment
- [x] Example 3: General n-dimensional system
- [x] Example 4: Composite systems / entanglement
- [x] Main paper summary paragraph

**Output**: 2-3 pages in Technical, 1 page in Main

**Acceptance criteria**: Reader can connect abstract IIS definition to concrete quantum systems

**Completed**: Session 31.0 (2025-11-29)

---

### Gap 2: Bell State Worked Calculation

**Location**: Main §4.3 (expanded)

**Deliverables**:
- [x] IIS representation of |Ψ⁻⟩
- [x] Step-by-step correlation calculation
- [x] E(n̂_A, n̂_B) = -n̂_A · n̂_B derived
- [x] CHSH violation shown (|S| = 2√2)
- [x] No-signaling demonstration
- [x] Contrast with classical/Bohmian

**Output**: 2-3 pages in Main

**Acceptance criteria**: Complete worked example a physicist can follow

**Completed**: Session 31.0 (2025-11-29)

---

### Gap 3: Real QM Local Tomography Proof

**Location**: Technical §5.2 (expanded)

**Deliverables**:
- [x] Construct two real QM states with identical local marginals
- [x] Show they're globally distinguishable
- [x] Prove complex QM distinguishes them via phase
- [x] Conclude: Real QM violates A3c

**Output**: 1-2 pages in Technical

**Acceptance criteria**: Explicit counterexample, not just assertion

**Completed**: Session 31.0 (2025-11-29)

---

### Gap 4: Hardy Kernel Verification

**Location**: Technical §3.3.1 (new subsection)

**Deliverables**:
- [x] Verify D is metric (reference Theorem 2.1)
- [x] Verify D ∈ [0,1] range explicitly
- [x] Verify continuity of D from A3a
- [x] Verify existence of perfectly distinguishable triplets
- [x] Conclude: Hardy construction applies

**Output**: 2-3 pages in Technical

**Acceptance criteria**: Each Hardy requirement explicitly verified for LRT's D

**Completed**: Session 31.0 (2025-11-29)

---

### Gap 5: Constitutive vs Descriptive Clarification

**Location**: Main §2 or Philosophy §2.2

**Deliverables**:
- [x] Address circularity objection head-on
- [x] Explain apparatus-level conformity as evidence FOR LRT
- [x] Distinguish constitutive claim from operational framework
- [x] Contrast with "3FLL merely descriptive" alternative

**Output**: 2-3 pages

**Acceptance criteria**: Circularity objection preempted

**Completed**: Session 31.0 (2025-11-29)

---

### Gap 6: MM5 Rigorous Derivation

**Location**: Technical §6 (revision)

**Feasibility Spike Result** (Session 31.0):
- Current Lemma 6.1 (CBP → Purification Uniqueness) is hand-wavy
- Correct path: Hilbert space structure → Uhlmann's theorem → Purification Uniqueness
- Risk reduced from HIGH to MEDIUM; time from 4-6 weeks to 1-2 weeks

**Revised Deliverables**:
- [x] **Step A**: Local Tomography → Tensor Product (new §6.2)
  - [x] State that A3c implies IIS_{AB} = IIS_A ⊗ IIS_B
  - [x] Cite Masanes-Müller 2011 for standard result
- [x] **Step B**: Uhlmann's Theorem (new §6.3)
  - [x] State Uhlmann's theorem formally
  - [x] Note this follows from Hilbert space + tensor product structure
  - [x] Show this = purification uniqueness (Lee-Selby condition 3)
- [x] **Step C**: Complete Derivation (revise §6.4)
  - [x] Chain: LRT → Hilbert space → Tensor product → Uhlmann → Lee-Selby → MM5
  - [x] Remove hand-wavy CBP argument from old Lemma 6.1

**Output**: 3-4 pages in Technical (revision, not expansion)

**Acceptance criteria**: Clean chain of established results with proper citations

**Key insight**: Purification uniqueness is Uhlmann's theorem applied to the Hilbert space structure that LRT already establishes in §3.3. We cite standard results, not prove from scratch.

**Completed**: Session 31.0 (2025-11-29)

---

### Gap 7: Figures and Diagrams

**Location**: Throughout all papers

**Deliverables**:
- [ ] IIS → QM → Boolean actuality flowchart
- [ ] Bloch sphere as IIS example
- [ ] Hardy triplet geometry
- [ ] Bell state correlation structure
- [ ] Comparison tables visualized

**Output**: 5-8 figures

**Acceptance criteria**: Key concepts have visual representation

---

## Open Decisions

### Decision 1: Ontic Booleanity Placement

**Options**:
- A) Keep in Technical paper only (current)
- B) Move to Main paper (stronger flagship)
- C) Split: theorem statement in Main, proof in Technical

**Current choice**: TBD

**Notes**: Theorem 7.1 closes epistemic loophole - high value for Main paper

---

### Decision 2: Submission Strategy

**Options**:
- A) Sequential: Main + Technical to Foundations of Physics together, then Philosophy to BJPS
- B) Parallel: Three papers to three venues simultaneously

**Current choice**: TBD

**Notes**: Sequential is lower risk; parallel is faster

---

### Decision 3: MM5 Fallback Framing

**If rigorous proof not achievable**:
- A) "Conjecture with detailed argument"
- B) "Open problem with pathway identified"
- C) Claim MM1-MM4 only, leave MM5 for future work

**Current choice**: TBD (assess after Gap 6 work)

---

## Timeline

### Phase 1: Foundation Building (Weeks 1-5)

| Week | Focus | Deliverable |
|------|-------|-------------|
| 1-2 | IIS Physical Interpretation | Technical §3.4 draft |
| 2-3 | Bell State Calculation | Main §4.3 expanded |
| 4 | Real QM Proof | Technical §5.2 expanded |
| 5 | Hardy Verification | Technical §3.3.1 draft |

**Checkpoint**: Papers strengthened regardless of MM5 outcome

### Phase 2: MM5 Assessment (Week 6)

| Week | Focus | Deliverable |
|------|-------|-------------|
| 6 | MM5 Feasibility Spike | Assessment document: tractable or not? |

**Decision point**: Commit to rigorous proof or fallback framing

### Phase 3: MM5 Work (Weeks 7-12)

| Week | Focus | Deliverable |
|------|-------|-------------|
| 7-10 | CBP → Purification Uniqueness | Lemma 6.1 draft |
| 11-12 | Lee-Selby Verification | Technical §6 complete |

**Or if fallback**: 2 weeks to write honest framing

### Phase 4: Polish (Weeks 13-16)

| Week | Focus | Deliverable |
|------|-------|-------------|
| 13 | Constitutive Clarification | Main §2 expanded |
| 14-15 | Figures and Diagrams | All figures |
| 16 | Final Polish | All papers submission-ready |

**Total**: ~4 months

---

## Progress Tracking

### Weekly Status Template

```markdown
## Week N Status (Date)

### Completed
- [ ] ...

### In Progress
- [ ] ...

### Blocked
- [ ] ...

### Next Week
- [ ] ...
```

### Gap Completion Checklist

| Gap | Started | Draft | Review | Complete |
|-----|---------|-------|--------|----------|
| 1. IIS Interpretation | [x] | [x] | [ ] | [x] |
| 2. Bell Calculation | [x] | [x] | [ ] | [x] |
| 3. Real QM Proof | [x] | [x] | [ ] | [x] |
| 4. Hardy Verification | [x] | [x] | [ ] | [x] |
| 5. Constitutive Clarification | [x] | [x] | [ ] | [x] |
| 6. MM5 Derivation | [x] | [x] | [ ] | [x] |
| 7. Figures | [ ] | [ ] | [ ] | [ ] |

---

## References

- Lee, C. M. & Selby, J. H. (2020). "Deriving Grover's lower bound from simple physical principles." *Quantum* 4, 231.
- Hardy, L. (2001). "Quantum theory from five reasonable axioms." arXiv:quant-ph/0101012.
- Masanes, L. & Müller, M. P. (2011). "A derivation of quantum theory from physical requirements." *New J. Phys.* 13, 063001.
- Renou, M.-O. et al. (2021). "Quantum theory based on real numbers can be experimentally falsified." *Nature* 600, 625-629.

---

## Document History

| Date | Change | Session |
|------|--------|---------|
| 2025-11-29 | Created | 30.0 |

---
