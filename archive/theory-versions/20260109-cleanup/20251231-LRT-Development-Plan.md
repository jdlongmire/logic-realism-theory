# LRT Development Plan: Hardening the Derivation Chain

**Created**: 2025-12-31
**Goal**: Address the four vulnerabilities identified in external evaluations
**Status**: Planning

---

## Executive Summary

External evaluations (Grok, ChatGPT) converge on the same assessment:
- **Overall**: 7.5-8/10 — unusually tight for an ambitious metaphysical project
- **Robust**: Anti-holism argument (§2.3), vehicle trilemma structure (§4.6), Bell reframing (Appendix C)
- **Vulnerable**: Vehicle-weight objectivity (fulcrum), dim ≥ 3 assumption, ontological/transcendental hedging, novelty positioning

The development plan addresses each vulnerability with minimal disruption to the existing chain.

---

## Phase 1: Vehicle-Weight Hardening (CRITICAL PATH)

**Priority**: Highest — this is the fulcrum on which the derivation turns
**Estimated scope**: New subsection §4.2 (~2-3 pages)
**Dependency**: None

### 1.1 Problem Statement

The claim that the Born measure is an objective property of the physical vehicle (not agent credence or predictive summary) is currently *sufficient* but not *forced* by L₃ in the same deductive way that anti-holism is.

Sophisticated Everettians and QBists can "pay the price" and take horn (a) or (c) cheerfully.

### 1.2 Hardening Strategy

**A. Reframe as identity criterion for dispositions**

Core insight: If you need modal facts for record stability, you already need them for the pre-record state.

New lemma (sketch):
```
Lemma (Dispositional continuity): If macroscopic records are objective and
counterfactually stable, then the pre-record state must have objective modal
structure relative to the record-alternatives.

Proof sketch: Record stability under irrelevant variation is itself a modal fact.
Denying modal facts for the immediate pre-record configuration while allowing
them for records introduces an identity discontinuity not grounded in any
physical transition. This violates Id (no description-dependent identity).
```

**B. Make rival horns pay in identity currency**

Against horn (a) "no objective poise":
- Collapses vehicle/content distinction
- Same physical vehicle paired with multiple incompatible outcome-measure contents
- = Representational underdetermination at vehicle level
- = Id violation

Against horn (c) "disposition exists but not in vehicle":
- Press the bearer principle
- Free-floating properties are category errors
- If disposition is real, it must attach to something in the ontology

**C. Add empirical calibration argument**

Independent agents with different priors converge on same empirical frequencies.
Best explained by preparation-level objective weight, not agent credence.
Otherwise intersubjective convergence is brute.

### 1.3 Deliverables

- [ ] New §4.2: "Record-Robustness and Vehicle Dispositions"
- [ ] Lemma: Dispositional continuity
- [ ] Expanded horn (a) and horn (c) attacks in §4.6
- [ ] Short calibration argument (1 paragraph)

---

## Phase 2: Dim ≥ 3 Compositional Lemma

**Priority**: High — currently "plausible hand-waving"
**Estimated scope**: 1 lemma + 2-3 paragraphs
**Dependency**: None

### 2.1 Problem Statement

Gleason/Busch requires dim ≥ 3. The current "every real system is embedded" argument is intuitive but not formalized.

### 2.2 Hardening Strategy

**A. Convert embedding to theorem-like statement**

```
Lemma (No physically closed 2D arena): Any system that admits (i) a nontrivial
measurement interaction and (ii) stable records must be composable with at least
one additional degree of freedom that participates in record formation; therefore
the relevant arena for the measure is at least 3D.
```

**B. Clean conditional for truly isolated 2D**

State explicitly:
- "In a strictly 2D universe, identity constraints do not uniquely fix weights"
- "That is not a failure of L₃; it is an underconstrained arena"
- "Our world's richness is what lets identity bite"

This turns the "pathology" into an explanatory discriminator.

**C. Reference actual physics**

Cite Zurek's decoherence work: qubits in labs are always coupled to higher-dim baths.

### 2.3 Deliverables

- [ ] New lemma in §4.3 or Appendix A
- [ ] Clean conditional statement
- [ ] Physics reference (Zurek)

---

## Phase 3: Id-Strong / Id-Weak Clarification

**Priority**: Medium — currently "hedging weakens punch"
**Estimated scope**: Boxed definition + 1 paragraph
**Dependency**: None

### 3.1 Problem Statement

The paper toggles between:
- **Id-Strong**: "Indeterminate identity is non-being"
- **Id-Weak**: "Any world with determinate records must satisfy Id at record level"

The strong reading is more exciting but harder to defend. The transcendental reading is safer but less dramatic.

### 3.2 Hardening Strategy

**A. State both theses explicitly in §2.2**

```
Definition (Two readings of Determinate Identity):

Id-Strong: To lack determinate identity is to be nothing. Indeterminate identity
is not a borderline case of existence but a failure to exist at all.

Id-Weak: Any physical reality that admits determinate description, measurement,
or record must satisfy Determinate Identity at least at the level of records.
```

**B. Label which the derivation needs**

"The Born-rule chain requires Id-Weak. Id-Strong is the intended ontology and strengthens the interpretation but is not required for the mathematics."

**C. Specify scope of application**

- Id applies to instantiated vehicles and record-bearing systems
- Id does not require classical value definiteness for all counterfactual micro-observables

### 3.3 Deliverables

- [ ] Boxed definition in §2.2
- [ ] "Scope of Id" paragraph
- [ ] Clear labeling of which reading is used where

---

## Phase 4: Novelty Positioning and Parsimony Table

**Priority**: Medium — affects reception, not validity
**Estimated scope**: 1 table + 2 paragraphs
**Dependency**: None

### 4.1 Problem Statement

The paper may overstate novelty relative to Masanes-Müller, Hardy, Chiribella-D'Ariano-Perinotti. What is genuinely new is grounding their operational axioms in a single metaphysical constraint.

### 4.2 Hardening Strategy

**A. Parsimony table**

| Framework | Independent Axioms | Type |
|-----------|-------------------|------|
| Hardy (2001) | 5 reasonable axioms | Operational |
| Chiribella et al. (2011) | 6 informational axioms | Operational |
| Masanes-Müller (2011) | 5 physical requirements | Operational |
| **LRT** | L₃ + anti-holism | Metaphysical |

**B. Own the division of labor**

"Masanes-Müller (and other reconstructions) do formal derivation from operational axioms. LRT explains *why* those axioms should hold if logic constrains instantiation. This is a grounding thesis, not a replacement."

**C. Acknowledge trade-off**

"You pay in metaphysics what they pay in operational postulates. The question is which is more fundamental."

### 4.3 Deliverables

- [ ] Parsimony table in §1 or §5
- [ ] Division of labor paragraph
- [ ] Trade-off acknowledgment

---

## Phase 5: Optional Alternative Routes (Exploratory)

**Priority**: Low — only if Phases 1-4 insufficient
**Estimated scope**: Variable
**Dependency**: Phases 1-4

### 5.1 Alternative Route A: Ellerman's Partition Approach

Replaces Gleason with partition-based derivation.
- Works in dim = 2
- Avoids Gleason pathology entirely
- Metaphysical fit: superposition as objective indefiniteness (pre-instantiation poise)

**Trade-off**: Requires substantial rewrite of §4 and Appendix A.

### 5.2 Alternative Route B: GPT Causal Consistency

Derives Born from no-signaling in generalized probabilistic theories.
- Grounds in causality (NC for spacelike events)
- Could unify with Appendix C (Bell)

**Trade-off**: More operational flavor, less direct L₃ grounding.

### 5.3 Alternative Route C: Dutch Book Coherence

Ties vehicle-weight objectivity to logical coherence via betting arguments.
- Strengthens trilemma by framing rivals as incoherent
- Works in deterministic multiverse setup

**Trade-off**: Still relies on Gleason (dim > 2 pathology remains).

### 5.4 Deliverables (if pursued)

- [ ] Feasibility assessment for each route
- [ ] Draft alternative appendix (boxed or supplementary)

---

## Implementation Schedule

| Phase | Scope | Priority | Dependencies |
|-------|-------|----------|--------------|
| 1 | ~3 pages | Critical | None |
| 2 | ~1 page | High | None |
| 3 | ~0.5 page | Medium | None |
| 4 | ~1 page | Medium | None |
| 5 | Variable | Low | 1-4 |

**Total estimated additions**: 5-6 pages

Phases 1-4 can be done in parallel. Phase 5 only if 1-4 prove insufficient after review.

---

## Success Criteria

1. **Vehicle-weight**: Reviewers cannot dismiss as "mere metaphysical posit" — must engage with dispositional continuity argument
2. **Dim ≥ 3**: Explicit lemma that critics must rebut, not hand-wave
3. **Id readings**: No charge of "hedging" — both readings stated, derivation needs labeled
4. **Novelty**: No charge of "overclaim" — parsimony table makes position clear

---

## Next Steps

1. Review this plan
2. Decide priority ordering (recommend: Phase 1 first as critical path)
3. Draft Phase 1 deliverables
4. Iterate based on your assessment

---

## Appendix: Key Quotes from Evaluations

**Grok on vehicle-weight**:
> "A sophisticated Everettian or QBist can (and will) simply take horn (a) or (c) and pay the ontological price cheerfully. The paper needs a stronger independent argument that vehicle-weight objectivity is cheaper than the alternatives, not merely that it is sufficient."

**ChatGPT on vehicle-weight**:
> "The trilemma is logically tight given that premise; the premise itself is not forced by L₃ in the same deductive way that anti-holism is."

**Grok on anti-holism**:
> "The trilemma in §2.3 is one of the cleaner destructions of global holism I have seen in the recent literature. Most people stop at 'unparsimonious'; this draft actually argues incoherent."

**ChatGPT on anti-holism**:
> "By showing that global holism is incompatible with Determinate Identity, you reduce the number of 'bridge assumptions' to essentially one: vehicle-weight objectivity."
