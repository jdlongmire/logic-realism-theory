# LRT Formalization: Work Plan & Agent Assignments

**Date:** 2026-03-17
**Status:** Active Development
**Goal:** Close critical gaps, expand subsumption coverage, strengthen philosophical claims

---

## Part 1: Critical Gap Closure

### Priority 1: K=2 Forcing (OPN-004)

**Current state:** `HardyK := 2` by definition — trivial
**Required:** Derivation from L₃ + Boolean + interference

**Three possible routes:**

| Route | Approach | Circularity Risk |
|-------|----------|------------------|
| **A: Hardy-style** | Boolean events → interference → K=2 | Medium (needs interference axiom) |
| **B: CDP purification** | Boolean → Purification → CDP theorem → K=2 | Low (established path) |
| **C: Categorical** | Symmetric monoidal structure → K=2 | Low (but infrastructure-heavy) |

**Recommendation:** Route B (CDP purification) is lowest risk. Need agent to formalize the chain:
- L₃ → Boolean events ✓ (done)
- Boolean + composition → purification structure
- Purification + H1 → CDP theorem
- CDP → K=2

**Agent task:** Formalize CDP purification axioms in Lean; prove K=2 follows

---

### Priority 2: Step 3 Strengthening (L₃ → H1/H2)

**Current state:** `stats_imply_events` is axiomatic bridge
**Critique (Grok):** "weakest conceptual step"

**Approaches:**

1. **Explicit witness construction:** For any state ρ, construct the event set that determines it
2. **Categorical characterization:** Use Chu spaces or effect algebras to make the bridge rigorous
3. **Information-theoretic bridge:** Shannon capacity → distinguishability → tomography

**Agent task:** Research Chu spaces / effect algebra characterization of tomography; propose Lean formalization

---

### Priority 3: FF1-FF3 Tightening

**Current state:** Frame function axioms mapped to logic laws "by analogy"
**Critique (Grok):** "more like analogies than tight entailments"

**Approach:** Make the mapping precise via:
- EM → normalization: every state is in some outcome class (exhaustive)
- NC → non-overlapping: no state in two incompatible outcome classes
- I → identity: outcome = outcome

**Agent task:** Write out the formal correspondence; identify if additional bridge axiom needed

---

## Part 2: Subsumption Research

### MWI / Deutsch-Wallace

**Key insight:** Deutsch-Wallace derive Born rule via decision theory in Everettian multiverse.

**LRT relationship:**
- They assume unitary evolution + branching structure
- LRT derives unitary evolution from L₃ + information preservation
- Born rule in both cases: probability measure over branches/actualities

**Subsumption claim:** LRT explains *why* the branching structure exists (from A) and *why* rational agents use Born weights (from MaxEnt uniqueness)

**Open question:** Can we formalize that Deutsch-Wallace rationality axioms follow from L₃?

**Research task:**
- Read [Wallace's formal proof](https://academic.oup.com/book/11755/chapter/160769125)
- Identify their core axioms
- Map to LRT primitives
- Flag any axiom not derivable from L₃

---

### Tegmark MUH

**Key insight:** MUH claims physical existence = mathematical existence. All consistent mathematical structures physically exist.

**LRT relationship:**
- MUH is ontologically stronger: all structures exist
- LRT: only L₃-consistent structures with actualization
- MUH has measure problem (which structures are "more real"?)
- LRT has A primitive: actualization distinguishes

**Subsumption claim:** LRT is a *restricted* MUH:
- MUH level 4 (all math) is larger than LRT
- LRT = MUH restricted to [L₃ : I∞ : A]-compatible structures
- This restriction is what yields QM specifically

**Research task:**
- Document MUH measure problem
- Show LRT's A primitive solves it
- Formalize: LRT ⊂ MUH, and QM is the interface structure for LRT-restricted MUH

---

### Hardy / CDP / Masanes-Müller

**Current status:** Already addressed in subsumption section of LRT-Lean-Proofs.md

**Key relationship:**
| Framework | Primitives | LRT Status |
|-----------|-----------|------------|
| Hardy | H1-H5 | H1/H2 derived (Step 3); H3-H5 external |
| CDP | Purification + tomography | Tomography derived; purification route open |
| Masanes-Müller | Information postulates | Derivable from I∞ + L₃ |

**Gap:** Need to formalize that Masanes-Müller postulates follow from LRT primitives.

---

### Categorical QM (CQM)

**Key insight:** Symmetric monoidal categories with daggers (†-SMC) characterize quantum processes.

**LRT relationship:**
- CQM is structural: describes the category, not why it exists
- LRT explains why physical processes form a †-SMC
- The "dagger" (adjoint) comes from L₃ symmetry

**Research task:**
- Formalize †-SMC structure in Lean
- Show LRT A_Ω naturally forms a †-SMC
- Connect to existing CQM Lean work (if any)

---

## Part 3: Agent Spawn Plan

### Phase 1: Immediate (Parallel)

| Agent ID | Task | Working Dir | Priority |
|----------|------|-------------|----------|
| **LRT-CDP-K2** | Formalize CDP purification → K=2 in Lean | logic-realism-theory | HIGH |
| **LRT-Step3** | Research Chu space / effect algebra for Step 3 | logic-realism-theory | HIGH |
| **LRT-MWI** | Analyze Deutsch-Wallace axioms; map to L₃ | ThinxS/research-programs | MEDIUM |
| **LRT-MUH** | Document Tegmark MUH measure problem; LRT solution | ThinxS/research-programs | MEDIUM |

### Phase 2: After Phase 1 (Dependent)

| Agent ID | Task | Depends On |
|----------|------|------------|
| **LRT-K2-Lean** | Implement K=2 derivation in Lean | LRT-CDP-K2 |
| **LRT-Step3-Lean** | Implement Step 3 tightening in Lean | LRT-Step3 |
| **LRT-Subsume** | Write unified subsumption paper section | LRT-MWI, LRT-MUH |

### Phase 3: Infrastructure

| Agent ID | Task | Notes |
|----------|------|-------|
| **LRT-Sorries** | Monitor Mathlib spectral theory; close sorries when available | Long-running |
| **LRT-CI** | Set up CI for formalization repo | DevOps |

---

## Part 4: Alternative Approaches Worth Exploring

### 4.1 Retrocausal / Two-Time Approaches

**Idea:** Some reconstructions (Schulman, Wharton) use retrocausality. LRT's A primitive is instantaneous, not directional. Does this help or hurt?

**Research question:** Can A be interpreted as boundary condition rather than dynamical?

### 4.2 Relational QM (Rovelli)

**Idea:** States are relative to observers. No absolute facts.

**LRT relationship:** A provides absolute facts (actual vs non-actual). LRT is not relational.

**Contrast paper:** Write up why LRT rejects relational QM and what predictive differences exist.

### 4.3 QBism

**Idea:** Quantum states are agent beliefs, not physical states.

**LRT relationship:** LRT is realist. States are objective configurations in I∞. Direct conflict.

**Contrast paper:** LRT vs QBism on measurement problem.

### 4.4 Constructor Theory (Deutsch)

**Idea:** Physics is about possible/impossible transformations, not states.

**LRT relationship:** A defines possible (actual) vs impossible (non-actual). Potential alignment.

**Research question:** Is constructor theory a subset of LRT? Do constructors = L₃-permitted transformations?

---

## Part 5: Success Criteria

### For K=2 (OPN-004)
- [ ] CDP purification axioms formalized
- [ ] `lrt_forces_k_equals_2` theorem has non-trivial proof (not `rfl`)
- [ ] AI reviews confirm non-circularity

### For Step 3
- [ ] `stats_imply_events` replaced with theorem
- [ ] Grok-style "hand-wave" critique addressed
- [ ] Documentation explains the bridge rigorously

### For Subsumption
- [ ] MWI decision theory axioms → LRT primitives mapping document
- [ ] MUH measure problem → LRT solution document
- [ ] Categorical QM → LRT structure document

---

## Sources

- [Deutsch-Wallace Born Rule](https://academic.oup.com/book/11755/chapter/160769125)
- [Hardy's Five Axioms](https://arxiv.org/abs/quant-ph/0101012)
- [Masanes-Müller Reconstruction](https://www.iqoqi-vienna.at/research/mueller-group/reconstructions-of-quantum-theory)
- [Tegmark MUH](https://arxiv.org/abs/0704.0646)
- [Categorical QM Reconstruction](http://cqm.wikidot.com/cqm-reconstruction)
- [CDP Purification](https://arxiv.org/abs/1011.6451)
- [Wallace Formal Proof](https://academic.oup.com/book/11755/chapter/160769125)
- [Information-theoretic Postulates](https://arxiv.org/abs/1203.4516)
