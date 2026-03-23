---
layout: default
title: "LRT Program Dashboard"
description: "Live status of the Logic Realism Theory research program — formalization progress, publication timeline, and open problems."
---

<div class="topic-header">
  <h1>LRT Program Dashboard</h1>
  <p>Research program status — updated with each commit</p>
</div>

---

## Formalization Status

| Metric | Value |
|--------|-------|
| **Lean Build** | [![Lean Build](https://github.com/jdlongmire/logic-realism-theory/actions/workflows/lean-build.yml/badge.svg)](https://github.com/jdlongmire/logic-realism-theory/actions/workflows/lean-build.yml) |
| **Last Build** | ✅ SUCCESS — 2491 jobs, 0 errors (2026-03-23) |
| **Total Claims Tracked** | 59 |
| **VERIFIED** | 26 |
| **DERIVED** | 16 |
| **AXIOMATIZED** | 11 |
| **IMPORTED (Tier 2)** | 6 |
| **OPEN** | 2 |
| **Sorries** | 0 |

See [axiom-status.md](formalization/axiom-status.md) for full classification.

---

## Derivation Chain

```
Step 0  ✅  X ≡ [L₃ : I∞ : A]           — ESTABLISHED
Step 1  ✅  A_Ω = L₃(I∞)                 — ESTABLISHED
Step 2  ✅  Determinate Identity          — ESTABLISHED
Step 3  ✅  Local Tomography (H1, H2)     — ARGUED / IMPORTED (Hardy)
Step 4  ✅  Complex Hilbert Space ℂH      — IMPORTED (Masanes-Müller)
Step 5  ✅  PVM Structure                 — ARGUED
Step 6  ✅  Born Rule                     — IMPORTED (Gleason) + DERIVED
Step 7  ✅  Unitarity                     — DERIVED
Step 8  ✅  Temporal Emergence            — ARGUED / DERIVED
Step 9  ✅  Energy as Generator           — IMPORTED (Stone)
Step 10 ✅  Schrödinger Equation          — DERIVED
```

---

## Publication Timeline

| Milestone | Target | Status |
|-----------|--------|--------|
| **M1: TAB Submission** (Foundations of Physics) | 2026-04-01 | 🔲 In preparation |
| **M2: LRT-MASTER v2.0 Complete** | 2026-06-01 | 🔲 Revision in progress |
| **M3: MASTER Submission** (Physical Review A / Synthese) | 2026-08-01 | 🔲 Pending M2 |

---

## Active Work

| Issue | Type | Priority | Status |
|-------|------|----------|--------|
| [#52 LRT-MASTER v2.0 Revision Plan](https://github.com/jdlongmire/logic-realism-theory/issues/52) | Publication | High | In progress |
| [#37 Publication Preparation Plan](https://github.com/jdlongmire/logic-realism-theory/issues/37) | Publication | High | In progress |
| [#53 Internal Gleason Derivation](https://github.com/jdlongmire/logic-realism-theory/issues/53) | Formalization | High | Open |
| [#36 Publication Strategy](https://github.com/jdlongmire/logic-realism-theory/issues/36) | Publication | High | Open |

---

## Open Problems (Choke Points)

| ID | Problem | Risk | Path |
|----|---------|------|------|
| **ACT-001** | X grounds A_Ω (bridge principle) | High | Philosophical; may remain argued |
| **QM-008** | K=2 (complex field forcing) | High | OPN-005 purification route (preferred) |
| **QM-011** | Eigenvalue-outcome correspondence | High | Derive from operational postulates |
| **OPN-004** | K=2 via Boolean-interference | High | Original research; primary target |
| **OPN-006** | Projection contraction from Mathlib | Low | Straightforward Mathlib lookup |

---

## Axiom Reduction History

| Date | Total Axioms | PRIMITIVE | EXTERNAL | REMAINING |
|------|-------------|-----------|----------|-----------|
| 2025-11-01 | ~45 | — | — | — |
| 2026-03-17 | 31 | 3 | 14 | 14 |
| 2026-03-21 | 24 | 3 | 18 | 3 |
| 2026-03-23 | **22** | 3 | 12 | **7** |

**Target:** 3 PRIMITIVE axioms (I∞, I_infinite, bridge_principle) — maintained.  
**Net reduction this session: Δ −9 axioms.**

---

## Key Documents

| Document | Description |
|----------|-------------|
| [LRT-MASTER.md](https://github.com/jdlongmire/logic-realism-theory/blob/master/theory/LRT-MASTER.md) | Canonical 13-step derivation |
| [TAB-v2.0.md](https://github.com/jdlongmire/logic-realism-theory/blob/master/theory/TAB-v2.0.md) | Transcendental Argument for the Bridge |
| [claims.yaml](https://github.com/jdlongmire/logic-realism-theory/blob/master/formalization/traceability/claims.yaml) | Full traceability matrix |
| [axiom-status.md](https://github.com/jdlongmire/logic-realism-theory/blob/master/docs/formalization/axiom-status.md) | Axiom classification and audit |

---

## GitHub Project

Full issue board: [LRT Research Program](https://github.com/users/jdlongmire/projects/3)

*Human-Curated, AI-Enabled (HCAE) — last updated 2026-03-23*
