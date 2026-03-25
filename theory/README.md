# LRT Theory Documents

Active theory documents for Logic Realism Theory. The canonical unified source is **LRT-MASTER.md**.

---

## The Theory in Brief

Logic Realism Theory (LRT) proposes a single ground-level commitment: reality is logical, informational, and dynamic. Expressed formally as X ≡ [L₃ : I∞ : A], this commitment grounds a derivation architecture for non-relativistic quantum mechanics.

| Component | Symbol | Role |
|-----------|--------|------|
| Three Fundamental Laws of Logic | L₃ | Admissibility filter (Identity, Non-Contradiction, Excluded Middle) |
| Infinite Information Space | I∞ | All representable configurations; structured by distinguishability |
| Continuous Binary Action | A | Instantiation primitive: actual vs. non-actual |

**Core equation:** A_Ω = L₃(I∞) — actuality is the L₃-admissible subset of all configurations.

**Falsifiable:** A stable physical record violating Boolean outcome structure would refute the framework.

---

## Active Documents

| Document | Description |
|----------|-------------|
| **[LRT-MASTER.md](LRT-MASTER.md)** | Canonical unified source: complete 13-step derivation chain |
| **[TAB-v2.0.md](TAB-v2.0.md)** | Transcendental Argument for Being: metaphysical groundwork |
| **[LRT-Lean-Proofing-Status.md](LRT-Lean-Proofing-Status.md)** | Current Lean formalization status |
| **[LRT-Lean-Approach.md](LRT-Lean-Approach.md)** | Formalization methodology |
| **[lrt-memory.md](lrt-memory.md)** | Project memory for AI agents |

---

## Technical Supplements

Located in `supplementary/`:

| ID | Document | Supports |
|----|----------|----------|
| S1 | [S1_PPC_Derivation.md](supplementary/S1_PPC_Derivation.md) | Foundation |
| S2 | [S2_H1_H2_Bridge.md](supplementary/S2_H1_H2_Bridge.md) | Step 3 |
| S3 | [S3_Eigenvalue_Restriction.md](supplementary/S3_Eigenvalue_Restriction.md) | Step 5 |
| S4 | [S4_Debreu_Nachbin.md](supplementary/S4_Debreu_Nachbin.md) | Step 10 |
| S5 | [S5_Dsing_BH_Entropy.md](supplementary/S5_Dsing_BH_Entropy.md) | Open Problem 9.5 |
| S6 | [S6_UNS_Theorem.md](supplementary/S6_UNS_Theorem.md) | Step 8 |
| S7 | [S7_G_Equivariance.md](supplementary/S7_G_Equivariance.md) | Step 11 |

---

## Derivation Chain (Steps 0-13)

| Step | Content | Status |
|------|---------|--------|
| 0 | X ≡ [L₃ : I∞ : A] | ESTABLISHED |
| 1 | X ⊣ A_Ω; A_Ω = L₃(I∞) | ESTABLISHED |
| 2 | Determinate Identity for all c ∈ A_Ω | ESTABLISHED |
| 3 | Local tomography from DI + L₃ framing | ARGUED |
| 4 | Complex Hilbert space ℂH (Masanes-Müller) | ESTABLISHED |
| 5 | PVM structure from Boolean A | ARGUED |
| 6 | Frame function on PVM structure | ESTABLISHED |
| 7 | Born rule via Gleason (1957) | ESTABLISHED |
| 8 | Unique Next State theorem | ARGUED |
| 9 | Ordinal time from UNS | ESTABLISHED |
| 10 | Continuous time via Debreu-Nachbin | ARGUED |
| 11 | G-equivariance; U(t) unitary | ARGUED |
| 12 | Stone's theorem; H self-adjoint | ESTABLISHED |
| 13 | Schrödinger equation | ESTABLISHED |

---

## Folder Structure

```
theory/
├── LRT-MASTER.md               # Canonical source
├── TAB-v2.0.md                 # Transcendental argument
├── LRT-Lean-*.md               # Formalization docs
├── lrt-memory.md               # Agent memory
├── figures/                    # Diagrams
├── issues/                     # Tracked gaps
├── LRT_Extended/               # Extension work
├── pdf/                        # PDF exports
├── submissions/                # Journal materials
└── supplementary/              # Technical supplements (S1-S7+)
```

**Archived materials:** See `/archive/theory-versions/` and `/archive/theory-pre-refactor/`.

---

## Cross-References

- **Lean formalization:** `/formalization/LrtFormalization/`
- **Documentation:** `/docs/formalization/`
- **Traceability:** `/traceability/`
- **Archives:** `/archive/`

---

**Last Updated**: 2026-03-20
