# LRT Theory Documents

Active theory documents for Logic Realism Theory. The canonical unified source is **100-LRT-CORE-PHYSICS.md**.

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
| **[002-LRT-TAB-PHILOSOPHY.md](002-LRT-TAB-PHILOSOPHY.md)** | Transcendental Argument for Being: metaphysical groundwork |
| **[100-LRT-CORE-PHYSICS.md](100-LRT-CORE-PHYSICS.md)** | Canonical unified source: complete 14-step derivation (Steps 0-14) |
| **[400-LRT-FORMALIZATION.md](400-LRT-FORMALIZATION.md)** | Complete formalization reference (static) |
| **[500-LRT-FORMALIZATION-STATUS.md](500-LRT-FORMALIZATION-STATUS.md)** | Current formalization status (living doc) |
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
| S8-S14 | Additional supplements | Various |

---

## Derivation Chain (Steps 0-14)

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
| 14 | Lagrangian and path integral | ESTABLISHED |

---

## Folder Structure

```
theory/
├── 002-LRT-TAB-PHILOSOPHY.md   # Philosophical foundation
├── 100-LRT-CORE-PHYSICS.md    # Core physics derivation
├── 300-LRT-COSMOLOGY.md       # Dark energy extension
├── 400-LRT-FORMALIZATION.md   # Complete formalization reference
├── 500-LRT-FORMALIZATION-STATUS.md  # Formalization status (living doc)
├── LRT-MEMORY.md               # Agent memory
├── tasks.md                    # Task tracking
├── figures/                    # Diagrams
├── issues/                     # Tracked gaps
├── submissions/                # Journal materials
└── supplementary/              # Technical supplements (S1-S7+)
```

**Archived materials:** See `/archive/` (theory-versions, theory-pre-refactor, 2026-03-pre-rename).

---

## Cross-References

- **Lean formalization:** `/formalization/LrtFormalization/`
- **Documentation:** `/docs/formalization/`
- **Traceability:** `/traceability/`
- **Archives:** `/archive/`

---

**Last Updated**: 2026-03-27
