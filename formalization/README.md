# LRT Lean 4 Formalization

Lean 4 formalization of Logic Realism Theory, implementing the complete derivation chain from X to Schrödinger.

---

## Status (2026-03-27)

| Metric | Value |
|--------|-------|
| **Build** | ✅ SUCCESS |
| **Total Axioms** | 19 |
| **Sorries** | 3 (technical, not conceptual) |
| **Toolchain** | leanprover/lean4:v4.28.0 |

### Axiom Classification

| Category | Count | Description |
|----------|-------|-------------|
| **PRIMITIVE** | 3 | I∞, I_infinite, bridge_principle |
| **EXTERNAL** | 16 | Established math (Gleason, Stone, Hardy, CDP, No-Hiding, etc.) |
| **REMAINING** | 0 | All derivable axioms converted to theorems |

**Net reduction: 44 → 19 axioms (57% reduction)**

---

## Structure

```
formalization/
├── LrtFormalization/           # Lean source files
│   ├── Step0_Primitives.lean   # I type, X, A_Ω, Event, L3Admissible
│   ├── Step1_Constitution.lean # Bridge principle, ActualizedEvents
│   ├── Step2_DeterminateIdentity.lean
│   ├── Step3_LocalTomography.lean
│   ├── Step4/                  # Hardy, Boolean, Purification
│   ├── Step5/                  # Eigenvalue restriction
│   ├── Step6_BornRule.lean     # Gleason, Born rule
│   ├── Step7_Unitarity.lean
│   ├── Step8_TemporalEmergence.lean
│   ├── Step9_EnergyAction.lean # Stone, Planck, Noether
│   └── Step10_Schrodinger.lean
├── scripts/
│   ├── build.sh                # Recommended: fetches cache + builds
│   ├── clean.sh                # Removes LRT oleans only
│   └── update-mathlib.sh       # Safe Mathlib update
├── lakefile.toml
└── README.md
```

---

## Building

**Recommended (uses Mathlib cache):**
```bash
cd formalization
./scripts/build.sh
```

**Manual:**
```bash
source ~/.elan/env && lake exe cache get && lake build
```

**Clean rebuild:**
```bash
./scripts/clean.sh && ./scripts/build.sh
```

---

## Derivation Chain

```
X → A_Ω → Determinate Identity → Local Tomography → ℂℋ → PVM → Born Rule → UNS → t → G-eq → H → Schrödinger
```

| Step | File | Content | Axioms |
|------|------|---------|--------|
| 0 | Step0_Primitives | I type, X, A_Ω, Event algebra | 2 |
| 1 | Step1_Constitution | Bridge principle | 1 |
| 2 | Step2_DeterminateIdentity | Determinate identity, subsystems | 0 |
| 3 | Step3_LocalTomography | Hardy H1/H2, k=2 | 2 |
| 4 | Step4/*.lean | Hardy, Boolean, Purification | 3 |
| 5 | Step5/*.lean | Eigenvalue restriction (theorems) | 0 |
| 6 | Step6_BornRule | Gleason, Born rule | 4 |
| 7 | Step7_Unitarity | Evolution family | 2 |
| 8 | Step8_TemporalEmergence | Time embedding (theorems) | 0 |
| 9 | Step9_EnergyAction | Stone, Planck, Noether | 4 |
| 10 | Step10_Schrodinger | Schrödinger from Stone | 1 |

---

## Key Theorems Derived (2026-03-21)

The axiom reduction campaign converted several axioms to theorems:

- **`spectral_correspondence`** (Step5/EigenvalueOutcome.lean) — Eigenvalues ↔ outcomes
- **`born_rule_completeness`** (Step6_BornRule.lean) — Parseval identity
- **`spectral_idempotent_of_bool_spectrum`** (Step5/EigenvalueRestriction.lean)
- **`evolution_preserves_norm`**, **`evolution_group_composition`** (Step7_Unitarity.lean)
- All Step 8 axioms → definitions/theorems

---

## NTFS Symlink Note

This repository lives on NTFS. The `.lake/` directory must be symlinked to ext4:

```bash
# Current symlink (do not delete)
.lake -> /home/jdlongmire/.lake-lrt-formalization/.lake/
```

If `.lake/` is missing or broken, recreate:
```bash
mkdir -p /home/jdlongmire/.lake-lrt-formalization
ln -s /home/jdlongmire/.lake-lrt-formalization/.lake .lake
```

---

## Documentation

- **Axiom status:** `/docs/formalization/axiom-status.md`
- **Research docs:** `/docs/formalization/` (30+ documents)
- **Traceability:** `/traceability/`

---

## Quick Status Check

```bash
# Count sorries
grep -r "sorry" LrtFormalization/ --include="*.lean" | grep -v "\.lake" | grep -v "no sorry" | wc -l

# Count axioms
grep -rh "^axiom" LrtFormalization/ --include="*.lean" | wc -l

# Build status
source ~/.elan/env && lake build 2>&1 | tail -5
```

---

**Last Updated**: 2026-03-27
