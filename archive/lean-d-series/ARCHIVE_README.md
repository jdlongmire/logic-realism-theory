# D-Series Lean Formalization (Archived)

**Archive Date:** 2026-03-20

**Status:** Superseded by `formalization/` (Step-series)

---

## Background

This directory contains the D-series Lean formalization of Logic Realism Theory, which used file naming convention `D0_1_*.lean`, `D1_3_*.lean`, etc.

**Toolchain:** Lean 4 v4.25.0-rc2

The D-series has been superseded by the Step-series formalization in `/formalization/`, which:
- Uses toolchain v4.28.0
- Follows a cleaner Step1-Step6 derivation chain structure
- Contains the authoritative axiom audit and traceability artifacts

---

## Directory Contents

| Item | Description |
|------|-------------|
| `LogicRealismTheory/` | Main source files (D-series naming) |
| `archive/` | Earlier iteration archives within D-series |
| `lakefile.toml` | Lake build configuration |
| `lake-manifest.json` | Dependency manifest |
| `lean-toolchain` | Toolchain version (v4.25.0-rc2) |
| `AXIOMS.md` | D-series axiom documentation |
| `AI_ROLE.md`, `BEST_PRACTICES.md` | Collaboration guidelines |
| `.github/` | CI configuration (no longer active) |

---

## Build Environment Note

The D-series required a `.lake` symlink to ext4 filesystem because the repo lives on NTFS:

```
.lake -> /home/jdlongmire/.lake-lrt/.lake/
```

This symlink is no longer needed and has been removed. The ext4 directory may still exist at `/home/jdlongmire/.lake-lrt/.lake/` but can be cleaned up.

---

## Current Authoritative Formalization

The authoritative Lean formalization is now:

```
/formalization/
```

See `/docs/formalization/axiom-status.md` for current axiom counts and build status.

---

*Archived as part of repo consolidation. For historical reference only.*
