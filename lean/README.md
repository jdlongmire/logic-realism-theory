# LogicRealismTheory - Lean 4 Formal Proofs

Formal verification of Logic Realism Theory using Lean 4 and Mathlib.

---

## Quick Links

- **Main Theory Paper**: [`../theory/Logic-realism-theory-foundational.md`](../theory/Logic-realism-theory-foundational.md)
- **Experimental Protocols**: [`../theory/predictions/`](../theory/predictions/) (Path 3 T1 vs T2)
- **QuTiP Validation**: [`../notebooks/Path3_T1_vs_T2_QuTiP_Validation.ipynb`](../notebooks/Path3_T1_vs_T2_QuTiP_Validation.ipynb)
- **Development Protocol**: `DEVELOPMENT.md` (CI/CD for Lean modules)
- **Session History**: [`../Session_Log/`](../Session_Log/)

---

## Structure

```
lean/
├── LogicRealismTheory.lean     ← ROOT: Imports all modules
├── DEVELOPMENT.md               ← CI/CD protocol
├── lakefile.lean                ← Build configuration
└── LogicRealismTheory/
    ├── Foundation/              ← Core definitions
    │   ├── IIS.lean            (Infinite Information Space)
    │   └── Actualization.lean  (Selection by logical operators)
    ├── Operators/               ← Logical operators
    │   └── Projectors.lean     (3FLL projectors)
    └── Derivations/             ← Derived results
        ├── Energy.lean
        ├── TimeEmergence.lean
        └── RussellParadox.lean
```

---

## Current Status

**Build Status**: Run `lake build` to verify
**Sorry Count**: 0 (all proofs complete in main build)
**Axiom Count**: 6 total (2 foundation + 4 established principles)
- **Foundation**: I exists, I infinite
- **Derivations**: Stone's theorem, Jaynes MaxEnt, Spohn's inequality, Energy additivity
- **Complete Documentation**: See [`AXIOMS.md`](AXIOMS.md) for full axiom inventory and justification
**Development**: See [`DEVELOPMENT.md`](DEVELOPMENT.md) for CI/CD protocol
**Last Updated**: 2025-10-29

---

## Quick Start

```bash
# Clone repository
git clone https://github.com/jdlongmire/logic-realism-theory
cd logic-realism-theory/lean

# Update dependencies
lake update

# Build project
lake build
```

---

## Integration with Experimental Work

This Lean codebase provides formal proofs for LRT's mathematical framework.

**Experimental Testing**: [`../theory/predictions/`](../theory/predictions/)
- **Path 3** (Primary): T1 vs T2 comparison protocol
- **Status**: Simulation-validated, ready for team re-review
- **Latest Work**: [Session 3.6](../Session_Log/Session_3.6.md)

---

## Related Documentation

- **Theory**: [`../theory/Logic-realism-theory-foundational.md`](../theory/Logic-realism-theory-foundational.md)
- **Protocols**: [`../theory/predictions/`](../theory/predictions/)
- **Sessions**: [`../Session_Log/`](../Session_Log/)
- **Multi-LLM**: [`../multi_LLM/README.md`](../multi_LLM/README.md)

---

**Last Updated**: 2025-10-27 (Session 3.6)
**Lean Version**: 4.25.0-rc2 (managed by elan)
**Dependencies**: Mathlib (Hilbert space theory, classical logic)
