# LRT Traceability System

Claim-control architecture for the Logic Realism Theory program.

## Purpose

This system makes every meaningful statement in LRT traceable across:
- Prose (papers, documentation)
- Lean formalization
- Imported mathematics
- Bridge principles
- Open problems
- Predictions

## Structure

```
traceability/
├── claims/           # One YAML file per claim
│   ├── ONT-001.yaml  # Primitive ontic state X
│   ├── QM-006.yaml   # Boolean spectrum bridge
│   └── ...
├── schemas/
│   └── claim.schema.yaml
├── scripts/
│   └── build.py      # Generate reports
├── generated/        # Auto-generated outputs
│   ├── claims.json
│   ├── dependency-graph.json
│   ├── dependency-graph.mmd
│   ├── coverage-report.md
│   └── risk-report.md
├── index.yaml        # Registry index
└── README.md
```

## Claim Prefixes

| Prefix | Meaning |
|--------|---------|
| ONT | Ontological primitives |
| LOG | Logical constraints |
| ACT | Actualization/constitution |
| QM | Quantum reconstruction chain |
| PHY | Dynamics/temporal structure |
| INT | Interpretive consequences |
| PRD | Empirical predictions |
| OPN | Open problems |
| EXT | Imported external theorems |

## Status Fields

### proof_status
- `verified` — Lean-proven theorem
- `axiomatized` — Lean axiom or sorry
- `imported` — External theorem used without re-proof
- `prose_only` — Argued in text, no formalization
- `open` — Not yet addressed

### epistemic_status
- `established` — Well-grounded, minimal dispute
- `argued` — Supported by argument, could be challenged
- `conjectured` — Plausible but uncertain
- `open` — No current position

## Usage

Generate all reports:
```bash
cd traceability
python scripts/build.py --all
```

Generate specific outputs:
```bash
python scripts/build.py --json      # claims.json
python scripts/build.py --graph     # dependency graph
python scripts/build.py --coverage  # coverage report
python scripts/build.py --risk      # risk assessment
```

## Core Derivation Chain

```
ONT-001  X ≡ [L₃ : I∞ : A]
   ↓
ACT-001  X grounds AΩ (bridge)
   ↓
LOG-001  Determinate Identity
   ↓
LOG-002  Physical Proposition Criterion
   ↓
QM-001/002  H1/H2 → Local Tomography
   ↓
EXT-001  Hardy Reconstruction (imported)
   ↓
QM-004  Complex Hilbert Space
   ↓
QM-005/006  Boolean Actualization → Spectrum Bridge
   ↓
QM-007  PVM Structure
   ↓
EXT-002  Gleason Theorem (imported)
   ↓
QM-008  Born Rule
   ↓
PHY-001  Unitarity
   ↓
EXT-003  Stone Theorem (imported)
   ↓
PHY-003  Hamiltonian Generator
   ↓
PHY-004  Schrödinger Equation
```

## Critical Choke Points

1. **ACT-001**: Bridge Principle (X grounds AΩ)
   - Philosophically argued, not logically forced
   - Risk: high

2. **QM-006**: Boolean Spectrum Bridge
   - Eigenvalue-measurement connection
   - Risk: high

3. **QM-001**: H1 Derivation
   - Structure exists, bridge to StateSpace incomplete
   - Risk: medium

## Governance Rules

1. Every major claim in prose must have a claim ID
2. Every Lean theorem that matters must reference a claim ID
3. No claim is "proved" unless `proof_status: verified`
4. Axiomatized claims remain visibly labeled
5. Imported mathematics must cite primary source
6. Open problems must not mix with established derivations
7. Predictions must identify exact dependencies
