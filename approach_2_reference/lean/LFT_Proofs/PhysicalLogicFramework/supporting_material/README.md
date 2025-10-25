# Supporting Materials

This directory contains supporting materials for the Physical Logic Framework Lean formalization that are not directly part of the core proof modules.

## Directory Structure

### `tests/`
Test files, namespace tests, integration tests, and demo files used during development:
- `Core_Framework_Status.lean` - Framework status tracking
- `Integration_Test.lean` - Integration testing
- `LFT_Achievement_Summary.lean` - Achievement documentation
- `NamespaceTest.lean` - Root namespace test
- `QuantumEmergence_NamespaceTest.lean` - QuantumEmergence namespace test
- `ScopingSuccess.lean` - Scoping test
- `Working_Core_Demo.lean` - Working demo file

### `early_versions/`
Earlier versions of modules that have been superseded by current implementations:
- `FeasibilityRatio.lean` - Early constraint theory (superseded by `Foundations/ConstraintThreshold.lean`)
- `PermutationGeometry.lean` - Early geometric structure (functionality now in multiple modules)
- `QuantumBridge.lean` - Early quantum bridge (superseded by `QuantumEmergence/` modules)
- `InformationSpace_OLD_BINARY.lean` - Old binary-based information space (superseded by current `InformationSpace.lean`)

### `exploratory/`
Exploratory proofs and research investigations not yet integrated into main modules:
- `BellInequality.lean` - Early Bell inequality work (superseded by `BellInequality_Fixed.lean`)
- `OrthomodularCore.lean` - Orthomodular structure exploration (has syntax errors, disabled)
- `OrthomodularStructure.lean` - Orthomodular lattice research
- `QuantumInevitability.lean` - Quantum inevitability proof exploration
- `QuantumInevitabilityCore.lean` - Core quantum inevitability concepts
- `QuantumInevitabilityFixed.lean` - Fixed version of inevitability proof
- `QuantumInevitabilitySimple.lean` - Simplified inevitability approach

## Core Proof Modules

The main proof modules (not in this directory) are organized as:

**Foundations/** - Core mathematical foundations
- `InformationSpace.lean` - Information space definitions
- `ThreeFundamentalLaws.lean` - Logical axioms (ID, NC, EM)
- `ConstraintThreshold.lean` - K(N) = N-2 theorem ✅ (0 sorrys)
- `MaximumEntropy.lean` - MaxEnt → Born rule ✅ (0 sorrys)

**LogicField/** - Logic field operator theory
- `Operator.lean` - L operator definition
- `ConstraintAccumulation.lean` - Constraint accumulation theory

**QuantumEmergence/** - Quantum mechanics emergence
- `BellInequality_Fixed.lean` - Bell inequality results
- `BornRule.lean` - Born rule derivation
- `HilbertSpace.lean` - Hilbert space structure
- `QuantumCore.lean` - Core quantum definitions

**Dynamics/** - Quantum dynamics (Theorem D.1)
- `GraphLaplacian.lean` - Graph Laplacian formalization
- `FisherGeometry.lean` - Fisher/Fubini-Study geometry
- `ConvergenceTheorem.lean` - Laplace-Beltrami convergence
- `TheoremD1.lean` - Complete Theorem D.1 synthesis

## Relationship to Main Paper

The core proof modules directly support the main paper "Logic Field Theory I: Quantum Probability" and related research. Supporting materials here represent:
1. Development history and evolution of ideas
2. Alternative approaches explored
3. Testing and validation infrastructure
4. Future research directions not yet formalized

## Status

**Core modules**: Production-ready proofs supporting paper submission
**Supporting materials**: Historical record and research exploration
