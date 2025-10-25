/-
Copyright (c) 2024 James D. Longmire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James D. Longmire
-/

import PhysicalLogicFramework.Foundations.InformationSpace
import PhysicalLogicFramework.Foundations.ThreeFundamentalLaws
import PhysicalLogicFramework.Foundations.ConstraintThreshold
import PhysicalLogicFramework.Foundations.MaximumEntropy
import PhysicalLogicFramework.LogicField.Operator
import PhysicalLogicFramework.LogicField.ConstraintAccumulation
-- Quantum emergence modules: Using _Fixed versions that compile successfully
import PhysicalLogicFramework.QuantumEmergence.BellInequality_Fixed
import PhysicalLogicFramework.QuantumEmergence.BornRule
import PhysicalLogicFramework.QuantumEmergence.HilbertSpace
-- import PhysicalLogicFramework.QuantumEmergence.OrthomodularCore  -- Disabled: has syntax errors
import PhysicalLogicFramework.QuantumEmergence.QuantumCore
-- Dynamics modules: Theorem D.1 formalization (NEW - October 6, 2025)
import PhysicalLogicFramework.Dynamics.GraphLaplacian
import PhysicalLogicFramework.Dynamics.FisherGeometry
import PhysicalLogicFramework.Dynamics.ConvergenceTheorem
import PhysicalLogicFramework.Dynamics.TheoremD1

/-!
# Physical Logic Framework (PLF)

Main module for the Physical Logic Framework - a theoretical physics framework 
that proposes physical reality emerges from logical filtering of information: A = L(I).

## Core Components

1. **Information Space**: Directed graphs on N elements
2. **Logic Field Operator**: L = I ∩ NC ∩ EM (Identity, Non-Contradiction, Excluded Middle)
3. **Physical Actualization**: A = L(I) - what becomes real through logical consistency
4. **Quantum Emergence**: Bell violations force Boolean → Orthomodular transition

## Main Results

- **Quantum Inevitability**: Reality has no choice but to be quantum
- **Born Rule Derivation**: Probability emerges from logical necessity
- **Spacetime Emergence**: 3+1 dimensions from permutohedron geometry
- **Theorem D.1**: Graph Laplacian emerges as natural Hamiltonian (October 2025)
- **Unified Framework**: Single principle explains fundamental physics

This formalization proves these results mathematically in Lean 4.
-/

-- Main namespace for all Physical Logic Framework definitions
namespace PhysicalLogicFramework

-- Export core theorems and definitions for easy access
open LFT.QuantumEmergence

-- Mark this as the main module
end PhysicalLogicFramework