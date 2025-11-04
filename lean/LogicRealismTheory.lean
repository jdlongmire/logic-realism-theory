-- This module serves as the root of the `LogicRealismTheory` library.
-- Import modules here that should be built as part of the library.
--
-- PROTOCOL: This file must be kept updated during development.
-- All new Lean files should be added here (or explicitly documented as experimental).
-- See CLAUDE.md for development protocols.

-- ═══════════════════════════════════════════════════════════════════════════
-- FOUNDATION MODULES
-- ═══════════════════════════════════════════════════════════════════════════

-- Layer 1: Core IIS and Actualization
import LogicRealismTheory.Foundation.IIS
import LogicRealismTheory.Foundation.Actualization

-- Layer 2: Metric Structure and Qubit Mappings
import LogicRealismTheory.Foundation.QuotientMetric
import LogicRealismTheory.Foundation.Distinguishability
import LogicRealismTheory.Foundation.QubitKMapping
import LogicRealismTheory.Foundation.ConstraintThreshold
import LogicRealismTheory.Foundation.ComplexFieldForcing

-- Layer 3: Quantum Mathematical Structure (Hilbert Space Framework)
import LogicRealismTheory.Foundation.InnerProduct
import LogicRealismTheory.Foundation.HilbertSpace
import LogicRealismTheory.Foundation.TensorProducts
import LogicRealismTheory.Foundation.UnitaryOperators
import LogicRealismTheory.Foundation.HermitianOperators

-- ═══════════════════════════════════════════════════════════════════════════
-- OPERATOR MODULES
-- ═══════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.Operators.Projectors

-- ═══════════════════════════════════════════════════════════════════════════
-- DERIVATION MODULES
-- ═══════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.Derivations.Energy
import LogicRealismTheory.Derivations.TimeEmergence
import LogicRealismTheory.Derivations.RussellParadox

-- ═══════════════════════════════════════════════════════════════════════════
-- DYNAMICS MODULES
-- ═══════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.Dynamics.DynamicsFromSymmetry

-- ═══════════════════════════════════════════════════════════════════════════
-- MEASUREMENT MODULES (EXPERIMENTAL - Contains sorry statements)
-- ═══════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.Measurement.NonCircularBornRule
import LogicRealismTheory.Measurement.MeasurementGeometry
import LogicRealismTheory.Measurement.NonUnitaryEvolution

-- ═══════════════════════════════════════════════════════════════════════════
-- LAYER SUMMARIES
-- ═══════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.Layer3

-- ═══════════════════════════════════════════════════════════════════════════
-- CURRENT MAIN BUILD STATUS
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Build status: ✅ SUCCESSFUL (type checking and syntax validation)
-- ⚠️ Formal verification: 0% complete (axiom structure only, NOT formal proofs)
-- Total Lean files: 22 active (1 deprecated)
-- Total lines: ~2,300 imported (~1,291 Session 8.1 files NOT imported - orphaned)
-- Build jobs: 6096 (successful compilation)
--
-- Imported modules: 22 active
--   Foundation (11):
--     Layer 1: IIS, Actualization
--     Layer 2: QuotientMetric, Distinguishability, QubitKMapping,
--              ConstraintThreshold, ComplexFieldForcing
--     Layer 3: InnerProduct, HilbertSpace, TensorProducts,
--              UnitaryOperators, HermitianOperators
--   Operators (1): Projectors
--   Derivations (3): Energy, TimeEmergence, RussellParadox
--   Dynamics (1): DynamicsFromSymmetry (Sprint 11 Track 3)
--   Measurement (3): NonCircularBornRule (Track 2), MeasurementGeometry, NonUnitaryEvolution
--   Layer Summaries (1): Layer3
--   Deprecated (1): Measurement/Common.lean (archived)
--
-- ⚠️ NOT IMPORTED (Session 8.1 orphaned files):
--   Foundation/GeometricStructure.lean (220 lines)
--   Foundation/EMRelaxation.lean (265 lines)
--   Foundation/VectorSpaceStructure.lean (380 lines)
--   Foundation/PhysicsEnablingStructures.lean (450 lines)
--   Total orphaned: ~1,291 lines (exist but not part of build)
--
-- Recent updates (2025-11-04):
--   ✅ Sprint 12 Track 1 complete: 4 sorrys resolved (converted to documented axioms)
--   ⚠️ Status correction: Discovered overstatement of formal verification claims
--   ⚠️ Lean files contain axiom structure, NOT formal proofs (0% verification complete)
--   ✅ Verification protocol added to CLAUDE.md to prevent future misrepresentation
--   ✅ SPRINT_11_LEAN_STATUS_CORRECTION.md created (comprehensive correction document)
--
-- Gap analysis (CORRECTED 2025-11-04):
--   Proof obligations: 10 total unproven
--     Sprint 12 Track 1: 4 sorrys → 4 axioms (RESOLVED)
--     NonCircularBornRule.lean: 3 theorems with `sorry` (not proven)
--     DynamicsFromSymmetry.lean: 3 theorems proving `True` (trivial placeholders, not real proofs)
--
--   Effective axiom count: ~67 total
--     Declared axioms: 61
--       K_math: 17 (after Sprint 12 Track 1)
--       LRT_foundational: 18 (after Sprint 12 Track 1)
--       Measurement_dynamics: 18 (after Sprint 12 Track 1)
--       Computational_helper: 4
--       Physical_postulate: 1
--       Placeholder: 5 (Layer3.lean track markers)
--     Unproven theorems (count as effective axioms): +6
--       Track 2: 3 theorems with `sorry`
--       Track 3: 3 theorems proving `True`
--
-- Sprint 12 priorities (UPDATED):
--   Track 1: ✅ COMPLETE - All 4 target sorrys resolved
--   Track 2: Reduce axiom count from ~67 to ~35-38
--   Track 3: Documentation correction (session logs, README, this file)
--   Track 4: Create peer review appendices with honest status
--
-- ⚠️ IMPORTANT: See SPRINT_11_LEAN_STATUS_CORRECTION.md for full details
--
-- Last verified: 2025-11-04
