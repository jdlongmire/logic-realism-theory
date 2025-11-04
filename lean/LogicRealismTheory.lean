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
-- MEASUREMENT MODULES (EXPERIMENTAL - Contains sorry statements)
-- ═══════════════════════════════════════════════════════════════════════════

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
-- Build status: ✅ SUCCESS (Layer 3 complete, file consolidation complete)
-- Total Lean files: 20 active (1 deprecated)
-- Total lines: 5,288
-- Build jobs: 6008
--
-- Imported modules: 20 active
--   Foundation (11):
--     Layer 1: IIS, Actualization
--     Layer 2: QuotientMetric, Distinguishability, QubitKMapping,
--              ConstraintThreshold, ComplexFieldForcing
--     Layer 3: InnerProduct, HilbertSpace, TensorProducts,
--              UnitaryOperators, HermitianOperators
--   Operators (1): Projectors
--   Derivations (3): Energy, TimeEmergence, RussellParadox
--   Measurement (2): MeasurementGeometry, NonUnitaryEvolution
--   Layer Summaries (1): Layer3
--   Deprecated (1): Measurement/Common.lean (archived)
--
-- Recent updates (2025-11-03):
--   ✅ Layer 3 quantum mathematical structure complete (5 modules)
--   ✅ File consolidation: Removed "Track" prefix from Layer 3 files
--   ✅ Consistent naming convention across all modules
--   ✅ All imports updated and verified
--   ✅ Sprint 12 plan created for verification cleanup
--
-- Gap analysis (see lean/Ongoing_Axiom_Count_Classification.md):
--   Sorry count: 4 total
--     InnerProduct.lean: 1 sorry (Jordan-von Neumann theorem)
--     NonUnitaryEvolution.lean: 3 sorrys (measurement dynamics)
--
--   Axiom count: 57 total (58 declarations - 1 false positive)
--     K_math: 16 (27.6%) - Established mathematical results
--     LRT_foundational: 14 (24.1%) - Theory-defining postulates
--     Measurement_dynamics: 15 (25.9%) - Measurement mechanism
--     Computational_helper: 4 (6.9%) - Function definitions
--     Physical_postulate: 1 (1.7%) - Energy additivity
--     Placeholder: 5 (8.6%) - Layer3.lean track markers
--
-- Sprint 12 priorities (see sprints/SPRINT_12_PLAN.md):
--   Track 1: Eliminate 4 sorrys OR document as K_math
--   Track 2: Reduce axiom count from 57 to ~35
--   Track 3: Update documentation (AXIOMS.md, Main.md Section 7)
--   Track 4: Create peer review appendices
--
-- Last verified: 2025-11-03
