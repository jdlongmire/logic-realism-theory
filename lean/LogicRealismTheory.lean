-- This module serves as the root of the `LogicRealismTheory` library.
-- Import modules here that should be built as part of the library.
--
-- PROTOCOL: This file must be kept updated during development.
-- All new Lean files should be added here (or explicitly documented as experimental).
-- See CLAUDE.md for development protocols.

-- ═══════════════════════════════════════════════════════════════════════════
-- FOUNDATION MODULES
-- ═══════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.Foundation.IIS
import LogicRealismTheory.Foundation.Actualization
import LogicRealismTheory.Foundation.QubitKMapping
import LogicRealismTheory.Foundation.ConstraintThreshold

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
-- CURRENT MAIN BUILD STATUS
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Build status: ✅ SUCCESS (refactoring COMPLETE - Session 5.3 Phase 2)
-- Imported modules: 10 active (all measurement modules now included!)
--   Foundation: IIS, Actualization, QubitKMapping, ConstraintThreshold
--   Operators: Projectors
--   Derivations: Energy, TimeEmergence, RussellParadox
--   Measurement: MeasurementGeometry, NonUnitaryEvolution
--
-- Refactoring Complete (Phase 2):
--   ✅ ConstraintThreshold.lean created with base definitions (Phase 1)
--   ✅ MeasurementGeometry.lean refactored - removed 4 duplicates (Phase 1)
--   ✅ NonUnitaryEvolution.lean refactored - removed 13 duplicates (Phase 2)
--   ✅ All measurement modules now use ConstraintThreshold
--   ✅ 0 duplicate definition errors
--   📦 Common.lean - orphaned (will be archived, all duplicates now eliminated)
--
-- Sorry count: 4 total (active build)
--   MeasurementGeometry.lean: 1 sorry
--   NonUnitaryEvolution.lean: 3 sorry
--
-- Axiom count: TBD (needs audit - previous count of 51 may be outdated)
--
-- Linter warnings: ⚠️ 26 unused variable warnings (non-blocking)
--   Energy.lean: 11 warnings
--   TimeEmergence.lean: 13 warnings
--   QubitKMapping.lean: 2 warnings
--
-- Next priorities:
--   1. Eliminate 1 sorry statement in MeasurementGeometry.lean
--   2. Refactor MeasurementGeometry/NonUnitaryEvolution to use Common.lean
--   3. Audit and document all axioms in lean/AXIOMS.md
--   4. Clean up 26 unused variable warnings
--
-- Last verified: 2025-10-30 (Session 5.2)
