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
-- Temporarily commented out due to duplicate definitions with MeasurementGeometry
-- TODO (Sprint 11): Refactor shared measurement definitions into common module
-- import LogicRealismTheory.Measurement.NonUnitaryEvolution

-- ═══════════════════════════════════════════════════════════════════════════
-- CURRENT MAIN BUILD STATUS
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Build status: ✅ SUCCESS (refactoring in progress - Session 5.3)
-- Imported modules: 9 active (after refactoring)
--   Foundation: IIS, Actualization, QubitKMapping, ConstraintThreshold
--   Operators: Projectors
--   Derivations: Energy, TimeEmergence, RussellParadox
--   Measurement: MeasurementGeometry (refactored to use ConstraintThreshold)
--
-- Refactoring Progress:
--   ✅ ConstraintThreshold.lean created with base definitions
--   ✅ MeasurementGeometry.lean refactored to import ConstraintThreshold
--   ⏳ NonUnitaryEvolution.lean - needs refactoring to avoid duplicates
--   ⏳ Common.lean - orphaned (may be archived after NonUnitaryEvolution fixed)
--
-- Sorry count: 1 (active build only)
--   MeasurementGeometry.lean: 1 sorry
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
