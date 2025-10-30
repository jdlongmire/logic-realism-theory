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
-- Imported modules: 9 (all modules active)
-- Axiom count: 51 (2 IIS + 2 QubitKMapping + 5 Energy + 6 TimeEmergence + 23 MeasurementGeometry + 12 NonUnitaryEvolution + 1 RussellParadox)
-- Sorry count: 3 (all in NonUnitaryEvolution)
-- Build status: FAILED (MeasurementGeometry compilation errors)
--
-- Sprint 11 (PLANNED): Lean Proof Cleanup
-- Objective 1: Fix MeasurementGeometry.lean compilation errors
-- Objective 2: Eliminate 3 sorry statements in NonUnitaryEvolution.lean
-- Objective 3: Audit and justify all 51 axioms per AXIOMS.md approach
-- Objective 4: Achieve clean build with justified axioms only
--
-- Last verified: 2025-10-29
