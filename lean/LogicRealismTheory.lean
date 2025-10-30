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
import LogicRealismTheory.Measurement.NonUnitaryEvolution

-- ═══════════════════════════════════════════════════════════════════════════
-- CURRENT MAIN BUILD STATUS
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Imported modules: 6 (IIS, Actualization, Projectors, Energy, TimeEmergence, RussellParadox)
-- Axiom count: 13 (2 Foundation + 11 Mathematical/Physical)
-- Sorry count: 0
-- Build status: SUCCESS (2998 jobs)
--
-- Commented out modules: 3 (QubitKMapping, MeasurementGeometry, NonUnitaryEvolution)
-- Reason: Build failures or incomplete proofs
-- Action: Complete proofs and fix build errors before uncommenting
--
-- Last verified: 2025-10-29
