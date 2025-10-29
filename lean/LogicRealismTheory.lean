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

-- Foundation.QubitKMapping: COMMENTED OUT - Build fails (rewrite tactic error at line 435)
-- Uncomment when fixed. Contains 2 axioms for qubit-K mapping.
-- import LogicRealismTheory.Foundation.QubitKMapping

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

-- Measurement.MeasurementGeometry: COMMENTED OUT - Contains 24 axioms (not yet documented in AXIOMS.md)
-- Status: Compiles successfully but needs axiom documentation review
-- import LogicRealismTheory.Measurement.MeasurementGeometry

-- Measurement.NonUnitaryEvolution: COMMENTED OUT - Contains 3 sorry statements + 13 axioms
-- Status: Work in progress, incomplete proofs at lines 141, 193, 211
-- import LogicRealismTheory.Measurement.NonUnitaryEvolution

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
