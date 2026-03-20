/-
Logic Realism Theory - Lean 4 Formalization

Copyright © 2025-2026 James D. (JD) Longmire
License: Apache License 2.0

This module serves as the root of the `LogicRealismTheory` library.

## Current Status

Active development resumed. Core derivation steps being formalized:
- D0: Tier 0 primitives (L₃, I∞)
- D1: Tier 1 structural consequences (Local Tomography, UNS)

## Axiom Documentation

See lean/AXIOMS.md for the complete 3-tier classification system.

-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- TIER 0: PRIMITIVES (Self-Grounding)
-- ═══════════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.D0_1_ThreeFundamentalLaws
import LogicRealismTheory.D0_2_InformationSpace

-- ═══════════════════════════════════════════════════════════════════════════════
-- TIER 1: STRUCTURAL CONSEQUENCES
-- ═══════════════════════════════════════════════════════════════════════════════
-- Derivations from Tier 0 primitives

import LogicRealismTheory.D1_3_LocalTomography    -- Step 3: H1→H2 bridge
import LogicRealismTheory.D1_8_UniqueNextState    -- Step 8: UNS theorem

-- ═══════════════════════════════════════════════════════════════════════════════
-- TIER 2: EXTERNAL THEOREMS (Established math tools)
-- ═══════════════════════════════════════════════════════════════════════════════
-- All external mathematical results are localized in this module.
-- See lean/AXIOMS.md for documentation.

import LogicRealismTheory.ExternalTheorems

-- ═══════════════════════════════════════════════════════════════════════════════
-- BUILD STATUS
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- Active modules: 5
--   - D0_1_ThreeFundamentalLaws.lean (Tier 0 - L₃ primitives)
--   - D0_2_InformationSpace.lean (Tier 0 - I∞ primitives)
--   - D1_3_LocalTomography.lean (Tier 1 - H1→H2 bridge, Step 3)
--   - D1_8_UniqueNextState.lean (Tier 1 - UNS theorem, Step 8)
--   - ExternalTheorems.lean (Tier 2 - established math)
--
-- Archived: lean/archive/
--
-- Last updated: 2026-03-13
--
