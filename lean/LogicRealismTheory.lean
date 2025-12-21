/-
Logic Realism Theory - Lean 4 Formalization

Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0

This module serves as the root of the `LogicRealismTheory` library.

## Current Status

Active development paused. ExternalTheorems.lean contains established
mathematical results (Tier 2 axioms) that may be useful for future work.

Previous formalization work archived: lean/archive/2025-12-21_LogicRealismTheory/

## Axiom Documentation

See lean/AXIOMS.md for the complete 3-tier classification system.

-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- TIER 0: PRIMITIVES (Self-Grounding)
-- ═══════════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.D0_1_ThreeFundamentalLaws

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
-- Active modules: 2
--   - D0_1_ThreeFundamentalLaws.lean (Tier 0 - L₃ primitives)
--   - ExternalTheorems.lean (Tier 2 established math)
--
-- Archived (2025-12-21): Foundation/, Dynamics/, Measurement/, Reconstruction/
--   Location: lean/archive/2025-12-21_LogicRealismTheory/
--
-- Last updated: 2025-12-21 (Session 49.0)
--
