/-
Logic Realism Theory - Lean 4 Formalization

Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0

This module serves as the root of the `LogicRealismTheory` library.

## Correspondence to Technical Paper

  Longmire, J.D. (2025). "Logic Realism Theory: Technical Foundations"
  DOI: 10.5281/zenodo.17831883

## Module Structure

The formalization mirrors the Technical paper structure:
- §2 Foundations → Foundation/IIS.lean, Foundation/Actualization.lean
- §3 State Space → Foundation/StateSpace.lean
- §4 Dynamics → Dynamics/TimeEvolution.lean
- §5 Measurement → Measurement/BornRule.lean
- §5.5 Reconstruction → Reconstruction/LRTReconstruction.lean
- Appendix A → ExternalTheorems.lean

## Axiom Classification

See lean/AXIOMS.md for the complete 3-tier classification system:
- Tier 1 (LRT Specific): 2 axioms (I, I_infinite)
- Tier 2 (Established Math): 9 axioms (ExternalTheorems.lean)
- Tier 3 (Universal Physics): 1 axiom (energy_additivity)
- Total: 12 axioms

-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXTERNAL THEOREMS (Tier 2 axioms - established math tools)
-- ═══════════════════════════════════════════════════════════════════════════════
-- All external mathematical results are localized in this module.
-- See lean/AXIOMS.md and Technical paper Appendix A for documentation.

import LogicRealismTheory.ExternalTheorems

-- ═══════════════════════════════════════════════════════════════════════════════
-- FOUNDATION MODULES (§2-3)
-- ═══════════════════════════════════════════════════════════════════════════════

-- §2: Infinite Information Space and Actualization
import LogicRealismTheory.Foundation.IIS
import LogicRealismTheory.Foundation.Actualization

-- §3: State Space Emergence
import LogicRealismTheory.Foundation.StateSpace

-- ═══════════════════════════════════════════════════════════════════════════════
-- DYNAMICS MODULES (§4)
-- ═══════════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.Dynamics.TimeEvolution

-- ═══════════════════════════════════════════════════════════════════════════════
-- MEASUREMENT MODULES (§5)
-- ═══════════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.Measurement.BornRule

-- ═══════════════════════════════════════════════════════════════════════════════
-- RECONSTRUCTION (§5.5 - Master Theorem)
-- ═══════════════════════════════════════════════════════════════════════════════

import LogicRealismTheory.Reconstruction.LRTReconstruction

-- ═══════════════════════════════════════════════════════════════════════════════
-- BUILD STATUS
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- Structure: Complete (mirrors Technical paper v3)
-- Build: Pending verification
--
-- Modules: 7 active
--   - ExternalTheorems.lean (Appendix A)
--   - Foundation/IIS.lean (§2)
--   - Foundation/Actualization.lean (§2.3)
--   - Foundation/StateSpace.lean (§3)
--   - Dynamics/TimeEvolution.lean (§4)
--   - Measurement/BornRule.lean (§5)
--   - Reconstruction/LRTReconstruction.lean (§5.5)
--
-- Axiom Count:
--   - Tier 1 (LRT Specific): 2 (I, I_infinite)
--   - Tier 2 (Established Math): 9 (E1-E8, Stone, Gleason)
--   - Tier 3 (Universal Physics): 1 (energy_additivity)
--   - Total: 12 axioms
--
-- Theorems: 15+ structured (see individual module summaries)
--
-- Archive: lean/archive/LogicRealismTheory/ contains previous approach files
--
-- Last updated: 2025-12-07 (Session 38.0)
