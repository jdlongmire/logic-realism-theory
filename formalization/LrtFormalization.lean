/-
  Logic Realism Theory — Lean 4 Formalization

  Main import file for the LRT formalization project.

  Derivation Chain:
  X → A_Ω → Determinate Identity → Local Tomography → ℂℋ →
  PVM → Born Rule → UNS → t → G-eq → H → Schrödinger

  Author: James D. Longmire
  Date: 2026-03-13
-/

-- Foundation (Steps 0-2)
import LrtFormalization.Basic
import LrtFormalization.Step0_Primitives
import LrtFormalization.Step1_Constitution
import LrtFormalization.Step2_DeterminateIdentity

-- Tomography and Hilbert Space (Steps 3-4)
import LrtFormalization.Step3_LocalTomography
import LrtFormalization.Step4_HardyAxiom

-- Eigenvalue Restriction (Step 5)
import LrtFormalization.Step5.EigenvalueRestriction
