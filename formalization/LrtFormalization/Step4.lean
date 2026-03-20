/-
  Logic Realism Theory — Step 4: Hilbert Space Structure

  Main import file for Step 4 submodules.

  **Contents:**
  - Step4.Hardy: Hilbert space from CP(H), states as rays, observables
  - Step4.Boolean: Boolean actualization → projection bridge (Phase 4 hinge)
  - Step4.Purification: Boolean → purification route to K=2 (OPN-005)

  **Derivation chain role:**
  Step 3 (Local Tomography) → **Step 4 (Hilbert Structure)** → Step 5 (Eigenvalue Restriction)

  Author: James D. Longmire
  Date: 2026-03-17
  Status: Foundation
-/

import LrtFormalization.Step4.Hardy
import LrtFormalization.Step4.Boolean
import LrtFormalization.Step4.Purification

/-! ## Namespace Re-exports

For backward compatibility, we re-export key definitions at the LRT.Step4 level.
-/

namespace LRT.Step4

-- Re-export from Hardy
export LRT.Step4.Hardy (
  QuantumStateSpace
  IsStateVector
  PhaseEquivalent
  Ray
  Observable
  MeasurementOutcome
  CompleteMeasurement
  TransitionAmplitude
  TransitionProbability
  MeasurementProbability
  step4_hilbert_space
)

-- Re-export from Boolean
export LRT.Step4.Boolean (
  isSharp
  all_events_sharp
  EventRepresentation
  RepresentsBooleanActualization
  event_operator_boolean_spectrum
  event_operator_is_projection
  PVM
  phase4_boolean_bridge
)

-- Re-export from Purification
export LRT.Step4.Purification (
  PurificationHolds
  BleachingOperation
  no_hiding_theorem
  information_conservation
  boolean_implies_purification
  boolean_plus_nohiding_implies_purification
  k2_via_purification
  local_tomography_purification_k2_chain
  moretti_oppio_k2
  gleason_d2_via_composite
  k2_via_poincare
  k2_via_tensor_consistency
)

end LRT.Step4
