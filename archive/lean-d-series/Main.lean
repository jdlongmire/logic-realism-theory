-- Main.lean - Optional executable entry point
--
-- This file is a convenience wrapper that allows `lake build` to work
-- without specifying the module name.
--
-- FOR THE ACTUAL THEORY CODE, SEE:
--   - LogicRealismTheory.lean (root import file listing all modules)
--   - LogicRealismTheory/ (directory containing all source code modules)
--
-- Directory structure:
--   LogicRealismTheory/
--   ├── Foundation/     - Core theory (IIS, actualization, metric, Hilbert space)
--   ├── Operators/      - Operator definitions (projectors, etc.)
--   ├── Derivations/    - Key derivations (energy, time emergence, Russell paradox)
--   ├── Measurement/    - Measurement theory
--   └── Layer3.lean     - Layer 3 summary (quantum mathematical structure)
--
-- This Main.lean file simply imports the library and provides an executable.

import LogicRealismTheory

def main : IO Unit := do
  IO.println "LogicRealismTheory - Lean 4 Formalization"
  IO.println "See LogicRealismTheory.lean for root imports"
  IO.println "See LogicRealismTheory/ for all source code"
