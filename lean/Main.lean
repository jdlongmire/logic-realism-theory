-- Main entry point for LogicRealismTheory project
-- Imports the complete theory for building

import LogicRealismTheory

-- This allows `lake build` to work without specifying the module name
-- The actual theory is in LogicRealismTheory.lean (root import file)

def main : IO Unit := do
  IO.println "LogicRealismTheory - Lean 4 Formalization"
  IO.println "Main build imports all modules from LogicRealismTheory.lean"
