#!/usr/bin/env python3
"""
Refactor MeasurementGeometry.lean to import ConstraintThreshold.

Removes duplicate definitions and adds import of Foundation.ConstraintThreshold.
"""

import re

# Read the file
with open('lean/LogicRealismTheory/Measurement/MeasurementGeometry.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Step 1: Add import after the existing Mathlib imports (after line 12)
old_imports = """import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic"""

new_imports = """import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import LogicRealismTheory.Foundation.ConstraintThreshold"""

content = content.replace(old_imports, new_imports)

# Step 2: Remove the Set.card axiom (lines 79-80)
content = re.sub(
    r'-- Axiomatize Set cardinality \(not available in current Mathlib\)\naxiom Set\.card \{α : Type\*\} : Set α → ℕ\n\n',
    '',
    content
)

# Step 3: Add open Foundation after namespace declaration
old_namespace = """namespace LogicRealismTheory.Measurement

open Complex
open Matrix"""

new_namespace = """namespace LogicRealismTheory.Measurement

open Complex
open Matrix
open LogicRealismTheory.Foundation"""

content = content.replace(old_namespace, new_namespace)

# Step 4: Remove the duplicate ConstraintViolations axiom (lines 91-97)
content = re.sub(
    r'/--\nConstraint violations for configuration σ\.\nMeasures how many logical constraints \(Identity, Non-Contradiction\) are violated\.\n\n\*\*TODO\*\*: Replace axiom with computed function from QubitKMapping \(Track 1\.2\)\n-/\naxiom ConstraintViolations \{V : Type\*\} : V → ℕ\n\n',
    '',
    content
)

# Step 5: Remove the duplicate StateSpace definition (lines 99-103)
content = re.sub(
    r'/--\nState space for constraint threshold K\.\nContains all configurations with at most K constraint violations\.\n-/\ndef StateSpace \{V : Type\*\} \(K : ℕ\) : Set V := \{σ : V \| ConstraintViolations σ ≤ K\}\n\n',
    '',
    content
)

# Step 6: Remove the duplicate statespace_monotone axiom (lines 105-107)
content = re.sub(
    r'/-- State space inclusion: V_\{K\'\} ⊆ V_K when K\' ≤ K -/\naxiom statespace_monotone \{V : Type\*\} \{K K\' : ℕ\} \(h : K\' ≤ K\) :\n  \(StateSpace K\' : Set V\) ⊆ \(StateSpace K : Set V\)\n\n',
    '',
    content
)

# Write back
with open('lean/LogicRealismTheory/Measurement/MeasurementGeometry.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print("[OK] Added import of Foundation.ConstraintThreshold")
print("[OK] Added open Foundation namespace")
print("[OK] Removed Set.card axiom (now in ConstraintThreshold)")
print("[OK] Removed ConstraintViolations axiom (now in ConstraintThreshold)")
print("[OK] Removed StateSpace definition (now in ConstraintThreshold)")
print("[OK] Removed statespace_monotone axiom (now in ConstraintThreshold)")
print("\nMeasurementGeometry.lean refactored successfully!")
