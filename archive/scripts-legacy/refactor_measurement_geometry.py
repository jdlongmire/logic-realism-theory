#!/usr/bin/env python3
"""
Refactor MeasurementGeometry.lean to import Common.lean and remove duplicates.
"""

with open('lean/LogicRealismTheory/Measurement/MeasurementGeometry.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Find the last Mathlib import line
last_import_idx = None
for i, line in enumerate(lines):
    if line.startswith('import Mathlib'):
        last_import_idx = i

if last_import_idx is None:
    print('ERROR: Could not find Mathlib imports')
    exit(1)

print(f'Last Mathlib import at line {last_import_idx + 1}')

# Add Common.lean import after last Mathlib import
new_import = 'import LogicRealismTheory.Measurement.Common\n'
lines.insert(last_import_idx + 1, new_import)

print(f'Added import LogicRealismTheory.Measurement.Common at line {last_import_idx + 2}')

# Find the start and end of duplicate definitions section
# Start: "-- Axiomatize Set cardinality" (line ~79)
# End: "/-! ## Quantum states before and after measurement" (line ~160)

dup_start = None
dup_end = None

for i, line in enumerate(lines):
    if '-- Axiomatize Set cardinality' in line and dup_start is None:
        dup_start = i
    if '/-! ## Quantum states before and after measurement' in line and dup_end is None:
        dup_end = i
        break

if dup_start is None or dup_end is None:
    print(f'ERROR: Could not find duplicate section boundaries')
    print(f'dup_start: {dup_start}, dup_end: {dup_end}')
    exit(1)

print(f'Duplicate section found: lines {dup_start + 1} to {dup_end}')
print(f'Removing {dup_end - dup_start} lines')

# Remove duplicate lines
new_lines = lines[:dup_start] + lines[dup_end:]

# Write back
with open('lean/LogicRealismTheory/Measurement/MeasurementGeometry.lean', 'w', encoding='utf-8') as f:
    f.writelines(new_lines)

print(f'\nSUCCESS: Refactored MeasurementGeometry.lean')
print(f'- Added import Common.lean')
print(f'- Removed {dup_end - dup_start} duplicate lines')
print(f'- New file size: {len(new_lines)} lines (was {len(lines)})')
