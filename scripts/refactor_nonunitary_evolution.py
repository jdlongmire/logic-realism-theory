#!/usr/bin/env python3
"""
Refactor NonUnitaryEvolution.lean to import Common.lean and remove duplicates.
"""

with open('lean/LogicRealismTheory/Measurement/NonUnitaryEvolution.lean', 'r', encoding='utf-8') as f:
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

# Strategy: Remove duplicates but keep unique definitions
# Duplicates to remove:
#   1. Set.card axiom (line ~78)
#   2. ConstraintViolations axiom (line ~86)
#   3. StateSpace def (line ~88)
#   4. statespace_monotone axiom (line ~90)
#   5. MeasurementOperator structure (lines ~114-120)
#   6. measurement_is_projection axiom (line ~122)
#   7. measurement_is_hermitian axiom (line ~126)
#   8. measurement_not_unitary axiom (line ~130)
#   9. wavefunction_collapse_normalized axiom (lines ~146-153)
#  10. wavefunction_collapse_support axiom (lines ~155-162)
#  11. wavefunction_collapse def (lines ~164-...)

# Keep unique:
#   - QuantumState structure (line ~93)
#   - UnitaryOperator structure (line ~98)
#   - unitary_preserves_norm axiom (line ~104)
#   - unitary_preserves_K theorem (line ~108)
#   - measurement_reduces_K theorem (line ~135)
#   - measurement_probability def (if it exists)

# Since this is complex, let me identify sections to remove by marker lines

# Remove section 1: "-- Axiomatize Set cardinality" to "variable {V : Type*}"
remove_1_start = None
remove_1_end = None
for i, line in enumerate(lines):
    if '-- Axiomatize Set cardinality' in line and remove_1_start is None:
        remove_1_start = i
    if 'variable {V : Type*}' in line and remove_1_start is not None and remove_1_end is None:
        remove_1_end = i + 1  # Keep the variable line
        break

# Remove section 2: "axiom ConstraintViolations" to "structure QuantumState"
remove_2_start = None
remove_2_end = None
for i, line in enumerate(lines):
    if 'axiom ConstraintViolations' in line and remove_2_start is None:
        remove_2_start = i
    if 'structure QuantumState' in line and remove_2_start is not None and remove_2_end is None:
        remove_2_end = i
        break

# Remove section 3: "structure MeasurementOperator" to "theorem measurement_reduces_K"
remove_3_start = None
remove_3_end = None
for i, line in enumerate(lines):
    if 'structure MeasurementOperator' in line and remove_3_start is None:
        remove_3_start = i
    if 'theorem measurement_reduces_K' in line and remove_3_start is not None and remove_3_end is None:
        remove_3_end = i
        break

# Remove section 4: "axiom wavefunction_collapse_normalized" to end of file
# (but we need to check what comes after)
remove_4_start = None
for i, line in enumerate(lines):
    if 'axiom wavefunction_collapse_normalized' in line and remove_4_start is None:
        remove_4_start = i
        break

# Let's just do sections 1-3 for now and check the result

if None in [remove_1_start, remove_1_end, remove_2_start, remove_2_end, remove_3_start, remove_3_end]:
    print('ERROR: Could not find all section boundaries')
    print(f'Section 1: {remove_1_start}-{remove_1_end}')
    print(f'Section 2: {remove_2_start}-{remove_2_end}')
    print(f'Section 3: {remove_3_start}-{remove_3_end}')
    exit(1)

print(f'Removing section 1: lines {remove_1_start + 1} to {remove_1_end}')
print(f'Removing section 2: lines {remove_2_start + 1} to {remove_2_end}')
print(f'Removing section 3: lines {remove_3_start + 1} to {remove_3_end}')

# Build new lines by excluding removed sections
new_lines = []
i = 0
while i < len(lines):
    # Skip removed sections
    if i >= remove_1_start and i < remove_1_end:
        i = remove_1_end
        continue
    elif i >= remove_2_start and i < remove_2_end:
        i = remove_2_end
        continue
    elif i >= remove_3_start and i < remove_3_end:
        i = remove_3_end
        continue
    else:
        new_lines.append(lines[i])
        i += 1

# Now handle section 4 (wavefunction_collapse axioms and def)
# These should be imported from Common.lean
# Find and remove them from new_lines
final_lines = []
skip_until = None
for i, line in enumerate(new_lines):
    if skip_until and i < skip_until:
        continue
    skip_until = None

    # Check for wavefunction collapse related definitions
    if 'axiom wavefunction_collapse_normalized' in line:
        # Skip until we find the next non-wavefunction_collapse definition
        for j in range(i+1, len(new_lines)):
            if new_lines[j].strip() and not new_lines[j].strip().startswith('--') and \
               'wavefunction_collapse' not in new_lines[j] and \
               not new_lines[j].strip().startswith('let ') and \
               not new_lines[j].strip().startswith('∑'):
                skip_until = j
                break
        continue
    elif 'axiom wavefunction_collapse_support' in line:
        for j in range(i+1, len(new_lines)):
            if new_lines[j].strip() and not new_lines[j].strip().startswith('--') and \
               'wavefunction_collapse' not in new_lines[j] and \
               not new_lines[j].strip().startswith('let ') and \
               not new_lines[j].strip().startswith('∑'):
                skip_until = j
                break
        continue
    elif 'noncomputable def wavefunction_collapse' in line:
        for j in range(i+1, len(new_lines)):
            if new_lines[j].strip() and not new_lines[j].strip().startswith('--') and \
               'wavefunction_collapse' not in new_lines[j] and \
               not new_lines[j].strip().startswith('let ') and \
               not new_lines[j].strip().startswith('fun ') and \
               not new_lines[j].strip().startswith('ψ_'):
                skip_until = j
                break
        continue

    final_lines.append(line)

# Write back
with open('lean/LogicRealismTheory/Measurement/NonUnitaryEvolution.lean', 'w', encoding='utf-8') as f:
    f.writelines(final_lines)

print(f'\nSUCCESS: Refactored NonUnitaryEvolution.lean')
print(f'- Added import Common.lean')
print(f'- Removed duplicate definitions')
print(f'- New file size: {len(final_lines)} lines (was {len(lines)})')
