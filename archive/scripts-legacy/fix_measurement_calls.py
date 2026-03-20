#!/usr/bin/env python3
"""
Fix wavefunction_collapse and measurement_probability calls to use .amplitude
"""

with open('lean/LogicRealismTheory/Measurement/MeasurementGeometry.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Replace patterns where we pass PreMeasurementState to functions expecting V → ℂ
# The pattern: calling with ψ where ψ is PreMeasurementState, should be ψ.amplitude

replacements = [
    # measurement_probability M ψ σ → measurement_probability M ψ.amplitude σ
    ('measurement_probability M ψ σ', 'measurement_probability M ψ.amplitude σ'),

    # wavefunction_collapse M ψ → wavefunction_collapse M ψ.amplitude
    ('wavefunction_collapse M ψ', 'wavefunction_collapse M ψ.amplitude'),

    # Handle ψ_pre cases
    ('measurement_probability M ψ_pre', 'measurement_probability M ψ_pre.amplitude'),
    ('wavefunction_collapse M ψ_pre', 'wavefunction_collapse M ψ_pre.amplitude'),
]

for old, new in replacements:
    count = content.count(old)
    if count > 0:
        print(f'Replacing: {count} occurrences')
        content = content.replace(old, new)

# Write back
with open('lean/LogicRealismTheory/Measurement/MeasurementGeometry.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('\nSUCCESS: Fixed measurement function calls')
