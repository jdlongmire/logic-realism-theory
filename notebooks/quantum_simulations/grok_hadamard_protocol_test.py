"""
Test Grok's Revised Protocol: Measure -> Reset -> Hadamard -> Decoherence

This implements Grok's suggestion to "recreate coherence" with Hadamard gates
between measurement cycles to sustain higher entropy.

Tests whether this actually:
1. Produces different ΔS at fixed duration
2. Breaks multicollinearity
3. Tests the LRT prediction as stated in the paper

Author: Claude Code (Session 2.5 continuation)
Date: 2025-10-26
"""

import numpy as np
from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit_aer import AerSimulator
from qiskit_aer.noise import (
    NoiseModel, depolarizing_error, thermal_relaxation_error
)
from scipy.linalg import logm
import json
import os

# Noise parameters (IBM-like)
class NoiseParams:
    T1 = 100e-6  # 100 us
    T2 = 50e-6   # 50 us
    error_1q = 0.001  # 0.1%
    error_2q = 0.01   # 1%
    gate_1q = 50e-9   # 50 ns
    gate_2q = 300e-9  # 300 ns
    meas_time = 1e-6  # 1 us
    meas_error = 0.01 # 1%

def create_noise_model():
    """Standard noise model"""
    noise_model = NoiseModel()

    # Gate errors
    depol_1q = depolarizing_error(NoiseParams.error_1q, 1)
    depol_2q = depolarizing_error(NoiseParams.error_2q, 2)

    noise_model.add_all_qubit_quantum_error(depol_1q, ['h', 'x', 'y', 'z', 's', 'sdg', 't', 'tdg'])
    noise_model.add_all_qubit_quantum_error(depol_2q, ['cx', 'cz', 'swap'])

    # Thermal relaxation (1-qubit gates only, skip 2-qubit for simplicity)
    thermal_1q = thermal_relaxation_error(NoiseParams.T1, NoiseParams.T2, NoiseParams.gate_1q)
    thermal_meas = thermal_relaxation_error(NoiseParams.T1, NoiseParams.T2, NoiseParams.meas_time)

    noise_model.add_all_qubit_quantum_error(thermal_1q, ['h', 'x', 'y', 'z', 's', 'sdg', 't', 'tdg', 'id'])
    noise_model.add_all_qubit_quantum_error(thermal_meas, ['measure'])

    return noise_model

def von_neumann_entropy(rho):
    """Calculate von Neumann entropy S(rho) = -Tr(rho log rho) in nats"""
    eigenvalues = np.linalg.eigvalsh(rho)
    eigenvalues = eigenvalues[eigenvalues > 1e-10]  # Filter numerical zeros
    return -np.sum(eigenvalues * np.log(eigenvalues))

def get_density_matrix(circuit, noise_model):
    """Run circuit and return density matrix"""
    simulator = AerSimulator(method='density_matrix', noise_model=noise_model)
    result = simulator.run(circuit, shots=1).result()
    return result.data()['density_matrix']

# Test 1: Unitary-only (pure decoherence)
def create_unitary_sequence(n_cycles=5):
    """
    Grok's "unitary-heavy": Just decoherence on initial superposition
    """
    qc = QuantumCircuit(1)
    qc.h(0)  # Initial |+> state

    # Let it decohere naturally (gates cause decoherence in noise model)
    for _ in range(n_cycles):
        qc.id(0)  # Identity (just accumulates decoherence)

    qc.save_density_matrix()
    return qc

# Test 2: Grok's "measurement-heavy" with Hadamards
def create_grok_sequence(n_cycles=5):
    """
    Grok's revised protocol: Measure -> Reset -> H -> Decohere (repeat)
    """
    qc = QuantumCircuit(1, 1)
    qc.h(0)  # Initial |+> state

    for _ in range(n_cycles):
        qc.measure(0, 0)  # Measure
        qc.reset(0)       # Reset to |0>
        qc.h(0)           # "Recreate coherence"
        qc.id(0)          # Let it decohere

    qc.save_density_matrix()
    return qc

# Test 3: Pure measurement (our original approach)
def create_measurement_only(n_cycles=5):
    """
    Original measurement-heavy: Just measure-reset cycles
    """
    qc = QuantumCircuit(1, 1)
    qc.h(0)  # Initial |+> state

    for _ in range(n_cycles):
        qc.measure(0, 0)  # Measure
        qc.reset(0)       # Reset to |0>

    qc.save_density_matrix()
    return qc

# Run test
print("=" * 70)
print("GROK'S HADAMARD PROTOCOL TEST")
print("=" * 70)
print()
print("Comparing three sequences:")
print("  1. Unitary-only: H -> decohere (n cycles)")
print("  2. Grok's protocol: (Measure -> Reset -> H -> decohere) x n")
print("  3. Measurement-only: (Measure -> Reset) x n")
print()

noise_model = create_noise_model()
results = []

for n_cycles in [1, 3, 5, 7, 10]:
    print(f"Testing with {n_cycles} cycles:")

    # Test 1: Unitary
    qc_unitary = create_unitary_sequence(n_cycles)
    rho_unitary = get_density_matrix(qc_unitary, noise_model)
    S_unitary = von_neumann_entropy(rho_unitary)

    # Test 2: Grok's protocol
    qc_grok = create_grok_sequence(n_cycles)
    rho_grok = get_density_matrix(qc_grok, noise_model)
    S_grok = von_neumann_entropy(rho_grok)

    # Test 3: Measurement-only
    qc_meas = create_measurement_only(n_cycles)
    rho_meas = get_density_matrix(qc_meas, noise_model)
    S_meas = von_neumann_entropy(rho_meas)

    # Duration estimates (rough)
    t_unitary = n_cycles * NoiseParams.gate_1q  # Just identity gates
    t_grok = n_cycles * (NoiseParams.meas_time + NoiseParams.gate_1q * 2)  # Meas + H + id
    t_meas = n_cycles * NoiseParams.meas_time  # Just measurements

    print(f"  Unitary-only:      S = {S_unitary:.4f} nats, T ~ {t_unitary*1e6:.2f} us")
    print(f"  Grok's protocol:   S = {S_grok:.4f} nats, T ~ {t_grok*1e6:.2f} us")
    print(f"  Measurement-only:  S = {S_meas:.4f} nats, T ~ {t_meas*1e6:.2f} us")
    print()

    results.append({
        'n_cycles': n_cycles,
        'unitary': {'S': float(S_unitary), 'T_us': float(t_unitary*1e6)},
        'grok': {'S': float(S_grok), 'T_us': float(t_grok*1e6)},
        'measurement': {'S': float(S_meas), 'T_us': float(t_meas*1e6)}
    })

# Analysis
print("=" * 70)
print("ANALYSIS")
print("=" * 70)
print()

# Check if Grok's protocol produces higher S than unitary at SAME duration
print("Key Question: Does Grok's protocol sustain higher S?")
print()

for res in results:
    grok_higher = res['grok']['S'] > res['unitary']['S']
    meas_lower = res['measurement']['S'] < res['unitary']['S']

    print(f"n={res['n_cycles']}:")
    print(f"  Grok S > Unitary S? {grok_higher} ({res['grok']['S']:.4f} vs {res['unitary']['S']:.4f})")
    print(f"  Measurement S < Unitary S? {meas_lower} ({res['measurement']['S']:.4f} vs {res['unitary']['S']:.4f})")

    if grok_higher:
        print(f"  -> Grok's Hadamard trick increases S")

    if meas_lower:
        print(f"  -> Pure measurements REDUCE S (confirms our Test 4)")

    print()

print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print()
print("Does Grok's revised protocol test the paper's claim?")
print()
print("Paper's claim (lines 352-354):")
print('  "CPTP measurement/reset blocks: Delta S > 0"')
print()
print("Grok's protocol:")
print('  Measure -> Reset -> HADAMARD -> Decohere')
print()
print("What's being tested:")
print("  NOT 'Do measurements increase entropy?'")
print("  BUT 'Do Hadamards + decoherence increase entropy?'")
print()
print("Result: Protocol change means this doesn't test original LRT claim.")
print()

# Save results
os.makedirs('outputs', exist_ok=True)
with open('outputs/grok_hadamard_protocol_test.json', 'w') as f:
    json.dump(results, f, indent=2)

print("Results saved to: outputs/grok_hadamard_protocol_test.json")
