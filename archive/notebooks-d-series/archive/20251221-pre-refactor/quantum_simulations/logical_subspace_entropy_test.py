"""
Test Grok's "Logical Subspace Entropy" Proposal

This tests whether logical subspace entropy (entropy of the effective logical qubit)
behaves differently from full system entropy in QEC circuits.

For a 3-qubit repetition code:
- Logical |0>_L = |000>
- Logical |1>_L = |111>
- Logical subspace = span{|000>, |111>}

Question: Does measurement-heavy increase logical entropy more than unitary-only?

Author: Claude Code (Session 2.5 continuation)
Date: 2025-10-26
"""

import numpy as np
from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit_aer import AerSimulator
from qiskit_aer.noise import NoiseModel, depolarizing_error, thermal_relaxation_error
from scipy.linalg import logm
import json
import os

# Noise parameters (IBM-like)
class NoiseParams:
    T1 = 100e-6  # 100 us
    T2 = 50e-6   # 50 us
    error_1q = 0.001  # 0.1%
    gate_1q = 50e-9   # 50 ns
    meas_time = 1e-6  # 1 us

def create_noise_model():
    """Standard noise model"""
    noise_model = NoiseModel()

    # Gate errors
    depol_1q = depolarizing_error(NoiseParams.error_1q, 1)
    noise_model.add_all_qubit_quantum_error(depol_1q, ['h', 'x', 'y', 'z', 'id'])

    # Thermal relaxation
    thermal_1q = thermal_relaxation_error(NoiseParams.T1, NoiseParams.T2, NoiseParams.gate_1q)
    thermal_meas = thermal_relaxation_error(NoiseParams.T1, NoiseParams.T2, NoiseParams.meas_time)

    noise_model.add_all_qubit_quantum_error(thermal_1q, ['h', 'x', 'y', 'z', 'id'])
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

def logical_subspace_entropy(rho_full):
    """
    Calculate entropy of logical qubit for 3-qubit repetition code.

    Logical basis:
    - |0>_L = |000>  (basis index 0)
    - |1>_L = |111>  (basis index 7)

    Logical density matrix:
    ρ_L = ( <000|ρ|000>  <000|ρ|111> )
          ( <111|ρ|000>  <111|ρ|111> )

    This is the effective 2x2 density matrix of the encoded logical qubit.
    """
    # Extract logical subspace elements
    rho_00 = rho_full[0, 0]  # <000|ρ|000>
    rho_01 = rho_full[0, 7]  # <000|ρ|111>
    rho_10 = rho_full[7, 0]  # <111|ρ|000>
    rho_11 = rho_full[7, 7]  # <111|ρ|111>

    # Construct 2x2 logical density matrix
    rho_logical = np.array([[rho_00, rho_01],
                            [rho_10, rho_11]], dtype=complex)

    # Renormalize (in case there's leakage out of code space)
    trace = np.trace(rho_logical)
    if abs(trace) > 1e-10:
        rho_logical = rho_logical / trace
    else:
        # Complete leakage - undefined logical state
        return None

    # Calculate entropy
    return von_neumann_entropy(rho_logical)

# Test 1: Unitary-only (just decoherence)
def create_unitary_sequence(n_cycles=5):
    """
    Unitary-only: Encode to |000>_L, apply identity gates (decoherence), measure
    """
    qc = QuantumCircuit(3)

    # Encode logical |0>_L = |000>
    qc.reset([0, 1, 2])

    # Apply identity gates (just accumulate decoherence)
    for _ in range(n_cycles):
        qc.id([0, 1, 2])

    qc.save_density_matrix()
    return qc

# Test 2: Measurement-heavy
def create_measurement_sequence(n_cycles=5):
    """
    Measurement-heavy: Repeated syndrome measurements + reset
    """
    qc = QuantumCircuit(3, 3)

    # Encode logical |0>_L = |000>
    qc.reset([0, 1, 2])

    # Repeated measurement-reset cycles
    for _ in range(n_cycles):
        qc.measure([0, 1, 2], [0, 1, 2])
        qc.reset([0, 1, 2])

    qc.save_density_matrix()
    return qc

# Test 3: Mixed sequence (some measurements, some unitaries)
def create_mixed_sequence(n_cycles=5):
    """
    Mixed: Alternate between unitary and measurement
    """
    qc = QuantumCircuit(3, 3)

    # Encode logical |0>_L
    qc.reset([0, 1, 2])

    for i in range(n_cycles):
        if i % 2 == 0:
            qc.id([0, 1, 2])  # Unitary
        else:
            qc.measure([0, 1, 2], [0, 1, 2])  # Measurement
            qc.reset([0, 1, 2])

    qc.save_density_matrix()
    return qc

print("=" * 70)
print("LOGICAL SUBSPACE ENTROPY TEST")
print("=" * 70)
print()
print("Testing Grok's claim: 'Logical entropy increases with measurements'")
print()
print("3-qubit repetition code:")
print("  Logical |0>_L = |000>")
print("  Logical |1>_L = |111>")
print()
print("Measuring:")
print("  S_full = full system entropy (our Test 4)")
print("  S_logical = logical subspace entropy (Grok's proposal)")
print()

noise_model = create_noise_model()
results = []

for n_cycles in [1, 3, 5, 7, 10]:
    print(f"Testing with {n_cycles} cycles:")

    # Test 1: Unitary
    qc_unitary = create_unitary_sequence(n_cycles)
    rho_unitary = get_density_matrix(qc_unitary, noise_model)
    S_full_unitary = von_neumann_entropy(rho_unitary)
    S_logical_unitary = logical_subspace_entropy(rho_unitary)

    # Test 2: Measurement
    qc_meas = create_measurement_sequence(n_cycles)
    rho_meas = get_density_matrix(qc_meas, noise_model)
    S_full_meas = von_neumann_entropy(rho_meas)
    S_logical_meas = logical_subspace_entropy(rho_meas)

    # Test 3: Mixed
    qc_mixed = create_mixed_sequence(n_cycles)
    rho_mixed = get_density_matrix(qc_mixed, noise_model)
    S_full_mixed = von_neumann_entropy(rho_mixed)
    S_logical_mixed = logical_subspace_entropy(rho_mixed)

    print(f"  Unitary-only:")
    print(f"    S_full = {S_full_unitary:.4f} nats, S_logical = {S_logical_unitary:.4f} nats")
    print(f"  Measurement-heavy:")
    print(f"    S_full = {S_full_meas:.4f} nats, S_logical = {S_logical_meas if S_logical_meas else 'undefined'}{'nats' if S_logical_meas else ''}")
    print(f"  Mixed:")
    print(f"    S_full = {S_full_mixed:.4f} nats, S_logical = {S_logical_mixed:.4f} nats")
    print()

    results.append({
        'n_cycles': n_cycles,
        'unitary': {
            'S_full': float(S_full_unitary),
            'S_logical': float(S_logical_unitary) if S_logical_unitary else None
        },
        'measurement': {
            'S_full': float(S_full_meas),
            'S_logical': float(S_logical_meas) if S_logical_meas else None
        },
        'mixed': {
            'S_full': float(S_full_mixed),
            'S_logical': float(S_logical_mixed) if S_logical_mixed else None
        }
    })

print("=" * 70)
print("ANALYSIS")
print("=" * 70)
print()

print("Question 1: Does measurement-heavy increase logical entropy?")
print()
for res in results:
    n = res['n_cycles']
    S_log_u = res['unitary']['S_logical']
    S_log_m = res['measurement']['S_logical']

    if S_log_m is not None and S_log_u is not None:
        higher = S_log_m > S_log_u
        print(f"n={n}: S_logical(meas) = {S_log_m:.4f} {'>' if higher else '<='} S_logical(unitary) = {S_log_u:.4f}")
        if higher:
            print(f"  -> Grok's claim SUPPORTED for n={n}")
        else:
            print(f"  -> Grok's claim NOT supported for n={n}")
    else:
        print(f"n={n}: Cannot compare (undefined logical entropy)")
    print()

print("=" * 70)
print("Question 2: Is logical entropy different from full entropy?")
print()
for res in results:
    n = res['n_cycles']
    print(f"n={n}:")
    print(f"  Unitary: S_full={res['unitary']['S_full']:.4f}, S_logical={res['unitary']['S_logical']:.4f}")

    S_full_m = res['measurement']['S_full']
    S_log_m = res['measurement']['S_logical']
    print(f"  Measurement: S_full={S_full_m:.4f}, S_logical={S_log_m if S_log_m else 'undefined'}")

    if S_log_m is not None:
        if abs(S_full_m - S_log_m) > 0.01:
            print(f"  -> DIFFERENT measures (S_full != S_logical)")
        else:
            print(f"  -> SAME (S_full ~= S_logical)")
    print()

print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print()
print("Does Grok's 'logical subspace entropy' proposal work?")
print()
print("If S_logical(measurement) > S_logical(unitary):")
print("  -> Grok's proposal is viable")
print("  -> Paper should be revised to specify logical entropy")
print()
print("If S_logical(measurement) <= S_logical(unitary):")
print("  -> Grok's proposal also fails")
print("  -> Need different approach")
print()

# Save results
os.makedirs('outputs', exist_ok=True)
with open('outputs/logical_subspace_entropy_test.json', 'w') as f:
    json.dump(results, f, indent=2)

print("Results saved to: outputs/logical_subspace_entropy_test.json")
