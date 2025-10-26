"""
Check IBM Torino backend specifications for LRT test.
"""
from qiskit_ibm_runtime import QiskitRuntimeService
import numpy as np

# Load API token
with open('../../theory/predictions/IBM_Q_API.txt', 'r') as f:
    token = f.read().strip()

# Connect to IBM Quantum
print("Connecting to IBM Quantum...")
try:
    service = QiskitRuntimeService(channel="ibm_quantum_platform", token=token)
except:
    # If already saved, just load
    service = QiskitRuntimeService(channel="ibm_quantum_platform")

# Get ibm_torino backend
backend = service.backend('ibm_torino')
print(f"\nBackend: {backend.name}")
print(f"Status: {backend.status().status_msg}")
print(f"Queue: {backend.status().pending_jobs} pending jobs")

# Get configuration
config = backend.configuration()
print(f"\nConfiguration:")
print(f"  Num qubits: {config.n_qubits}")
print(f"  Basis gates: {config.basis_gates}")
print(f"  Max shots: {config.max_shots}")
print(f"  Max experiments: {config.max_experiments}")

# Get qubit properties (T1, T2, frequency)
try:
    properties = backend.properties()

    print(f"\nQubit Properties (first 5 qubits):")
    print(f"{'Qubit':<8} {'T1 (us)':<12} {'T2 (us)':<12} {'Frequency (GHz)':<18} {'Readout Error':<15}")
    print("-" * 75)

    for qubit_idx in range(min(5, config.n_qubits)):
        t1 = properties.t1(qubit_idx) * 1e6  # Convert to microseconds
        t2 = properties.t2(qubit_idx) * 1e6
        freq = properties.frequency(qubit_idx) * 1e-9  # Convert to GHz
        readout_error = properties.readout_error(qubit_idx)

        print(f"{qubit_idx:<8} {t1:<12.2f} {t2:<12.2f} {freq:<18.5f} {readout_error:<15.4f}")

    # Find best qubit for T2
    t2_values = [properties.t2(i) * 1e6 for i in range(config.n_qubits)]
    best_qubit = np.argmax(t2_values)
    best_t2 = t2_values[best_qubit]

    print(f"\nBest qubit for T2: Qubit {best_qubit} (T2 = {best_t2:.2f} us)")

    # Gate errors (2-qubit gates)
    print(f"\nGate Errors (first 5 qubits):")
    for qubit_idx in range(min(5, config.n_qubits)):
        try:
            sx_error = properties.gate_error('sx', qubit_idx)
            print(f"  Qubit {qubit_idx} SX gate error: {sx_error:.6f}")
        except:
            pass

except Exception as e:
    print(f"\nError fetching properties: {e}")
    print("Backend may not have detailed properties available.")

print("\n" + "="*75)
print("RECOMMENDATION FOR LRT TEST:")
print(f"  Use qubit {best_qubit if 'best_qubit' in locals() else '0'}")
print(f"  T2 = {best_t2 if 'best_t2' in locals() else 'unknown'} us")
print(f"  Duration sweep: 1 us to {int(best_t2*5) if 'best_t2' in locals() else '300'} us")
print(f"  Reduced test: 25 points x 2500 shots (fits 10 min budget)")
print("="*75)
