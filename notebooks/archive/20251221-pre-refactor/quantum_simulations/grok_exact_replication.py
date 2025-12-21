"""
EXACT Replication of Grok's QuTiP Code

This implements EXACTLY what Grok's code does, step by step, to verify
our interpretation is correct.

Grok's code (from their message):
```python
rho_logical_unitary = qt.partial_trace(rho_unitary, [1, 2])  # Trace out qubits 2, 3
S_unitary = qt.entropy_vn(rho_logical_unitary)
```

We'll replicate this in Qiskit and show explicitly what it computes.

Author: Claude Code (Session 2.5 continuation)
Date: 2025-10-26
"""

import numpy as np
from qiskit import QuantumCircuit
from qiskit.quantum_info import DensityMatrix, partial_trace, entropy
import json

print("=" * 70)
print("EXACT REPLICATION: What Does Grok's Code Compute?")
print("=" * 70)
print()
print("Grok's QuTiP code:")
print("  rho_logical = qt.partial_trace(rho, [1, 2])  # Trace out qubits 2, 3")
print("  S = qt.entropy_vn(rho_logical)")
print()
print("Translation to Qiskit:")
print("  rho_logical = partial_trace(rho, [1, 2])  # Trace out qubits 1, 2")
print("  S = entropy(rho_logical)")
print()
print("=" * 70)
print()

# Test Case 1: Pure logical |0>_L = |000>
print("TEST CASE 1: Logical |0>_L = |000>")
print("-" * 70)

qc1 = QuantumCircuit(3)
# Initialize to |000> (already initialized to |0>)
rho1 = DensityMatrix.from_instruction(qc1)

print("State: |000>")
print("  This is logical |0>_L (pure logical state)")
print()

# Grok's method: partial_trace to keep qubit 0
rho_grok_1 = partial_trace(rho1, [1, 2])
S_grok_1 = entropy(rho_grok_1, base=np.e)  # Use natural log for nats

print("Grok's method (partial_trace, keep qubit 0):")
print(f"  Resulting state: {rho_grok_1.data}")
print(f"  Entropy S_grok = {S_grok_1:.4f} nats")
print()

# Correct logical entropy: Extract {|000>, |111>} subspace
rho1_array = rho1.data
rho_logical_1 = np.array([[rho1_array[0, 0], rho1_array[0, 7]],
                          [rho1_array[7, 0], rho1_array[7, 7]]], dtype=complex)
trace1 = np.trace(rho_logical_1).real
if trace1 > 1e-10:
    rho_logical_1 = rho_logical_1 / trace1
    eigenvalues_1 = np.linalg.eigvalsh(rho_logical_1)
    eigenvalues_1 = eigenvalues_1[eigenvalues_1 > 1e-10]
    S_logical_1 = -np.sum(eigenvalues_1 * np.log(eigenvalues_1))
else:
    S_logical_1 = None

print("Correct logical entropy ({|000>, |111>} subspace):")
print(f"  Logical rho_L = {rho_logical_1}")
print(f"  Entropy S_logical = {S_logical_1:.4f} nats")
print()
print("Comparison:")
print(f"  Grok:    S = {S_grok_1:.4f} nats")
print(f"  Correct: S = {S_logical_1:.4f} nats")
print(f"  Match? {abs(S_grok_1 - S_logical_1) < 0.01}")
print()
print("=" * 70)
print()

# Test Case 2: Logical superposition (|000> + |111>)/sqrt(2) = |+>_L
print("TEST CASE 2: Logical |+>_L = (|000> + |111>)/sqrt(2)")
print("-" * 70)

qc2 = QuantumCircuit(3)
qc2.h(0)
qc2.cx(0, 1)
qc2.cx(0, 2)
rho2 = DensityMatrix.from_instruction(qc2)

print("State: (|000> + |111>)/sqrt(2)")
print("  This is logical |+>_L (superposition of |0>_L and |1>_L)")
print("  Also known as GHZ state")
print()

# Grok's method
rho_grok_2 = partial_trace(rho2, [1, 2])
S_grok_2 = entropy(rho_grok_2, base=np.e)

print("Grok's method (partial_trace, keep qubit 0):")
print(f"  Resulting state:")
print(f"    {rho_grok_2.data}")
print(f"  Entropy S_grok = {S_grok_2:.4f} nats")
print()
print("Physical interpretation:")
print("  Qubit 0 is MAXIMALLY ENTANGLED with qubits 1,2")
print("  Reduced state is maximally mixed: 0.5|0><0| + 0.5|1><1|")
print("  S = ln(2) = 0.693 nats (entanglement entropy)")
print()

# Correct logical entropy
rho2_array = rho2.data
rho_logical_2 = np.array([[rho2_array[0, 0], rho2_array[0, 7]],
                          [rho2_array[7, 0], rho2_array[7, 7]]], dtype=complex)
print(f"Logical density matrix in {{|000>, |111>}} basis:")
print(f"  {rho_logical_2}")
print()

trace2 = np.trace(rho_logical_2).real
if trace2 > 1e-10:
    rho_logical_2 = rho_logical_2 / trace2
    eigenvalues_2 = np.linalg.eigvalsh(rho_logical_2)
    eigenvalues_2 = eigenvalues_2[eigenvalues_2 > 1e-10]
    S_logical_2 = -np.sum(eigenvalues_2 * np.log(eigenvalues_2))
else:
    S_logical_2 = None

print(f"  Eigenvalues: {eigenvalues_2}")
print(f"  Entropy S_logical = {S_logical_2:.4f} nats")
print()
print("Physical interpretation:")
print("  This is a PURE logical superposition (rank-1 density matrix)")
print("  S = 0 nats (pure logical state, no logical errors)")
print()
print("Comparison:")
print(f"  Grok:    S = {S_grok_2:.4f} nats (measures entanglement)")
print(f"  Correct: S = {S_logical_2:.4f} nats (pure logical state)")
print(f"  Difference: {abs(S_grok_2 - S_logical_2):.4f} nats")
print()
print("KEY DIFFERENCE:")
print("  Grok sees ENTANGLEMENT (qubit 0 with environment)")
print("  Correct method sees LOGICAL PURITY (no logical errors)")
print()
print("=" * 70)
print()

# Test Case 3: Logical bit flip (|0>_L -> |1>_L with some probability)
print("TEST CASE 3: Mixed logical state (bit flip error)")
print("-" * 70)

# Create 0.8|000> + 0.6|111> (not normalized, but will normalize)
psi_000 = np.zeros(8, dtype=complex)
psi_000[0] = 0.8
psi_111 = np.zeros(8, dtype=complex)
psi_111[7] = 0.6

psi3 = psi_000 + psi_111
psi3 = psi3 / np.linalg.norm(psi3)
rho3 = np.outer(psi3, psi3.conj())
rho3_dm = DensityMatrix(rho3)

print("State: 0.8|000> + 0.6|111> (normalized)")
print("  This is a mixed logical state (partially flipped)")
print()

# Grok's method
rho_grok_3 = partial_trace(rho3_dm, [1, 2])
S_grok_3 = entropy(rho_grok_3, base=np.e)

print("Grok's method:")
print(f"  Entropy S_grok = {S_grok_3:.4f} nats")
print()

# Correct logical entropy
rho_logical_3 = np.array([[rho3[0, 0], rho3[0, 7]],
                          [rho3[7, 0], rho3[7, 7]]], dtype=complex)
trace3 = np.trace(rho_logical_3).real
if trace3 > 1e-10:
    rho_logical_3 = rho_logical_3 / trace3
    eigenvalues_3 = np.linalg.eigvalsh(rho_logical_3)
    eigenvalues_3 = eigenvalues_3[eigenvalues_3 > 1e-10]
    S_logical_3 = -np.sum(eigenvalues_3 * np.log(eigenvalues_3))
else:
    S_logical_3 = None

print("Correct logical entropy:")
print(f"  Logical rho_L = {rho_logical_3}")
print(f"  Eigenvalues: {eigenvalues_3}")
print(f"  Entropy S_logical = {S_logical_3:.4f} nats")
print()
print("Comparison:")
print(f"  Grok:    S = {S_grok_3:.4f} nats")
print(f"  Correct: S = {S_logical_3:.4f} nats")
print()
print("=" * 70)
print()

# Summary
print("SUMMARY: What is Grok Computing?")
print("=" * 70)
print()
print("Grok's operation: partial_trace(rho, [1, 2])")
print("  -> Traces out qubits 1 and 2")
print("  -> Returns reduced density matrix of qubit 0 alone")
print("  -> Measures ENTANGLEMENT between qubit 0 and {qubits 1,2}")
print()
print("Correct operation: Extract {|000>, |111>} subspace")
print("  -> Builds 2x2 matrix from code space amplitudes")
print("  -> Returns density matrix of ENCODED logical qubit")
print("  -> Measures MIXEDNESS of logical information")
print()
print("These are DIFFERENT physical quantities!")
print()

results = {
    'test_case_1': {
        'state': '|000> (logical |0>)',
        'S_grok': float(S_grok_1),
        'S_logical': float(S_logical_1),
        'match': abs(S_grok_1 - S_logical_1) < 0.01
    },
    'test_case_2': {
        'state': '(|000> + |111>)/sqrt(2) (logical |+>)',
        'S_grok': float(S_grok_2),
        'S_logical': float(S_logical_2),
        'difference': float(abs(S_grok_2 - S_logical_2)),
        'interpretation': 'Grok measures entanglement, not logical entropy'
    },
    'test_case_3': {
        'state': '0.8|000> + 0.6|111> (mixed logical)',
        'S_grok': float(S_grok_3),
        'S_logical': float(S_logical_3)
    },
    'conclusion': 'Groks partial_trace computes single-qubit reduced entropy (entanglement), not logical subspace entropy'
}

import os
os.makedirs('outputs', exist_ok=True)
with open('outputs/grok_exact_replication.json', 'w') as f:
    json.dump(results, f, indent=2)

print("Detailed results saved to: outputs/grok_exact_replication.json")
print()
print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print()
print("Grok's code computes:")
print("  - Single-qubit reduced density matrix (qubit 0 after tracing out 1,2)")
print("  - This measures entanglement with the environment")
print("  - Gives S = ln(2) for pure GHZ state (even though logically pure)")
print()
print("What's needed for QEC:")
print("  - Logical subspace density matrix in {|000>, |111>} basis")
print("  - This measures logical error rate / mixedness")
print("  - Gives S = 0 for pure logical states (like GHZ)")
print()
print("For pure logical superposition (|000> + |111>)/sqrt(2):")
print(f"  Grok's method:    S = {S_grok_2:.3f} nats (entanglement)")
print(f"  Correct method:   S = {S_logical_2:.3f} nats (pure logical state)")
print(f"  Difference:       {abs(S_grok_2 - S_logical_2):.3f} nats")
print()
print("This confirms Grok is computing a different quantity.")
print("The claimed beta = 0.784 is based on entanglement entropy,")
print("not logical QEC entropy.")
