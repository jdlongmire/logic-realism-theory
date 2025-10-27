"""
Path 3: T2 (Ramsey) Measurement Circuit Generation

This script generates T2 (phase coherence) measurement circuits using Ramsey
interferometry for testing LRT's prediction that superposition states are less stable.

T2 Circuit: |0⟩ → H → delay(T) → H → Measure
Measures: Phase coherence loss in superposition |+⟩

Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
"""

import numpy as np
from qiskit import QuantumCircuit
from typing import List, Dict, Optional


def create_T2_circuit(
    delay_us: float,
    qubit: int = 0,
    dt: Optional[float] = None
) -> QuantumCircuit:
    """
    Create a single T2 (Ramsey) measurement circuit.

    Circuit: |0⟩ → H → delay(T) → H → Measure

    Physical Process:
    - Initialize in ground state |0⟩
    - Apply Hadamard: |0⟩ → |+⟩ = (|0⟩ + |1⟩)/√2 (superposition)
    - Wait for duration T (free evolution in superposition)
    - Apply Hadamard: Converts phase errors to population errors
    - Measure in computational basis

    Expected: P_error(T) = 0.5 * (1 - exp(-T/T2)) + p0
    where p0 = baseline error from gates + measurement

    LRT Prediction: T2 < T1 (superposition unstable due to relaxed EM constraint)
    QM Prediction: T2 ≈ T1 (no fundamental state preference)

    Args:
        delay_us: Delay duration in microseconds
        qubit: Qubit index to use
        dt: Backend sampling time in seconds (if None, uses µs units)

    Returns:
        QuantumCircuit configured for T2 measurement
    """
    qc = QuantumCircuit(1, 1)
    qc.name = f"T2_{delay_us:.2f}us"

    # Prepare |+⟩ (superposition state)
    qc.h(qubit)

    # Wait for T microseconds (free evolution in superposition)
    if dt is not None:
        # Use backend dt units (seconds)
        delay_samples = int(delay_us * 1e-6 / dt)
        qc.delay(delay_samples, qubit, unit='dt')
    else:
        # Use microseconds directly
        qc.delay(delay_us, qubit, unit='us')

    # Second Hadamard: Convert phase to population
    # If no dephasing: |+⟩ → H → |0⟩ (zero error)
    # If dephasing: mixed state → H → population in |1⟩
    qc.h(qubit)

    # Measure in computational basis
    # P(|1⟩) increases with phase errors
    qc.measure(qubit, 0)

    return qc


def create_T2_circuits(
    duration_points: Optional[np.ndarray] = None,
    qubit: int = 0,
    dt: Optional[float] = None
) -> List[QuantumCircuit]:
    """
    Create a full sweep of T2 measurement circuits.

    Uses same duration points as T1 for direct comparison.

    Args:
        duration_points: Array of delay durations (µs). If None, uses default from circuits_t1.
        qubit: Qubit index to use
        dt: Backend sampling time (seconds)

    Returns:
        List of QuantumCircuit objects for T2 sweep
    """
    if duration_points is None:
        # Import from circuits_t1 to ensure consistency
        from circuits_t1 import generate_duration_points
        duration_points = generate_duration_points()

    circuits = [
        create_T2_circuit(T, qubit=qubit, dt=dt)
        for T in duration_points
    ]

    return circuits


def get_circuit_metadata(duration_points: np.ndarray) -> Dict:
    """
    Generate metadata for T2 circuit sweep.

    Args:
        duration_points: Array of duration values

    Returns:
        Dictionary with sweep metadata
    """
    return {
        "measurement_type": "T2_phase_coherence",
        "circuit_structure": "|0⟩ → H → delay(T) → H → Measure",
        "physical_process": "Phase coherence loss in superposition |+⟩",
        "expected_model": "P_error(T) = 0.5 * (1 - exp(-T/T2)) + p0",
        "num_points": len(duration_points),
        "duration_range_us": {
            "min": float(duration_points.min()),
            "max": float(duration_points.max())
        },
        "duration_points_us": duration_points.tolist(),
        "lrt_prediction": "T2 < T1 - Superposition less stable (EM constraint relaxed)",
        "qm_prediction": "T2 ≈ T1 - No fundamental state preference",
        "test_type": "Ramsey_interferometry",
        "note": "P_error = 0 means perfect coherence, 0.5 means complete dephasing"
    }


# Example usage
if __name__ == "__main__":
    print("Path 3 - T2 (Ramsey) Circuit Generation\n")

    # Import duration generation from T1 script
    from circuits_t1 import generate_duration_points

    # Generate same duration sweep as T1
    durations = generate_duration_points()
    print(f"Duration sweep: {len(durations)} points (same as T1)")
    print(f"Range: {durations.min():.2f} - {durations.max():.2f} µs\n")

    # Create circuits
    circuits = create_T2_circuits(durations)
    print(f"Created {len(circuits)} T2 circuits\n")

    # Show first circuit
    print("Example T2 circuit (first point):")
    print(circuits[0])

    # Get metadata
    metadata = get_circuit_metadata(durations)
    print(f"\nMetadata: {metadata['num_points']} points")
    print(f"LRT Prediction: {metadata['lrt_prediction']}")
    print(f"QM Prediction: {metadata['qm_prediction']}")
