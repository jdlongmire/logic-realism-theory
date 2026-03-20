"""
Path 3: T2echo (Hahn Echo) Measurement Circuit Generation

This script generates T2echo (Hahn echo) measurement circuits for CONFOUND CONTROL.
T2echo refocuses low-frequency noise, allowing separation of LRT effects from
pure dephasing.

T2echo Circuit: |0⟩ → H → delay(T/2) → X → delay(T/2) → H → Measure
Measures: Phase coherence with refocusing (cancels slow noise)

Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
"""

import numpy as np
from qiskit import QuantumCircuit
from typing import List, Dict, Optional


def create_T2echo_circuit(
    delay_us: float,
    qubit: int = 0,
    dt: Optional[float] = None
) -> QuantumCircuit:
    """
    Create a single T2echo (Hahn echo) measurement circuit.

    Circuit: |0⟩ → H → delay(T/2) → X → delay(T/2) → H → Measure

    Physical Process:
    - Initialize in ground state |0⟩
    - Apply Hadamard: |0⟩ → |+⟩ (superposition)
    - Wait T/2 (accumulate phase errors)
    - Apply X (π-pulse): Refocus phase errors
    - Wait T/2 (low-frequency errors cancel, high-frequency persist)
    - Apply Hadamard: Convert phase to population
    - Measure in computational basis

    Expected: P_error(T) = 0.5 * (1 - exp(-T/T2echo)) + p0

    Purpose: Distinguish LRT effect from pure dephasing
    - If T2echo ≈ 2T1 but T2 < T1 → Pure dephasing (not LRT)
    - If T2echo < T1 also → Possible LRT effect

    Relationship: 1/T2 = 1/(2T1) + 1/T2Φ
    - T2 (Ramsey): Total dephasing
    - T2echo (Hahn): High-frequency dephasing only
    - If T2echo >> T2 → Low-frequency noise dominant (not LRT)

    Args:
        delay_us: Total delay duration in microseconds (split into T/2 on each side)
        qubit: Qubit index to use
        dt: Backend sampling time in seconds (if None, uses µs units)

    Returns:
        QuantumCircuit configured for T2echo measurement
    """
    qc = QuantumCircuit(1, 1)
    qc.name = f"T2echo_{delay_us:.2f}us"

    # Prepare |+⟩ (superposition state)
    qc.h(qubit)

    # First delay period: T/2
    half_delay = delay_us / 2.0
    if dt is not None:
        # Use backend dt units (seconds)
        delay_samples = int(half_delay * 1e-6 / dt)
        qc.delay(delay_samples, qubit, unit='dt')
    else:
        # Use microseconds directly
        qc.delay(half_delay, qubit, unit='us')

    # Refocusing pulse: X gate (π-pulse)
    # This reverses the phase accumulation direction
    qc.x(qubit)

    # Second delay period: T/2
    if dt is not None:
        delay_samples = int(half_delay * 1e-6 / dt)
        qc.delay(delay_samples, qubit, unit='dt')
    else:
        qc.delay(half_delay, qubit, unit='us')

    # Final Hadamard: Convert phase to population
    qc.h(qubit)

    # Measure in computational basis
    qc.measure(qubit, 0)

    return qc


def create_T2echo_circuits(
    duration_points: Optional[np.ndarray] = None,
    qubit: int = 0,
    dt: Optional[float] = None
) -> List[QuantumCircuit]:
    """
    Create a full sweep of T2echo measurement circuits.

    Uses same duration points as T1 and T2 for direct comparison.

    Args:
        duration_points: Array of delay durations (µs). If None, uses default.
        qubit: Qubit index to use
        dt: Backend sampling time (seconds)

    Returns:
        List of QuantumCircuit objects for T2echo sweep
    """
    if duration_points is None:
        # Import from circuits_t1 to ensure consistency
        from circuits_t1 import generate_duration_points
        duration_points = generate_duration_points()

    circuits = [
        create_T2echo_circuit(T, qubit=qubit, dt=dt)
        for T in duration_points
    ]

    return circuits


def get_circuit_metadata(duration_points: np.ndarray) -> Dict:
    """
    Generate metadata for T2echo circuit sweep.

    Args:
        duration_points: Array of duration values

    Returns:
        Dictionary with sweep metadata
    """
    return {
        "measurement_type": "T2echo_hahn_echo",
        "circuit_structure": "|0⟩ → H → delay(T/2) → X → delay(T/2) → H → Measure",
        "physical_process": "Phase coherence with refocusing (cancels low-frequency noise)",
        "expected_model": "P_error(T) = 0.5 * (1 - exp(-T/T2echo)) + p0",
        "num_points": len(duration_points),
        "duration_range_us": {
            "min": float(duration_points.min()),
            "max": float(duration_points.max())
        },
        "duration_points_us": duration_points.tolist(),
        "purpose": "Confound control - separate LRT effect from pure dephasing",
        "interpretation": {
            "T2echo_approx_2T1_and_T2_less_T1": "Pure dephasing (QM), not LRT",
            "T2echo_less_T1_also": "Possible LRT effect (superposition instability)",
            "T2echo_much_greater_T2": "Low-frequency noise dominant"
        },
        "relationship": "1/T2 = 1/(2T1) + 1/T2Φ (Φ = pure dephasing)",
        "qm_expectation": "T2echo ≈ 2T1 (limited by T1 only)",
        "note": "Refocusing pulse (X) cancels quasi-static noise"
    }


# Example usage
if __name__ == "__main__":
    print("Path 3 - T2echo (Hahn Echo) Circuit Generation\n")
    print("Purpose: Confound control for separating LRT from pure dephasing\n")

    # Import duration generation from T1 script
    from circuits_t1 import generate_duration_points

    # Generate same duration sweep as T1 and T2
    durations = generate_duration_points()
    print(f"Duration sweep: {len(durations)} points (same as T1/T2)")
    print(f"Range: {durations.min():.2f} - {durations.max():.2f} µs\n")

    # Create circuits
    circuits = create_T2echo_circuits(durations)
    print(f"Created {len(circuits)} T2echo circuits\n")

    # Show first circuit
    print("Example T2echo circuit (first point):")
    print(circuits[0])

    # Get metadata
    metadata = get_circuit_metadata(durations)
    print(f"\nMetadata: {metadata['num_points']} points")
    print(f"Purpose: {metadata['purpose']}")
    print("\nInterpretation Guide:")
    for condition, meaning in metadata['interpretation'].items():
        print(f"  - {condition}: {meaning}")
