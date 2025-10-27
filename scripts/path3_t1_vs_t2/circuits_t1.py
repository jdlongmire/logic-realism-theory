"""
Path 3: T1 Measurement Circuit Generation

This script generates T1 (amplitude relaxation) measurement circuits for testing
Logic Realism Theory's prediction that superposition states are less stable.

T1 Circuit: |0⟩ → X → delay(T) → Measure
Measures: Population decay from |1⟩ to |0⟩

Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
"""

import numpy as np
from qiskit import QuantumCircuit
from typing import List, Dict, Optional


def generate_duration_points(
    min_duration_us: float = 1.0,
    max_duration_us: float = 1000.0,
    n_short: int = 24,
    n_long: int = 25,
    transition_us: float = 100.0
) -> np.ndarray:
    """
    Generate duration sweep points with hybrid log-linear spacing.

    Strategy:
    - Short times (1-100 µs): Log spacing (dense for rapid decay)
    - Long times (100-1000 µs): Linear spacing (adequate for asymptote)

    Args:
        min_duration_us: Minimum duration (microseconds)
        max_duration_us: Maximum duration (microseconds)
        n_short: Number of points in log-spaced region
        n_long: Number of points in linear-spaced region
        transition_us: Transition point between log and linear

    Returns:
        Array of duration points (microseconds)
    """
    # Short-time log spacing
    T_short = np.logspace(
        np.log10(min_duration_us),
        np.log10(transition_us),
        n_short
    )

    # Long-time linear spacing
    T_long = np.linspace(transition_us, max_duration_us, n_long)

    # Combine and remove duplicate at transition
    T_all = np.unique(np.concatenate([T_short, T_long]))

    return T_all


def create_T1_circuit(
    delay_us: float,
    qubit: int = 0,
    dt: Optional[float] = None
) -> QuantumCircuit:
    """
    Create a single T1 measurement circuit.

    Circuit: |0⟩ → X → delay(T) → Measure

    Physical Process:
    - Initialize in ground state |0⟩
    - Apply X gate to excite to |1⟩
    - Wait for duration T
    - Measure population (decays from |1⟩ to |0⟩)

    Expected: P_1(T) = exp(-T/T1)

    Args:
        delay_us: Delay duration in microseconds
        qubit: Qubit index to use
        dt: Backend sampling time in seconds (if None, uses µs units)

    Returns:
        QuantumCircuit configured for T1 measurement
    """
    qc = QuantumCircuit(1, 1)
    qc.name = f"T1_{delay_us:.2f}us"

    # Prepare |1⟩ (excited state)
    qc.x(qubit)

    # Wait for T microseconds
    if dt is not None:
        # Use backend dt units (seconds)
        delay_samples = int(delay_us * 1e-6 / dt)
        qc.delay(delay_samples, qubit, unit='dt')
    else:
        # Use microseconds directly
        qc.delay(delay_us, qubit, unit='us')

    # Measure in computational basis
    qc.measure(qubit, 0)

    return qc


def create_T1_circuits(
    duration_points: Optional[np.ndarray] = None,
    qubit: int = 0,
    dt: Optional[float] = None
) -> List[QuantumCircuit]:
    """
    Create a full sweep of T1 measurement circuits.

    Args:
        duration_points: Array of delay durations (µs). If None, uses default sweep.
        qubit: Qubit index to use
        dt: Backend sampling time (seconds)

    Returns:
        List of QuantumCircuit objects for T1 sweep
    """
    if duration_points is None:
        duration_points = generate_duration_points()

    circuits = [
        create_T1_circuit(T, qubit=qubit, dt=dt)
        for T in duration_points
    ]

    return circuits


def get_circuit_metadata(duration_points: np.ndarray) -> Dict:
    """
    Generate metadata for T1 circuit sweep.

    Args:
        duration_points: Array of duration values

    Returns:
        Dictionary with sweep metadata
    """
    return {
        "measurement_type": "T1_amplitude_relaxation",
        "circuit_structure": "|0⟩ → X → delay(T) → Measure",
        "physical_process": "Energy relaxation from |1⟩ to |0⟩",
        "expected_model": "P_1(T) = exp(-T/T1)",
        "num_points": len(duration_points),
        "duration_range_us": {
            "min": float(duration_points.min()),
            "max": float(duration_points.max())
        },
        "duration_points_us": duration_points.tolist(),
        "lrt_prediction": "Classical state (|1⟩) - only T1 relaxation, no EM constraint",
        "qm_prediction": "Energy relaxation via environment coupling"
    }


# Example usage
if __name__ == "__main__":
    print("Path 3 - T1 Circuit Generation\n")

    # Generate duration sweep
    durations = generate_duration_points()
    print(f"Duration sweep: {len(durations)} points")
    print(f"Range: {durations.min():.2f} - {durations.max():.2f} µs")
    print(f"First 5 points: {durations[:5]}")
    print(f"Last 5 points: {durations[-5:]}\n")

    # Create circuits
    circuits = create_T1_circuits(durations)
    print(f"Created {len(circuits)} T1 circuits\n")

    # Show first circuit
    print("Example T1 circuit (first point):")
    print(circuits[0])

    # Get metadata
    metadata = get_circuit_metadata(durations)
    print(f"\nMetadata: {metadata['num_points']} points, "
          f"{metadata['duration_range_us']['min']:.1f}-{metadata['duration_range_us']['max']:.1f} µs")
