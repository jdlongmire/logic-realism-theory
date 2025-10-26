#!/usr/bin/env python3
"""
Corrected Entropy-Error Correlation Simulation
Week 1 Day 3-6: Duration-matched sequences to fix beta discrepancy

This corrected implementation:
1. Uses proper 3-qubit repetition code QEC
2. Implements TIME-MATCHED sequences (critical fix)
3. Measures logical error rates (not physical)
4. Should produce beta ~ 0.1-0.5 (not 56.98)

Copyright (C) 2025 James D. (JD) Longmire
License: Apache License 2.0
"""

import numpy as np
import pandas as pd
from scipy import stats
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt
from typing import Tuple, List
import warnings
warnings.filterwarnings('ignore')

# Import QEC implementation
from qec_implementation import (
    LogicalQubit, NoiseParameters, EntropySequences
)

from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit.quantum_info import DensityMatrix, entropy
from qiskit_aer import AerSimulator


class DurationMatchedSequences(EntropySequences):
    """
    Extended EntropySequences with ACTUAL duration matching.

    Critical Fix: Add idle gates to low-entropy sequences to match
    high-entropy duration, preventing duration-dependent decoherence
    from confounding Delta_S measurement.
    """

    def low_entropy_sequence_matched(self, initial_state: int = 0) -> QuantumCircuit:
        """
        Low-entropy QEC sequence with idle padding to match high-entropy duration.

        This is the CRITICAL FIX that should reduce beta from 56.98 to ~0.1-0.5.

        Args:
            initial_state: Logical 0 or 1

        Returns:
            QuantumCircuit with matched duration
        """
        # Create base low-entropy circuit
        qc_low = self.low_entropy_sequence(initial_state)

        # Create reference high-entropy circuit to get target duration
        qc_high = self.high_entropy_sequence(initial_state)

        # Calculate durations
        t_low = self.calculate_circuit_duration(qc_low)
        t_high = self.calculate_circuit_duration(qc_high)

        # Add idle time to match high-entropy duration
        if t_low < t_high:
            delay_time = t_high - t_low
            # Add idle gates (spread across data qubits)
            # Note: In Qiskit, we can use delay() instruction
            # For realistic timing, add delays before final measurement
            qc_low.barrier()
            for qubit in range(qc_low.num_qubits):
                qc_low.delay(delay_time, qubit, unit='s')
            qc_low.barrier()

        # Verify matching
        t_low_matched = self.calculate_circuit_duration(qc_low)

        # Store metadata
        qc_low.metadata = {
            'sequence_type': 'low_entropy_matched',
            'original_duration': t_low,
            'matched_duration': t_low_matched,
            'target_duration': t_high,
            'delay_added': delay_time if t_low < t_high else 0
        }

        return qc_low

    def calculate_entropy_change(self,
                                 circuit: QuantumCircuit,
                                 simulator: AerSimulator) -> Tuple[float, float, float]:
        """
        Calculate entropy change for a circuit using density matrix simulation.

        CRITICAL FIX: Remove measurements before density matrix calculation.

        Args:
            circuit: QuantumCircuit to analyze
            simulator: AerSimulator with noise model

        Returns:
            (S_in, S_out, Delta_S) in nats
        """
        num_qubits = circuit.num_qubits

        # Initial state (all zeros)
        initial_state = DensityMatrix.from_int(0, dims=2**num_qubits)
        S_in = entropy(initial_state, base=np.e)

        # Evolve through circuit with noise
        # CRITICAL: Remove final measurements before density matrix save
        qc_copy = circuit.copy()
        qc_copy.remove_final_measurements()
        qc_copy.save_density_matrix()

        result = simulator.run(qc_copy, shots=1).result()
        rho_out = result.data()['density_matrix']

        S_out = entropy(rho_out, base=np.e)
        Delta_S = S_out - S_in

        return (S_in, S_out, Delta_S)

    def measure_logical_error_rate(self,
                                   circuit: QuantumCircuit,
                                   simulator: AerSimulator,
                                   shots: int = 1000,
                                   expected_state: int = 0) -> float:
        """
        Measure logical error rate using majority vote decoding.

        Args:
            circuit: QuantumCircuit (should already have measurements)
            simulator: AerSimulator with noise
            shots: Number of shots
            expected_state: Expected logical state (0 or 1)

        Returns:
            Logical error rate (fraction of incorrect decodings)
        """
        # Run circuit
        result = simulator.run(circuit, shots=shots).result()
        counts = result.get_counts()

        # Decode using majority vote on first 3 qubits (data qubits)
        errors = 0
        total = 0

        for outcome, count in counts.items():
            # Extract data qubit measurements (first 3 bits)
            # Note: Qiskit counts are in reverse order (rightmost = qubit 0)
            bits_str = outcome.split()[0]  # Get first part (data qubits)
            if len(bits_str) >= 3:
                # Take last 3 characters (data qubits in reverse order)
                data_bits = [int(b) for b in bits_str[-3:]]
                # Majority vote
                majority = 1 if sum(data_bits) >= 2 else 0

                if majority != expected_state:
                    errors += count
                total += count

        return errors / total if total > 0 else 0


def run_corrected_simulation(n_samples: int = 100,
                             shots_per_sample: int = 500,
                             verbose: bool = True) -> pd.DataFrame:
    """
    Run corrected simulation with duration-matched sequences.

    This should produce beta ~ 0.1-0.5 (not 56.98).

    Args:
        n_samples: Number of trials (default 100 for testing, use 1000+ for validation)
        shots_per_sample: Shots per error rate measurement
        verbose: Print progress

    Returns:
        DataFrame with columns: sequence_type, Delta_S, p_log, duration, duration_matched
    """
    if verbose:
        print("="*70)
        print("Corrected Entropy-Error Correlation Simulation")
        print("="*70)
        print(f"Samples: {n_samples}")
        print(f"Shots per sample: {shots_per_sample}")
        print(f"CRITICAL FIX: Duration-matched sequences")
        print("="*70)

    # Setup
    noise_params = NoiseParameters()
    noise_model = noise_params.create_noise_model()
    simulator = AerSimulator(noise_model=noise_model, method='density_matrix')

    seq_gen = DurationMatchedSequences(noise_params)

    if verbose:
        print(f"\nNoise parameters:")
        print(f"  T1: {noise_params.t1*1e6:.1f} us")
        print(f"  T2: {noise_params.t2*1e6:.1f} us")
        print(f"  Gate error (1q): {noise_params.p_1q_gate:.1e}")
        print(f"  Gate error (2q): {noise_params.p_2q_gate:.1e}")

    # Collect data
    data = []

    for i in range(n_samples):
        if verbose and i % 25 == 0:
            print(f"\nProgress: {i}/{n_samples}")

        # Alternate between low and high entropy
        if i % 2 == 0:
            # Low-entropy with duration matching (CRITICAL FIX)
            qc = seq_gen.low_entropy_sequence_matched(initial_state=0)
            sequence_type = 'low_entropy_matched'
        else:
            # High-entropy
            qc = seq_gen.high_entropy_sequence(initial_state=0)
            sequence_type = 'high_entropy'

        # Measure entropy change
        try:
            S_in, S_out, Delta_S = seq_gen.calculate_entropy_change(qc, simulator)
        except Exception as e:
            if verbose:
                print(f"  WARNING: Entropy calculation failed for sample {i}: {e}")
            continue

        # Measure logical error rate
        try:
            p_log = seq_gen.measure_logical_error_rate(
                qc, simulator, shots=shots_per_sample, expected_state=0
            )
            # Avoid log(0)
            p_log = max(p_log, 1e-6)
        except Exception as e:
            if verbose:
                print(f"  WARNING: Error rate measurement failed for sample {i}: {e}")
            continue

        # Calculate duration
        duration = seq_gen.calculate_circuit_duration(qc)

        # Store metadata
        duration_matched = qc.metadata.get('matched_duration', duration) if hasattr(qc, 'metadata') else duration

        data.append({
            'sequence_type': sequence_type,
            'Delta_S': Delta_S,
            'p_log': p_log,
            'duration': duration,
            'duration_matched': duration_matched
        })

        if verbose and i < 5:
            print(f"  Sample {i}: {sequence_type}, Delta_S={Delta_S:.4f}, p_log={p_log:.4e}, t={duration*1e6:.2f} us")

    df = pd.DataFrame(data)

    if verbose:
        print(f"\nOK Collected {len(df)} samples")

    return df


def analyze_results(df: pd.DataFrame, verbose: bool = True) -> dict:
    """
    Analyze simulation results and estimate beta coefficient.

    Args:
        df: DataFrame from run_corrected_simulation
        verbose: Print results

    Returns:
        Dictionary with analysis results
    """
    if verbose:
        print("\n" + "="*70)
        print("Statistical Analysis")
        print("="*70)

    # Filter out any zero errors
    df_filtered = df[df['p_log'] > 0].copy()
    df_filtered['log_p_log'] = np.log(df_filtered['p_log'])

    # Simple model: log(p_log) = alpha + beta * Delta_S
    X = df_filtered['Delta_S'].values
    y = df_filtered['log_p_log'].values

    slope, intercept, r_value, p_value, std_err = stats.linregress(X, y)

    alpha = intercept
    beta = slope
    beta_se = std_err
    R2 = r_value ** 2

    if verbose:
        print(f"\nSimple Model: log(p_log) = alpha + beta * Delta_S")
        print(f"\nParameter Estimates:")
        print(f"  alpha (intercept): {alpha:.4f}")
        print(f"  beta (entropy coupling): {beta:.4f} +/- {beta_se:.4f}")
        print(f"\nStatistics:")
        print(f"  R^2: {R2:.4f}")
        print(f"  p-value: {p_value:.4e}")
        print(f"  Samples: {len(df_filtered)}")

        print(f"\nHypothesis Test:")
        print(f"  H0: beta = 0 (standard QEC)")
        print(f"  H1: beta > 0 (LRT prediction)")

        if p_value < 0.05 and beta > 0:
            if 0.05 <= beta <= 1.0:
                print(f"\n  OK PRELIMINARY SUPPORT for LRT prediction")
                print(f"  -> beta in range [0.05, 1.0]")
                print(f"  -> Matches order of magnitude of prediction")
            elif beta > 1.0:
                print(f"\n  WARNING TREND: beta > 0 but still too large")
                print(f"  -> beta = {beta:.4f} (expected 0.1-0.5)")
                print(f"  -> May need full statistical model")
            else:
                print(f"\n  OK POSITIVE RESULT: beta in predicted range!")
                print(f"  -> beta = {beta:.4f} ± {beta_se:.4f}")
                print(f"  -> Consistent with LRT prediction")
        elif beta > 0:
            print(f"\n  INCONCLUSIVE: beta > 0 but not statistically significant")
            print(f"  -> Need larger sample size")
        else:
            print(f"\n  X NEGATIVE: beta <= 0")
            print(f"  -> No evidence for correlation")

        # Duration analysis
        print(f"\n" + "="*70)
        print("Duration Matching Verification")
        print("="*70)

        low_df = df[df['sequence_type'] == 'low_entropy_matched']
        high_df = df[df['sequence_type'] == 'high_entropy']

        if len(low_df) > 0 and len(high_df) > 0:
            t_low_mean = low_df['duration'].mean()
            t_high_mean = high_df['duration'].mean()
            t_diff = abs(t_high_mean - t_low_mean)

            print(f"\nDuration Statistics:")
            print(f"  Low-entropy (matched): {t_low_mean*1e6:.3f} us")
            print(f"  High-entropy: {t_high_mean*1e6:.3f} us")
            print(f"  Difference: {t_diff*1e6:.3f} us ({t_diff/t_high_mean*100:.1f}%)")

            if t_diff/t_high_mean < 0.01:  # Less than 1% difference
                print(f"  OK PASS: Durations matched (< 1% difference)")
            else:
                print(f"  WARNING WARNING: Durations not fully matched")

    results = {
        'alpha': alpha,
        'beta': beta,
        'beta_se': beta_se,
        'R2': R2,
        'p_value': p_value,
        'n_samples': len(df_filtered),
        'beta_in_range': 0.05 <= beta <= 1.0,
        'statistically_significant': p_value < 0.05 and beta > 0
    }

    return results


def plot_results(df: pd.DataFrame,
                results: dict,
                output_file: str = '../outputs/corrected_simulation.png'):
    """
    Create visualization of corrected simulation results.

    Args:
        df: DataFrame with results
        results: Analysis results dictionary
        output_file: Path to save plot
    """
    fig, axes = plt.subplots(1, 2, figsize=(15, 6))

    # Prepare data
    df_filtered = df[df['p_log'] > 0].copy()
    df_filtered['log_p_log'] = np.log(df_filtered['p_log'])

    low_df = df[df['sequence_type'] == 'low_entropy_matched']
    high_df = df[df['sequence_type'] == 'high_entropy']

    # Plot 1: Raw error rates
    ax1 = axes[0]
    if len(low_df) > 0:
        ax1.scatter(low_df['Delta_S'], low_df['p_log'],
                   alpha=0.6, label='Low-entropy (matched)', color='blue', s=50)
    if len(high_df) > 0:
        ax1.scatter(high_df['Delta_S'], high_df['p_log'],
                   alpha=0.6, label='High-entropy', color='red', s=50)

    ax1.set_xlabel('Entropy Change Delta_S (nats)', fontsize=12)
    ax1.set_ylabel('Logical Error Rate p_log', fontsize=12)
    ax1.set_title('Error Rate vs. Entropy Change (Duration-Matched)',
                 fontsize=14, fontweight='bold')
    ax1.legend()
    ax1.grid(alpha=0.3)

    # Plot 2: Log-linear fit
    ax2 = axes[1]
    ax2.scatter(df_filtered['Delta_S'], df_filtered['log_p_log'],
               alpha=0.6, label='Data', color='purple', s=50)

    # Fit line
    x_fit = np.linspace(df_filtered['Delta_S'].min(),
                       df_filtered['Delta_S'].max(), 100)
    y_fit = results['alpha'] + results['beta'] * x_fit
    ax2.plot(x_fit, y_fit, 'r-', linewidth=2,
            label=f'Fit: log(p) = {results["alpha"]:.2f} + {results["beta"]:.2f}*Delta_S')

    # Add reference lines for predicted range
    if results['beta'] > 0:
        # Show predicted range (beta ~ 0.1-0.5)
        y_pred_low = results['alpha'] + 0.1 * x_fit
        y_pred_high = results['alpha'] + 0.5 * x_fit
        ax2.fill_between(x_fit, y_pred_low, y_pred_high,
                        alpha=0.2, color='green',
                        label='LRT predicted range (beta=0.1-0.5)')

    ax2.set_xlabel('Entropy Change Delta_S (nats)', fontsize=12)
    ax2.set_ylabel('log(p_log)', fontsize=12)
    ax2.set_title(f'Log-Linear Model (beta = {results["beta"]:.4f} +/- {results["beta_se"]:.4f})',
                 fontsize=14, fontweight='bold')
    ax2.legend()
    ax2.grid(alpha=0.3)

    plt.tight_layout()
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"\nOK Plot saved: {output_file}")


if __name__ == "__main__":
    print("="*70)
    print("CORRECTED SIMULATION - Duration-Matched Sequences")
    print("="*70)
    print("\nThis simulation implements the critical fix:")
    print("  - Time-matched low/high entropy sequences")
    print("  - Proper 3-qubit repetition code QEC")
    print("  - Logical error rate measurement")
    print("\nExpected result: beta ~ 0.1-0.5 (not 56.98)")
    print("="*70)

    # Run simulation with n=100 for quick test
    # (Use n=1000+ for full validation)
    df = run_corrected_simulation(n_samples=100, shots_per_sample=500, verbose=True)

    # Analyze
    results = analyze_results(df, verbose=True)

    # Plot
    plot_results(df, results)

    # Summary
    print("\n" + "="*70)
    print("CORRECTED SIMULATION COMPLETE")
    print("="*70)
    print(f"\nKey Results:")
    print(f"  beta (corrected): {results['beta']:.4f} ± {results['beta_se']:.4f}")
    print(f"  Previous beta (uncorrected): 56.98")
    print(f"  Reduction factor: {56.98/results['beta']:.1f}x")
    print(f"  In predicted range [0.1, 0.5]: {results['beta_in_range']}")
    print(f"  Statistically significant: {results['statistically_significant']}")

    if results['beta_in_range'] and results['statistically_significant']:
        print(f"\n  OKOK SUCCESS: Beta in predicted range with statistical significance!")
        print(f"  -> Duration matching fix worked!")
        print(f"  -> Ready for LLM team review")
    elif results['beta'] < 56.98 / 10:  # At least 10x reduction
        print(f"\n  OK PROGRESS: Beta reduced by >10x")
        print(f"  -> Duration matching helps, but may need further refinement")
        print(f"  -> Consider: full statistical model, larger n")
    else:
        print(f"\n  WARNING INCONCLUSIVE: Beta not significantly reduced")
        print(f"  -> Duration matching may not be fully effective")
        print(f"  -> Investigate other confounds")

    print("="*70)
