"""
Path 3: T1 vs T2 Analysis Pipeline

This script analyzes T1 and T2 measurement data to test LRT's prediction
that superposition states are less stable (T2 < T1).

Analysis Steps:
1. Fit T1 data: P_1(T) = exp(-T/T1)
2. Fit T2 data: P_error(T) = 0.5 * (1 - exp(-T/T2)) + p0
3. Compute ratio: R = T2/T1
4. Hypothesis test: Is T2 < T1 significantly?
5. Effect size: Cohen's d
6. Visualization

Copyright © 2025 James D. (JD) Longmire
License: Apache License 2.0
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from scipy import stats
from typing import Dict, Tuple, Optional
import json


# ═══════════════════════════════════════════════════════════════════════════
# MODEL FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════════

def T1_model(T: np.ndarray, T1: float) -> np.ndarray:
    """
    T1 (amplitude relaxation) model.

    P_1(T) = exp(-T/T1)

    Args:
        T: Delay times (seconds)
        T1: Amplitude relaxation time (seconds)

    Returns:
        Predicted probability of measuring |1⟩
    """
    return np.exp(-T / T1)


def T2_model(T: np.ndarray, T2: float, p0: float) -> np.ndarray:
    """
    T2 (Ramsey) model with baseline error.

    P_error(T) = 0.5 * (1 - exp(-T/T2)) + p0

    Args:
        T: Delay times (seconds)
        T2: Phase coherence time (seconds)
        p0: Baseline error (gate + measurement)

    Returns:
        Predicted error probability
    """
    return 0.5 * (1.0 - np.exp(-T / T2)) + p0


# ═══════════════════════════════════════════════════════════════════════════
# FITTING FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════════

def fit_T1_data(
    T_data: np.ndarray,
    P1_data: np.ndarray,
    T1_guess: float = 200e-6
) -> Tuple[float, float, float]:
    """
    Fit T1 data to exponential decay model.

    Args:
        T_data: Delay times (seconds)
        P1_data: Measured probabilities of |1⟩
        T1_guess: Initial guess for T1 (seconds)

    Returns:
        Tuple of (T1_fit, T1_err, R_squared)
    """
    # Fit
    popt, pcov = curve_fit(
        T1_model,
        T_data,
        P1_data,
        p0=[T1_guess],
        bounds=([1e-6], [10e-3])  # 1 µs to 10 ms
    )

    T1_fit = popt[0]
    T1_err = np.sqrt(pcov[0, 0])

    # R²
    P1_pred = T1_model(T_data, T1_fit)
    SS_res = np.sum((P1_data - P1_pred)**2)
    SS_tot = np.sum((P1_data - np.mean(P1_data))**2)
    R_squared = 1.0 - (SS_res / SS_tot)

    return T1_fit, T1_err, R_squared


def fit_T2_data(
    T_data: np.ndarray,
    P_error_data: np.ndarray,
    T2_guess: float = 200e-6,
    p0_guess: float = 0.10
) -> Tuple[float, float, float, float, float]:
    """
    Fit T2 data to Ramsey model with baseline error.

    Args:
        T_data: Delay times (seconds)
        P_error_data: Measured error probabilities
        T2_guess: Initial guess for T2 (seconds)
        p0_guess: Initial guess for baseline error

    Returns:
        Tuple of (T2_fit, T2_err, p0_fit, p0_err, R_squared)
    """
    # Fit
    popt, pcov = curve_fit(
        T2_model,
        T_data,
        P_error_data,
        p0=[T2_guess, p0_guess],
        bounds=([1e-6, 0.0], [10e-3, 0.5])  # T2: 1µs-10ms, p0: 0-50%
    )

    T2_fit = popt[0]
    p0_fit = popt[1]
    T2_err = np.sqrt(pcov[0, 0])
    p0_err = np.sqrt(pcov[1, 1])

    # R²
    P_error_pred = T2_model(T_data, T2_fit, p0_fit)
    SS_res = np.sum((P_error_data - P_error_pred)**2)
    SS_tot = np.sum((P_error_data - np.mean(P_error_data))**2)
    R_squared = 1.0 - (SS_res / SS_tot)

    return T2_fit, T2_err, p0_fit, p0_err, R_squared


# ═══════════════════════════════════════════════════════════════════════════
# HYPOTHESIS TESTING
# ═══════════════════════════════════════════════════════════════════════════

def compute_ratio_and_test(
    T1_fit: float,
    T1_err: float,
    T2_fit: float,
    T2_err: float
) -> Dict:
    """
    Compute T2/T1 ratio and perform hypothesis test.

    Null Hypothesis (H0): T2 = T1 (QM prediction)
    Alternative (H1): T2 < T1 (LRT prediction)

    Args:
        T1_fit: Fitted T1 value (seconds)
        T1_err: Standard error on T1
        T2_fit: Fitted T2 value (seconds)
        T2_err: Standard error on T2

    Returns:
        Dictionary with ratio, errors, hypothesis test results
    """
    # Ratio
    ratio = T2_fit / T1_fit

    # Error propagation for ratio
    ratio_err = ratio * np.sqrt((T2_err / T2_fit)**2 + (T1_err / T1_fit)**2)

    # Test statistic: t = (T2 - T1) / sqrt(σ_T2² + σ_T1²)
    t_stat = (T2_fit - T1_fit) / np.sqrt(T2_err**2 + T1_err**2)

    # Degrees of freedom (conservative estimate)
    df = 96  # ~49 points × 2 measurements - 4 parameters

    # One-tailed p-value (testing if T2 < T1)
    p_value = stats.t.cdf(t_stat, df)

    # Effect size: Cohen's d
    cohens_d = (T2_fit - T1_fit) / np.sqrt((T2_err**2 + T1_err**2) / 2)

    # Interpret effect size
    if abs(cohens_d) < 0.2:
        effect_interpretation = "Negligible"
    elif abs(cohens_d) < 0.5:
        effect_interpretation = "Small"
    elif abs(cohens_d) < 0.8:
        effect_interpretation = "Medium"
    else:
        effect_interpretation = "Large"

    return {
        "ratio": ratio,
        "ratio_error": ratio_err,
        "T2_minus_T1_seconds": T2_fit - T1_fit,
        "t_statistic": t_stat,
        "p_value": p_value,
        "degrees_of_freedom": df,
        "cohens_d": cohens_d,
        "effect_size": effect_interpretation,
        "significant_at_0.05": p_value < 0.05,
        "interpretation": interpret_result(ratio, p_value, cohens_d)
    }


def interpret_result(ratio: float, p_value: float, cohens_d: float) -> str:
    """
    Interpret the hypothesis test result.

    Args:
        ratio: T2/T1 ratio
        p_value: One-tailed p-value
        cohens_d: Effect size

    Returns:
        Interpretation string
    """
    if p_value < 0.05 and ratio < 0.9:
        return (f"EVIDENCE FOR LRT: T2/T1 = {ratio:.3f}, p = {p_value:.4f}. "
                f"Superposition states significantly less stable than classical states.")
    elif p_value < 0.05 and ratio > 1.1:
        return (f"UNEXPECTED: T2/T1 = {ratio:.3f}, p = {p_value:.4f}. "
                f"Superposition MORE stable (contradicts both LRT and typical QM).")
    else:
        return (f"CONSISTENT WITH QM: T2/T1 = {ratio:.3f}, p = {p_value:.4f}. "
                f"No significant difference (T2 ≈ T1). LRT effect not detected.")


# ═══════════════════════════════════════════════════════════════════════════
# VISUALIZATION
# ═══════════════════════════════════════════════════════════════════════════

def plot_results(
    T_data_us: np.ndarray,
    P1_data: np.ndarray,
    P_error_data: np.ndarray,
    T1_fit: float,
    T2_fit: float,
    p0_fit: float,
    results: Dict,
    backend_name: str = "Backend",
    save_path: Optional[str] = None
):
    """
    Create comprehensive visualization of T1 vs T2 results.

    Args:
        T_data_us: Delay times (microseconds)
        P1_data: T1 measurement data (P(|1⟩))
        P_error_data: T2 measurement data (P(error))
        T1_fit: Fitted T1 (seconds)
        T2_fit: Fitted T2 (seconds)
        p0_fit: Fitted baseline error
        results: Hypothesis test results dictionary
        backend_name: Name of backend
        save_path: Optional path to save figure
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Convert T_data to seconds for fitting
    T_data_s = T_data_us * 1e-6

    # --- T1 Plot ---
    ax = axes[0, 0]
    ax.scatter(T_data_us, P1_data, alpha=0.6, label='Data', s=30)
    T_fit = np.linspace(T_data_us.min(), T_data_us.max(), 200)
    P1_fit = T1_model(T_fit * 1e-6, T1_fit)
    ax.plot(T_fit, P1_fit, 'r-', linewidth=2,
            label=f'Fit: T1 = {T1_fit*1e6:.1f} ± {results["T1_error"]*1e6:.1f} µs')
    ax.set_xlabel('Delay Time (µs)', fontsize=12)
    ax.set_ylabel('P(|1⟩)', fontsize=12)
    ax.set_title(f'T1 Measurement - {backend_name}', fontsize=14, fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # --- T2 Plot ---
    ax = axes[0, 1]
    ax.scatter(T_data_us, P_error_data, alpha=0.6, label='Data', s=30, color='orange')
    P_error_fit = T2_model(T_fit * 1e-6, T2_fit, p0_fit)
    ax.plot(T_fit, P_error_fit, 'r-', linewidth=2,
            label=f'Fit: T2 = {T2_fit*1e6:.1f} ± {results["T2_error"]*1e6:.1f} µs')
    ax.set_xlabel('Delay Time (µs)', fontsize=12)
    ax.set_ylabel('P(error)', fontsize=12)
    ax.set_title(f'T2 Measurement - {backend_name}', fontsize=14, fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # --- Residuals ---
    ax = axes[1, 0]
    P1_pred = T1_model(T_data_s, T1_fit)
    P_error_pred = T2_model(T_data_s, T2_fit, p0_fit)
    ax.scatter(T_data_us, P1_data - P1_pred, alpha=0.6, label='T1 residuals', s=20)
    ax.scatter(T_data_us, P_error_data - P_error_pred, alpha=0.6,
               label='T2 residuals', s=20, color='orange')
    ax.axhline(0, color='black', linestyle='--', alpha=0.5)
    ax.set_xlabel('Delay Time (µs)', fontsize=12)
    ax.set_ylabel('Residual', fontsize=12)
    ax.set_title('Fit Residuals', fontsize=14, fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # --- Summary Statistics ---
    ax = axes[1, 1]
    ax.axis('off')

    summary_text = f"""
**HYPOTHESIS TEST RESULTS**

Backend: {backend_name}

**Measurements:**
T1 = {T1_fit*1e6:.1f} ± {results['T1_error']*1e6:.1f} µs
T2 = {T2_fit*1e6:.1f} ± {results['T2_error']*1e6:.1f} µs
Baseline error (p0) = {p0_fit*100:.2f}%

**Ratio:**
T2/T1 = {results['ratio']:.3f} ± {results['ratio_error']:.3f}

**Hypothesis Test:**
H0: T2 = T1 (QM - no state preference)
H1: T2 < T1 (LRT - superposition unstable)

t-statistic = {results['t_statistic']:.3f}
p-value = {results['p_value']:.4f}
Significant at α=0.05: {results['significant_at_0.05']}

Effect size (Cohen's d): {results['cohens_d']:.3f}
Interpretation: {results['effect_size']}

**Fit Quality:**
T1 R² = {results['T1_R_squared']:.4f}
T2 R² = {results['T2_R_squared']:.4f}

**VERDICT:**
{results['interpretation']}
"""

    ax.text(0.05, 0.95, summary_text, transform=ax.transAxes,
            fontsize=10, verticalalignment='top', family='monospace',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Figure saved to {save_path}")

    return fig


# ═══════════════════════════════════════════════════════════════════════════
# MAIN ANALYSIS PIPELINE
# ═══════════════════════════════════════════════════════════════════════════

def analyze_T1_vs_T2(
    T1_data_file: str,
    T2_data_file: str,
    backend_name: str = "Backend",
    output_prefix: str = "results"
) -> Dict:
    """
    Complete analysis pipeline for Path 3.

    Args:
        T1_data_file: Path to T1 measurement JSON
        T2_data_file: Path to T2 measurement JSON
        backend_name: Name of backend
        output_prefix: Prefix for output files

    Returns:
        Complete results dictionary
    """
    print(f"\n{'='*80}")
    print(f"Path 3 Analysis: T1 vs T2 Comparison")
    print(f"Backend: {backend_name}")
    print(f"{'='*80}\n")

    # Load data
    print("Loading data...")
    with open(T1_data_file, 'r') as f:
        T1_data = json.load(f)
    with open(T2_data_file, 'r') as f:
        T2_data = json.load(f)

    T_data_us = np.array([m['T_us'] for m in T1_data['measurements']])
    P1_data = np.array([m['P_1'] for m in T1_data['measurements']])
    P_error_data = np.array([m['P_error'] for m in T2_data['measurements']])

    T_data_s = T_data_us * 1e-6  # Convert to seconds

    # Fit T1
    print("\nFitting T1 data...")
    T1_fit, T1_err, T1_R2 = fit_T1_data(T_data_s, P1_data)
    print(f"  T1 = {T1_fit*1e6:.2f} ± {T1_err*1e6:.2f} µs")
    print(f"  R² = {T1_R2:.4f}")

    # Fit T2
    print("\nFitting T2 data...")
    T2_fit, T2_err, p0_fit, p0_err, T2_R2 = fit_T2_data(T_data_s, P_error_data)
    print(f"  T2 = {T2_fit*1e6:.2f} ± {T2_err*1e6:.2f} µs")
    print(f"  Baseline error (p0) = {p0_fit*100:.2f} ± {p0_err*100:.2f}%")
    print(f"  R² = {T2_R2:.4f}")

    # Hypothesis test
    print("\nPerforming hypothesis test...")
    results = compute_ratio_and_test(T1_fit, T1_err, T2_fit, T2_err)
    results['T1_fit'] = T1_fit
    results['T1_error'] = T1_err
    results['T1_R_squared'] = T1_R2
    results['T2_fit'] = T2_fit
    results['T2_error'] = T2_err
    results['p0_fit'] = p0_fit
    results['p0_error'] = p0_err
    results['T2_R_squared'] = T2_R2
    results['backend'] = backend_name

    print(f"\n  Ratio T2/T1 = {results['ratio']:.3f} ± {results['ratio_error']:.3f}")
    print(f"  p-value = {results['p_value']:.4f}")
    print(f"  Effect size (Cohen's d) = {results['cohens_d']:.3f} ({results['effect_size']})")
    print(f"\n  {results['interpretation']}")

    # Visualize
    print("\nGenerating visualization...")
    plot_results(
        T_data_us, P1_data, P_error_data,
        T1_fit, T2_fit, p0_fit,
        results, backend_name,
        save_path=f"{output_prefix}_{backend_name}_analysis.png"
    )

    # Save results
    output_file = f"{output_prefix}_{backend_name}_results.json"
    with open(output_file, 'w') as f:
        # Convert numpy types to Python types for JSON serialization
        json_results = {k: (float(v) if isinstance(v, (np.floating, np.integer)) else v)
                        for k, v in results.items()}
        json.dump(json_results, f, indent=2)
    print(f"\nResults saved to {output_file}")

    print(f"\n{'='*80}\n")

    return results


# Example usage
if __name__ == "__main__":
    print("Path 3 - T1 vs T2 Analysis")
    print("\nUsage:")
    print("  python analyze_t1_vs_t2.py T1_data.json T2_data.json backend_name")
    print("\nThis script performs:")
    print("  1. Exponential fit to T1 data")
    print("  2. Ramsey fit to T2 data")
    print("  3. Hypothesis test: T2 < T1?")
    print("  4. Effect size calculation")
    print("  5. Comprehensive visualization")
