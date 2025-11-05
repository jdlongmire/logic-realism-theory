#!/usr/bin/env python3
"""
Bell State Asymmetry Data Analysis Script
==========================================

Path 2: Bell State Asymmetry (T2/T1 differential between |Φ+⟩ and |Ψ+⟩)

This script analyzes experimental T1 and T2 measurements for Bell states,
fits decay curves, calculates T2/T1 ratios, and performs statistical
comparison between QM (no asymmetry) and LRT (ΔT2/T1 ≈ 0.19) models.

Author: James D. (JD) Longmire (ORCID: 0009-0009-1383-7698)
Date: 2025-11-05 (Session 10.0)
Version: 1.0

Usage:
    # With experimental data
    python bell_asymmetry_analysis.py --data experimental_data.csv --output results/

    # Demo mode with synthetic data
    python bell_asymmetry_analysis.py --demo

    # With custom parameters
    python bell_asymmetry_analysis.py --demo --delta-ratio 0.19 --noise 0.03

Features:
    - Exponential decay fitting (T1, T2) with error estimation
    - T2/T1 ratio calculation with error propagation
    - Statistical hypothesis testing (QM vs LRT)
    - Publication-quality visualization
    - Synthetic data generation for protocol testing
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from scipy import stats
import argparse
import json
from pathlib import Path
from typing import Dict, Tuple, Optional
import warnings

warnings.filterwarnings('ignore', category=RuntimeWarning)

# ============================================================================
# CONSTANTS
# ============================================================================

# LRT predicted differential (from derivation)
LRT_DELTA_RATIO = 0.19  # ΔT2/T1

# Typical experimental values (superconducting qubits)
TYPICAL_T1 = 150.0  # microseconds
TYPICAL_T2_RATIO = 0.50  # T2/T1 for |Φ+⟩

# Statistical significance threshold
SIGNIFICANCE_LEVEL = 0.01  # 99% confidence


# ============================================================================
# DECAY MODELS
# ============================================================================

def t1_decay(tau: np.ndarray, T1: float, A: float, B: float) -> np.ndarray:
    """
    T1 (energy relaxation) decay model.

    P_excited(τ) = A · exp(-τ/T1) + B

    Parameters:
        tau: Delay times (array)
        T1: Energy relaxation time
        A: Amplitude
        B: Offset (steady-state population)

    Returns:
        Excited state population at each delay
    """
    return A * np.exp(-tau / T1) + B


def t2_decay(tau: np.ndarray, T2: float, C: float, freq: float,
             phase: float, D: float) -> np.ndarray:
    """
    T2 (dephasing) decay model with oscillation.

    Coherence(τ) = C · exp(-τ/T2) · cos(2πf·τ + φ) + D

    Parameters:
        tau: Delay times (array)
        T2: Dephasing time
        C: Amplitude
        freq: Oscillation frequency (detuning)
        phase: Phase offset
        D: Offset

    Returns:
        Coherence at each delay
    """
    return C * np.exp(-tau / T2) * np.cos(2 * np.pi * freq * tau + phase) + D


def t2_decay_simple(tau: np.ndarray, T2: float, C: float, D: float) -> np.ndarray:
    """
    Simplified T2 decay (no oscillation, for echo sequences).

    Coherence(τ) = C · exp(-τ/T2) + D
    """
    return C * np.exp(-tau / T2) + D


# ============================================================================
# FITTING FUNCTIONS
# ============================================================================

def fit_t1(delays: np.ndarray, populations: np.ndarray,
           sigma: Optional[np.ndarray] = None) -> Dict:
    """
    Fit T1 decay curve.

    Parameters:
        delays: Delay times (microseconds)
        populations: Measured excited state populations
        sigma: Measurement uncertainties (optional)

    Returns:
        Dictionary with fit results:
            T1: Fitted T1 value
            T1_err: Uncertainty in T1
            A, B: Fit parameters
            chi2: Reduced chi-squared
            residuals: Fit residuals
    """
    # Initial guess
    T1_guess = delays[len(delays)//2]  # Rough estimate from midpoint
    A_guess = populations[0] - populations[-1]
    B_guess = populations[-1]
    p0 = [T1_guess, A_guess, B_guess]

    # Bounds (physical constraints)
    bounds = ([1.0, 0.0, 0.0], [np.inf, 1.0, 1.0])

    try:
        popt, pcov = curve_fit(t1_decay, delays, populations, p0=p0,
                                bounds=bounds, sigma=sigma, absolute_sigma=True)
        perr = np.sqrt(np.diag(pcov))

        # Calculate residuals and chi-squared
        fitted = t1_decay(delays, *popt)
        residuals = populations - fitted
        if sigma is not None:
            chi2_red = np.sum((residuals / sigma)**2) / (len(delays) - 3)
        else:
            chi2_red = np.sum(residuals**2) / (len(delays) - 3)

        return {
            'T1': popt[0],
            'T1_err': perr[0],
            'A': popt[1],
            'B': popt[2],
            'chi2': chi2_red,
            'residuals': residuals,
            'fitted': fitted
        }
    except RuntimeError as e:
        print(f"Warning: T1 fit failed: {e}")
        return None


def fit_t2(delays: np.ndarray, coherence: np.ndarray,
           sigma: Optional[np.ndarray] = None,
           simple: bool = True) -> Dict:
    """
    Fit T2 decay curve.

    Parameters:
        delays: Delay times (microseconds)
        coherence: Measured coherence values
        sigma: Measurement uncertainties (optional)
        simple: Use simple exponential (True) or include oscillation (False)

    Returns:
        Dictionary with fit results (similar to fit_t1)
    """
    if simple:
        # Simple exponential (recommended for echo sequences)
        T2_guess = delays[len(delays)//2]
        C_guess = coherence[0] - coherence[-1]
        D_guess = coherence[-1]
        p0 = [T2_guess, C_guess, D_guess]
        bounds = ([1.0, 0.0, 0.0], [np.inf, 1.0, 1.0])

        try:
            popt, pcov = curve_fit(t2_decay_simple, delays, coherence, p0=p0,
                                    bounds=bounds, sigma=sigma, absolute_sigma=True)
            perr = np.sqrt(np.diag(pcov))

            fitted = t2_decay_simple(delays, *popt)
            residuals = coherence - fitted
            if sigma is not None:
                chi2_red = np.sum((residuals / sigma)**2) / (len(delays) - 3)
            else:
                chi2_red = np.sum(residuals**2) / (len(delays) - 3)

            return {
                'T2': popt[0],
                'T2_err': perr[0],
                'C': popt[1],
                'D': popt[2],
                'chi2': chi2_red,
                'residuals': residuals,
                'fitted': fitted
            }
        except RuntimeError as e:
            print(f"Warning: T2 fit failed: {e}")
            return None
    else:
        # Full model with oscillation
        T2_guess = delays[len(delays)//2]
        C_guess = (coherence.max() - coherence.min()) / 2
        freq_guess = 0.1  # MHz
        phase_guess = 0.0
        D_guess = coherence.mean()
        p0 = [T2_guess, C_guess, freq_guess, phase_guess, D_guess]
        bounds = ([1.0, 0.0, 0.0, -np.pi, 0.0],
                  [np.inf, 1.0, 10.0, np.pi, 1.0])

        try:
            popt, pcov = curve_fit(t2_decay, delays, coherence, p0=p0,
                                    bounds=bounds, sigma=sigma, absolute_sigma=True)
            perr = np.sqrt(np.diag(pcov))

            fitted = t2_decay(delays, *popt)
            residuals = coherence - fitted
            if sigma is not None:
                chi2_red = np.sum((residuals / sigma)**2) / (len(delays) - 5)
            else:
                chi2_red = np.sum(residuals**2) / (len(delays) - 5)

            return {
                'T2': popt[0],
                'T2_err': perr[0],
                'C': popt[1],
                'freq': popt[2],
                'phase': popt[3],
                'D': popt[4],
                'chi2': chi2_red,
                'residuals': residuals,
                'fitted': fitted
            }
        except RuntimeError as e:
            print(f"Warning: T2 fit failed: {e}")
            return None


# ============================================================================
# RATIO CALCULATION
# ============================================================================

def calculate_ratio(T2: float, T2_err: float, T1: float, T1_err: float) -> Tuple[float, float]:
    """
    Calculate T2/T1 ratio with error propagation.

    Uses standard error propagation for ratio:
    σ_(T2/T1) = (T2/T1) · sqrt[(σ_T2/T2)² + (σ_T1/T1)²]

    Parameters:
        T2, T2_err: T2 value and uncertainty
        T1, T1_err: T1 value and uncertainty

    Returns:
        (ratio, ratio_err): T2/T1 ratio and its uncertainty
    """
    ratio = T2 / T1
    rel_err_T2 = T2_err / T2
    rel_err_T1 = T1_err / T1
    ratio_err = ratio * np.sqrt(rel_err_T2**2 + rel_err_T1**2)
    return ratio, ratio_err


def calculate_differential(ratio_psi: float, err_psi: float,
                           ratio_phi: float, err_phi: float) -> Tuple[float, float]:
    """
    Calculate differential ΔT2/T1 = (T2/T1)_Ψ+ - (T2/T1)_Φ+.

    Error propagation for difference (assuming uncorrelated):
    σ_Δ = sqrt(σ_Ψ+² + σ_Φ+²)

    Returns:
        (delta, delta_err): Differential and its uncertainty
    """
    delta = ratio_psi - ratio_phi
    delta_err = np.sqrt(err_psi**2 + err_phi**2)
    return delta, delta_err


# ============================================================================
# STATISTICAL TESTS
# ============================================================================

def hypothesis_test_qm_vs_lrt(delta: float, delta_err: float,
                               lrt_pred: float = LRT_DELTA_RATIO) -> Dict:
    """
    Statistical hypothesis test: QM (Δ=0) vs LRT (Δ≈0.19).

    Tests:
        1. Null hypothesis (QM): ΔT2/T1 = 0
        2. Alternative hypothesis (LRT): ΔT2/T1 = 0.19

    Returns:
        Dictionary with test results:
            z_qm: z-score for QM hypothesis
            p_qm: p-value for QM hypothesis (two-tailed)
            z_lrt: z-score for LRT hypothesis
            p_lrt: p-value for LRT hypothesis (two-tailed)
            significance: 'QM', 'LRT', or 'Ambiguous'
    """
    # Test QM (Δ = 0)
    z_qm = delta / delta_err
    p_qm = 2 * (1 - stats.norm.cdf(abs(z_qm)))

    # Test LRT (Δ = 0.19)
    z_lrt = (delta - lrt_pred) / delta_err
    p_lrt = 2 * (1 - stats.norm.cdf(abs(z_lrt)))

    # Determine significance
    if p_qm < SIGNIFICANCE_LEVEL and p_lrt >= SIGNIFICANCE_LEVEL:
        significance = 'LRT'  # QM rejected, LRT consistent
    elif p_qm >= SIGNIFICANCE_LEVEL and p_lrt < SIGNIFICANCE_LEVEL:
        significance = 'QM'  # QM consistent, LRT rejected
    else:
        significance = 'Ambiguous'  # Either both rejected or both consistent

    return {
        'z_qm': z_qm,
        'p_qm': p_qm,
        'z_lrt': z_lrt,
        'p_lrt': p_lrt,
        'significance': significance,
        'sigma_qm': abs(z_qm),
        'sigma_lrt': abs(z_lrt)
    }


def likelihood_ratio_test(delta: float, delta_err: float,
                          lrt_pred: float = LRT_DELTA_RATIO) -> Dict:
    """
    Likelihood ratio test comparing QM vs LRT models.

    Returns:
        Dictionary with:
            LR: Likelihood ratio
            p_value: p-value from chi-squared distribution
            AIC_qm, AIC_lrt: Akaike Information Criterion
            BIC_qm, BIC_lrt: Bayesian Information Criterion
    """
    # Log-likelihoods (assuming Gaussian errors)
    # QM: Δ = 0 (0 parameters)
    # LRT: Δ = free (1 parameter)

    N = 1  # One differential measurement

    # QM likelihood
    chi2_qm = (delta - 0)**2 / delta_err**2
    log_L_qm = -0.5 * chi2_qm

    # LRT likelihood (maximum likelihood at measured value)
    chi2_lrt = 0  # Perfect fit to data
    log_L_lrt = 0

    # Likelihood ratio
    LR = -2 * (log_L_qm - log_L_lrt)
    p_value = 1 - stats.chi2.cdf(LR, df=1)

    # AIC (penalizes extra parameters)
    k_qm = 0  # No free parameters
    k_lrt = 1  # One free parameter (Δ)
    AIC_qm = 2 * k_qm - 2 * log_L_qm
    AIC_lrt = 2 * k_lrt - 2 * log_L_lrt

    # BIC (stronger penalty for parameters)
    BIC_qm = k_qm * np.log(N) - 2 * log_L_qm
    BIC_lrt = k_lrt * np.log(N) - 2 * log_L_lrt

    return {
        'LR': LR,
        'p_value': p_value,
        'AIC_qm': AIC_qm,
        'AIC_lrt': AIC_lrt,
        'delta_AIC': AIC_lrt - AIC_qm,
        'BIC_qm': BIC_qm,
        'BIC_lrt': BIC_lrt,
        'delta_BIC': BIC_lrt - BIC_qm,
        'preferred': 'QM' if AIC_qm < AIC_lrt else 'LRT'
    }


# ============================================================================
# VISUALIZATION
# ============================================================================

def plot_decay_curves(delays_phi: np.ndarray, data_phi: Dict,
                      delays_psi: np.ndarray, data_psi: Dict,
                      observable: str, output_path: Optional[Path] = None):
    """
    Plot decay curves with fits for both Bell states.

    Parameters:
        delays_phi: Delay times for |Φ+⟩
        data_phi: Dict with 'measured', 'fitted', 'residuals' for |Φ+⟩
        delays_psi: Delay times for |Ψ+⟩
        data_psi: Dict with same structure for |Ψ+⟩
        observable: 'T1' or 'T2'
        output_path: Save path (optional)
    """
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # |Φ+⟩ decay
    ax = axes[0, 0]
    ax.errorbar(delays_phi, data_phi['measured'],
                yerr=data_phi.get('error', None),
                fmt='o', color='blue', label='|Φ+⟩ data', alpha=0.6)
    ax.plot(delays_phi, data_phi['fitted'], '-', color='blue',
            linewidth=2, label='Fit')
    ax.set_xlabel('Delay (μs)', fontsize=12)
    ax.set_ylabel('Population' if observable == 'T1' else 'Coherence', fontsize=12)
    ax.set_title(f'{observable} Decay: |Φ+⟩', fontsize=14)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    # |Ψ+⟩ decay
    ax = axes[0, 1]
    ax.errorbar(delays_psi, data_psi['measured'],
                yerr=data_psi.get('error', None),
                fmt='s', color='red', label='|Ψ+⟩ data', alpha=0.6)
    ax.plot(delays_psi, data_psi['fitted'], '-', color='red',
            linewidth=2, label='Fit')
    ax.set_xlabel('Delay (μs)', fontsize=12)
    ax.set_ylabel('Population' if observable == 'T1' else 'Coherence', fontsize=12)
    ax.set_title(f'{observable} Decay: |Ψ+⟩', fontsize=14)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    # |Φ+⟩ residuals
    ax = axes[1, 0]
    ax.axhline(0, color='black', linestyle='--', linewidth=1)
    ax.plot(delays_phi, data_phi['residuals'], 'o', color='blue', alpha=0.6)
    ax.set_xlabel('Delay (μs)', fontsize=12)
    ax.set_ylabel('Residuals', fontsize=12)
    ax.set_title('|Φ+⟩ Fit Residuals', fontsize=14)
    ax.grid(True, alpha=0.3)

    # |Ψ+⟩ residuals
    ax = axes[1, 1]
    ax.axhline(0, color='black', linestyle='--', linewidth=1)
    ax.plot(delays_psi, data_psi['residuals'], 's', color='red', alpha=0.6)
    ax.set_xlabel('Delay (μs)', fontsize=12)
    ax.set_ylabel('Residuals', fontsize=12)
    ax.set_title('|Ψ+⟩ Fit Residuals', fontsize=14)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    if output_path:
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        print(f"Saved decay curves to {output_path}")
    plt.show()


def plot_ratio_comparison(results: Dict, output_path: Optional[Path] = None):
    """
    Plot T2/T1 ratio comparison between Bell states.

    Parameters:
        results: Dictionary with analysis results
        output_path: Save path (optional)
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    # Extract values
    ratio_phi = results['phi']['ratio']
    err_phi = results['phi']['ratio_err']
    ratio_psi = results['psi']['ratio']
    err_psi = results['psi']['ratio_err']
    delta = results['differential']['delta']
    delta_err = results['differential']['delta_err']

    # Left panel: Bar chart of ratios
    ax = axes[0]
    x = [0, 1]
    ratios = [ratio_phi, ratio_psi]
    errors = [err_phi, err_psi]
    colors = ['blue', 'red']
    labels = ['|Φ+⟩', '|Ψ+⟩']

    bars = ax.bar(x, ratios, yerr=errors, color=colors, alpha=0.6,
                  capsize=5, edgecolor='black', linewidth=1.5)
    ax.set_xticks(x)
    ax.set_xticklabels(labels, fontsize=14)
    ax.set_ylabel('T2/T1 Ratio', fontsize=14)
    ax.set_title('T2/T1 Comparison', fontsize=16)
    ax.grid(True, axis='y', alpha=0.3)

    # Add value labels on bars
    for i, (bar, ratio, err) in enumerate(zip(bars, ratios, errors)):
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2, height + err + 0.02,
                f'{ratio:.3f}±{err:.3f}',
                ha='center', va='bottom', fontsize=10)

    # Right panel: Differential with QM and LRT predictions
    ax = axes[1]

    # QM prediction (Δ = 0)
    ax.axhline(0, color='black', linestyle='--', linewidth=2, label='QM (Δ=0)')

    # LRT prediction (Δ ≈ 0.19)
    lrt_pred = results['statistical']['hypothesis_test']['lrt_prediction']
    ax.axhline(lrt_pred, color='green', linestyle='--', linewidth=2,
               label=f'LRT (Δ≈{lrt_pred:.2f})')

    # Measured differential
    ax.errorbar([0.5], [delta], yerr=[delta_err], fmt='o', markersize=12,
                color='purple', capsize=8, linewidth=2, label='Measured')

    ax.set_xlim(-0.5, 1.5)
    ax.set_xticks([])
    ax.set_ylabel('ΔT2/T1', fontsize=14)
    ax.set_title('Differential Measurement', fontsize=16)
    ax.legend(fontsize=12, loc='best')
    ax.grid(True, axis='y', alpha=0.3)

    # Add significance annotation
    sig = results['statistical']['hypothesis_test']['significance']
    sigma_qm = results['statistical']['hypothesis_test']['sigma_qm']
    ax.text(0.5, delta + delta_err + 0.03,
            f'{sig}\n{sigma_qm:.1f}σ from QM',
            ha='center', va='bottom', fontsize=10,
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.tight_layout()
    if output_path:
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        print(f"Saved ratio comparison to {output_path}")
    plt.show()


# ============================================================================
# SYNTHETIC DATA GENERATION
# ============================================================================

def generate_synthetic_data(T1_phi: float = 150.0, T2_T1_phi: float = 0.50,
                           delta_ratio: float = 0.19, noise_level: float = 0.03,
                           num_points: int = 20, seed: Optional[int] = None) -> Dict:
    """
    Generate synthetic experimental data for protocol testing.

    Parameters:
        T1_phi: T1 for |Φ+⟩ (microseconds)
        T2_T1_phi: T2/T1 ratio for |Φ+⟩
        delta_ratio: LRT differential ΔT2/T1
        noise_level: Relative noise level (fraction of signal)
        num_points: Number of delay points
        seed: Random seed for reproducibility

    Returns:
        Dictionary with synthetic data for both states
    """
    if seed is not None:
        np.random.seed(seed)

    # Derived parameters
    T2_phi = T2_T1_phi * T1_phi
    T2_T1_psi = T2_T1_phi + delta_ratio
    T1_psi = T1_phi * 1.15  # 15% T1 asymmetry (from derivation)
    T2_psi = T2_T1_psi * T1_psi

    # Delay arrays
    t1_delays = np.linspace(0, 3*T1_phi, num_points)
    t2_delays = np.linspace(0, 2*T2_phi, num_points)

    # Generate T1 data for |Φ+⟩
    t1_phi_true = t1_decay(t1_delays, T1_phi, 0.95, 0.05)
    t1_phi_noise = noise_level * np.random.randn(num_points)
    t1_phi_measured = t1_phi_true + t1_phi_noise

    # Generate T1 data for |Ψ+⟩
    t1_psi_true = t1_decay(t1_delays, T1_psi, 0.95, 0.05)
    t1_psi_noise = noise_level * np.random.randn(num_points)
    t1_psi_measured = t1_psi_true + t1_psi_noise

    # Generate T2 data for |Φ+⟩
    t2_phi_true = t2_decay_simple(t2_delays, T2_phi, 0.9, 0.1)
    t2_phi_noise = noise_level * np.random.randn(num_points)
    t2_phi_measured = t2_phi_true + t2_phi_noise

    # Generate T2 data for |Ψ+⟩
    t2_psi_true = t2_decay_simple(t2_delays, T2_psi, 0.9, 0.1)
    t2_psi_noise = noise_level * np.random.randn(num_points)
    t2_psi_measured = t2_psi_true + t2_psi_noise

    return {
        'phi': {
            't1': {'delays': t1_delays, 'measured': t1_phi_measured,
                   'error': noise_level * np.ones(num_points)},
            't2': {'delays': t2_delays, 'measured': t2_phi_measured,
                   'error': noise_level * np.ones(num_points)},
            'true_T1': T1_phi,
            'true_T2': T2_phi
        },
        'psi': {
            't1': {'delays': t1_delays, 'measured': t1_psi_measured,
                   'error': noise_level * np.ones(num_points)},
            't2': {'delays': t2_delays, 'measured': t2_psi_measured,
                   'error': noise_level * np.ones(num_points)},
            'true_T1': T1_psi,
            'true_T2': T2_psi
        },
        'true_delta_ratio': delta_ratio
    }


# ============================================================================
# MAIN ANALYSIS PIPELINE
# ============================================================================

def analyze_bell_asymmetry(data: Dict, verbose: bool = True) -> Dict:
    """
    Complete analysis pipeline for Bell state asymmetry.

    Parameters:
        data: Dictionary with experimental data (see generate_synthetic_data format)
        verbose: Print analysis progress

    Returns:
        Dictionary with complete analysis results
    """
    if verbose:
        print("=" * 70)
        print("BELL STATE ASYMMETRY ANALYSIS")
        print("=" * 70)

    results = {}

    # Fit |Φ+⟩ data
    if verbose:
        print("\n[1/6] Fitting |Φ+⟩ T1 decay...")
    phi_t1_fit = fit_t1(data['phi']['t1']['delays'],
                         data['phi']['t1']['measured'],
                         data['phi']['t1'].get('error'))
    if phi_t1_fit is None:
        raise RuntimeError("Failed to fit |Φ+⟩ T1 data")

    if verbose:
        print(f"  T1 = {phi_t1_fit['T1']:.2f} ± {phi_t1_fit['T1_err']:.2f} μs")
        print(f"  χ²_red = {phi_t1_fit['chi2']:.3f}")

    if verbose:
        print("\n[2/6] Fitting |Φ+⟩ T2 decay...")
    phi_t2_fit = fit_t2(data['phi']['t2']['delays'],
                         data['phi']['t2']['measured'],
                         data['phi']['t2'].get('error'))
    if phi_t2_fit is None:
        raise RuntimeError("Failed to fit |Φ+⟩ T2 data")

    if verbose:
        print(f"  T2 = {phi_t2_fit['T2']:.2f} ± {phi_t2_fit['T2_err']:.2f} μs")
        print(f"  χ²_red = {phi_t2_fit['chi2']:.3f}")

    # Fit |Ψ+⟩ data
    if verbose:
        print("\n[3/6] Fitting |Ψ+⟩ T1 decay...")
    psi_t1_fit = fit_t1(data['psi']['t1']['delays'],
                         data['psi']['t1']['measured'],
                         data['psi']['t1'].get('error'))
    if psi_t1_fit is None:
        raise RuntimeError("Failed to fit |Ψ+⟩ T1 data")

    if verbose:
        print(f"  T1 = {psi_t1_fit['T1']:.2f} ± {psi_t1_fit['T1_err']:.2f} μs")
        print(f"  χ²_red = {psi_t1_fit['chi2']:.3f}")

    if verbose:
        print("\n[4/6] Fitting |Ψ+⟩ T2 decay...")
    psi_t2_fit = fit_t2(data['psi']['t2']['delays'],
                         data['psi']['t2']['measured'],
                         data['psi']['t2'].get('error'))
    if psi_t2_fit is None:
        raise RuntimeError("Failed to fit |Ψ+⟩ T2 data")

    if verbose:
        print(f"  T2 = {psi_t2_fit['T2']:.2f} ± {psi_t2_fit['T2_err']:.2f} μs")
        print(f"  χ²_red = {psi_t2_fit['chi2']:.3f}")

    # Calculate ratios
    if verbose:
        print("\n[5/6] Calculating T2/T1 ratios...")

    phi_ratio, phi_ratio_err = calculate_ratio(phi_t2_fit['T2'], phi_t2_fit['T2_err'],
                                                phi_t1_fit['T1'], phi_t1_fit['T1_err'])
    psi_ratio, psi_ratio_err = calculate_ratio(psi_t2_fit['T2'], psi_t2_fit['T2_err'],
                                                psi_t1_fit['T1'], psi_t1_fit['T1_err'])

    if verbose:
        print(f"  (T2/T1)_Φ+ = {phi_ratio:.4f} ± {phi_ratio_err:.4f}")
        print(f"  (T2/T1)_Ψ+ = {psi_ratio:.4f} ± {psi_ratio_err:.4f}")

    # Calculate differential
    delta, delta_err = calculate_differential(psi_ratio, psi_ratio_err,
                                               phi_ratio, phi_ratio_err)

    if verbose:
        print(f"\n  ΔT2/T1 = {delta:.4f} ± {delta_err:.4f}")
        print(f"  Enhancement: {(delta/phi_ratio)*100:.1f}%")

    # Statistical tests
    if verbose:
        print("\n[6/6] Performing statistical tests...")

    hyp_test = hypothesis_test_qm_vs_lrt(delta, delta_err)
    lr_test = likelihood_ratio_test(delta, delta_err)

    if verbose:
        print(f"\n  Hypothesis Test:")
        print(f"    QM (Δ=0): z = {hyp_test['z_qm']:.2f}, p = {hyp_test['p_qm']:.4f} ({hyp_test['sigma_qm']:.1f}σ)")
        print(f"    LRT (Δ=0.19): z = {hyp_test['z_lrt']:.2f}, p = {hyp_test['p_lrt']:.4f} ({hyp_test['sigma_lrt']:.1f}σ)")
        print(f"    Conclusion: {hyp_test['significance']}")
        print(f"\n  Likelihood Ratio Test:")
        print(f"    LR = {lr_test['LR']:.2f}, p = {lr_test['p_value']:.4f}")
        print(f"    ΔAIC = {lr_test['delta_AIC']:.2f}, ΔBIC = {lr_test['delta_BIC']:.2f}")
        print(f"    Preferred model: {lr_test['preferred']}")

    # Package results
    results['phi'] = {
        'T1': phi_t1_fit['T1'],
        'T1_err': phi_t1_fit['T1_err'],
        'T2': phi_t2_fit['T2'],
        'T2_err': phi_t2_fit['T2_err'],
        'ratio': phi_ratio,
        'ratio_err': phi_ratio_err,
        't1_fit': phi_t1_fit,
        't2_fit': phi_t2_fit
    }

    results['psi'] = {
        'T1': psi_t1_fit['T1'],
        'T1_err': psi_t1_fit['T1_err'],
        'T2': psi_t2_fit['T2'],
        'T2_err': psi_t2_fit['T2_err'],
        'ratio': psi_ratio,
        'ratio_err': psi_ratio_err,
        't1_fit': psi_t1_fit,
        't2_fit': psi_t2_fit
    }

    results['differential'] = {
        'delta': delta,
        'delta_err': delta_err,
        'enhancement_percent': (delta / phi_ratio) * 100
    }

    results['statistical'] = {
        'hypothesis_test': {**hyp_test, 'lrt_prediction': LRT_DELTA_RATIO},
        'likelihood_ratio': lr_test
    }

    if verbose:
        print("\n" + "=" * 70)
        print("ANALYSIS COMPLETE")
        print("=" * 70)

    return results


# ============================================================================
# COMMAND-LINE INTERFACE
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='Bell State Asymmetry Data Analysis',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )

    parser.add_argument('--data', type=str, help='Path to experimental data CSV')
    parser.add_argument('--output', type=str, default='results/',
                       help='Output directory for results and figures')
    parser.add_argument('--demo', action='store_true',
                       help='Run demo with synthetic data')
    parser.add_argument('--delta-ratio', type=float, default=0.19,
                       help='Synthetic data: ΔT2/T1 value (default: 0.19)')
    parser.add_argument('--noise', type=float, default=0.03,
                       help='Synthetic data: noise level (default: 0.03)')
    parser.add_argument('--seed', type=int, default=42,
                       help='Random seed for synthetic data (default: 42)')

    args = parser.parse_args()

    # Create output directory
    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Generate or load data
    if args.demo:
        print("Running in DEMO mode with synthetic data")
        print(f"  ΔT2/T1 = {args.delta_ratio}")
        print(f"  Noise level = {args.noise}")
        print(f"  Random seed = {args.seed}\n")

        data = generate_synthetic_data(delta_ratio=args.delta_ratio,
                                       noise_level=args.noise,
                                       seed=args.seed)
    elif args.data:
        # TODO: Implement CSV loading
        raise NotImplementedError("CSV data loading not yet implemented")
    else:
        parser.error("Either --data or --demo must be specified")

    # Run analysis
    results = analyze_bell_asymmetry(data, verbose=True)

    # Save results to JSON
    results_file = output_dir / 'analysis_results.json'
    # Convert numpy types to Python types for JSON serialization
    def convert_to_serializable(obj):
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, (np.int64, np.int32)):
            return int(obj)
        elif isinstance(obj, (np.float64, np.float32)):
            return float(obj)
        elif isinstance(obj, dict):
            return {k: convert_to_serializable(v) for k, v in obj.items()}
        else:
            return obj

    serializable_results = convert_to_serializable(results)
    with open(results_file, 'w') as f:
        json.dump(serializable_results, f, indent=2)
    print(f"\nResults saved to {results_file}")

    # Generate plots
    print("\nGenerating figures...")

    # T1 decay curves
    plot_decay_curves(
        data['phi']['t1']['delays'],
        {'measured': data['phi']['t1']['measured'],
         'fitted': results['phi']['t1_fit']['fitted'],
         'residuals': results['phi']['t1_fit']['residuals'],
         'error': data['phi']['t1'].get('error')},
        data['psi']['t1']['delays'],
        {'measured': data['psi']['t1']['measured'],
         'fitted': results['psi']['t1_fit']['fitted'],
         'residuals': results['psi']['t1_fit']['residuals'],
         'error': data['psi']['t1'].get('error')},
        'T1',
        output_dir / 't1_decay_curves.png'
    )

    # T2 decay curves
    plot_decay_curves(
        data['phi']['t2']['delays'],
        {'measured': data['phi']['t2']['measured'],
         'fitted': results['phi']['t2_fit']['fitted'],
         'residuals': results['phi']['t2_fit']['residuals'],
         'error': data['phi']['t2'].get('error')},
        data['psi']['t2']['delays'],
        {'measured': data['psi']['t2']['measured'],
         'fitted': results['psi']['t2_fit']['fitted'],
         'residuals': results['psi']['t2_fit']['residuals'],
         'error': data['psi']['t2'].get('error')},
        'T2',
        output_dir / 't2_decay_curves.png'
    )

    # Ratio comparison
    plot_ratio_comparison(results, output_dir / 'ratio_comparison.png')

    print("\n✓ Analysis pipeline complete!")
    print(f"All results saved to {output_dir}/")


if __name__ == '__main__':
    main()
