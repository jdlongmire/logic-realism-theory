"""
AC Stark θ-Dependence Data Analysis

Fits experimental AC Stark shift data to LRT vs QM models and performs statistical comparison.

LRT Model: Δω(θ) = Δω₀ · [1 + η · sin²(θ)]
QM Model:  Δω(θ) = Δω₀ (constant)

Author: James D. Longmire
Date: November 2025
License: MIT
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from scipy.stats import chi2
import pandas as pd
from typing import Tuple, Dict
import warnings
warnings.filterwarnings('ignore')


# ============================================================================
# Model Definitions
# ============================================================================

def lrt_model(theta: np.ndarray, delta_omega_0: float, eta: float) -> np.ndarray:
    """
    LRT prediction for AC Stark shift vs superposition angle.

    Δω(θ) = Δω₀ · [1 + η · sin²(θ)]

    Parameters
    ----------
    theta : array_like
        Superposition angles in radians
    delta_omega_0 : float
        Base AC Stark shift (kHz or MHz)
    eta : float
        EM coupling strength (predicted ≈ 0.23)

    Returns
    -------
    array_like
        AC Stark shift values
    """
    return delta_omega_0 * (1 + eta * np.sin(theta)**2)


def qm_model(theta: np.ndarray, delta_omega_0: float) -> np.ndarray:
    """
    Standard QM prediction for AC Stark shift (constant).

    Δω(θ) = Δω₀

    Parameters
    ----------
    theta : array_like
        Superposition angles in radians
    delta_omega_0 : float
        AC Stark shift (constant)

    Returns
    -------
    array_like
        Constant AC Stark shift values
    """
    return np.full_like(theta, delta_omega_0)


# ============================================================================
# Fitting Functions
# ============================================================================

def fit_lrt_model(theta: np.ndarray, delta_omega: np.ndarray,
                  sigma: np.ndarray = None) -> Tuple[np.ndarray, np.ndarray]:
    """
    Fit LRT model to experimental data.

    Parameters
    ----------
    theta : array_like
        Superposition angles (radians)
    delta_omega : array_like
        Measured AC Stark shifts
    sigma : array_like, optional
        Measurement uncertainties

    Returns
    -------
    popt : array
        Optimal parameters [Δω₀, η]
    pcov : array
        Covariance matrix
    """
    # Initial guess: Δω₀ from mean, η = 0.23
    p0 = [np.mean(delta_omega), 0.23]

    # Bounds: Δω₀ > 0, 0 < η < 1
    bounds = ([0, 0], [np.inf, 1.0])

    popt, pcov = curve_fit(lrt_model, theta, delta_omega, p0=p0,
                           sigma=sigma, bounds=bounds, absolute_sigma=True)

    return popt, pcov


def fit_qm_model(theta: np.ndarray, delta_omega: np.ndarray,
                 sigma: np.ndarray = None) -> Tuple[np.ndarray, np.ndarray]:
    """
    Fit QM model (constant) to experimental data.

    Parameters
    ----------
    theta : array_like
        Superposition angles (radians)
    delta_omega : array_like
        Measured AC Stark shifts
    sigma : array_like, optional
        Measurement uncertainties

    Returns
    -------
    popt : array
        Optimal parameter [Δω₀]
    pcov : array
        Covariance matrix
    """
    # Initial guess: mean of data
    p0 = [np.mean(delta_omega)]

    popt, pcov = curve_fit(qm_model, theta, delta_omega, p0=p0,
                           sigma=sigma, absolute_sigma=True)

    return popt, pcov


# ============================================================================
# Statistical Analysis
# ============================================================================

def calculate_chi_squared(observed: np.ndarray, expected: np.ndarray,
                          sigma: np.ndarray) -> float:
    """
    Calculate χ² statistic.

    χ² = Σ [(observed - expected)² / σ²]
    """
    return np.sum(((observed - expected) / sigma)**2)


def calculate_reduced_chi_squared(chi_sq: float, n_data: int,
                                  n_params: int) -> float:
    """
    Calculate reduced χ² (χ²/dof).

    χ²_red = χ² / (n_data - n_params)
    """
    dof = n_data - n_params
    return chi_sq / dof if dof > 0 else np.inf


def calculate_p_value(chi_sq: float, dof: int) -> float:
    """
    Calculate p-value from χ² distribution.

    p = P(X > χ² | dof)
    """
    return 1 - chi2.cdf(chi_sq, dof)


def calculate_aic(chi_sq: float, n_params: int) -> float:
    """
    Calculate Akaike Information Criterion.

    AIC = χ² + 2k
    """
    return chi_sq + 2 * n_params


def calculate_bic(chi_sq: float, n_params: int, n_data: int) -> float:
    """
    Calculate Bayesian Information Criterion.

    BIC = χ² + k·ln(n)
    """
    return chi_sq + n_params * np.log(n_data)


def compare_models(theta: np.ndarray, delta_omega: np.ndarray,
                   sigma: np.ndarray) -> Dict:
    """
    Fit both models and perform statistical comparison.

    Parameters
    ----------
    theta : array_like
        Superposition angles (radians)
    delta_omega : array_like
        Measured AC Stark shifts
    sigma : array_like
        Measurement uncertainties

    Returns
    -------
    results : dict
        Statistical comparison results
    """
    n_data = len(theta)

    # Fit LRT model (2 parameters)
    popt_lrt, pcov_lrt = fit_lrt_model(theta, delta_omega, sigma)
    delta_omega_0_lrt, eta_lrt = popt_lrt
    delta_omega_0_err_lrt, eta_err_lrt = np.sqrt(np.diag(pcov_lrt))

    expected_lrt = lrt_model(theta, *popt_lrt)
    chi_sq_lrt = calculate_chi_squared(delta_omega, expected_lrt, sigma)
    dof_lrt = n_data - 2
    chi_sq_red_lrt = calculate_reduced_chi_squared(chi_sq_lrt, n_data, 2)
    p_value_lrt = calculate_p_value(chi_sq_lrt, dof_lrt)
    aic_lrt = calculate_aic(chi_sq_lrt, 2)
    bic_lrt = calculate_bic(chi_sq_lrt, 2, n_data)

    # Fit QM model (1 parameter)
    popt_qm, pcov_qm = fit_qm_model(theta, delta_omega, sigma)
    delta_omega_0_qm = popt_qm[0]
    delta_omega_0_err_qm = np.sqrt(pcov_qm[0, 0])

    expected_qm = qm_model(theta, *popt_qm)
    chi_sq_qm = calculate_chi_squared(delta_omega, expected_qm, sigma)
    dof_qm = n_data - 1
    chi_sq_red_qm = calculate_reduced_chi_squared(chi_sq_qm, n_data, 1)
    p_value_qm = calculate_p_value(chi_sq_qm, dof_qm)
    aic_qm = calculate_aic(chi_sq_qm, 1)
    bic_qm = calculate_bic(chi_sq_qm, 1, n_data)

    # Model comparison
    delta_chi_sq = chi_sq_qm - chi_sq_lrt
    delta_dof = dof_qm - dof_lrt

    # Likelihood ratio test
    # H0: QM model (nested in LRT with η=0)
    # ΔχIJ² ~ χ²(Δdof) under H0
    p_value_comparison = 1 - chi2.cdf(delta_chi_sq, delta_dof)

    # ΔAIC > 10 → strong evidence for lower AIC model
    delta_aic = aic_qm - aic_lrt
    delta_bic = bic_qm - bic_lrt

    # Assess η significance (is it consistent with 0?)
    eta_sigma = eta_lrt / eta_err_lrt if eta_err_lrt > 0 else np.inf

    results = {
        'lrt': {
            'delta_omega_0': delta_omega_0_lrt,
            'delta_omega_0_err': delta_omega_0_err_lrt,
            'eta': eta_lrt,
            'eta_err': eta_err_lrt,
            'chi_squared': chi_sq_lrt,
            'dof': dof_lrt,
            'chi_squared_red': chi_sq_red_lrt,
            'p_value': p_value_lrt,
            'aic': aic_lrt,
            'bic': bic_lrt,
        },
        'qm': {
            'delta_omega_0': delta_omega_0_qm,
            'delta_omega_0_err': delta_omega_0_err_qm,
            'chi_squared': chi_sq_qm,
            'dof': dof_qm,
            'chi_squared_red': chi_sq_red_qm,
            'p_value': p_value_qm,
            'aic': aic_qm,
            'bic': bic_qm,
        },
        'comparison': {
            'delta_chi_squared': delta_chi_sq,
            'delta_dof': delta_dof,
            'p_value': p_value_comparison,
            'delta_aic': delta_aic,
            'delta_bic': delta_bic,
            'eta_significance_sigma': eta_sigma,
        }
    }

    return results


# ============================================================================
# Visualization
# ============================================================================

def plot_fit_results(theta: np.ndarray, delta_omega: np.ndarray,
                     sigma: np.ndarray, results: Dict,
                     save_path: str = None, platform: str = "Unknown"):
    """
    Create publication-quality plot of fit results.

    Parameters
    ----------
    theta : array_like
        Superposition angles (radians)
    delta_omega : array_like
        Measured AC Stark shifts
    sigma : array_like
        Measurement uncertainties
    results : dict
        Fitting results from compare_models()
    save_path : str, optional
        Path to save figure
    platform : str, optional
        Experimental platform name
    """
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 10),
                                     gridspec_kw={'height_ratios': [3, 1]})

    # Convert theta to degrees for plotting
    theta_deg = np.degrees(theta)
    theta_fine_deg = np.linspace(0, 90, 200)
    theta_fine = np.radians(theta_fine_deg)

    # Extract fit parameters
    lrt_params = results['lrt']
    qm_params = results['qm']

    # Plot data
    ax1.errorbar(theta_deg, delta_omega, yerr=sigma, fmt='o',
                 markersize=8, capsize=5, capthick=2,
                 label='Experimental Data', color='black', zorder=3)

    # Plot LRT fit
    lrt_fit = lrt_model(theta_fine, lrt_params['delta_omega_0'],
                        lrt_params['eta'])
    ax1.plot(theta_fine_deg, lrt_fit, '-', linewidth=2.5,
             label=f"LRT: η = {lrt_params['eta']:.3f} ± {lrt_params['eta_err']:.3f}",
             color='#E63946', zorder=2)

    # Plot QM fit
    qm_fit = qm_model(theta_fine, qm_params['delta_omega_0'])
    ax1.plot(theta_fine_deg, qm_fit, '--', linewidth=2.5,
             label=f"QM: Δω = {qm_params['delta_omega_0']:.2f} (constant)",
             color='#457B9D', zorder=1)

    # Labels and formatting
    ax1.set_xlabel('Superposition Angle θ (degrees)', fontsize=14)
    ax1.set_ylabel('AC Stark Shift Δω (kHz or MHz)', fontsize=14)
    ax1.set_title(f'AC Stark Shift θ-Dependence - {platform}',
                  fontsize=16, fontweight='bold')
    ax1.legend(fontsize=12, loc='best')
    ax1.grid(True, alpha=0.3)
    ax1.tick_params(labelsize=12)

    # Add statistics box
    comp = results['comparison']
    stats_text = f"Δχ² = {comp['delta_chi_squared']:.2f}\n"
    stats_text += f"p = {comp['p_value']:.4f}\n"
    stats_text += f"η significance: {comp['eta_significance_sigma']:.1f}σ"

    ax1.text(0.05, 0.95, stats_text, transform=ax1.transAxes,
             fontsize=11, verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    # Residuals plot
    lrt_residuals = delta_omega - lrt_model(theta, lrt_params['delta_omega_0'],
                                             lrt_params['eta'])
    qm_residuals = delta_omega - qm_model(theta, qm_params['delta_omega_0'])

    ax2.errorbar(theta_deg, lrt_residuals, yerr=sigma, fmt='o',
                 markersize=6, capsize=4, label='LRT Residuals',
                 color='#E63946', alpha=0.7)
    ax2.errorbar(theta_deg, qm_residuals, yerr=sigma, fmt='s',
                 markersize=6, capsize=4, label='QM Residuals',
                 color='#457B9D', alpha=0.7)
    ax2.axhline(0, color='black', linestyle='-', linewidth=1, alpha=0.3)
    ax2.set_xlabel('Superposition Angle θ (degrees)', fontsize=14)
    ax2.set_ylabel('Residuals', fontsize=14)
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    ax2.tick_params(labelsize=12)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Figure saved to {save_path}")

    plt.show()


def print_results_table(results: Dict):
    """
    Print formatted results table.

    Parameters
    ----------
    results : dict
        Fitting results from compare_models()
    """
    print("\n" + "="*70)
    print("AC STARK θ-DEPENDENCE: MODEL COMPARISON")
    print("="*70)

    # LRT Results
    lrt = results['lrt']
    print("\n📊 LRT Model: Δω(θ) = Δω₀ · [1 + η · sin²(θ)]")
    print("-" * 70)
    print(f"  Δω₀ = {lrt['delta_omega_0']:.4f} ± {lrt['delta_omega_0_err']:.4f}")
    print(f"  η   = {lrt['eta']:.4f} ± {lrt['eta_err']:.4f} (predicted: 0.23)")
    print(f"  χ²  = {lrt['chi_squared']:.2f} (dof = {lrt['dof']})")
    print(f"  χ²_red = {lrt['chi_squared_red']:.3f}")
    print(f"  p-value = {lrt['p_value']:.4f}")
    print(f"  AIC = {lrt['aic']:.2f}")
    print(f"  BIC = {lrt['bic']:.2f}")

    # QM Results
    qm = results['qm']
    print("\n📊 QM Model: Δω(θ) = Δω₀ (constant)")
    print("-" * 70)
    print(f"  Δω₀ = {qm['delta_omega_0']:.4f} ± {qm['delta_omega_0_err']:.4f}")
    print(f"  χ²  = {qm['chi_squared']:.2f} (dof = {qm['dof']})")
    print(f"  χ²_red = {qm['chi_squared_red']:.3f}")
    print(f"  p-value = {qm['p_value']:.4f}")
    print(f"  AIC = {qm['aic']:.2f}")
    print(f"  BIC = {qm['bic']:.2f}")

    # Model Comparison
    comp = results['comparison']
    print("\n🔬 Model Comparison")
    print("-" * 70)
    print(f"  Δχ² = {comp['delta_chi_squared']:.2f} (Δdof = {comp['delta_dof']})")
    print(f"  p-value (likelihood ratio test) = {comp['p_value']:.4e}")
    print(f"  ΔAIC = {comp['delta_aic']:.2f} (QM - LRT)")
    print(f"  ΔBIC = {comp['delta_bic']:.2f} (QM - LRT)")
    print(f"  η significance: {comp['eta_significance_sigma']:.2f}σ")

    # Interpretation
    print("\n📝 Interpretation")
    print("-" * 70)

    if comp['p_value'] < 0.01:
        print("  ✅ LRT model STRONGLY preferred (p < 0.01)")
    elif comp['p_value'] < 0.05:
        print("  ✅ LRT model preferred (p < 0.05)")
    else:
        print("  ❌ No significant difference between models")

    if abs(comp['delta_aic']) > 10:
        if comp['delta_aic'] > 0:
            print("  ✅ LRT model STRONGLY preferred (ΔAIC > 10)")
        else:
            print("  ❌ QM model preferred (ΔAIC < -10)")
    elif abs(comp['delta_aic']) > 4:
        if comp['delta_aic'] > 0:
            print("  ✅ LRT model preferred (ΔAIC > 4)")
        else:
            print("  ⚠️  QM model preferred (ΔAIC < -4)")
    else:
        print("  ⚠️  Models comparable (|ΔAIC| < 4)")

    if comp['eta_significance_sigma'] > 3:
        print(f"  ✅ η significantly different from 0 ({comp['eta_significance_sigma']:.1f}σ)")
    elif comp['eta_significance_sigma'] > 2:
        print(f"  ⚠️  η marginally significant ({comp['eta_significance_sigma']:.1f}σ)")
    else:
        print(f"  ❌ η consistent with 0 ({comp['eta_significance_sigma']:.1f}σ)")

    # Check if η consistent with prediction
    eta_prediction = 0.23
    eta_meas = lrt['eta']
    eta_err = lrt['eta_err']
    eta_dev = abs(eta_meas - eta_prediction) / eta_err

    if eta_dev < 2:
        print(f"  ✅ η consistent with LRT prediction (0.23 ± {eta_dev:.1f}σ)")
    else:
        print(f"  ⚠️  η deviates from prediction ({eta_dev:.1f}σ from 0.23)")

    print("\n" + "="*70 + "\n")


# ============================================================================
# Example Usage / Demo Mode
# ============================================================================

def generate_synthetic_data(n_points: int = 12, eta_true: float = 0.23,
                           delta_omega_0_true: float = 100.0,
                           noise_level: float = 2.0,
                           seed: int = 42) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Generate synthetic data for testing (LRT model with noise).

    Parameters
    ----------
    n_points : int
        Number of data points
    eta_true : float
        True η value
    delta_omega_0_true : float
        True base shift (kHz)
    noise_level : float
        Measurement uncertainty (kHz)
    seed : int
        Random seed

    Returns
    -------
    theta : array
        Superposition angles (radians)
    delta_omega : array
        AC Stark shifts with noise
    sigma : array
        Measurement uncertainties
    """
    np.random.seed(seed)

    # Evenly spaced angles from 0 to π/2
    theta = np.linspace(0, np.pi/2, n_points)

    # True LRT signal
    delta_omega_true = lrt_model(theta, delta_omega_0_true, eta_true)

    # Add Gaussian noise
    noise = np.random.normal(0, noise_level, n_points)
    delta_omega = delta_omega_true + noise

    # Uncertainties
    sigma = np.full(n_points, noise_level)

    return theta, delta_omega, sigma


def main():
    """
    Demo mode: Generate synthetic data and analyze.
    """
    print("\n" + "="*70)
    print("AC STARK θ-DEPENDENCE ANALYSIS - DEMO MODE")
    print("="*70)
    print("\nGenerating synthetic LRT data (η = 0.23, Δω₀ = 100 kHz, σ = 2 kHz)...\n")

    # Generate synthetic data
    theta, delta_omega, sigma = generate_synthetic_data(
        n_points=12,
        eta_true=0.23,
        delta_omega_0_true=100.0,
        noise_level=2.0
    )

    # Analyze
    results = compare_models(theta, delta_omega, sigma)

    # Print results
    print_results_table(results)

    # Plot
    plot_fit_results(theta, delta_omega, sigma, results,
                     save_path='ac_stark_fit_demo.png',
                     platform='Synthetic Data (Demo)')


if __name__ == '__main__':
    main()
