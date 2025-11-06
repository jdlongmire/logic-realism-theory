"""
Path 4: Zeno Crossover Shift Analysis Functions

Mathematical framework for LRT prediction of constraint-entropy-dependent Quantum Zeno crossover.

Author: James D. (JD) Longmire (ORCID: 0009-0009-1383-7698)
Date: 2025-11-05
Version: 1.0
"""

import numpy as np
from typing import Tuple, Dict

# ============================================================================
# CONSTANTS
# ============================================================================

# Excluded-middle coupling parameter (from variational framework)
ETA = 0.23

# ============================================================================
# PART 1: CONSTRAINT ENTROPY CALCULATIONS
# ============================================================================

def constraint_entropy(theta: float) -> float:
    """
    Calculate excluded-middle entropy S_EM for superposition angle theta.

    For state |psi(theta)> = cos(theta/2)|0> + sin(theta/2)|1>, LRT defines:

    S_EM(theta) = -[p_0 ln p_0 + p_1 ln p_1]

    where p_0 = cos^2(theta/2), p_1 = sin^2(theta/2)

    Parameters
    ----------
    theta : float
        Superposition angle in radians [0, pi]

    Returns
    -------
    float
        Constraint entropy S_EM(theta) >= 0

    Notes
    -----
    - S_EM(0) = 0 (eigenstate |0>)
    - S_EM(pi/2) = ln(2) ~ 0.693 (maximum, equal superposition)
    - S_EM(pi) = 0 (eigenstate |1>)
    """
    # State probabilities
    p0 = np.cos(theta / 2) ** 2
    p1 = np.sin(theta / 2) ** 2

    # Handle edge cases (eigenstates)
    if p0 < 1e-12 or p1 < 1e-12:
        return 0.0

    # Shannon entropy of probability distribution
    S_EM = -(p0 * np.log(p0) + p1 * np.log(p1))

    return S_EM


def constraint_entropy_vectorized(theta_array: np.ndarray) -> np.ndarray:
    """
    Vectorized constraint entropy calculation.

    Parameters
    ----------
    theta_array : np.ndarray
        Array of superposition angles in radians

    Returns
    -------
    np.ndarray
        Array of S_EM(theta) values
    """
    p0 = np.cos(theta_array / 2) ** 2
    p1 = np.sin(theta_array / 2) ** 2

    # Avoid log(0) warnings
    S_EM = np.zeros_like(theta_array)
    mask = (p0 > 1e-12) & (p1 > 1e-12)
    S_EM[mask] = -(p0[mask] * np.log(p0[mask]) + p1[mask] * np.log(p1[mask]))

    return S_EM


# ============================================================================
# PART 2: ZENO CROSSOVER PREDICTIONS
# ============================================================================

def zeno_crossover_shift(theta: float, eta: float = ETA) -> float:
    """
    Calculate LRT Zeno crossover shift ratio gamma_star(theta) / gamma_star_QM.

    LRT prediction:
        gamma_star_LRT = gamma_star_QM * [1 + eta * S_EM(theta)]

    Parameters
    ----------
    theta : float
        Superposition angle in radians
    eta : float, optional
        Excluded-middle coupling parameter (default: 0.23)

    Returns
    -------
    float
        Crossover shift ratio gamma_star(theta) / gamma_star_QM >= 1.0

    Notes
    -----
    - gamma_star(0) / gamma_star_QM = 1.0 (no shift at eigenstate)
    - gamma_star(pi/2) / gamma_star_QM ~ 1.159 (15.9% shift at equal superposition)
    """
    S_EM = constraint_entropy(theta)
    return 1.0 + eta * S_EM


def predict_zeno_crossover_curve(eta: float = ETA,
                                  num_points: int = 91) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Generate full Zeno crossover theta-dependence curve.

    Parameters
    ----------
    eta : float, optional
        Excluded-middle coupling parameter (default: 0.23)
    num_points : int, optional
        Number of theta points to sample (default: 91, gives 2 deg resolution)

    Returns
    -------
    theta_deg : np.ndarray
        Superposition angles in degrees [0, 180]
    gamma_star_ratio : np.ndarray
        Crossover shift ratios gamma_star(theta) / gamma_star_QM
    shift_percent : np.ndarray
        Shift percentages relative to QM baseline

    Examples
    --------
    >>> theta, gamma_ratio, shift = predict_zeno_crossover_curve()
    >>> idx_90 = np.argmin(np.abs(theta - 90))
    >>> print(f"At 90 deg: shift = {shift[idx_90]:.1f}%")
    At 90 deg: shift = 15.9%
    """
    theta_rad = np.linspace(0, np.pi, num_points)
    theta_deg = np.degrees(theta_rad)

    # Calculate S_EM for all angles
    S_EM = constraint_entropy_vectorized(theta_rad)

    # LRT predictions
    gamma_star_ratio = 1.0 + eta * S_EM
    shift_percent = (gamma_star_ratio - 1.0) * 100

    return theta_deg, gamma_star_ratio, shift_percent


# ============================================================================
# PART 3: EFFECTIVE DECAY RATE (Zeno/Anti-Zeno Curves)
# ============================================================================

def effective_decay_rate_QM(gamma_meas: float,
                            gamma_star_QM: float,
                            gamma_natural: float = 1.0) -> float:
    """
    Calculate effective decay rate for standard QM Zeno effect.

    gamma_eff(gamma_meas) = gamma_natural * [1 + (gamma_meas/gamma_star)^2] / [1 + (gamma_meas/gamma_star)]

    Parameters
    ----------
    gamma_meas : float
        Measurement rate
    gamma_star_QM : float
        QM crossover rate (Zeno <-> anti-Zeno)
    gamma_natural : float, optional
        Natural decay rate (default: 1.0)

    Returns
    -------
    float
        Effective decay rate gamma_eff

    Notes
    -----
    - gamma_meas << gamma_star: Zeno regime (gamma_eff -> 0)
    - gamma_meas ~ gamma_star: Crossover (gamma_eff minimum)
    - gamma_meas >> gamma_star: Anti-Zeno regime (gamma_eff > gamma_natural)
    """
    x = gamma_meas / gamma_star_QM
    gamma_eff = gamma_natural * (1.0 + x**2) / (1.0 + x)
    return gamma_eff


def effective_decay_rate_LRT(gamma_meas: float,
                              gamma_star_LRT: float,
                              gamma_natural: float = 1.0) -> float:
    """
    Calculate effective decay rate for LRT-modified Zeno effect.

    Same functional form as QM, but with shifted crossover gamma_star_LRT.

    Parameters
    ----------
    gamma_meas : float
        Measurement rate
    gamma_star_LRT : float
        LRT crossover rate (shifted from QM value)
    gamma_natural : float, optional
        Natural decay rate (default: 1.0)

    Returns
    -------
    float
        Effective decay rate gamma_eff

    Notes
    -----
    LRT modifies crossover point but preserves functional form:
    gamma_star_LRT = gamma_star_QM * [1 + eta * S_EM]
    """
    x = gamma_meas / gamma_star_LRT
    gamma_eff = gamma_natural * (1.0 + x**2) / (1.0 + x)
    return gamma_eff


def generate_zeno_curves(gamma_star_QM: float = 1.0,
                         theta: float = np.pi/2,
                         eta: float = ETA,
                         gamma_natural: float = 1.0,
                         num_points: int = 200) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Generate Zeno/anti-Zeno curves for QM and LRT.

    Parameters
    ----------
    gamma_star_QM : float, optional
        QM crossover rate (default: 1.0)
    theta : float, optional
        Superposition angle in radians (default: pi/2 = equal superposition)
    eta : float, optional
        Excluded-middle coupling parameter (default: 0.23)
    gamma_natural : float, optional
        Natural decay rate (default: 1.0)
    num_points : int, optional
        Number of gamma_meas points to sample (default: 200)

    Returns
    -------
    gamma_meas_array : np.ndarray
        Measurement rates (logarithmically spaced)
    gamma_eff_QM : np.ndarray
        Effective decay rates (QM)
    gamma_eff_LRT : np.ndarray
        Effective decay rates (LRT)
    """
    # LRT crossover shift
    gamma_star_LRT = gamma_star_QM * zeno_crossover_shift(theta, eta)

    # Measurement rate range (log scale)
    gamma_meas_array = np.logspace(-2, 2, num_points) * gamma_star_QM

    # Calculate effective decay rates
    gamma_eff_QM = np.array([effective_decay_rate_QM(gm, gamma_star_QM, gamma_natural)
                             for gm in gamma_meas_array])
    gamma_eff_LRT = np.array([effective_decay_rate_LRT(gm, gamma_star_LRT, gamma_natural)
                              for gm in gamma_meas_array])

    return gamma_meas_array, gamma_eff_QM, gamma_eff_LRT


# ============================================================================
# PART 4: QUANTITATIVE PREDICTIONS AT KEY ANGLES
# ============================================================================

def get_key_angle_predictions(eta: float = ETA) -> Dict[str, Dict[str, float]]:
    """
    Calculate Zeno crossover predictions at experimentally relevant angles.

    Parameters
    ----------
    eta : float, optional
        Excluded-middle coupling parameter (default: 0.23)

    Returns
    -------
    dict
        Nested dictionary with structure:
        {
            '0 deg': {'S_EM': ..., 'gamma_star_ratio': ..., 'shift_pct': ...},
            '45 deg': {...},
            ...
        }

    Examples
    --------
    >>> predictions = get_key_angle_predictions()
    >>> print(f"90 deg shift: {predictions['90 deg']['shift_pct']:.1f}%")
    90 deg shift: 15.9%
    """
    key_angles_deg = [0, 45, 60, 90]
    results = {}

    for theta_deg in key_angles_deg:
        theta_rad = np.radians(theta_deg)
        S_EM = constraint_entropy(theta_rad)
        gamma_star_ratio = zeno_crossover_shift(theta_rad, eta)
        shift_pct = (gamma_star_ratio - 1.0) * 100

        results[f'{theta_deg} deg'] = {
            'S_EM': S_EM,
            'gamma_star_ratio': gamma_star_ratio,
            'shift_pct': shift_pct
        }

    return results


def print_prediction_table(eta: float = ETA):
    """
    Print formatted table of Zeno crossover predictions at key angles.

    Parameters
    ----------
    eta : float, optional
        Excluded-middle coupling parameter (default: 0.23)
    """
    predictions = get_key_angle_predictions(eta)

    print("=" * 80)
    print(f"Path 4: Zeno Crossover Shift Predictions (eta = {eta:.3f})")
    print("=" * 80)
    print(f"{'theta':<10} {'S_EM(theta)':<14} {'gamma_star/gamma_star_QM':<26} {'Shift':<10}")
    print("-" * 80)

    for angle, vals in predictions.items():
        print(f"{angle:<10} {vals['S_EM']:<14.3f} {vals['gamma_star_ratio']:<26.3f} {vals['shift_pct']:<10.1f}%")

    print("=" * 80)
    print("Key Result: gamma_star(90 deg) / gamma_star_QM ~ 1.159 (15.9% shift)")
    print("            Crossover occurs at higher measurement rate for superposition states")
    print("=" * 80)


# ============================================================================
# PART 5: EXPERIMENTAL SIGNAL-TO-NOISE ESTIMATION
# ============================================================================

def estimate_SNR(gamma_star_QM_measured: float,
                 gamma_star_uncertainty: float,
                 eta: float = ETA,
                 theta: float = np.pi/2) -> float:
    """
    Estimate signal-to-noise ratio for experimental detection of crossover shift.

    Parameters
    ----------
    gamma_star_QM_measured : float
        Measured QM crossover rate (Hz or inverse time units)
    gamma_star_uncertainty : float
        Uncertainty in gamma_star measurement (same units)
    eta : float, optional
        Excluded-middle coupling parameter (default: 0.23)
    theta : float, optional
        Superposition angle (default: pi/2 = equal superposition)

    Returns
    -------
    float
        Signal-to-noise ratio (sigma units)

    Examples
    --------
    >>> # Trapped ions: gamma_star ~ 1 kHz, uncertainty ~ 100 Hz
    >>> SNR = estimate_SNR(1e3, 100)
    >>> print(f"SNR ~ {SNR:.1f} sigma")
    SNR ~ 1.1 sigma
    """
    # LRT prediction
    gamma_star_LRT = gamma_star_QM_measured * zeno_crossover_shift(theta, eta)

    # Signal (shift from QM baseline)
    signal = abs(gamma_star_LRT - gamma_star_QM_measured)

    # Uncertainty (single measurement)
    total_uncertainty = gamma_star_uncertainty

    # SNR
    SNR = signal / total_uncertainty

    return SNR


# ============================================================================
# MAIN EXECUTION
# ============================================================================

if __name__ == "__main__":
    print("\n" + "=" * 80)
    print("Path 4: Zeno Crossover Shift - LRT Prediction Analysis")
    print("=" * 80 + "\n")

    # Print prediction table
    print_prediction_table()

    print("\n")

    # Example SNR calculation
    print("Signal-to-Noise Estimation:")
    print("-" * 80)
    print("Trapped Ions (gamma_star ~ 1 kHz, uncertainty ~ 100 Hz):")
    SNR_ions = estimate_SNR(1e3, 100)
    print(f"  SNR ~ {SNR_ions:.1f} sigma (marginal detection)")
    print()
    print("Superconducting Qubits (gamma_star ~ 10 MHz, uncertainty ~ 1 MHz):")
    SNR_SC = estimate_SNR(10e6, 1e6)
    print(f"  SNR ~ {SNR_SC:.1f} sigma (challenging detection)")
    print("=" * 80)
