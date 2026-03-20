"""
Analyze IBM Quantum hardware results for Logic Realism Theory signal.

This script performs the same analysis as Phase 3, but on real hardware data.
We look for systematic deviations from the QM baseline (exponential T2 decay).
"""
import numpy as np
import json
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from scipy import stats
import pandas as pd

print("="*70)
print("HARDWARE RESULTS ANALYSIS - LRT SIGNAL DETECTION")
print("="*70)

# Load hardware results
print("\nLoading hardware data...")
with open('hardware_test_CORRECTED_results.json', 'r') as f:
    data = json.load(f)

metadata = data['metadata']
measurements = data['measurements']

print(f"Backend: {metadata['backend']}")
print(f"Job ID: {metadata['job_id']}")
print(f"Total shots: {metadata['total_shots']:,}")
print(f"Data points: {len(measurements)}")

# Extract arrays
T = np.array([m['T'] for m in measurements])
T_us = np.array([m['T_us'] for m in measurements])
p_error = np.array([m['p_error'] for m in measurements])
shots = np.array([m['shots'] for m in measurements])

print(f"\nDuration range: {T_us.min():.2f} - {T_us.max():.2f} us")
print(f"Error rate range: {p_error.min()*100:.2f}% - {p_error.max()*100:.2f}%")

# QM baseline model: exponential T2 decay
def qm_baseline(T, T2, p0):
    """
    Standard quantum mechanics prediction for Ramsey experiment.

    p_error(T) = 0.5 * (1 - exp(-T/T2)) + p0

    where:
    - T2 is the coherence time
    - p0 is the short-time baseline error (measurement + gate errors)
    """
    return 0.5 * (1.0 - np.exp(-T / T2)) + p0

# Fit QM baseline to data
print("\n" + "="*70)
print("FITTING QM BASELINE (Standard Quantum Mechanics)")
print("="*70)

# Initial guess: T2 ~ 100 us, p0 ~ 0.10
p0_guess = p_error[0]  # Use first measurement as baseline
T2_guess = 100e-6

try:
    popt, pcov = curve_fit(
        qm_baseline,
        T,
        p_error,
        p0=[T2_guess, p0_guess],
        bounds=([1e-6, 0.0], [1e-3, 0.5])  # T2 in [1us, 1ms], p0 in [0, 0.5]
    )

    T2_fit, p0_fit = popt
    T2_err, p0_err = np.sqrt(np.diag(pcov))

    print(f"\nFit Results:")
    print(f"  T2 = {T2_fit*1e6:.2f} +/- {T2_err*1e6:.2f} us")
    print(f"  p0 = {p0_fit*100:.2f}% +/- {p0_err*100:.2f}%")

    # Compute R^2
    p_pred = qm_baseline(T, T2_fit, p0_fit)
    ss_res = np.sum((p_error - p_pred)**2)
    ss_tot = np.sum((p_error - np.mean(p_error))**2)
    r_squared = 1 - (ss_res / ss_tot)

    print(f"  R^2 = {r_squared:.6f} ({r_squared*100:.4f}% variance explained)")

    fit_success = True

except Exception as e:
    print(f"\nFIT FAILED: {e}")
    fit_success = False
    T2_fit, p0_fit = T2_guess, p0_guess
    p_pred = qm_baseline(T, T2_fit, p0_fit)

# Compute residuals (observed - predicted)
residuals = p_error - p_pred
residuals_percent = residuals * 100

print("\n" + "="*70)
print("RESIDUAL ANALYSIS (Looking for LRT signal)")
print("="*70)

print(f"\nResidual Statistics:")
print(f"  Mean: {np.mean(residuals_percent):.4f}%")
print(f"  Std Dev: {np.std(residuals_percent, ddof=1):.4f}%")
print(f"  Max: {np.max(residuals_percent):.4f}%")
print(f"  Min: {np.min(residuals_percent):.4f}%")
print(f"  RMS: {np.sqrt(np.mean(residuals**2))*100:.4f}%")

# Test for systematic deviations
# 1. Mean residual test (should be ~0 if QM is correct)
mean_residual = np.mean(residuals)
sem_residual = stats.sem(residuals)
t_stat = mean_residual / sem_residual
p_value_mean = 2 * (1 - stats.t.cdf(abs(t_stat), df=len(residuals)-1))

print(f"\nMean Residual Test:")
print(f"  t-statistic: {t_stat:.4f}")
print(f"  p-value: {p_value_mean:.4f}")
if p_value_mean < 0.05:
    print(f"  SIGNIFICANT: Systematic deviation detected (p < 0.05)")
else:
    print(f"  Not significant: No systematic deviation (p > 0.05)")

# 2. Normality test (residuals should be normally distributed)
_, p_value_norm = stats.shapiro(residuals)
print(f"\nNormality Test (Shapiro-Wilk):")
print(f"  p-value: {p_value_norm:.4f}")
if p_value_norm > 0.05:
    print(f"  PASS: Residuals are normally distributed (p > 0.05)")
else:
    print(f"  WARNING: Residuals not normally distributed (p < 0.05)")

# 3. Runs test (check for time-dependent patterns)
median_resid = np.median(residuals)
runs_above = (residuals > median_resid).astype(int)
runs = np.diff(runs_above)
n_runs = np.sum(np.abs(runs)) + 1
n = len(residuals)
n1 = np.sum(runs_above)
n2 = n - n1

# Expected runs and variance under null hypothesis
expected_runs = (2 * n1 * n2 / n) + 1
var_runs = (2 * n1 * n2 * (2 * n1 * n2 - n)) / (n**2 * (n - 1))
z_runs = (n_runs - expected_runs) / np.sqrt(var_runs) if var_runs > 0 else 0
p_value_runs = 2 * (1 - stats.norm.cdf(abs(z_runs)))

print(f"\nRuns Test (time-dependence check):")
print(f"  Observed runs: {n_runs}")
print(f"  Expected runs: {expected_runs:.2f}")
print(f"  z-statistic: {z_runs:.4f}")
print(f"  p-value: {p_value_runs:.4f}")
if p_value_runs < 0.05:
    print(f"  SIGNIFICANT: Non-random pattern detected (p < 0.05)")
else:
    print(f"  Not significant: Random residuals (p > 0.05)")

# Create comprehensive visualization
print("\n" + "="*70)
print("GENERATING VISUALIZATIONS")
print("="*70)

fig = plt.figure(figsize=(16, 10))

# 1. Error rate vs time with QM fit
ax1 = plt.subplot(2, 3, 1)
ax1.scatter(T_us, p_error * 100, s=50, alpha=0.6, label='Hardware Data', zorder=3)
T_fine = np.linspace(T.min(), T.max(), 1000)
p_fine = qm_baseline(T_fine, T2_fit, p0_fit)
ax1.plot(T_fine * 1e6, p_fine * 100, 'r-', linewidth=2, label=f'QM Fit (T2={T2_fit*1e6:.1f} us)', zorder=2)
ax1.set_xlabel('Delay Time (us)', fontsize=12)
ax1.set_ylabel('Error Rate (%)', fontsize=12)
ax1.set_title('Hardware Data vs QM Baseline', fontsize=14, fontweight='bold')
ax1.legend(fontsize=10)
ax1.grid(True, alpha=0.3)

# 2. Residuals vs time
ax2 = plt.subplot(2, 3, 2)
ax2.scatter(T_us, residuals_percent, s=50, alpha=0.6, color='blue', zorder=3)
ax2.axhline(0, color='red', linestyle='--', linewidth=2, label='Zero residual', zorder=2)
ax2.axhline(np.mean(residuals_percent), color='green', linestyle='--', linewidth=1,
            label=f'Mean = {np.mean(residuals_percent):.3f}%', zorder=2)
ax2.fill_between(T_us, -2*np.std(residuals_percent), 2*np.std(residuals_percent),
                 alpha=0.2, color='gray', label='±2σ band')
ax2.set_xlabel('Delay Time (us)', fontsize=12)
ax2.set_ylabel('Residual (%)', fontsize=12)
ax2.set_title('Residuals (Observed - QM Prediction)', fontsize=14, fontweight='bold')
ax2.legend(fontsize=9)
ax2.grid(True, alpha=0.3)

# 3. Residual histogram
ax3 = plt.subplot(2, 3, 3)
ax3.hist(residuals_percent, bins=15, alpha=0.7, color='blue', edgecolor='black', density=True)
# Overlay normal distribution
x_norm = np.linspace(residuals_percent.min(), residuals_percent.max(), 100)
y_norm = stats.norm.pdf(x_norm, np.mean(residuals_percent), np.std(residuals_percent))
ax3.plot(x_norm, y_norm, 'r-', linewidth=2, label='Normal fit')
ax3.axvline(0, color='green', linestyle='--', linewidth=2, label='Zero')
ax3.set_xlabel('Residual (%)', fontsize=12)
ax3.set_ylabel('Probability Density', fontsize=12)
ax3.set_title(f'Residual Distribution (Shapiro p={p_value_norm:.3f})', fontsize=14, fontweight='bold')
ax3.legend(fontsize=10)
ax3.grid(True, alpha=0.3)

# 4. Q-Q plot (test normality)
ax4 = plt.subplot(2, 3, 4)
stats.probplot(residuals_percent, dist="norm", plot=ax4)
ax4.set_title('Q-Q Plot (Normality Test)', fontsize=14, fontweight='bold')
ax4.grid(True, alpha=0.3)

# 5. Residuals vs predicted (check for heteroscedasticity)
ax5 = plt.subplot(2, 3, 5)
ax5.scatter(p_pred * 100, residuals_percent, s=50, alpha=0.6, color='purple')
ax5.axhline(0, color='red', linestyle='--', linewidth=2)
ax5.set_xlabel('Predicted Error Rate (%)', fontsize=12)
ax5.set_ylabel('Residual (%)', fontsize=12)
ax5.set_title('Residuals vs Fitted Values', fontsize=14, fontweight='bold')
ax5.grid(True, alpha=0.3)

# 6. Summary statistics panel
ax6 = plt.subplot(2, 3, 6)
ax6.axis('off')
summary_text = f"""
HARDWARE TEST SUMMARY
Backend: {metadata['backend']}
Job ID: {metadata['job_id'][:16]}...
Total Shots: {metadata['total_shots']:,}

QM FIT RESULTS
T2 = {T2_fit*1e6:.2f} ± {T2_err*1e6:.2f} us
p0 = {p0_fit*100:.2f}% ± {p0_err*100:.2f}%
R² = {r_squared:.6f}

RESIDUAL ANALYSIS
Mean: {np.mean(residuals_percent):.4f}%
Std Dev: {np.std(residuals_percent, ddof=1):.4f}%
RMS: {np.sqrt(np.mean(residuals**2))*100:.4f}%

STATISTICAL TESTS
Mean Residual: p = {p_value_mean:.4f}
Normality (SW): p = {p_value_norm:.4f}
Runs Test: p = {p_value_runs:.4f}

LRT SIGNAL DETECTION
{'SIGNIFICANT deviation from QM' if p_value_mean < 0.05 else 'No significant deviation from QM'}
{'Non-normal residuals detected' if p_value_norm < 0.05 else 'Residuals consistent with noise'}
{'Non-random pattern detected' if p_value_runs < 0.05 else 'Residuals appear random'}
"""
ax6.text(0.05, 0.95, summary_text, transform=ax6.transAxes,
         fontsize=10, verticalalignment='top', fontfamily='monospace',
         bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))

plt.tight_layout()
plt.savefig('hardware_analysis_results.png', dpi=300, bbox_inches='tight')
print(f"\nVisualization saved to: hardware_analysis_results.png")

# Save detailed results to CSV
print("\nSaving detailed results to CSV...")
df_results = pd.DataFrame({
    'T_us': T_us,
    'p_error_observed': p_error,
    'p_error_qm_predicted': p_pred,
    'residual': residuals,
    'residual_percent': residuals_percent,
    'shots': shots
})
df_results.to_csv('hardware_analysis_detailed.csv', index=False)
print(f"Detailed results saved to: hardware_analysis_detailed.csv")

# Final verdict
print("\n" + "="*70)
print("FINAL VERDICT")
print("="*70)

print(f"\nQM Baseline Fit Quality: {'EXCELLENT' if r_squared > 0.99 else 'GOOD' if r_squared > 0.95 else 'MODERATE'} (R² = {r_squared:.6f})")

if p_value_mean < 0.05:
    print(f"\nLRT SIGNAL: POTENTIALLY DETECTED")
    print(f"  - Systematic deviation from QM baseline (p = {p_value_mean:.4f})")
    print(f"  - Mean residual: {np.mean(residuals_percent):.4f}%")
    print(f"  - Further investigation recommended")
else:
    print(f"\nLRT SIGNAL: NOT DETECTED")
    print(f"  - No significant deviation from QM baseline (p = {p_value_mean:.4f})")
    print(f"  - Hardware data consistent with standard quantum mechanics")
    print(f"  - Residuals consistent with measurement noise")

print("\n" + "="*70)
print("ANALYSIS COMPLETE")
print("="*70)
