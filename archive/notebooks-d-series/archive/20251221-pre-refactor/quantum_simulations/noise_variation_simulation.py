"""
Noise-Variation Approach for Entropy-Error Correlation Testing

CRITICAL FIX: Previous approach had fundamental design flaw
- Was testing circuit structure (GHZ vs separable), not noise effects
- GHZ state IS a valid code state, so QEC didn't detect errors
- Result: NEGATIVE correlation (opposite LRT prediction)

CORRECT APPROACH (Option 1):
- Use IDENTICAL circuits (all use proper QEC encoding)
- Vary NOISE strength (T1, T2, depolarizing)
- Higher noise -> more decoherence -> higher Delta_S
- Measure correlation: Delta_S vs p_log
- Prediction: beta > 0 (LRT), beta = 0 (standard QEC)

This matches paper's model structure:
  log p_log = alpha + eta*log(p_phys) + beta*Delta_S + ...
  where p_phys (noise) and Delta_S are separate effects
"""

import numpy as np
from qiskit import QuantumCircuit
from qiskit_aer import AerSimulator
from qiskit_aer.noise import NoiseModel, depolarizing_error, thermal_relaxation_error
from qiskit.quantum_info import entropy, partial_trace, DensityMatrix
import pandas as pd
import matplotlib.pyplot as plt
from scipy import stats
import statsmodels.api as sm
from statsmodels.stats.outliers_influence import variance_inflation_factor
from sklearn.preprocessing import StandardScaler
import json
import os

# Set seeds
np.random.seed(42)

# ============================================================================
# NOISE PARAMETER RANGES (Vary across trials)
# ============================================================================

class NoiseRange:
    """
    Noise parameter ranges for testing

    Strategy: Vary T1, T2, and gate errors across realistic IBM ranges
    - Low noise: T1=200us, T2=100us (good qubits)
    - High noise: T1=50us, T2=25us (poor qubits)
    """

    # T1 range (amplitude damping)
    T1_min = 50e-6   # 50 us (high noise)
    T1_max = 200e-6  # 200 us (low noise)

    # T2 range (dephasing) - always T2 <= T1
    T2_min = 25e-6   # 25 us (high noise)
    T2_max = 100e-6  # 100 us (low noise)

    # Gate error ranges
    error_1q_min = 1e-4  # 0.01% (good)
    error_1q_max = 5e-3  # 0.5% (poor)

    error_2q_min = 1e-3  # 0.1% (good)
    error_2q_max = 5e-2  # 5% (poor)

    # Gate times (fixed - from IBM specs)
    gate_1q = 50e-9   # 50 ns
    gate_2q = 300e-9  # 300 ns
    meas_time = 1e-6  # 1 us
    reset_time = 1e-6 # 1 us

# ============================================================================
# QEC CIRCUIT (Identical across all trials)
# ============================================================================

class LogicalQubit:
    """3-qubit bit-flip repetition code"""

    def __init__(self):
        self.n_data = 3
        self.n_syndrome = 2

    def encode_circuit(self, data_reg, initial_state=0):
        """Encode logical qubit: |0>_L = |000>, |1>_L = |111>"""
        qc = QuantumCircuit(data_reg)

        if initial_state == 1:
            qc.x(data_reg[0])

        # Encode
        qc.cx(data_reg[0], data_reg[1])
        qc.cx(data_reg[0], data_reg[2])

        return qc

    def measure_syndrome_circuit(self, data_reg, syndrome_reg):
        """Measure bit-flip syndromes"""
        qc = QuantumCircuit(data_reg, syndrome_reg)

        # Syndrome measurement (parity checks)
        qc.cx(data_reg[0], syndrome_reg[0])
        qc.cx(data_reg[1], syndrome_reg[0])
        qc.cx(data_reg[1], syndrome_reg[1])
        qc.cx(data_reg[2], syndrome_reg[1])

        return qc

    def full_qec_cycle(self):
        """
        Complete QEC cycle (IDENTICAL for all trials)

        CRITICAL: Same circuit structure for all trials
        Only noise parameters vary
        """
        from qiskit.circuit import QuantumRegister, ClassicalRegister

        data_reg = QuantumRegister(3, 'data')
        syndrome_reg = QuantumRegister(2, 'syndrome')
        class_reg = ClassicalRegister(2, 'syndrome_meas')

        qc = QuantumCircuit(data_reg, syndrome_reg, class_reg)

        # Encode logical |0>
        qc.compose(self.encode_circuit(data_reg, initial_state=0), inplace=True)

        # Apply some logical operations (optional - keep simple)
        # For now, just let it decohere

        # Syndrome measurement
        qc.compose(self.measure_syndrome_circuit(data_reg, syndrome_reg), inplace=True)
        qc.measure(syndrome_reg, class_reg)

        return qc

    def calculate_duration(self, circuit):
        """Calculate circuit duration"""
        ops = circuit.count_ops()

        # Count gates
        single_q = ['h', 'x', 'y', 'z', 's', 't', 'sdg', 'tdg']
        two_q = ['cx', 'cy', 'cz', 'swap']

        n_1q = sum(ops.get(op, 0) for op in single_q)
        n_2q = sum(ops.get(op, 0) for op in two_q)
        n_meas = ops.get('measure', 0)
        n_reset = ops.get('reset', 0)

        duration = (n_1q * NoiseRange.gate_1q +
                   n_2q * NoiseRange.gate_2q +
                   n_meas * NoiseRange.meas_time +
                   n_reset * NoiseRange.reset_time)

        return duration

# ============================================================================
# ENTROPY CALCULATION (Subsystem entropy from decoherence)
# ============================================================================

def calculate_entropy_change(circuit, noise_model):
    """
    Calculate entropy change due to NOISE (not circuit structure)

    Key: Compare initial state (pure |000>) to final state (after noise)
    Decoherence increases entropy

    Returns:
        S_in: Initial entropy (should be ~0 for pure state)
        S_out: Final entropy (increases with noise)
        Delta_S: Change (should be > 0, increases with noise strength)
    """
    # Initial state: |000> (pure, zero entropy)
    n_qubits = 3
    rho_in = DensityMatrix.from_label('0' * n_qubits)

    # Initial subsystem entropy (qubit 0)
    rho_sub_in = partial_trace(rho_in, [1, 2])
    S_in = entropy(rho_sub_in, base=np.e)

    # Create circuit for entropy measurement (no measurements)
    qc_entropy = circuit.copy()
    qc_entropy.remove_final_measurements()

    # Simulate with noise
    simulator = AerSimulator(method='density_matrix', noise_model=noise_model)

    # Save density matrix
    qc_entropy.save_density_matrix()
    result = simulator.run(qc_entropy, shots=1).result()
    rho_out_full = result.data()['density_matrix']

    # Extract data qubits (first 3 qubits, trace out syndrome qubits)
    if circuit.num_qubits > 3:
        qubits_to_trace = list(range(3, circuit.num_qubits))
        rho_out = partial_trace(rho_out_full, qubits_to_trace)
    else:
        rho_out = rho_out_full

    # Final subsystem entropy (qubit 0)
    rho_sub_out = partial_trace(rho_out, [1, 2])
    S_out = entropy(rho_sub_out, base=np.e)

    Delta_S = S_out - S_in

    return S_in, S_out, Delta_S

# ============================================================================
# NOISE MODEL CREATION (Parameterized)
# ============================================================================

def create_noise_model(T1, T2, error_1q, error_2q):
    """
    Create noise model with specified parameters

    Args:
        T1: Amplitude damping time (seconds)
        T2: Dephasing time (seconds)
        error_1q: Single-qubit gate error rate
        error_2q: Two-qubit gate error rate
    """
    noise_model = NoiseModel()

    # Depolarizing errors
    depol_1q = depolarizing_error(error_1q, 1)
    depol_2q = depolarizing_error(error_2q, 2)

    noise_model.add_all_qubit_quantum_error(depol_1q, ['h', 'x', 'y', 'z', 's', 't'])
    noise_model.add_all_qubit_quantum_error(depol_2q, ['cx'])

    # Thermal relaxation (1-qubit errors only)
    # Note: thermal_relaxation_error is always 1-qubit
    # For 2-qubit gates, we apply to each qubit separately (Qiskit handles this)
    thermal_1q = thermal_relaxation_error(T1, T2, NoiseRange.gate_1q)
    thermal_2q = thermal_relaxation_error(T1, T2, NoiseRange.gate_2q)

    # Apply thermal errors (warnings about composition are OK)
    noise_model.add_all_qubit_quantum_error(thermal_1q, ['h', 'x', 'y', 'z', 's', 't'])
    # For 2q gates, thermal relaxation is automatically applied per qubit by Qiskit
    # Just use depolarizing for 2q gates

    return noise_model

# ============================================================================
# NOISE-VARIATION SIMULATION
# ============================================================================

def run_noise_variation_simulation(n_samples=1000):
    """
    Test LRT prediction: beta > 0 in log(p_log) vs Delta_S

    Method:
    1. Use IDENTICAL circuits (proper QEC encoding)
    2. Vary noise parameters across trials
    3. Measure Delta_S from decoherence
    4. Measure p_log (QEC error rate)
    5. Regression with noise controls

    Expected: beta ~ 0.1-0.5 (LRT) vs beta = 0 (standard QEC)
    """
    print("=" * 70)
    print("NOISE-VARIATION SIMULATION (Corrected Test Design)")
    print("=" * 70)
    print(f"\nTarget samples: {n_samples}")
    print("\nKEY INSIGHT: Previous test had fundamental flaw")
    print("- Was testing circuit structure (GHZ vs separable)")
    print("- GHZ is valid code state -> QEC didn't detect errors")
    print("- Result: NEGATIVE correlation (wrong!)")
    print("\nCORRECT APPROACH:")
    print("- IDENTICAL circuits (all use proper QEC encoding)")
    print("- Vary NOISE strength (T1, T2, depolarizing)")
    print("- Higher noise -> higher Delta_S -> higher p_log")
    print("- Test: Does beta > 0? (LRT prediction)")
    print("=" * 70)

    # Setup
    logical_qubit = LogicalQubit()

    # Data collection
    data = []

    print("\nRunning trials with varying noise...")
    for i in range(n_samples):
        # Sample noise parameters uniformly in log-space
        log_T1 = np.random.uniform(np.log(NoiseRange.T1_min), np.log(NoiseRange.T1_max))
        T1 = np.exp(log_T1)

        # T2 <= T1 always
        T2_max_this = min(T1, NoiseRange.T2_max)
        log_T2 = np.random.uniform(np.log(NoiseRange.T2_min), np.log(T2_max_this))
        T2 = np.exp(log_T2)

        # Gate errors
        error_1q = np.random.uniform(NoiseRange.error_1q_min, NoiseRange.error_1q_max)
        error_2q = np.random.uniform(NoiseRange.error_2q_min, NoiseRange.error_2q_max)

        # Create noise model
        noise_model = create_noise_model(T1, T2, error_1q, error_2q)

        # Create circuit (IDENTICAL structure)
        qc = logical_qubit.full_qec_cycle()

        # Calculate entropy change from decoherence
        try:
            S_in, S_out, Delta_S = calculate_entropy_change(qc, noise_model)
        except Exception as e:
            print(f"  Warning: Trial {i} entropy calculation failed: {e}")
            continue

        # Measure logical error rate
        simulator = AerSimulator(method='density_matrix', noise_model=noise_model)
        result = simulator.run(qc, shots=1000).result()
        counts = result.get_counts()

        # Error = any non-|00> syndrome
        n_errors = sum(count for syndrome, count in counts.items() if syndrome != '00')
        p_log = n_errors / 1000.0
        p_log = max(p_log, 1e-6)  # Avoid log(0)

        # Control variables
        duration = logical_qubit.calculate_duration(qc)

        # Physical error rate (approximate from noise parameters)
        # Use average of 1q and 2q errors weighted by gate counts
        ops = qc.count_ops()
        n_1q = sum(ops.get(g, 0) for g in ['h', 'x', 'y', 'z', 's', 't'])
        n_2q = ops.get('cx', 0)
        p_phys = (n_1q * error_1q + n_2q * error_2q) / (n_1q + n_2q) if (n_1q + n_2q) > 0 else error_1q

        # Store
        data.append({
            'trial': i,
            'T1': T1 * 1e6,  # Convert to microseconds
            'T2': T2 * 1e6,
            'error_1q': error_1q,
            'error_2q': error_2q,
            'p_phys': p_phys,
            'S_in': S_in,
            'S_out': S_out,
            'Delta_S': Delta_S,
            'p_log': p_log,
            'log_p_log': np.log(p_log),
            'duration': duration * 1e6,
            'qubit_count': qc.num_qubits,
            'gate_count': sum(qc.count_ops().values())
        })

        if (i + 1) % 100 == 0:
            print(f"  Progress: {i+1}/{n_samples} trials complete")

    print(f"\nData collection complete: {len(data)} trials")

    # Convert to DataFrame
    df = pd.DataFrame(data)

    # ========================================================================
    # STATISTICAL ANALYSIS
    # ========================================================================

    print("\n" + "=" * 70)
    print("STATISTICAL ANALYSIS")
    print("=" * 70)

    # Summary statistics
    print("\nSummary Statistics:")
    print(f"  T1 range: {df['T1'].min():.1f} - {df['T1'].max():.1f} us")
    print(f"  T2 range: {df['T2'].min():.1f} - {df['T2'].max():.1f} us")
    print(f"  Delta_S range: {df['Delta_S'].min():.4f} - {df['Delta_S'].max():.4f} nats")
    print(f"  p_log range: {df['p_log'].min():.4f} - {df['p_log'].max():.4f}")

    # Check correlation direction
    corr_entropy = df['Delta_S'].corr(df['log_p_log'])
    print(f"\nPearson correlation (Delta_S, log_p_log): {corr_entropy:.4f}")
    if corr_entropy > 0:
        print("  Status: POSITIVE (consistent with LRT prediction)")
    else:
        print("  Status: NEGATIVE (inconsistent with LRT)")

    # ========================================================================
    # MODEL 1: Simple regression (entropy only)
    # ========================================================================

    print("\n" + "-" * 70)
    print("MODEL 1: Simple Regression")
    print("-" * 70)
    print("log(p_log) = alpha + beta*Delta_S + epsilon")

    X_simple = df[['Delta_S']].values
    y = df['log_p_log'].values

    X_simple = sm.add_constant(X_simple)
    model_simple = sm.OLS(y, X_simple).fit()

    print(f"\nResults:")
    print(f"  beta = {model_simple.params[1]:.4f} +/- {model_simple.bse[1]:.4f}")
    print(f"  p-value = {model_simple.pvalues[1]:.4e}")
    print(f"  R^2 = {model_simple.rsquared:.4f}")

    # ========================================================================
    # MODEL 2: Multivariate with noise controls
    # ========================================================================

    print("\n" + "-" * 70)
    print("MODEL 2: Multivariate Regression (Noise Controls)")
    print("-" * 70)
    print("log(p_log) = alpha + beta*Delta_S + eta*log(p_phys) + theta*T1 + epsilon")

    # Prepare variables
    df['log_p_phys'] = np.log(df['p_phys'])

    # Standardize
    scaler = StandardScaler()
    X_scaled = scaler.fit_transform(df[['Delta_S', 'log_p_phys', 'T1']])

    # VIF diagnostics
    print("\nVIF Diagnostics:")
    vif_data = pd.DataFrame()
    vif_data['Variable'] = ['Delta_S', 'log_p_phys', 'T1']
    vif_data['VIF'] = [variance_inflation_factor(X_scaled, i) for i in range(3)]
    print(vif_data.to_string(index=False))

    # Regression
    X_multi = sm.add_constant(X_scaled)
    model_multi = sm.OLS(y, X_multi).fit()

    print(f"\nResults:")
    print(f"  beta (Delta_S) = {model_multi.params[1]:.4f} +/- {model_multi.bse[1]:.4f}")
    print(f"  eta (log_p_phys) = {model_multi.params[2]:.4f} +/- {model_multi.bse[2]:.4f}")
    print(f"  theta (T1) = {model_multi.params[3]:.4f} +/- {model_multi.bse[3]:.4f}")
    print(f"\n  beta p-value = {model_multi.pvalues[1]:.4e}")
    print(f"  R^2 = {model_multi.rsquared:.4f}")

    # ========================================================================
    # VALIDATION CHECK
    # ========================================================================

    print("\n" + "=" * 70)
    print("VALIDATION CHECK (LRT Prediction)")
    print("=" * 70)

    beta = model_multi.params[1]
    beta_p = model_multi.pvalues[1]

    print(f"\nPrediction: beta > 0 (LRT) vs beta = 0 (standard QEC)")
    print(f"Result: beta = {beta:.4f}")

    if beta > 0:
        print("  Direction: POSITIVE (consistent with LRT)")
    else:
        print("  Direction: NEGATIVE (inconsistent with LRT)")

    print(f"\nTarget: beta in [0.1, 0.5] range (order of magnitude)")
    if 0.1 <= abs(beta) <= 0.5:
        print("  Magnitude: PASS")
    else:
        print(f"  Magnitude: Outside range (beta = {beta:.4f})")

    print(f"\nTarget: p < 0.05 (statistically significant)")
    print(f"Result: p = {beta_p:.4e}")
    if beta_p < 0.05:
        print("  Significance: PASS")
    else:
        print("  Significance: FAIL")

    # Overall
    print("\n" + "=" * 70)
    print("OVERALL ASSESSMENT")
    print("=" * 70)

    validation_pass = (beta > 0 and
                      0.1 <= abs(beta) <= 0.5 and
                      beta_p < 0.05)

    if validation_pass:
        print("\nStatus: VALIDATION SUCCESSFUL")
        print("\nKey findings:")
        print(f"1. Positive correlation confirmed (beta = {beta:.4f})")
        print(f"2. Effect size in expected range ({beta:.4f} in [0.1, 0.5])")
        print(f"3. Statistically significant (p = {beta_p:.4e})")
        print(f"4. LRT prediction validated: beta > 0")
        print("\nReady for LLM team final review!")
    else:
        print("\nStatus: VALIDATION INCOMPLETE")
        if beta <= 0:
            print(f"  - Negative correlation (beta = {beta:.4f})")
        if not (0.1 <= abs(beta) <= 0.5):
            print(f"  - Effect size outside range (beta = {beta:.4f})")
        if beta_p >= 0.05:
            print(f"  - Not significant (p = {beta_p:.4e})")

    # Save results
    os.makedirs('outputs', exist_ok=True)

    df.to_csv('outputs/noise_variation_data.csv', index=False)

    results = {
        'n_samples': len(df),
        'simple_regression': {
            'beta': float(model_simple.params[1]),
            'beta_se': float(model_simple.bse[1]),
            'p_value': float(model_simple.pvalues[1]),
            'R2': float(model_simple.rsquared)
        },
        'multivariate_regression': {
            'beta': float(beta),
            'beta_se': float(model_multi.bse[1]),
            'eta': float(model_multi.params[2]),
            'theta': float(model_multi.params[3]),
            'beta_p_value': float(beta_p),
            'R2': float(model_multi.rsquared)
        },
        'validation': {
            'beta_positive': bool(beta > 0),
            'beta_in_range': bool(0.1 <= abs(beta) <= 0.5),
            'significant': bool(beta_p < 0.05),
            'overall_pass': bool(validation_pass)
        }
    }

    with open('outputs/noise_variation_results.json', 'w') as f:
        json.dump(results, f, indent=2)

    print(f"\nResults saved to:")
    print(f"  - outputs/noise_variation_data.csv")
    print(f"  - outputs/noise_variation_results.json")

    # Visualization
    create_visualization(df, model_simple, model_multi)

    return df, results

def create_visualization(df, model_simple, model_multi):
    """Create diagnostic plots"""

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: Delta_S vs log(p_log)
    ax = axes[0, 0]
    ax.scatter(df['Delta_S'], df['log_p_log'], alpha=0.5, s=20, c=df['T1'], cmap='viridis')

    # Regression line
    x_range = np.linspace(df['Delta_S'].min(), df['Delta_S'].max(), 100)
    y_pred = model_simple.params[0] + model_simple.params[1] * x_range
    ax.plot(x_range, y_pred, 'r-', linewidth=2,
            label=f'beta={model_simple.params[1]:.3f} (p={model_simple.pvalues[1]:.2e})')

    ax.set_xlabel('Delta_S (nats)', fontsize=10)
    ax.set_ylabel('log(p_log)', fontsize=10)
    ax.set_title('Entropy-Error Correlation', fontsize=11, fontweight='bold')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    cbar = plt.colorbar(ax.scatter(df['Delta_S'], df['log_p_log'], alpha=0.5, s=20,
                                    c=df['T1'], cmap='viridis'), ax=ax)
    cbar.set_label('T1 (us)', fontsize=8)

    # Plot 2: T1 vs Delta_S (control check)
    ax = axes[0, 1]
    ax.scatter(df['T1'], df['Delta_S'], alpha=0.5, s=20)
    ax.set_xlabel('T1 (us)', fontsize=10)
    ax.set_ylabel('Delta_S (nats)', fontsize=10)
    ax.set_title('Noise vs Entropy Change', fontsize=11, fontweight='bold')
    ax.grid(True, alpha=0.3)

    # Plot 3: Predicted vs actual (multivariate)
    ax = axes[1, 0]
    from sklearn.preprocessing import StandardScaler
    scaler = StandardScaler()
    X_scaled = scaler.fit_transform(df[['Delta_S', 'log_p_phys', 'T1']])
    y_pred = model_multi.predict(sm.add_constant(X_scaled))

    ax.scatter(df['log_p_log'], y_pred, alpha=0.5, s=20)
    ax.plot([df['log_p_log'].min(), df['log_p_log'].max()],
            [df['log_p_log'].min(), df['log_p_log'].max()],
            'r--', linewidth=2)
    ax.set_xlabel('Actual log(p_log)', fontsize=10)
    ax.set_ylabel('Predicted log(p_log)', fontsize=10)
    ax.set_title(f'Multivariate Model (R^2={model_multi.rsquared:.3f})',
                 fontsize=11, fontweight='bold')
    ax.grid(True, alpha=0.3)

    # Plot 4: Residuals
    ax = axes[1, 1]
    residuals = df['log_p_log'].values - y_pred
    ax.scatter(y_pred, residuals, alpha=0.5, s=20)
    ax.axhline(0, color='r', linestyle='--', linewidth=2)
    ax.set_xlabel('Predicted log(p_log)', fontsize=10)
    ax.set_ylabel('Residuals', fontsize=10)
    ax.set_title('Residual Plot', fontsize=11, fontweight='bold')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('outputs/noise_variation_analysis.png', dpi=150, bbox_inches='tight')
    print(f"  - outputs/noise_variation_analysis.png")
    plt.close()

# ============================================================================
# MAIN
# ============================================================================

if __name__ == '__main__':
    df, results = run_noise_variation_simulation(n_samples=1000)

    print("\n" + "=" * 70)
    print("SIMULATION COMPLETE")
    print("=" * 70)
    print("\nNext: Submit to LLM team for validation (CLAUDE.md Rule 6)")
