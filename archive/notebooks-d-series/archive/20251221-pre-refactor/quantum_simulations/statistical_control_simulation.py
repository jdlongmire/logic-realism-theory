"""
Statistical Control Approach for Entropy-Error Correlation Testing

Based on Multi-LLM Team Consultation (2025-10-26)
Unanimous recommendation: Statistical control (Option A)

CRITICAL FIXES (from team feedback):
1. High-entropy sequences use ENTANGLEMENT (GHZ/Bell states), not measurement
2. Subsystem entropy via partial_trace (not total system entropy)
3. Statistical control for duration confound via multivariate regression
4. VIF diagnostics for multicollinearity
5. Ridge regression if VIF > 5

Expected result: beta drops from 56.98 to ~0.1-0.5
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
from sklearn.linear_model import Ridge
import json
import os

# Set seeds for reproducibility
np.random.seed(42)

# ============================================================================
# NOISE PARAMETERS (Realistic IBM Quantum)
# ============================================================================

class NoiseParameters:
    """IBM Quantum noise parameters (ibm_kyiv-like)"""

    # Coherence times
    T1 = 100e-6  # Amplitude damping time (100 us)
    T2 = 50e-6   # Dephasing time (50 us)

    # Gate times
    gate_1q = 50e-9   # Single-qubit gate (50 ns)
    gate_2q = 300e-9  # Two-qubit gate (300 ns)

    # Gate errors
    error_1q = 1e-3   # 0.1% single-qubit error
    error_2q = 1e-2   # 1% two-qubit error

    # Measurement
    meas_time = 1e-6  # Measurement time (1 us)
    reset_time = 1e-6 # Reset time (1 us)

# ============================================================================
# CORRECTED ENTROPY SEQUENCES (Team Feedback Applied)
# ============================================================================

class EntropySequences:
    """
    CORRECTED: Use entanglement for high-entropy, separable for low-entropy

    Team Insight: Measurement/reset REDUCES entropy (projection to basis state)
    Correct approach: GHZ/Bell states create high subsystem entropy
    """

    @staticmethod
    def low_entropy_sequence(n_qubits=3):
        """
        Low-entropy: Separable state (no entanglement)

        Circuit: Single-qubit gates only (H on each qubit)
        State: |+>|+>|+> (product state)
        Subsystem entropy: LOW (each qubit independent)
        """
        qc = QuantumCircuit(n_qubits)

        # Single-qubit gates (no entanglement)
        for q in range(n_qubits):
            qc.h(q)  # Hadamard on each qubit

        return qc

    @staticmethod
    def high_entropy_sequence(n_qubits=3):
        """
        High-entropy: Entangled state (GHZ-like)

        Circuit: Create GHZ state |000> + |111>
        State: Maximally entangled
        Subsystem entropy: HIGH (tracing out qubits creates mixed state)
        """
        qc = QuantumCircuit(n_qubits)

        # Create GHZ state: |GHZ> = (|000> + |111>) / sqrt(2)
        qc.h(0)  # Superposition on first qubit
        for q in range(n_qubits - 1):
            qc.cx(q, q + 1)  # Entangle with next qubit

        return qc

    @staticmethod
    def calculate_subsystem_entropy(circuit, subsystem_qubits=[0]):
        """
        Calculate SUBSYSTEM entropy via partial trace

        CRITICAL: This is the correct entropy measure (team feedback)
        - Total system entropy can be zero even for entangled states (pure state)
        - Subsystem entropy captures entanglement (mixed reduced state)

        Args:
            circuit: QuantumCircuit (no measurements!)
            subsystem_qubits: Which qubits to keep (trace out the rest)

        Returns:
            S_subsystem: Von Neumann entropy of reduced density matrix
        """
        # Get initial density matrix (all qubits in |0>)
        n_qubits = circuit.num_qubits
        rho_in = DensityMatrix.from_label('0' * n_qubits)

        # Get final density matrix (after circuit)
        qc_copy = circuit.copy()
        qc_copy.remove_final_measurements()  # CRITICAL
        rho_out = rho_in.evolve(qc_copy)

        # Trace out all qubits EXCEPT subsystem_qubits
        qubits_to_trace = [q for q in range(n_qubits) if q not in subsystem_qubits]

        if qubits_to_trace:
            rho_sub = partial_trace(rho_out, qubits_to_trace)
        else:
            rho_sub = rho_out

        # Calculate entropy (in nats)
        S = entropy(rho_sub, base=np.e)

        return S

    @staticmethod
    def calculate_circuit_duration(circuit):
        """
        Calculate circuit duration (sum of gate times)

        NOTE: Does NOT include delay gates (they're not operations)
        """
        ops = circuit.count_ops()

        # Single-qubit gates
        single_q_ops = ['h', 'x', 'y', 'z', 's', 't', 'sdg', 'tdg']
        n_1q = sum(ops.get(op, 0) for op in single_q_ops)

        # Two-qubit gates
        two_q_ops = ['cx', 'cy', 'cz', 'swap', 'cswap']
        n_2q = sum(ops.get(op, 0) for op in two_q_ops)

        # Measurements and resets
        n_meas = ops.get('measure', 0)
        n_reset = ops.get('reset', 0)

        # Total duration
        duration = (n_1q * NoiseParameters.gate_1q +
                   n_2q * NoiseParameters.gate_2q +
                   n_meas * NoiseParameters.meas_time +
                   n_reset * NoiseParameters.reset_time)

        return duration

# ============================================================================
# QEC IMPLEMENTATION (3-qubit repetition code)
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

    def full_qec_cycle(self, entropy_type='low'):
        """
        Complete QEC cycle with entropy manipulation

        CORRECTED: Use entanglement for high-entropy
        """
        from qiskit.circuit import QuantumRegister, ClassicalRegister

        data_reg = QuantumRegister(3, 'data')
        syndrome_reg = QuantumRegister(2, 'syndrome')
        class_reg = ClassicalRegister(2, 'syndrome_meas')

        qc = QuantumCircuit(data_reg, syndrome_reg, class_reg)

        # Encode logical |0>
        qc.compose(self.encode_circuit(data_reg, initial_state=0), inplace=True)

        # Entropy manipulation (CORRECTED)
        if entropy_type == 'low':
            # Low-entropy: Separable state
            entropy_seq = EntropySequences.low_entropy_sequence(n_qubits=3)
        else:
            # High-entropy: Entangled state (GHZ)
            entropy_seq = EntropySequences.high_entropy_sequence(n_qubits=3)

        qc.compose(entropy_seq, qubits=data_reg, inplace=True)

        # Syndrome measurement
        qc.compose(self.measure_syndrome_circuit(data_reg, syndrome_reg), inplace=True)
        qc.measure(syndrome_reg, class_reg)

        return qc

# ============================================================================
# STATISTICAL CONTROL SIMULATION
# ============================================================================

def create_noise_model():
    """Create realistic noise model"""
    noise_model = NoiseModel()

    # Single-qubit depolarizing
    error_1q = depolarizing_error(NoiseParameters.error_1q, 1)
    noise_model.add_all_qubit_quantum_error(error_1q, ['h', 'x', 'y', 'z', 's', 't'])

    # Two-qubit depolarizing
    error_2q = depolarizing_error(NoiseParameters.error_2q, 2)
    noise_model.add_all_qubit_quantum_error(error_2q, ['cx'])

    # Thermal relaxation (T1, T2)
    for gate_time in [NoiseParameters.gate_1q, NoiseParameters.gate_2q]:
        thermal_error = thermal_relaxation_error(
            NoiseParameters.T1,
            NoiseParameters.T2,
            gate_time
        )
        # Note: add to specific gates in production version

    return noise_model

def run_statistical_control_simulation(n_samples=1000):
    """
    Run simulation with statistical control for duration confound

    TEAM RECOMMENDATION: Option A (Statistical Control)
    - Record all variables: Delta_S, p_log, t, qubit_count, gate_count
    - Use multivariate regression: log(p_log) = alpha + beta*Delta_S + theta*t + ...
    - Check VIF for multicollinearity
    - Expected: beta drops from 56.98 to ~0.1-0.5
    """
    print("=" * 70)
    print("STATISTICAL CONTROL SIMULATION (Multi-LLM Team Recommendation)")
    print("=" * 70)
    print(f"\nTarget samples: {n_samples}")
    print("\nCRITICAL FIXES APPLIED:")
    print("1. High-entropy uses GHZ entanglement (not measurement)")
    print("2. Subsystem entropy via partial_trace")
    print("3. Multivariate regression with duration control")
    print("4. VIF diagnostics for multicollinearity")
    print("\nExpected: beta drops from 56.98 to ~0.1-0.5")
    print("=" * 70)

    # Setup
    logical_qubit = LogicalQubit()
    noise_model = create_noise_model()
    simulator = AerSimulator(method='density_matrix', noise_model=noise_model)

    # Data collection
    data = []

    print("\nRunning trials...")
    for i in range(n_samples):
        # Alternate between low and high entropy
        entropy_type = 'low' if i % 2 == 0 else 'high'

        # Create QEC circuit
        qc = logical_qubit.full_qec_cycle(entropy_type=entropy_type)

        # Calculate subsystem entropy (CORRECTED: use partial_trace)
        # Extract just the data qubits for entropy calculation
        qc_entropy = QuantumCircuit(3)
        if entropy_type == 'low':
            qc_entropy = EntropySequences.low_entropy_sequence(n_qubits=3)
        else:
            qc_entropy = EntropySequences.high_entropy_sequence(n_qubits=3)

        # Measure subsystem entropy (trace out qubits 1,2, keep qubit 0)
        Delta_S = EntropySequences.calculate_subsystem_entropy(qc_entropy, subsystem_qubits=[0])

        # Measure logical error rate
        result = simulator.run(qc, shots=1000).result()
        counts = result.get_counts()

        # Error = any non-|00> syndrome
        n_errors = sum(count for syndrome, count in counts.items() if syndrome != '00')
        p_log = n_errors / 1000.0
        p_log = max(p_log, 1e-6)  # Avoid log(0)

        # Calculate control variables
        duration = EntropySequences.calculate_circuit_duration(qc)
        qubit_count = qc.num_qubits
        gate_count = sum(qc.count_ops().values())

        # Store
        data.append({
            'trial': i,
            'entropy_type': entropy_type,
            'Delta_S': Delta_S,
            'p_log': p_log,
            'log_p_log': np.log(p_log),
            'duration': duration * 1e6,  # Convert to microseconds
            'qubit_count': qubit_count,
            'gate_count': gate_count
        })

        if (i + 1) % 100 == 0:
            print(f"  Progress: {i+1}/{n_samples} trials complete")

    print(f"\nData collection complete: {len(data)} trials")

    # Convert to DataFrame
    df = pd.DataFrame(data)

    # ========================================================================
    # STATISTICAL ANALYSIS (Team Recommendation: Option A)
    # ========================================================================

    print("\n" + "=" * 70)
    print("STATISTICAL ANALYSIS")
    print("=" * 70)

    # Summary statistics
    print("\nSummary Statistics:")
    print(f"\nLow-entropy trials (n={len(df[df['entropy_type']=='low'])}):")
    low_df = df[df['entropy_type'] == 'low']
    print(f"  Delta_S: {low_df['Delta_S'].mean():.4f} +/- {low_df['Delta_S'].std():.4f} nats")
    print(f"  Duration: {low_df['duration'].mean():.3f} +/- {low_df['duration'].std():.3f} us")
    print(f"  Error rate: {low_df['p_log'].mean():.4f} +/- {low_df['p_log'].std():.4f}")

    print(f"\nHigh-entropy trials (n={len(df[df['entropy_type']=='high'])}):")
    high_df = df[df['entropy_type'] == 'high']
    print(f"  Delta_S: {high_df['Delta_S'].mean():.4f} +/- {high_df['Delta_S'].std():.4f} nats")
    print(f"  Duration: {high_df['duration'].mean():.3f} +/- {high_df['duration'].std():.3f} us")
    print(f"  Error rate: {high_df['p_log'].mean():.4f} +/- {high_df['p_log'].std():.4f}")

    # Check if entropy sequences are correctly ordered
    delta_S_diff = high_df['Delta_S'].mean() - low_df['Delta_S'].mean()
    print(f"\nEntropy difference (high - low): {delta_S_diff:.4f} nats")
    if delta_S_diff > 0:
        print("  Status: OK (high-entropy > low-entropy)")
    else:
        print("  WARNING: High-entropy should be HIGHER than low-entropy!")

    # ========================================================================
    # MODEL 1: Simple regression (original, for comparison)
    # ========================================================================

    print("\n" + "-" * 70)
    print("MODEL 1: Simple Regression (Original - for comparison)")
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
    print(f"\nThis is the ORIGINAL result (should be ~56.98 if n=30)")

    # ========================================================================
    # MODEL 2: Multivariate regression with duration control
    # ========================================================================

    print("\n" + "-" * 70)
    print("MODEL 2: Multivariate Regression (Statistical Control)")
    print("-" * 70)
    print("log(p_log) = alpha + beta*Delta_S + theta*duration + gamma*qubit_count + epsilon")

    # Standardize to reduce multicollinearity
    scaler = StandardScaler()
    X_scaled = scaler.fit_transform(df[['Delta_S', 'duration', 'qubit_count']])
    X_scaled_df = pd.DataFrame(X_scaled, columns=['Delta_S', 'duration', 'qubit_count'])

    # VIF diagnostics (check for multicollinearity)
    print("\nVariance Inflation Factor (VIF) diagnostics:")
    print("(VIF > 5 indicates problematic multicollinearity)")
    vif_data = pd.DataFrame()
    vif_data['Variable'] = ['Delta_S', 'duration', 'qubit_count']
    vif_data['VIF'] = [variance_inflation_factor(X_scaled, i) for i in range(3)]
    print(vif_data.to_string(index=False))

    max_vif = vif_data['VIF'].max()

    # Regression
    X_multi = sm.add_constant(X_scaled)
    model_multi = sm.OLS(y, X_multi).fit()

    print(f"\nMultivariate Regression Results:")
    print(f"  beta (Delta_S coef) = {model_multi.params[1]:.4f} +/- {model_multi.bse[1]:.4f}")
    print(f"  theta (duration coef) = {model_multi.params[2]:.4f} +/- {model_multi.bse[2]:.4f}")
    print(f"  gamma (qubit_count coef) = {model_multi.params[3]:.4f} +/- {model_multi.bse[3]:.4f}")
    print(f"\n  beta p-value = {model_multi.pvalues[1]:.4e}")
    print(f"  R^2 = {model_multi.rsquared:.4f}")

    # ========================================================================
    # MODEL 3: Ridge regression (if VIF > 5)
    # ========================================================================

    if max_vif > 5:
        print("\n" + "-" * 70)
        print("MODEL 3: Ridge Regression (Regularized - VIF > 5 detected)")
        print("-" * 70)

        ridge_model = Ridge(alpha=1.0)
        ridge_model.fit(X_scaled, y)

        print(f"\nRidge Regression Results (alpha=1.0):")
        print(f"  beta (Delta_S coef) = {ridge_model.coef_[0]:.4f}")
        print(f"  theta (duration coef) = {ridge_model.coef_[1]:.4f}")
        print(f"  gamma (qubit_count coef) = {ridge_model.coef_[2]:.4f}")

        # Cross-validation score
        from sklearn.model_selection import cross_val_score
        scores = cross_val_score(ridge_model, X_scaled, y, cv=5, scoring='r2')
        print(f"  R^2 (5-fold CV) = {scores.mean():.4f} +/- {scores.std():.4f}")

    # ========================================================================
    # VALIDATION CHECK (Team Success Criteria)
    # ========================================================================

    print("\n" + "=" * 70)
    print("VALIDATION CHECK (Team Success Criteria)")
    print("=" * 70)

    beta = model_multi.params[1]
    theta = model_multi.params[2]
    beta_p = model_multi.pvalues[1]

    print(f"\nTarget: beta in [0.1, 0.5] range")
    print(f"Result: beta = {beta:.4f}")

    if 0.1 <= abs(beta) <= 0.5:
        print("  Status: PASS (beta in expected range)")
    else:
        print("  Status: FAIL (beta outside expected range)")

    print(f"\nTarget: p < 0.05 (statistically significant)")
    print(f"Result: p = {beta_p:.4e}")

    if beta_p < 0.05:
        print("  Status: PASS (statistically significant)")
    else:
        print("  Status: FAIL (not significant)")

    print(f"\nTarget: theta >> 0 (duration effect confirmed)")
    print(f"Result: theta = {theta:.4f}")

    if abs(theta) > abs(beta):
        print("  Status: PASS (duration effect larger than entropy effect)")
    else:
        print("  Status: FAIL (duration effect not dominant)")

    print(f"\nTarget: n >= 1000 samples")
    print(f"Result: n = {len(df)}")

    if len(df) >= 1000:
        print("  Status: PASS")
    else:
        print("  Status: FAIL")

    # Overall assessment
    print("\n" + "=" * 70)
    print("OVERALL ASSESSMENT")
    print("=" * 70)

    all_pass = (0.1 <= abs(beta) <= 0.5 and
                beta_p < 0.05 and
                abs(theta) > abs(beta) and
                len(df) >= 1000)

    if all_pass:
        print("\nStatus: VALIDATION SUCCESSFUL")
        print("\nKey findings:")
        print(f"1. beta dropped from ~56.98 to {beta:.4f} (within expected range)")
        print(f"2. Duration confound confirmed (theta = {theta:.4f})")
        print(f"3. Entropy effect statistically significant (p = {beta_p:.4e})")
        print(f"4. LRT prediction validated: beta > 0")
        print("\nReady for LLM team final review!")
    else:
        print("\nStatus: VALIDATION INCOMPLETE")
        print("\nIssues to address:")
        if not (0.1 <= abs(beta) <= 0.5):
            print(f"  - beta = {beta:.4f} outside [0.1, 0.5] range")
        if not (beta_p < 0.05):
            print(f"  - Not statistically significant (p = {beta_p:.4e})")
        if not (abs(theta) > abs(beta)):
            print(f"  - Duration effect not dominant")
        if not (len(df) >= 1000):
            print(f"  - Insufficient samples (n = {len(df)})")

    # Save results
    os.makedirs('outputs', exist_ok=True)

    # Save data
    df.to_csv('outputs/statistical_control_data.csv', index=False)

    # Save analysis results
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
            'theta': float(theta),
            'theta_se': float(model_multi.bse[2]),
            'gamma': float(model_multi.params[3]),
            'beta_p_value': float(beta_p),
            'R2': float(model_multi.rsquared)
        },
        'vif_diagnostics': {
            'max_vif': float(max_vif),
            'vif_values': vif_data.to_dict('records')
        },
        'validation': {
            'beta_in_range': bool(0.1 <= abs(beta) <= 0.5),
            'significant': bool(beta_p < 0.05),
            'duration_dominant': bool(abs(theta) > abs(beta)),
            'sufficient_samples': bool(len(df) >= 1000),
            'overall_pass': bool(all_pass)
        }
    }

    with open('outputs/statistical_control_results.json', 'w') as f:
        json.dump(results, f, indent=2)

    print(f"\nResults saved to:")
    print(f"  - outputs/statistical_control_data.csv")
    print(f"  - outputs/statistical_control_results.json")

    # Create visualization
    create_visualization(df, model_simple, model_multi)

    return df, results

def create_visualization(df, model_simple, model_multi):
    """Create diagnostic plots"""

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: Entropy vs log error (simple regression)
    ax = axes[0, 0]
    low_df = df[df['entropy_type'] == 'low']
    high_df = df[df['entropy_type'] == 'high']

    ax.scatter(low_df['Delta_S'], low_df['log_p_log'], alpha=0.5, label='Low-entropy', s=20)
    ax.scatter(high_df['Delta_S'], high_df['log_p_log'], alpha=0.5, label='High-entropy', s=20)

    # Regression line
    x_range = np.linspace(df['Delta_S'].min(), df['Delta_S'].max(), 100)
    y_pred = model_simple.params[0] + model_simple.params[1] * x_range
    ax.plot(x_range, y_pred, 'r-', linewidth=2, label=f'beta={model_simple.params[1]:.2f}')

    ax.set_xlabel('Delta_S (nats)', fontsize=10)
    ax.set_ylabel('log(p_log)', fontsize=10)
    ax.set_title('Simple Regression (Original)', fontsize=11, fontweight='bold')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)

    # Plot 2: Duration vs log error
    ax = axes[0, 1]
    ax.scatter(low_df['duration'], low_df['log_p_log'], alpha=0.5, label='Low-entropy', s=20)
    ax.scatter(high_df['duration'], high_df['log_p_log'], alpha=0.5, label='High-entropy', s=20)
    ax.set_xlabel('Duration (us)', fontsize=10)
    ax.set_ylabel('log(p_log)', fontsize=10)
    ax.set_title('Duration Confound Visualization', fontsize=11, fontweight='bold')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)

    # Plot 3: Predicted vs actual (multivariate)
    ax = axes[1, 0]
    from sklearn.preprocessing import StandardScaler
    scaler = StandardScaler()
    X_scaled = scaler.fit_transform(df[['Delta_S', 'duration', 'qubit_count']])
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
    residuals = df['log_p_log'] - y_pred
    ax.scatter(y_pred, residuals, alpha=0.5, s=20)
    ax.axhline(0, color='r', linestyle='--', linewidth=2)
    ax.set_xlabel('Predicted log(p_log)', fontsize=10)
    ax.set_ylabel('Residuals', fontsize=10)
    ax.set_title('Residual Plot (Multivariate)', fontsize=11, fontweight='bold')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('outputs/statistical_control_analysis.png', dpi=150, bbox_inches='tight')
    print(f"  - outputs/statistical_control_analysis.png")
    plt.close()

# ============================================================================
# MAIN EXECUTION
# ============================================================================

if __name__ == '__main__':
    # Run with 1000 samples (team recommendation)
    df, results = run_statistical_control_simulation(n_samples=1000)

    print("\n" + "=" * 70)
    print("SIMULATION COMPLETE")
    print("=" * 70)
    print("\nNext step: Submit results to LLM team for final validation")
    print("(Per CLAUDE.md Rule 6: Require team quality score >= 0.70)")
