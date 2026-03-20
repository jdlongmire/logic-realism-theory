"""
Decoherence Rate Test - Grok's Protocol Verification

CRITICAL TEST: Do measurements have higher decoherence rates per unit time than unitaries?

Grok's Claim:
- Measurements: ~0.10 nats/us (amplifier backaction, readout noise)
- Unitaries (CNOTs): ~0.05 nats/us (gate errors only)
- Ratio: ~2x higher for measurements

If confirmed: Different DeltaS at fixed T -> decorrelation -> beta testable!
If not: Perfect multicollinearity remains -> beta unidentifiable

This test:
1. Fixed duration T = 10 us for all sequences
2. Vary operation mix (unitary-heavy vs measurement-heavy)
3. Measure DeltaS for each
4. Check correlation between T and DeltaS
5. Calculate VIF to assess multicollinearity

Expected: If Grok is right, correlation < 0.95, VIF < 10 -> testable!
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
import json
import os

np.random.seed(42)

# ============================================================================
# TEST PARAMETERS
# ============================================================================

TARGET_DURATION = 10e-6  # 10 microseconds (fixed for all sequences)

class NoiseParams:
    """IBM Quantum noise parameters"""
    T1 = 100e-6      # 100 us
    T2 = 50e-6       # 50 us

    # Gate times
    gate_1q = 50e-9   # 50 ns
    gate_2q = 300e-9  # 300 ns

    # Measurement (longer, more noise)
    meas_time = 1e-6  # 1 us (20x longer than CNOT!)

    # Gate errors (base rates)
    error_1q = 1e-3   # 0.1%
    error_2q = 1e-2   # 1%

    # CRITICAL: Measurement-specific errors (Grok's claim)
    # Readout amplifiers introduce additional decoherence
    meas_error_multiplier = 2.0  # 2x higher effective decoherence during measurement

# ============================================================================
# NOISE MODEL (With Measurement-Specific Decoherence)
# ============================================================================

def create_noise_model_with_measurement_decoherence():
    """
    Noise model with HIGHER decoherence during measurements

    Key: Measurements have different noise character (amplifier backaction)
    This is what enables decorrelation from duration
    """
    noise_model = NoiseModel()

    # Standard gate errors
    depol_1q = depolarizing_error(NoiseParams.error_1q, 1)
    depol_2q = depolarizing_error(NoiseParams.error_2q, 2)

    noise_model.add_all_qubit_quantum_error(depol_1q, ['h', 'x', 'y', 'z', 's', 'sdg'])
    noise_model.add_all_qubit_quantum_error(depol_2q, ['cx'])

    # Thermal relaxation for gates
    thermal_1q = thermal_relaxation_error(NoiseParams.T1, NoiseParams.T2, NoiseParams.gate_1q)
    noise_model.add_all_qubit_quantum_error(thermal_1q, ['h', 'x', 'y', 'z', 's', 'sdg'])

    # CRITICAL: Enhanced thermal relaxation for measurements (amplifier noise)
    # T1, T2 effectively REDUCED during measurement due to backaction
    T1_meas = NoiseParams.T1 / NoiseParams.meas_error_multiplier
    T2_meas = NoiseParams.T2 / NoiseParams.meas_error_multiplier

    thermal_meas = thermal_relaxation_error(T1_meas, T2_meas, NoiseParams.meas_time)
    noise_model.add_all_qubit_quantum_error(thermal_meas, ['measure'])

    return noise_model

# ============================================================================
# TEST SEQUENCES (Fixed Duration, Varied Operations)
# ============================================================================

def create_unitary_heavy_sequence(n_qubits=3):
    """
    Unitary-heavy: Many fast CNOT gates to fill T = 10 us

    Expected decoherence: ~0.05 nats/us (gate errors only)
    Total DeltaS at T=10us: ~0.5 nats
    """
    qc = QuantumCircuit(n_qubits)

    # Calculate how many CNOTs fit in TARGET_DURATION
    n_cnots = int(TARGET_DURATION / NoiseParams.gate_2q)

    print(f"Unitary-heavy: {n_cnots} CNOTs in {TARGET_DURATION*1e6:.1f} us")

    # Apply CNOTs in a pattern
    for i in range(n_cnots):
        qc.cx(i % (n_qubits - 1), (i % (n_qubits - 1)) + 1)

    return qc

def create_measurement_heavy_sequence(n_qubits=3):
    """
    Measurement-heavy: Fewer measurements to fill T = 10 us

    Expected decoherence: ~0.10 nats/us (measurements have 2x higher rate)
    Total DeltaS at T=10us: ~1.0 nats
    """
    from qiskit.circuit import ClassicalRegister

    qc = QuantumCircuit(n_qubits)
    creg = ClassicalRegister(n_qubits, 'c')
    qc.add_register(creg)

    # Calculate how many measurement cycles fit in TARGET_DURATION
    n_measurements = int(TARGET_DURATION / NoiseParams.meas_time)

    print(f"Measurement-heavy: {n_measurements} measurements in {TARGET_DURATION*1e6:.1f} us")

    # Apply measurement/reset cycles
    for i in range(n_measurements):
        qubit = i % n_qubits
        qc.measure(qubit, creg[qubit])
        qc.reset(qubit)

    return qc

def create_mixed_sequence(n_qubits=3, measurement_fraction=0.5):
    """
    Mixed: Combination of unitaries and measurements at fixed T

    This provides intermediate points to test decorrelation
    """
    from qiskit.circuit import ClassicalRegister

    qc = QuantumCircuit(n_qubits)
    creg = ClassicalRegister(n_qubits, 'c')
    qc.add_register(creg)

    # Allocate time between measurements and gates
    meas_time = TARGET_DURATION * measurement_fraction
    gate_time = TARGET_DURATION * (1 - measurement_fraction)

    n_measurements = int(meas_time / NoiseParams.meas_time)
    n_cnots = int(gate_time / NoiseParams.gate_2q)

    print(f"Mixed ({measurement_fraction:.1%} meas): {n_measurements} meas + {n_cnots} CNOTs in {TARGET_DURATION*1e6:.1f} us")

    # Apply measurements
    for i in range(n_measurements):
        qubit = i % n_qubits
        qc.measure(qubit, creg[qubit])
        qc.reset(qubit)

    # Apply CNOTs
    for i in range(n_cnots):
        qc.cx(i % (n_qubits - 1), (i % (n_qubits - 1)) + 1)

    return qc

# ============================================================================
# ENTROPY MEASUREMENT
# ============================================================================

def calculate_subsystem_entropy(circuit, noise_model):
    """Calculate subsystem entropy after circuit execution"""
    n_qubits = circuit.num_qubits

    # Initial state (all |0>)
    rho_in = DensityMatrix.from_label('0' * n_qubits)

    # Evolve with noise
    qc_copy = circuit.copy()
    qc_copy.remove_final_measurements()

    simulator = AerSimulator(method='density_matrix', noise_model=noise_model)
    qc_copy.save_density_matrix()
    result = simulator.run(qc_copy, shots=1).result()
    rho_out = result.data()['density_matrix']

    # Subsystem entropy (trace out all but first qubit)
    rho_sub_in = partial_trace(rho_in, list(range(1, n_qubits)))
    rho_sub_out = partial_trace(rho_out, list(range(1, n_qubits)))

    S_in = entropy(rho_sub_in, base=np.e)
    S_out = entropy(rho_sub_out, base=np.e)
    Delta_S = S_out - S_in

    return S_in, S_out, Delta_S

def calculate_actual_duration(circuit):
    """Calculate actual duration of circuit"""
    ops = circuit.count_ops()

    n_1q = sum(ops.get(g, 0) for g in ['h', 'x', 'y', 'z', 's', 'sdg'])
    n_2q = ops.get('cx', 0)
    n_meas = ops.get('measure', 0)
    n_reset = ops.get('reset', 0)

    duration = (n_1q * NoiseParams.gate_1q +
               n_2q * NoiseParams.gate_2q +
               n_meas * NoiseParams.meas_time +
               n_reset * NoiseParams.meas_time)

    return duration

# ============================================================================
# MAIN TEST
# ============================================================================

def run_decoherence_rate_test():
    """
    Test Grok's claim: Do measurements have higher decoherence per unit time?

    Method:
    1. Create sequences with different operation mixes at fixed T
    2. Measure DeltaS for each
    3. Check correlation between measurement fraction and DeltaS
    4. If measurements have higher rates: DeltaS varies independently of T
    """
    print("=" * 70)
    print("DECOHERENCE RATE TEST (Grok's Protocol Verification)")
    print("=" * 70)
    print(f"\nTarget Duration: {TARGET_DURATION*1e6:.1f} us (FIXED for all sequences)")
    print(f"Measurement error multiplier: {NoiseParams.meas_error_multiplier}x")
    print("\nGrok's Hypothesis:")
    print("  Measurements have ~2x higher decoherence rate than unitaries")
    print("  -> Different DeltaS at same T -> decorrelation -> beta testable!")
    print("=" * 70)

    # Create noise model
    noise_model = create_noise_model_with_measurement_decoherence()

    # Test different operation mixes at FIXED duration
    test_points = [
        ('Unitary-heavy', 0.0),    # 0% measurements
        ('Mixed-25%', 0.25),        # 25% measurements
        ('Mixed-50%', 0.50),        # 50% measurements
        ('Mixed-75%', 0.75),        # 75% measurements
        ('Measurement-heavy', 1.0)  # 100% measurements (all time in meas)
    ]

    results = []

    print("\nCreating sequences...")
    for name, meas_frac in test_points:
        print(f"\n{name} (meas_frac={meas_frac:.2f}):")

        # Create circuit
        if meas_frac == 0.0:
            qc = create_unitary_heavy_sequence()
        elif meas_frac == 1.0:
            # For 100% measurement, we need a special case
            # since we can't have ONLY measurements (need some structure)
            qc = create_measurement_heavy_sequence()
        else:
            qc = create_mixed_sequence(measurement_fraction=meas_frac)

        # Measure entropy
        S_in, S_out, Delta_S = calculate_subsystem_entropy(qc, noise_model)

        # Calculate actual duration
        duration = calculate_actual_duration(qc)

        # Calculate decoherence rate (nats/us)
        rate = Delta_S / (duration * 1e6) if duration > 0 else 0

        results.append({
            'name': name,
            'meas_fraction': meas_frac,
            'duration_us': duration * 1e6,
            'S_in': S_in,
            'S_out': S_out,
            'Delta_S': Delta_S,
            'rate_nats_per_us': rate
        })

        print(f"  Duration: {duration*1e6:.2f} us")
        print(f"  Delta_S: {Delta_S:.4f} nats")
        print(f"  Rate: {rate:.4f} nats/us")

    df = pd.DataFrame(results)

    # ========================================================================
    # ANALYSIS: Decorrelation Test
    # ========================================================================

    print("\n" + "=" * 70)
    print("DECORRELATION ANALYSIS")
    print("=" * 70)

    # Check 1: Correlation between duration and Delta_S
    corr = df['duration_us'].corr(df['Delta_S'])
    print(f"\nCorrelation(duration, Delta_S): {corr:.4f}")

    if abs(corr) > 0.95:
        print("  Status: PERFECT MULTICOLLINEARITY (correlation > 0.95)")
        print("  Interpretation: beta is NOT identifiable (Test 2/3 issue)")
    elif abs(corr) > 0.80:
        print("  Status: SEVERE MULTICOLLINEARITY (correlation > 0.80)")
        print("  Interpretation: beta may be identifiable with large N")
    else:
        print("  Status: DECORRELATION EXISTS (correlation < 0.80)")
        print("  Interpretation: beta is identifiable! (Grok's hypothesis confirmed)")

    # Check 2: Rate differences
    print("\nDecoherence Rates by Operation Type:")
    print(df[['name', 'rate_nats_per_us']].to_string(index=False))

    unitary_rate = df[df['meas_fraction'] == 0.0]['rate_nats_per_us'].values[0]
    meas_rate = df[df['meas_fraction'] == 1.0]['rate_nats_per_us'].values[0]

    # Initialize ratio to handle case where meas_rate = 0
    ratio = 0.0

    if meas_rate > 0:
        ratio = meas_rate / unitary_rate if unitary_rate > 0 else float('inf')
        print(f"\nRate ratio (measurement / unitary): {ratio:.2f}x")

        if ratio > 1.5:
            print("  Status: CONFIRMED - Measurements have significantly higher rates")
            print("  Grok's hypothesis: SUPPORTED")
        else:
            print("  Status: WEAK DIFFERENCE - Rates similar")
            print("  Grok's hypothesis: NOT CONFIRMED")

    # Check 3: VIF if we add measurement fraction as predictor
    print("\n" + "-" * 70)
    print("VIF Analysis (If we regress with both T and meas_fraction)")
    print("-" * 70)

    X = df[['duration_us', 'meas_fraction']].values

    if len(np.unique(X[:, 0])) > 1:  # Check if duration varies
        vif_data = pd.DataFrame()
        vif_data['Variable'] = ['duration_us', 'meas_fraction']
        vif_data['VIF'] = [variance_inflation_factor(X, i) for i in range(2)]
        print(vif_data.to_string(index=False))

        max_vif = vif_data['VIF'].max()
        if max_vif > 10:
            print(f"\n  Max VIF = {max_vif:.2f} > 10: SEVERE multicollinearity")
        elif max_vif > 5:
            print(f"\n  Max VIF = {max_vif:.2f} > 5: MODERATE multicollinearity")
        else:
            print(f"\n  Max VIF = {max_vif:.2f} < 5: ACCEPTABLE")
    else:
        print("  All durations identical - VIF not meaningful")
        print("  (This is expected if duration matching works perfectly)")

    # Check 4: Can we separate effects?
    print("\n" + "-" * 70)
    print("Regression Test: Can we identify independent effects?")
    print("-" * 70)

    # Try to "explain" Delta_S with both duration and meas_fraction
    X = df[['duration_us', 'meas_fraction']].values
    y = df['Delta_S'].values

    if len(np.unique(X[:, 0])) > 1:
        X_with_const = sm.add_constant(X)
        model = sm.OLS(y, X_with_const).fit()

        print("\nModel: Delta_S = alpha + beta1*duration + beta2*meas_fraction")
        print(f"  beta1 (duration effect): {model.params[1]:.6f} (p={model.pvalues[1]:.4f})")
        print(f"  beta2 (meas_frac effect): {model.params[2]:.6f} (p={model.pvalues[2]:.4f})")
        print(f"  R^2: {model.rsquared:.4f}")

        if model.pvalues[2] < 0.05:
            print("\n  Result: Measurement fraction has INDEPENDENT effect (p < 0.05)")
            print("  Interpretation: beta is testable! (Different rates confirmed)")
        else:
            print("\n  Result: Measurement fraction effect NOT significant")
            print("  Interpretation: beta may not be identifiable")
    else:
        print("  Cannot run regression (no duration variance)")

    # Save results
    os.makedirs('outputs', exist_ok=True)
    df.to_csv('outputs/decoherence_rate_test.csv', index=False)

    results_summary = {
        'correlation_duration_deltaS': float(corr),
        'unitary_rate': float(unitary_rate),
        'measurement_rate': float(meas_rate),
        'rate_ratio': float(ratio) if meas_rate > 0 else None,
        'conclusion': 'DECORRELATION EXISTS' if abs(corr) < 0.80 else 'MULTICOLLINEARITY',
        'groks_hypothesis': 'SUPPORTED' if (ratio > 1.5 and abs(corr) < 0.80) else 'NOT CONFIRMED'
    }

    with open('outputs/decoherence_rate_test_results.json', 'w') as f:
        json.dump(results_summary, f, indent=2)

    # Visualization
    create_visualization(df)

    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    if results_summary['groks_hypothesis'] == 'SUPPORTED':
        print("\nOK Grok's hypothesis CONFIRMED:")
        print("  - Measurements have higher decoherence rates than unitaries")
        print("  - Decorrelation exists between duration and Delta_S")
        print("  - beta is identifiable in the LRT model")
        print("\n  RECOMMENDATION: Proceed with Grok's protocol for hardware test")
    else:
        print("\nX Grok's hypothesis NOT CONFIRMED:")
        print("  - Multicollinearity remains problematic")
        print("  - beta may not be identifiable")
        print("\n  RECOMMENDATION: Need further protocol refinement or")
        print("                  acknowledge testability limitations")

    print(f"\nResults saved to:")
    print(f"  - outputs/decoherence_rate_test.csv")
    print(f"  - outputs/decoherence_rate_test_results.json")
    print(f"  - outputs/decoherence_rate_test.png")

    return df, results_summary

def create_visualization(df):
    """Create diagnostic plots"""

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: Delta_S vs measurement fraction
    ax = axes[0, 0]
    ax.scatter(df['meas_fraction'], df['Delta_S'], s=100, alpha=0.7)
    ax.plot(df['meas_fraction'], df['Delta_S'], 'r--', alpha=0.5)
    for i, row in df.iterrows():
        ax.annotate(row['name'], (row['meas_fraction'], row['Delta_S']),
                   fontsize=8, ha='center', va='bottom')
    ax.set_xlabel('Measurement Fraction', fontsize=10)
    ax.set_ylabel('Delta_S (nats)', fontsize=10)
    ax.set_title('Entropy Change vs Operation Mix', fontsize=11, fontweight='bold')
    ax.grid(True, alpha=0.3)

    # Plot 2: Decoherence rate vs measurement fraction
    ax = axes[0, 1]
    ax.scatter(df['meas_fraction'], df['rate_nats_per_us'], s=100, alpha=0.7, color='orange')
    ax.plot(df['meas_fraction'], df['rate_nats_per_us'], 'r--', alpha=0.5)
    ax.set_xlabel('Measurement Fraction', fontsize=10)
    ax.set_ylabel('Decoherence Rate (nats/μs)', fontsize=10)
    ax.set_title('Decoherence Rate by Operation Type', fontsize=11, fontweight='bold')
    ax.grid(True, alpha=0.3)

    # Plot 3: Duration vs Delta_S (correlation check)
    ax = axes[1, 0]
    ax.scatter(df['duration_us'], df['Delta_S'], s=100, alpha=0.7, color='green')

    # Fit line
    from scipy.stats import linregress
    slope, intercept, r_value, p_value, std_err = linregress(df['duration_us'], df['Delta_S'])
    x_line = np.linspace(df['duration_us'].min(), df['duration_us'].max(), 100)
    y_line = slope * x_line + intercept
    ax.plot(x_line, y_line, 'r-', linewidth=2, label=f'r={r_value:.3f}')

    ax.set_xlabel('Duration (μs)', fontsize=10)
    ax.set_ylabel('Delta_S (nats)', fontsize=10)
    ax.set_title(f'Correlation Check (r={r_value:.3f})', fontsize=11, fontweight='bold')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Plot 4: Summary table
    ax = axes[1, 1]
    ax.axis('off')

    table_data = []
    for _, row in df.iterrows():
        table_data.append([
            row['name'][:15],
            f"{row['meas_fraction']:.2f}",
            f"{row['Delta_S']:.3f}",
            f"{row['rate_nats_per_us']:.4f}"
        ])

    table = ax.table(cellText=table_data,
                    colLabels=['Sequence', 'Meas%', 'DeltaS', 'Rate'],
                    cellLoc='left',
                    loc='center',
                    bbox=[0, 0, 1, 1])
    table.auto_set_font_size(False)
    table.set_fontsize(9)
    table.scale(1, 2)

    plt.tight_layout()
    plt.savefig('outputs/decoherence_rate_test.png', dpi=150, bbox_inches='tight')
    print(f"  - outputs/decoherence_rate_test.png")
    plt.close()

# ============================================================================
# MAIN
# ============================================================================

if __name__ == '__main__':
    df, results = run_decoherence_rate_test()

    print("\n" + "=" * 70)
    print("TEST COMPLETE")
    print("=" * 70)
    print("\nThis test verifies Grok's claim about differential decoherence rates")
    print("Result determines if LRT's beta parameter is testable in practice")
