"""
Extract and save the actual hardware test results with correct key types.
"""
import numpy as np
import json
from datetime import datetime
from qiskit_ibm_runtime import QiskitRuntimeService

# Load credentials
with open('../../theory/predictions/IBM_Q_API.txt', 'r') as f:
    token = f.read().strip()

with open('../../theory/predictions/IBM_Q_CRN.txt', 'r') as f:
    instance = f.read().strip()

# Connect
print("Connecting to IBM Quantum Platform...")
service = QiskitRuntimeService(
    channel="ibm_quantum_platform",
    token=token,
    instance=instance
)

# Load job
with open('hardware_test_job_id.txt', 'r') as f:
    job_id = f.read().strip()

print(f"Retrieving job: {job_id}")
job = service.job(job_id)
backend_name = 'ibm_torino'

print(f"Job status: {job.status()}")
result = job.result()

print(f"\nNumber of circuits: {len(result)}")

# Re-create the duration sweep (same as in run_hardware_test.py)
N_SHOTS = 2500
N_POINTS = 25
T2_ESTIMATE = 100e-6

T_MIN = 1e-6
T_MAX = 5 * T2_ESTIMATE
T_log = np.logspace(np.log10(T_MIN), np.log10(T2_ESTIMATE), 13)
T_lin = np.linspace(T2_ESTIMATE, T_MAX, 13)
T_sweep = np.sort(np.concatenate([T_log, T_lin[1:]]))

print(f"Duration sweep: {len(T_sweep)} points")

# Extract measurement counts with CORRECT key types (strings!)
results_data = []
for i, T in enumerate(T_sweep):
    counts = result[i].data.c.get_counts()

    # FIX: Use string keys '0' and '1', not integer keys
    counts_0 = counts.get('0', 0)  # |0> state (logical |+>, no error)
    counts_1 = counts.get('1', 0)  # |1> state (logical |-, error)
    total = counts_0 + counts_1

    p_error = counts_1 / total if total > 0 else 0

    results_data.append({
        'T': float(T),
        'T_us': float(T * 1e6),
        'counts_0': int(counts_0),
        'counts_1': int(counts_1),
        'p_error': float(p_error),
        'shots': int(total)
    })

    print(f"  T={T*1e6:7.2f} us: counts={counts}, shots={total}, p_error={p_error:.4f}")

# Save to JSON
report = {
    'metadata': {
        'backend': backend_name,
        'job_id': job_id,
        'timestamp': datetime.now().isoformat(),
        'n_shots': N_SHOTS,
        'n_points': N_POINTS,
        'total_shots': N_SHOTS * N_POINTS,
        'status': 'DONE',
        'extraction_note': 'Fixed: using string keys for counts dictionary'
    },
    'measurements': results_data
}

with open('hardware_test_CORRECTED_results.json', 'w') as f:
    json.dump(report, f, indent=2)

print(f"\n=== EXTRACTION COMPLETE ===")
print(f"Results saved to: hardware_test_CORRECTED_results.json")
print(f"Total shots collected: {sum(r['shots'] for r in results_data):,}")
print(f"Data points: {len(results_data)}")
