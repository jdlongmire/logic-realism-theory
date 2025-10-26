"""
Standalone script to submit and monitor LRT hardware test on IBM Quantum.
This handles the long queue wait better than notebook execution.
"""
import numpy as np
import time
import json
from datetime import datetime
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, Session, SamplerV2 as Sampler

print("="*70)
print("HARDWARE LRT TEST - IBM ibm_torino")
print("="*70)
print(f"Start time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")

# Load API token and instance
with open('../../theory/predictions/IBM_Q_API.txt', 'r') as f:
    token = f.read().strip()

with open('../../theory/predictions/IBM_Q_CRN.txt', 'r') as f:
    instance = f.read().strip()

# Connect to IBM Quantum with instance
print("Connecting to IBM Quantum Platform...")
try:
    service = QiskitRuntimeService(
        channel="ibm_quantum_platform",
        token=token,
        instance=instance
    )
    print(f"Connected successfully to instance: LFT-1.0\n")
except Exception as e:
    print(f"Connection failed: {e}")
    print("Trying with saved credentials...")
    service = QiskitRuntimeService(channel="ibm_quantum_platform")
    print("Connected successfully (saved credentials)\n")

# Get backend
backend = service.backend('ibm_torino')
print(f"Backend: {backend.name}")
print(f"Status: {backend.status().status_msg}")
print(f"Queue: {backend.status().pending_jobs} pending jobs\n")

# Test parameters
N_SHOTS = 2500
N_POINTS = 25
T2_ESTIMATE = 100e-6

# Generate duration sweep
T_MIN = 1e-6
T_MAX = 5 * T2_ESTIMATE
T_log = np.logspace(np.log10(T_MIN), np.log10(T2_ESTIMATE), 13)
T_lin = np.linspace(T2_ESTIMATE, T_MAX, 13)
T_sweep = np.sort(np.concatenate([T_log, T_lin[1:]]))

print(f"Test Parameters:")
print(f"  Shots: {N_SHOTS:,} per circuit")
print(f"  Duration points: {N_POINTS}")
print(f"  Total shots: {N_SHOTS * N_POINTS:,}")
print(f"  Estimated time: ~5-7 minutes\n")

# Build circuits
print("Building Ramsey circuits...")
def build_ramsey_circuit(duration_sec):
    qc = QuantumCircuit(1, 1)
    qc.h(0)
    qc.delay(duration_sec, 0, unit='s')
    qc.h(0)
    qc.measure(0, 0)
    return qc

circuits = [build_ramsey_circuit(T) for T in T_sweep]
print(f"Built {len(circuits)} circuits\n")

# Transpile
print("Transpiling for ibm_torino...")
start_transpile = time.time()
transpiled_circuits = transpile(
    circuits,
    backend=backend,
    optimization_level=3,
    initial_layout=[0]
)
elapsed_transpile = time.time() - start_transpile
print(f"Transpilation complete ({elapsed_transpile:.1f}s)\n")

# SUBMISSION
print("="*70)
print("SUBMITTING TO HARDWARE")
print("="*70)
print(f"This will use ~5-7 minutes of quantum time")
print(f"Current queue: {backend.status().pending_jobs} jobs")
print("\nAuto-submitting job...")

print("\nSubmitting job in job mode (no session)...")
# Use Sampler without Session (job mode for open plan)
sampler = Sampler(mode=backend)

print("Submitting circuits...")
job = sampler.run(transpiled_circuits, shots=N_SHOTS)

job_id = job.job_id()
print(f"\nOK Job submitted successfully!")
print(f"Job ID: {job_id}")

# Save job ID
with open('hardware_test_job_id.txt', 'w') as f:
    f.write(job_id)
print(f"Job ID saved to: hardware_test_job_id.txt\n")

# Monitor status
print("="*70)
print("MONITORING JOB STATUS")
print("="*70)
print("Waiting for results (you can Ctrl+C and resume later using job ID)...\n")

check_count = 0
while True:
    status = job.status()
    check_count += 1
    timestamp = datetime.now().strftime('%H:%M:%S')

    print(f"[{check_count}] {timestamp} - Status: {status}")

    if status in ['DONE', 'CANCELLED', 'ERROR']:
        break

    time.sleep(30)  # Check every 30 seconds

print(f"\n{'='*70}")
print(f"JOB COMPLETED: {status}")
print(f"{'='*70}\n")

if status == 'DONE':
    print("Retrieving results...")
    result = job.result()

    # Save raw result data
    print("Processing measurement counts...")
    results_data = []
    for i, T in enumerate(T_sweep):
        counts = result[i].data.c.get_counts()
        counts_0 = counts.get(0, 0)
        counts_1 = counts.get(1, 0)
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

    # Save to JSON
    report = {
        'metadata': {
            'backend': backend.name,
            'job_id': job_id,
            'timestamp': datetime.now().isoformat(),
            'n_shots': N_SHOTS,
            'n_points': N_POINTS,
            'total_shots': N_SHOTS * N_POINTS,
            'status': 'DONE'
        },
        'measurements': results_data
    }

    with open('hardware_test_raw_results.json', 'w') as f:
        json.dump(report, f, indent=2)

    print(f"\nOK Results saved to: hardware_test_raw_results.json")
    print(f"Total shots collected: {N_SHOTS * N_POINTS:,}")
    print(f"\nTo analyze results, run: python analyze_hardware_results.py")
else:
    print(f"\nX Job failed with status: {status}")
    print("Check IBM Quantum dashboard for details.")

print(f"\nEnd time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
print("="*70)
