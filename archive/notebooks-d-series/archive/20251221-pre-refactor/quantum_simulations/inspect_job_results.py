"""
Inspect the actual job results to debug data extraction.
"""
from qiskit_ibm_runtime import QiskitRuntimeService
import json

# Load credentials
with open('../../theory/predictions/IBM_Q_API.txt', 'r') as f:
    token = f.read().strip()

with open('../../theory/predictions/IBM_Q_CRN.txt', 'r') as f:
    instance = f.read().strip()

# Connect
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

print(f"Job status: {job.status()}")

# Get results
result = job.result()

print(f"\n=== RESULT STRUCTURE ===")
print(f"Type: {type(result)}")
print(f"Dir: {[x for x in dir(result) if not x.startswith('_')]}")

# Try different access patterns
print(f"\n=== TRYING DIFFERENT ACCESS METHODS ===")

# Method 1: Direct indexing
try:
    print(f"\nMethod 1: result[0]")
    res0 = result[0]
    print(f"  Type: {type(res0)}")
    print(f"  Dir: {[x for x in dir(res0) if not x.startswith('_')]}")

    if hasattr(res0, 'data'):
        print(f"  data: {type(res0.data)}")
        print(f"  data.dir: {[x for x in dir(res0.data) if not x.startswith('_')]}")

        # Try accessing classical register
        if hasattr(res0.data, 'c'):
            print(f"  data.c: {res0.data.c}")
            counts = res0.data.c.get_counts()
            print(f"  counts: {counts}")

        if hasattr(res0.data, 'meas'):
            print(f"  data.meas: {res0.data.meas}")

        # Check all attributes
        for attr in dir(res0.data):
            if not attr.startswith('_'):
                try:
                    val = getattr(res0.data, attr)
                    print(f"  data.{attr}: {val} (type: {type(val)})")
                except Exception as e:
                    print(f"  data.{attr}: ERROR - {e}")

except Exception as e:
    print(f"  ERROR: {e}")

# Method 2: Check if there's a quasi_dists attribute
try:
    print(f"\nMethod 2: result.quasi_dists")
    if hasattr(result, 'quasi_dists'):
        print(f"  quasi_dists: {result.quasi_dists}")
except Exception as e:
    print(f"  ERROR: {e}")

# Method 3: Check metadata
try:
    print(f"\nMethod 3: result.metadata")
    if hasattr(result, 'metadata'):
        print(f"  metadata: {result.metadata}")
except Exception as e:
    print(f"  ERROR: {e}")

# Save raw result structure for analysis
print(f"\n=== SAVING DIAGNOSTIC DATA ===")
diagnostic = {
    'job_id': job_id,
    'result_type': str(type(result)),
    'result_attrs': [x for x in dir(result) if not x.startswith('_')],
}

try:
    diagnostic['len_result'] = len(result)
except:
    diagnostic['len_result'] = 'N/A'

with open('result_diagnostic.json', 'w') as f:
    json.dump(diagnostic, f, indent=2)

print(f"Diagnostic saved to: result_diagnostic.json")
