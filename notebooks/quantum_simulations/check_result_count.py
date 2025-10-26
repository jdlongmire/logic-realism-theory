"""
Check how many circuit results we got.
"""
from qiskit_ibm_runtime import QiskitRuntimeService

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
result = job.result()

print(f"\n=== RESULT STRUCTURE ===")
print(f"len(result): {len(result)}")
print(f"type(result): {type(result)}")

# If we have multiple results, print counts for each
if len(result) > 0:
    for i in range(min(len(result), 5)):  # First 5 results
        try:
            counts = result[i].data.c.get_counts()
            print(f"\nresult[{i}] counts: {counts}")
        except Exception as e:
            print(f"\nresult[{i}] ERROR: {e}")

    if len(result) > 5:
        print(f"\n... ({len(result) - 5} more results)")
else:
    print("NO RESULTS FOUND!")
