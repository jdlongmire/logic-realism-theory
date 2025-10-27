# Path 3: T1 vs T2 Comparison Test - Implementation Scripts

**Date**: October 27, 2025
**Status**: Ready for Execution (pending multi-LLM review)
**Protocol Reference**: `theory/predictions/T1_vs_T2_Protocol.md`

---

## Overview

This directory contains the complete implementation for Path 3 experimental testing:

**LRT Prediction**: T2 < T1 (superposition states less stable due to relaxed Excluded Middle constraint)
**QM Prediction**: T2 ≈ T1 (no fundamental state preference)

---

## Scripts

### 1. `circuits_t1.py` - T1 Circuit Generation

Generates amplitude relaxation (T1) measurement circuits.

**Circuit**: `|0⟩ → X → delay(T) → Measure`

**Features**:
- Hybrid log-linear duration sweep (49 points, 1-1000 µs)
- Configurable qubit and backend timing
- Metadata generation for tracking

**Usage**:
```python
from circuits_t1 import create_T1_circuits, generate_duration_points

durations = generate_duration_points()  # 49 points
circuits = create_T1_circuits(durations, qubit=0)
```

### 2. `circuits_t2.py` - T2 (Ramsey) Circuit Generation

Generates phase coherence (T2) measurement circuits using Ramsey interferometry.

**Circuit**: `|0⟩ → H → delay(T) → H → Measure`

**Features**:
- Same duration sweep as T1 (for direct comparison)
- Superposition state preparation
- Phase-to-population conversion

**Usage**:
```python
from circuits_t2 import create_T2_circuits

circuits = create_T2_circuits(durations, qubit=0)
```

### 3. `circuits_t2echo.py` - T2echo (Hahn Echo) Circuit Generation

Generates Hahn echo (T2echo) measurement circuits for confound control.

**Circuit**: `|0⟩ → H → delay(T/2) → X → delay(T/2) → H → Measure`

**Purpose**: Distinguish LRT effects from pure dephasing
- If T2echo ≈ 2T1 but T2 < T1 → Pure dephasing (QM), not LRT
- If T2echo < T1 also → Possible LRT effect

**Usage**:
```python
from circuits_t2echo import create_T2echo_circuits

circuits = create_T2echo_circuits(durations, qubit=0)
```

### 4. `analyze_t1_vs_t2.py` - Complete Analysis Pipeline

Comprehensive analysis of T1 vs T2 data with hypothesis testing.

**Features**:
- Exponential fitting for T1: `P_1(T) = exp(-T/T1)`
- Ramsey fitting for T2: `P_error(T) = 0.5 * (1 - exp(-T/T2)) + p0`
- Ratio computation with error propagation
- Hypothesis testing (one-tailed t-test)
- Effect size calculation (Cohen's d)
- Comprehensive visualization
- JSON results output

**Usage**:
```python
from analyze_t1_vs_t2 import analyze_T1_vs_T2

results = analyze_T1_vs_T2(
    'T1_data.json',
    'T2_data.json',
    backend_name='ibm_torino',
    output_prefix='path3_results'
)
```

---

## Workflow

### Phase 1: Circuit Generation

```python
from circuits_t1 import create_T1_circuits, generate_duration_points
from circuits_t2 import create_T2_circuits
from circuits_t2echo import create_T2echo_circuits

# Generate duration sweep (49 points)
durations = generate_duration_points()

# Create circuits
T1_circuits = create_T1_circuits(durations, qubit=0)
T2_circuits = create_T2_circuits(durations, qubit=0)
T2echo_circuits = create_T2echo_circuits(durations, qubit=0)
```

### Phase 2: Execution (Requires IBM Quantum Access)

```python
from qiskit_ibm_runtime import QiskitRuntimeService, Sampler
from qiskit import transpile

# Initialize service
service = QiskitRuntimeService(channel="ibm_quantum")
backend = service.backend("ibm_torino")

# Transpile circuits
T1_transpiled = transpile(T1_circuits, backend=backend, optimization_level=3)
T2_transpiled = transpile(T2_circuits, backend=backend, optimization_level=3)

# Run with Sampler
sampler = Sampler(mode=backend)
job_T1 = sampler.run(T1_transpiled, shots=10000)
job_T2 = sampler.run(T2_transpiled, shots=10000)

# Wait for completion and extract data
# (save to JSON files)
```

### Phase 3: Analysis

```python
from analyze_t1_vs_t2 import analyze_T1_vs_T2

results = analyze_T1_vs_T2(
    'T1_ibm_torino_data.json',
    'T2_ibm_torino_data.json',
    backend_name='ibm_torino',
    output_prefix='path3_results'
)

# Interpretation
if results['p_value'] < 0.05 and results['ratio'] < 0.9:
    print("EVIDENCE FOR LRT: Superposition less stable")
else:
    print("CONSISTENT WITH QM: No state preference detected")
```

---

## Resource Requirements

**Per Backend**:
- T1 measurement: 49 points × 10,000 shots = 490,000 shots (~10-12 hours)
- T2 measurement: 49 points × 10,000 shots = 490,000 shots (~10-12 hours)
- T2echo measurement: 49 points × 10,000 shots = 490,000 shots (~10-12 hours)
- **Total**: ~30-40 hours quantum time

**Three Backends** (recommended for cross-validation):
- Total: ~100-120 hours quantum time
- Requires: IBM Quantum Researchers or Educators Program

---

## Expected Outcomes

### Scenario 1: LRT Signal Detected (T2 < T1, p < 0.05)

**Observed**:
- T2/T1 < 0.9 across all backends
- p < 0.05 (statistically significant)
- T2echo also < T1 (rules out pure dephasing)

**Interpretation**: Strong evidence for LRT prediction - superposition states fundamentally less stable.

### Scenario 2: No LRT Signal (T2 ≈ T1, p > 0.05)

**Observed**:
- T2/T1 ≈ 0.9-1.1 across backends
- p > 0.05 (not statistically significant)
- T2echo ≈ 2T1 (pure dephasing explains T2 < T1)

**Interpretation**: Consistent with QM - no LRT deviation detected.

---

## Dependencies

```
qiskit >= 1.0.0
qiskit-ibm-runtime >= 0.15.0
numpy >= 1.20.0
scipy >= 1.7.0
matplotlib >= 3.4.0
```

Install:
```bash
pip install qiskit qiskit-ibm-runtime numpy scipy matplotlib
```

---

## Next Steps

1. **Multi-LLM Review**: Submit protocol to consultation team (quality score > 0.70 required)
2. **Enhanced Access**: Apply to IBM Quantum Researchers Program (~120 hours)
3. **Pilot Test**: Optional reduced test on free tier (5 points × 1000 shots)
4. **Full Execution**: Run on 3 backends with full protocol
5. **Analysis & Publication**: Analyze results, write paper, release data

---

## References

- Protocol: `theory/predictions/T1_vs_T2_Protocol.md`
- Prediction Paths: `theory/predictions/Prediction_Paths_Master.md`
- Path 1 Results: `Hardware_Test_Report.md` (baseline methodology)

---

**Copyright © 2025 James D. (JD) Longmire**
**License**: Apache License 2.0
