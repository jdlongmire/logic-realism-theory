# LRT Simulations

Computational toy models exploring predictions of Logic Realism Theory.

## ICH Dark Energy Model

**File:** `ich_dark_energy.ipynb`

### Overview

A toy simulation of the Information Circulation Hypothesis (ICH), demonstrating how late-time cosmic acceleration (dark energy) can emerge from an influx/outflux imbalance in the logical circulation cycle.

### Core Concept

LRT posits that physical reality is constrained by logical laws (L₃: Identity, Non-Contradiction, Excluded Middle). The ICH extends this by proposing:

- **I∞**: Infinite logical possibility space (source of new instantiations)
- **AΩ**: Actualized physical instantiations (particles in simulation)
- **Black holes**: Recycling mechanism returning instantiations to I∞

When influx from I∞ exceeds outflux through black holes, the net positive imbalance drives an effective dark energy density that accelerates cosmic expansion.

### Features

- Entropy-dependent influx (self-regulating feedback loop)
- Emergent black hole formation, absorption, Hawking-like evaporation, merging
- Friedmann-like expansion driven by the circulation imbalance
- Distance modulus μ(z) calculation with comparison to SNe Ia anchors
- χ² goodness-of-fit assessment

### Key Results (v1.0)

- **w_eff ≈ -1**: Equation of state matches cosmological constant
- **Self-regulation**: High entropy suppresses influx, creating stable dynamics
- **BH formation**: Emerges from local density fluctuations
- **Circulation balance**: ~7500 particles instantiated and recycled over cosmic history

### Parameters

Key tunable parameters in the first code cell:

| Parameter | Description | Default |
|-----------|-------------|---------|
| `A_INITIAL` | Starting scale factor (z=3) | 0.25 |
| `INFLUX_PEAK` | Max influx rate at low entropy | 0.25 |
| `BH_FORM_DENSITY_TH` | Density threshold for BH formation | 0.5 |
| `IMBALANCE_COUPLING` | Strength of imbalance → expansion | 0.002 |

### Running

```python
# In Jupyter:
# Run all cells in order

# From command line:
jupyter execute ich_dark_energy.ipynb
```

### Output

- Console progress during simulation
- 8-panel visualization saved to `ich_simulation_results.png`
- Summary statistics including χ² fit quality

### Limitations

This is a **toy model** for conceptual demonstration:

- 1D spatial domain (periodic boundary)
- Simplified particle/BH dynamics
- Distance modulus normalization is qualitative, not calibrated to real units
- Not a replacement for full cosmological simulations

### References

- Longmire, J.D. (2026). Logic Realism Theory. Zenodo.
- LRT derivation: L₃ → Distinguishability → Hilbert Space → Born Rule → QM

---

*Part of the Logic Realism Theory research program*
