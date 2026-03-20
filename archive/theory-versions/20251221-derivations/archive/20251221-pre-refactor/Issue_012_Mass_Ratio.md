# Extension: Muon-Electron Mass Ratio

**Status:** Extension of Issue 012 (uses derived constant c)
**Created:** 2025-12-16
**Session:** 45.0
**Dependencies:** Issue 012 (α derivation, constant c)

---

## The Result

The muon-to-electron mass ratio using the self-interaction coefficient from Issue 012:

```
m_μ/m_e = (d/2)α⁻¹ + c/4
        = (3/2)(137.036) + (74/15)/4
        = 205.554 + 1.233
        = 206.787

Observed: 206.768
Error:    92 ppm (0.009%)
```

---

## The Formula

### Components

| Term | Expression | Value | Origin |
|------|------------|-------|--------|
| Base | (d/2)α⁻¹ | 205.554 | Nambu relation (1952) |
| Correction | c/4 | 1.233 | Issue 012 c, spinor factor |
| **Total** | | **206.787** | |

### The Nambu Relation

Yoichiro Nambu observed (1952) that lepton masses relate to α via half-integer steps:

```
m_μ/m_e ≈ (3/2)α⁻¹ ≈ 205.5
```

This accounts for 99.4% of the mass ratio. The remaining ~1.2 is the correction.

### The Correction Term

From Issue 012, the self-interaction coefficient is:

```
c = (d+2) - 1/(d(d+2)) = 74/15 ≈ 4.933
```

The division by 4 comes from spinor structure:
- Dirac spinor has 4 components (2 particle × 2 chirality)
- The self-interaction overhead c distributes across these DOF

---

## Physical Interpretation

| Component | LRT Meaning |
|-----------|-------------|
| (d/2)α⁻¹ | Geometric energy of charged shell in d dimensions |
| c/4 | Self-consistency cost distributed over spinor components |

The muon appears as an **excited state** where geometric embedding becomes a dominant mass contribution.

---

## Comparison to Koide Formula

The Koide formula relates e, μ, τ geometrically:

```
(m_e + m_μ + m_τ) / (√m_e + √m_μ + √m_τ)² = 2/3
```

Differences:
- Koide describes **relations** between generations
- This formula derives **magnitude** of second generation from vacuum parameters
- This formula doesn't require τ as input

---

## Honest Assessment

### What's Derived (from Issue 012)
- The coefficient c = 74/15 (dimensional structure)
- The connection between α and c

### What's Assumed (not derived)
- The Nambu relation (d/2)α⁻¹ is empirical, not derived
- The factor of 4 (spinor components) is plausible but not proven
- Why mass ratio and not absolute mass

### Status

**Extension, not independent derivation.** The formula uses Issue 012's c in a new context. The 92 ppm accuracy is good but relies on the empirical Nambu base.

This is weaker than Issue 012 because:
- Issue 012 derived the Lagrangian form from 3FLL
- This formula assumes the Nambu relation

---

## Predictions for Other Dimensions

Using m/m_e = (d/2)α⁻¹(d) + c(d)/4:

| d | α⁻¹ | (d/2)α⁻¹ | c/4 | Mass Ratio |
|---|-----|----------|-----|------------|
| 2 | 36.1 | 36.1 | 0.97 | 37.1 |
| **3** | **137.0** | **205.5** | **1.23** | **206.8** |
| 4 | 528.0 | 1056.0 | 1.49 | 1057.5 |

The muon mass ratio ~207 is specific to d = 3.

---

## Verification

```python
import math

d = 3
c = (d+2) - 1/(d*(d+2))       # 74/15
alpha_inv = 137.035999177     # CODATA

base = (d/2) * alpha_inv      # Nambu
correction = c / 4            # Spinor distribution

predicted = base + correction
observed = 206.7682830        # CODATA m_mu/m_e

print(f"Base (Nambu): {base:.4f}")
print(f"Correction (c/4): {correction:.4f}")
print(f"Predicted: {predicted:.4f}")
print(f"Observed:  {observed:.4f}")
print(f"Error: {abs(predicted-observed)/observed*1e6:.1f} ppm")
```

Output:
```
Base (Nambu): 205.5540
Correction (c/4): 1.2333
Predicted: 206.7873
Observed:  206.7683
Error: 92.1 ppm
```
