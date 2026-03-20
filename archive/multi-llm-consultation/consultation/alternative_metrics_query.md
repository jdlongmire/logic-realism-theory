# Expert Consultation: Alternative Metrics for K(N)=N-2

## Context

We are investigating **why K(N) = N-2** in Logic Field Theory, where:
- K is the constraint threshold on inversion count h(sigma) <= K
- N is the number of elements in permutation group S_N
- Empirically validated: K(3)=1, K(4)=2, K(5)=3

## Previous Hypothesis: PARTIALLY REFUTED

**Original claim**: K=N-2 maximizes entropy density H/(N-1) on permutohedron

**Computational result**:
- Entropy density H/(N-1) increases monotonically - NO peak at K=N-2 ❌
- BUT: Alternative metric H/(K+1) DOES peak at K=N-2 for N=3,4 ✓

## Data Summary at K=N-2

| N | K | Entropy H | H/(N-1) | H/(K+1) | Feasibility rho |
|---|---|-----------|---------|---------|-----------------|
| 3 | 1 | 1.099     | 0.549   | 0.549   | 0.500           |
| 4 | 2 | 2.197     | 0.732   | 0.732   | 0.375           |
| 5 | 3 | 3.367     | 0.842   | 0.842   | 0.242           |
| 6 | 4 | 4.585     | 0.917   | 0.917   | 0.136           |
| 7 | 5 | 5.838     | 0.973   | 0.973   | 0.068           |
| 8 | 6 | 7.115     | 1.016   | 1.016   | 0.031           |

**Observations**:
1. Entropy gradient dH/dK: Monotonically decreasing (max at K=1, not K=N-2)
2. H/(K+1): Peaks at K=N-2 for N=3,4, but NOT for N>=5
3. Feasibility ratio rho: Decreasing exponentially
4. Graphs: Always connected (no transition at K=N-2)

## Question for Experts

**We need to explore alternative optimization principles. What OTHER metrics or geometric properties might K=N-2 optimize?**

Candidates to consider:

### Information-Theoretic Metrics
1. **Relative entropy rate**: H/K instead of H/(N-1)?
2. **Information gain per constraint**: Delta H / Delta K?
3. **Fisher information**: Does it peak at K=N-2?
4. **Quantum relative entropy**: Connection to quantum information?
5. **Conditional entropy**: H(next state | current state)?

### Graph-Theoretic Metrics
6. **Edge-to-vertex ratio**: E/V at K=N-2?
7. **Spectral gap**: First non-zero eigenvalue of graph Laplacian?
8. **Algebraic connectivity**: Fiedler eigenvalue?
9. **Mixing time**: Random walk convergence rate?
10. **Diameter normalization**: d/(N-1) or d/K?

### Geometric Metrics
11. **Effective dimension**: Does system transition from (N-1)-D to lower effective dimension?
12. **Volume-to-surface ratio**: On permutohedron?
13. **Curvature**: Is there a geometric transition in constraint manifold?
14. **Packing efficiency**: Information per degree of freedom?

### Physical/Dynamical Metrics
15. **Constraint saturation**: Ratio of actual to maximum possible constraints?
16. **Thermodynamic efficiency**: Free energy-like quantity?
17. **Distinguishability**: Can observers distinguish states efficiently?
18. **Computational complexity**: Resources needed to enumerate valid states?

### Alternative Formulations
19. **Is K=N-2 exact or approximate?**: Maybe true formula is K(N) = f(N) where f(N) ~ N-2 for small N?
20. **Is there a dimensionless ratio?**: K/(N-1) = (N-2)/(N-1) → 1 as N→∞?
21. **Asymptotic behavior**: Does the pattern hold for large N or break down?

## Specific Questions

1. **Which metric(s) are most likely to be optimized at K=N-2?**

2. **Is H/(K+1) peaking at K=N-2 for small N significant, or coincidence?**

3. **Should we test spectral properties of the constraint graph?**

4. **Could K=N-2 be a stability condition rather than optimization?**

5. **Are there information-theoretic principles beyond maximum entropy that could derive K=N-2?**

Please prioritize the most promising metrics to test computationally.
