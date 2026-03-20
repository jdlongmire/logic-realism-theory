#!/usr/bin/env python3
"""
Figure Generation Orchestrator
Generates all data-driven figures for Logic Field Theory paper
"""

import os
import sys

def main():
    """Run all figure generation scripts"""

    # Ensure output directory exists
    os.makedirs('outputs', exist_ok=True)

    print("=" * 60)
    print("Logic Field Theory: Figure Generation")
    print("=" * 60)

    # Import and run figure generators
    try:
        from n3_permutohedron import generate_n3_permutohedron
        from validation_histogram import generate_validation_histogram
        from born_rule_convergence import generate_born_rule_convergence
        from lflow_trajectory import generate_lflow_trajectory
        from logical_operator_diagram import generate_logical_operator_diagram
        from quantum_bridge import generate_quantum_bridge
        from godel_hierarchy import generate_godel_hierarchy
        from family_tree import generate_family_tree

        print("\n[1/8] Generating N=3 Permutohedron...")
        generate_n3_permutohedron()

        print("\n[2/8] Generating Validation Histogram...")
        generate_validation_histogram()

        print("\n[3/8] Generating Born Rule Convergence...")
        generate_born_rule_convergence()

        print("\n[4/8] Generating L-Flow Trajectory...")
        generate_lflow_trajectory()

        print("\n[5/8] Generating Logical Operator Diagram...")
        generate_logical_operator_diagram()

        print("\n[6/8] Generating Quantum Bridge Mapping...")
        generate_quantum_bridge()

        print("\n[7/8] Generating Gödel Escape Hatch Hierarchy...")
        generate_godel_hierarchy()

        print("\n[8/8] Generating Family Tree of Theories...")
        generate_family_tree()

        print("\n" + "=" * 60)
        print("[SUCCESS] All 8 figures generated successfully!")
        print("=" * 60)

        # Generate Markdown embed snippets
        generate_embed_snippets()

    except ImportError as e:
        print(f"\n[ERROR] Missing dependency - {e}")
        print("Install required packages:")
        print("  pip install matplotlib networkx pandas numpy scipy")
        sys.exit(1)
    except Exception as e:
        print(f"\n[ERROR] Error generating figures: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)

def generate_embed_snippets():
    """Generate Markdown snippets for embedding figures in paper"""

    snippets = """
## Markdown Embed Snippets
Copy these to Logic_Field_Theory_I_Quantum_Probability.md

---

### Figure 1: Logical Operator Breakdown (Section 1 / Appendix A)

```markdown
![Logical Operator Breakdown: L = EM ∘ NC ∘ ID](figures/outputs/figure_logical_operator.svg)

**Figure 1**: Sequential application of the logical operator L = EM ∘ NC ∘ ID. Starting from the unrestricted information space I, the Identity axiom (a=a) eliminates self-loops, Non-Contradiction (¬(P∧¬P)) removes cycles to produce DAGs, and Excluded Middle (P∨¬P) enforces total orderings, yielding the N! permutations of the symmetric group S_N. This flowchart demonstrates how pure logical consistency requirements filter information space into physical configuration space.
```

---

### Figure 2: N=3 Permutohedron (Section 2.2)

```markdown
![N=3 Permutohedron: Valid States V₁](figures/outputs/figure_n3_permutohedron.svg)

**Figure 2**: N=3 Permutohedron showing all 6 permutations of S₃. Green nodes indicate valid states V₁ = {σ : h(σ) ≤ 1} consisting of 3 permutations (identity and two adjacent transpositions). Red nodes show invalid states with h(σ) > 1. Edges connect permutations differing by one adjacent transposition (Kendall tau distance 1). This visualization demonstrates how the constraint K=N-2=1 partitions the permutation space.
```

---

### Figure 3: Born Rule Convergence (Section 2.3 / 3.1)

```markdown
![Born Rule Convergence: P(σ) vs Constraint Threshold K](figures/outputs/figure_born_rule_convergence.svg)

**Figure 3**: Convergence of probability distribution P(σ) to the Born rule as constraint threshold K increases. For N=3, panels show K=0,1,2,3 with uniform distribution over valid states (green bars) and zero probability for invalid states (gray bars). At K=1 (Born rule case), P(σ) = 1/3 for the three valid states, matching quantum mechanical predictions. Red dashed line highlights the Born rule probability.
```

---

### Figure 4: L-Flow Trajectory (Section 2.4 / 3.2)

```markdown
![L-Flow: Monotonic Descent on N=3 Permutohedron](figures/outputs/figure_lflow_trajectory.svg)

**Figure 4**: L-Flow trajectory demonstrating monotonic descent h(σ_{t+1}) ≤ h(σ_t) on the N=3 permutohedron. Blue arrows show an example path (3,2,1) → (2,3,1) → (2,1,3) → (1,2,3) with inversion counts h = 3 → 2 → 1 → 0. Yellow highlighting marks path vertices, colored nodes indicate constraint levels (red: h=3, orange: h=2, light green: h=1, green: h=0). This visualization illustrates how the logical operator L induces directed dynamics toward the identity permutation.
```

---

### Figure 5: Validation Data (Section 2.5 / 4.2)

```markdown
![Validation Data: |V_K| and Feasibility Ratio ρ_N](figures/outputs/figure_validation_data.svg)

**Figure 5**: Computational validation results for N=3-10. **(Left)** Valid state space size |V_{N-2}| grows sub-exponentially (log scale). **(Right)** Feasibility ratio ρ_N = |V_K|/N! exhibits exponential decay ≈ 3.37·exp(-0.56N), demonstrating that the constraint K=N-2 becomes increasingly restrictive as system size grows. All 8 test cases show perfect match with theoretical predictions.
```

---

### Figure 6: Quantum Bridge Mapping (Section 3.3 / Appendix C)

```markdown
![Quantum Bridge: Permutohedron → Hilbert Space](figures/outputs/figure_quantum_bridge.svg)

**Figure 6**: Correspondence between geometric (permutohedron) and quantum (Hilbert space) representations. **(Left)** N=3 permutohedron with valid states V₁ highlighted in green. **(Right)** Hilbert space ℋ showing quantum basis states |σ⟩ for each valid permutation. Blue arrows indicate basis vectors, yellow circle at center represents superposition state |ψ⟩ = (1/√3)Σ|σ⟩. This mapping demonstrates how geometric constraints on the permutohedron translate to quantum probability amplitudes via the Born rule.
```

---

### Figure 7: Gödel Escape Hatch (Section 5 / Discussion)

```markdown
![Gödel Escape Hatch: LFT's Meta-Logical Position](figures/outputs/figure_godel_hierarchy.svg)

**Figure 7**: Hierarchical relationship showing how Logic Field Theory avoids Gödel incompleteness. LFT operates at the meta-logical level (green), deriving mathematical structures like arithmetic and number theory (yellow) without relying on formal axiomatic systems (red) that are subject to Gödel's theorems. The green escape hatch arrow illustrates LFT's immunity to incompleteness by operating on information space I rather than self-referential formal statements.
```

---

### Figure 8: Family Tree of Physical Theories (Section 6 / Conclusion)

```markdown
![Family Tree: Physical Theories Derived from LFT](figures/outputs/figure_family_tree.svg)

**Figure 8**: Derivational hierarchy showing how Logic Field Theory provides first-principles foundations for established physical theories. From the LFT root (A = L(I)), quantum mechanics emerges from geometric constraints, statistical mechanics from Mahonian permutation statistics, and thermodynamics from L-Flow dynamics. Second-tier phenomena (wave-particle duality, measurement problem, entropy increase, time asymmetry) are explained as consequences of these core derivations. Third-tier theories (general relativity, quantum field theory, quantum gravity) represent future research directions.
```

---

## Usage

1. **PNG format** (for paper submission): `figures/outputs/figure_*.png` (300 DPI)
2. **SVG format** (for GitHub/web): `figures/outputs/figure_*.svg` (scalable)

## Regenerating Figures

If paper tables are updated, regenerate all figures with:

```bash
cd paper/figures
python generate_figures.py
```

## Figure Sources

**Data-driven figures** (regenerate automatically from CSV):
- Figure 2: `data/n3_permutations.csv` (Section 2.2 table)
- Figure 3: Computed from N=3 permutation statistics
- Figure 4: Computed L-Flow path on N=3 permutohedron
- Figure 5: `data/validation_data.csv` (Section 2.5 table)

**Conceptual diagrams** (manually designed):
- Figure 1: Logical operator flowchart
- Figure 6: Permutohedron-Hilbert space mapping
- Figure 7: Gödel incompleteness hierarchy
- Figure 8: Theory family tree
"""

    with open('outputs/README_embeds.md', 'w', encoding='utf-8') as f:
        f.write(snippets)

    print("\n[OK] Markdown snippets: outputs/README_embeds.md")
    print("\n" + "=" * 60)
    print("Next steps:")
    print("  1. Review figures in outputs/")
    print("  2. Copy snippets from outputs/README_embeds.md to paper")
    print("  3. Commit changes to git")
    print("=" * 60)

if __name__ == "__main__":
    main()
