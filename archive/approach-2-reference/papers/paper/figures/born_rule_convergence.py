#!/usr/bin/env python3
"""
Generate Born Rule Convergence visualization
Shows how P(σ) converges to Born rule as constraint accumulates
"""

import matplotlib.pyplot as plt
import numpy as np
from itertools import permutations

def compute_inversion_count(perm):
    """Compute inversion count for a permutation"""
    n = len(perm)
    count = 0
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                count += 1
    return count

def generate_born_rule_convergence():
    """Generate convergence plot for N=3 system"""

    # Generate all permutations for N=3
    N = 3
    all_perms = list(permutations(range(1, N+1)))
    n_perms = len(all_perms)

    # Compute inversion counts
    inv_counts = [compute_inversion_count(p) for p in all_perms]

    # For each K value, compute probabilities
    K_values = [0, 1, 2, 3]  # Full range for N=3

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    axes = axes.flatten()

    for idx, K in enumerate(K_values):
        ax = axes[idx]

        # Valid states for this K
        valid_mask = np.array(inv_counts) <= K
        n_valid = np.sum(valid_mask)

        # Probabilities: 1/|V_K| for valid, 0 for invalid
        probs = np.where(valid_mask, 1.0/n_valid if n_valid > 0 else 0, 0)

        # Bar colors: green for valid, gray for invalid
        colors = ['lightgreen' if valid else 'lightgray' for valid in valid_mask]

        # Plot
        x_pos = np.arange(n_perms)
        bars = ax.bar(x_pos, probs, color=colors, edgecolor='navy', alpha=0.8)

        # Labels
        perm_labels = [str(p) for p in all_perms]
        ax.set_xticks(x_pos)
        ax.set_xticklabels(perm_labels, rotation=45, ha='right', fontsize=8)
        ax.set_ylabel('P(σ)', fontsize=11, fontweight='bold')
        ax.set_title(f'K = {K}: |V_K| = {n_valid}, P(σ) = {1.0/n_valid if n_valid > 0 else 0:.3f}',
                     fontsize=12, fontweight='bold')
        ax.set_ylim(0, 0.6)
        ax.grid(alpha=0.3, axis='y')

        # Add h(σ) values below
        for i, (p, h) in enumerate(zip(all_perms, inv_counts)):
            ax.text(i, -0.05, f'h={h}', ha='center', va='top', fontsize=8, color='darkred')

        # Highlight Born rule case (K=1 for N=3)
        if K == 1:
            ax.axhline(y=1.0/3, color='red', linestyle='--', linewidth=2,
                      label='Born Rule: 1/3', alpha=0.7)
            ax.legend(fontsize=10)

    plt.suptitle('Born Rule Convergence: N=3 System\nProbability Distribution P(σ) vs Constraint Threshold K',
                 fontsize=14, fontweight='bold')
    plt.tight_layout()

    # Save
    plt.savefig('outputs/figure_born_rule_convergence.png', dpi=300, bbox_inches='tight')
    plt.savefig('outputs/figure_born_rule_convergence.svg', format='svg', bbox_inches='tight')
    plt.close()

    print("[OK] Generated Born Rule convergence: outputs/figure_born_rule_convergence.[png|svg]")

if __name__ == "__main__":
    generate_born_rule_convergence()
