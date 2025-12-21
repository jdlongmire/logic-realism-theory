#!/usr/bin/env python3
"""
Generate Quantum Bridge mapping visualization
Shows permutohedron → Hilbert space correspondence
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyArrowPatch, Circle
import networkx as nx
from itertools import permutations
import numpy as np

def compute_inversion_count(perm):
    """Compute inversion count for a permutation"""
    n = len(perm)
    count = 0
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                count += 1
    return count

def generate_quantum_bridge():
    """Generate side-by-side permutohedron and Hilbert space mapping"""

    fig = plt.figure(figsize=(16, 10))

    # Create two side-by-side plots
    ax_left = plt.subplot(1, 2, 1)
    ax_right = plt.subplot(1, 2, 2)

    # === LEFT PANEL: Permutohedron ===
    all_perms = list(permutations([1, 2, 3]))
    G = nx.Graph()
    G.add_nodes_from(all_perms)

    # Add edges for adjacent transpositions
    for p in all_perms:
        for i in range(2):
            q = list(p)
            q[i], q[i+1] = q[i+1], q[i]
            G.add_edge(p, tuple(q))

    # Compute inversion counts
    perm_to_h = {p: compute_inversion_count(p) for p in all_perms}

    # Layout
    pos = nx.spring_layout(G, seed=42, k=2, iterations=50)

    # Node colors based on h(σ)
    node_colors = []
    for p in all_perms:
        h = perm_to_h[p]
        if h == 0:
            node_colors.append('limegreen')
        elif h == 1:
            node_colors.append('lightgreen')
        elif h == 2:
            node_colors.append('orange')
        else:  # h == 3
            node_colors.append('lightcoral')

    # Draw permutohedron
    nx.draw_networkx_edges(G, pos, ax=ax_left, alpha=0.5, width=2, edge_color='gray')
    nx.draw_networkx_nodes(G, pos, ax=ax_left, node_color=node_colors,
                          node_size=2500, edgecolors='black', linewidths=2)

    labels = {p: f"{p}\nh={perm_to_h[p]}" for p in all_perms}
    nx.draw_networkx_labels(G, pos, labels, ax=ax_left, font_size=9, font_weight='bold')

    ax_left.set_title('Geometric Space: N=3 Permutohedron\n(Classical Configuration Space)',
                     fontsize=13, fontweight='bold', pad=15)
    ax_left.axis('off')

    # === RIGHT PANEL: Hilbert Space ===
    # For N=3, we have 3 valid states (K=1): V₁ = {(1,2,3), (1,3,2), (2,1,3)}
    valid_perms = [(1,2,3), (1,3,2), (2,1,3)]

    # Position quantum states in a triangle
    angles = np.linspace(0, 2*np.pi, len(valid_perms), endpoint=False) + np.pi/2
    radius = 0.35
    center = (0.5, 0.5)

    state_positions = {}
    for i, perm in enumerate(valid_perms):
        x = center[0] + radius * np.cos(angles[i])
        y = center[1] + radius * np.sin(angles[i])
        state_positions[perm] = (x, y)

    # Draw quantum states as circles
    for perm, (x, y) in state_positions.items():
        circle = Circle((x, y), 0.08, facecolor='lightblue',
                       edgecolor='navy', linewidth=2.5, transform=ax_right.transAxes)
        ax_right.add_patch(circle)

        # Quantum state label
        state_label = f"|{perm}⟩"
        ax_right.text(x, y, state_label, fontsize=11, fontweight='bold',
                     ha='center', va='center', transform=ax_right.transAxes)

    # Draw Born rule probabilities
    for perm, (x, y) in state_positions.items():
        prob_text = "P = 1/3"
        ax_right.text(x, y - 0.12, prob_text, fontsize=9,
                     ha='center', va='top', color='darkred',
                     transform=ax_right.transAxes)

    # Draw superposition state at center
    center_circle = Circle(center, 0.10, facecolor='yellow',
                          edgecolor='red', linewidth=3, alpha=0.6,
                          transform=ax_right.transAxes)
    ax_right.add_patch(center_circle)
    ax_right.text(center[0], center[1], "|ψ⟩", fontsize=13, fontweight='bold',
                 ha='center', va='center', transform=ax_right.transAxes)

    # Superposition label
    superposition_text = ("|ψ⟩ = (1/√3)[|(1,2,3)⟩ + |(1,3,2)⟩ + |(2,1,3)⟩]")
    ax_right.text(0.5, 0.12, superposition_text, fontsize=9,
                 ha='center', va='top', style='italic',
                 bbox=dict(boxstyle='round,pad=0.5', facecolor='lightyellow',
                          edgecolor='black', linewidth=1),
                 transform=ax_right.transAxes)

    # Draw basis vectors
    for perm, (x, y) in state_positions.items():
        arrow = FancyArrowPatch(center, (x, y),
                               arrowstyle='->', mutation_scale=20,
                               linewidth=1.5, color='blue', alpha=0.4,
                               transform=ax_right.transAxes)
        ax_right.add_patch(arrow)

    ax_right.set_title('Quantum Space: Hilbert Space ℋ\n(Quantum State Space)',
                      fontsize=13, fontweight='bold', pad=15)
    ax_right.set_xlim(0, 1)
    ax_right.set_ylim(0, 1)
    ax_right.axis('off')

    # === CENTER: Mapping Arrow ===
    # Add annotation showing the bridge
    fig.text(0.5, 0.95, 'Quantum Bridge: Permutohedron → Hilbert Space',
            fontsize=15, fontweight='bold', ha='center', va='top')

    fig.text(0.5, 0.05,
            'Mapping: σ ∈ V_K → |σ⟩ ∈ ℋ     •     Probability: Geometry → Born Rule     •     Dynamics: L-Flow → Schrödinger',
            fontsize=10, ha='center', va='bottom', style='italic',
            bbox=dict(boxstyle='round,pad=0.8', facecolor='lightgray',
                     edgecolor='black', linewidth=2))

    # Legend
    legend_elements = [
        mpatches.Patch(facecolor='limegreen', edgecolor='black', label='h=0 (identity)'),
        mpatches.Patch(facecolor='lightgreen', edgecolor='black', label='h=1 (valid)'),
        mpatches.Patch(facecolor='lightblue', edgecolor='navy', label='Quantum basis states'),
        mpatches.Patch(facecolor='yellow', edgecolor='red', label='Superposition')
    ]
    fig.legend(handles=legend_elements, loc='upper right', fontsize=9, framealpha=0.9)

    plt.tight_layout(rect=[0, 0.08, 1, 0.93])

    # Save
    plt.savefig('outputs/figure_quantum_bridge.png', dpi=300, bbox_inches='tight')
    plt.savefig('outputs/figure_quantum_bridge.svg', format='svg', bbox_inches='tight')
    plt.close()

    print("[OK] Generated Quantum Bridge mapping: outputs/figure_quantum_bridge.[png|svg]")

if __name__ == "__main__":
    generate_quantum_bridge()
