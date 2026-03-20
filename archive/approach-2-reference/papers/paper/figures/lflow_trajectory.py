#!/usr/bin/env python3
"""
Generate L-Flow trajectory visualization
Shows monotonic descent path h(σ_t+1) ≤ h(σ_t) on permutohedron
"""

import matplotlib.pyplot as plt
import networkx as nx
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

def generate_lflow_trajectory():
    """Generate L-Flow trajectory on N=3 permutohedron"""

    # Create permutohedron graph for N=3
    all_perms = list(permutations([1,2,3]))
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

    # Create layout
    pos = nx.spring_layout(G, seed=42, k=2, iterations=50)

    # Example L-Flow path: (3,2,1) → (2,3,1) → (2,1,3) → (1,2,3)
    # This shows monotonic descent: h=3 → h=2 → h=1 → h=0
    flow_path = [
        (3, 2, 1),  # h=3
        (2, 3, 1),  # h=2
        (2, 1, 3),  # h=1
        (1, 2, 3)   # h=0 (identity)
    ]

    # Colors: gradient from red (high h) to green (low h)
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

    # Create figure
    fig, ax = plt.subplots(figsize=(12, 10))

    # Draw base graph
    nx.draw_networkx_edges(G, pos, alpha=0.3, width=1, edge_color='gray')
    nx.draw_networkx_nodes(G, pos, node_color=node_colors, node_size=3000,
                           edgecolors='black', linewidths=2)

    # Draw labels
    labels = {p: f"{p}\nh={perm_to_h[p]}" for p in all_perms}
    nx.draw_networkx_labels(G, pos, labels, font_size=9, font_weight='bold')

    # Draw L-Flow path
    path_edges = [(flow_path[i], flow_path[i+1]) for i in range(len(flow_path)-1)]
    nx.draw_networkx_edges(G, pos, edgelist=path_edges,
                           edge_color='blue', width=4, alpha=0.7,
                           arrows=True, arrowsize=30, arrowstyle='-|>',
                           connectionstyle='arc3,rad=0.1')

    # Highlight path nodes
    nx.draw_networkx_nodes(G, pos, nodelist=flow_path, node_color='yellow',
                          node_size=3500, edgecolors='blue', linewidths=3,
                          alpha=0.5)

    # Add legend
    from matplotlib.patches import Patch, FancyArrow
    from matplotlib.lines import Line2D
    legend_elements = [
        Patch(facecolor='lightcoral', edgecolor='black', label='h=3 (max disorder)'),
        Patch(facecolor='orange', edgecolor='black', label='h=2'),
        Patch(facecolor='lightgreen', edgecolor='black', label='h=1'),
        Patch(facecolor='limegreen', edgecolor='black', label='h=0 (identity)'),
        Line2D([0], [0], color='blue', linewidth=4, label='L-Flow trajectory')
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=10, framealpha=0.9)

    ax.set_title('L-Flow: Monotonic Descent on N=3 Permutohedron\n' +
                 'Path: (3,2,1) → (2,3,1) → (2,1,3) → (1,2,3) shows h(σ_t+1) ≤ h(σ_t)',
                 fontsize=14, fontweight='bold', pad=20)
    ax.axis('off')

    plt.tight_layout()

    # Save
    plt.savefig('outputs/figure_lflow_trajectory.png', dpi=300, bbox_inches='tight')
    plt.savefig('outputs/figure_lflow_trajectory.svg', format='svg', bbox_inches='tight')
    plt.close()

    print("[OK] Generated L-Flow trajectory: outputs/figure_lflow_trajectory.[png|svg]")

if __name__ == "__main__":
    generate_lflow_trajectory()
