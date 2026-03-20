#!/usr/bin/env python3
"""
Generate N=3 permutohedron visualization
Shows all 6 permutations with valid states (h≤1) highlighted
"""

import matplotlib.pyplot as plt
import networkx as nx
import pandas as pd
from itertools import permutations

def generate_n3_permutohedron():
    """Generate permutohedron for N=3 with valid states highlighted"""

    # Load data
    df = pd.read_csv('data/n3_permutations.csv')

    # Create graph of S_3 with adjacent transposition edges
    G = nx.Graph()
    all_perms = list(permutations([1,2,3]))
    G.add_nodes_from(all_perms)

    # Add edges for adjacent transpositions
    for p in all_perms:
        for i in range(2):
            q = list(p)
            q[i], q[i+1] = q[i+1], q[i]
            G.add_edge(p, tuple(q))

    # Create layout (hexagon for N=3)
    pos = nx.spring_layout(G, seed=42, k=2, iterations=50)

    # Map permutations to inversion counts
    perm_to_h = {}
    for _, row in df.iterrows():
        # Parse sigma string like "(1,2,3)" to tuple (1,2,3)
        sigma_str = row['sigma'].strip('()').split(',')
        sigma = tuple(int(x) for x in sigma_str)
        perm_to_h[sigma] = row['h']

    # Colors: green for valid (h≤1), red for invalid (h>1)
    node_colors = ['lightgreen' if perm_to_h[p] <= 1 else 'lightcoral'
                   for p in all_perms]

    # Labels with permutation and h value
    labels = {p: f"{p}\nh={perm_to_h[p]}" for p in all_perms}

    # Create figure
    plt.figure(figsize=(10, 8))
    nx.draw(G, pos, labels=labels, node_color=node_colors,
            node_size=3000, font_size=10, font_weight='bold',
            with_labels=True, edge_color='gray', width=2)

    plt.title("N=3 Permutohedron: Valid States V₁ (h≤1) in Green",
              fontsize=14, fontweight='bold')

    # Add legend
    from matplotlib.patches import Patch
    legend_elements = [
        Patch(facecolor='lightgreen', label='Valid (h≤K=1): |V₁|=3'),
        Patch(facecolor='lightcoral', label='Invalid (h>K=1): 3 states')
    ]
    plt.legend(handles=legend_elements, loc='upper right', fontsize=10)

    plt.axis('off')

    # Save in multiple formats
    plt.savefig('outputs/figure_n3_permutohedron.png', dpi=300, bbox_inches='tight')
    plt.savefig('outputs/figure_n3_permutohedron.svg', format='svg', bbox_inches='tight')
    plt.close()

    print("[OK] Generated N=3 permutohedron: outputs/figure_n3_permutohedron.[png|svg]")

if __name__ == "__main__":
    generate_n3_permutohedron()
