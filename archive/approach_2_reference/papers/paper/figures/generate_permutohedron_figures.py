#!/usr/bin/env python3
"""
Generate permutohedron visualization for N=3 and N=4.

Creates publication-quality figures showing:
- All permutations of S_N (vertices)
- Adjacent transposition edges (Cayley graph)
- Valid state space V_K highlighted (h <= K = N-2)
"""

import networkx as nx
import matplotlib.pyplot as plt
import numpy as np
from itertools import permutations

def inversion_count(perm):
    """Count inversions in permutation tuple."""
    count = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                count += 1
    return count

def is_adjacent_transposition(p1, p2):
    """Check if p1 and p2 differ by exactly one adjacent swap."""
    diffs = [i for i in range(len(p1)) if p1[i] != p2[i]]
    if len(diffs) != 2:
        return False
    i, j = diffs
    # Check adjacent positions and swapped values
    if abs(i - j) == 1 and p1[i] == p2[j] and p1[j] == p2[i]:
        return True
    return False

def build_cayley_graph(N, K):
    """
    Build Cayley graph for S_N with constraint K.

    Returns:
    --------
    G : networkx.Graph
        Cayley graph with node attributes: perm, h, valid
    perms : list
        List of permutations (tuples)
    h_vals : list
        Inversion counts for each permutation
    """
    perms = list(permutations(range(1, N+1)))
    h_vals = [inversion_count(p) for p in perms]

    G = nx.Graph()
    for i, p in enumerate(perms):
        G.add_node(i, perm=p, h=h_vals[i], valid=(h_vals[i] <= K))

    # Add edges (adjacent transpositions)
    for i in range(len(perms)):
        for j in range(i+1, len(perms)):
            if is_adjacent_transposition(perms[i], perms[j]):
                G.add_edge(i, j)

    return G, perms, h_vals

def generate_N3_figure():
    """Generate N=3 permutohedron figure."""
    print("Generating N=3 permutohedron...")

    N = 3
    K = N - 2  # K = 1
    G, perms, h_vals = build_cayley_graph(N, K)

    # Hexagon layout (manually positioned for clarity)
    pos = {
        0: (0, 2),           # (123) top
        1: (1.732, 1),       # (132) upper right
        2: (-1.732, 1),      # (213) upper left
        3: (-1.732, -1),     # (231) lower left
        4: (1.732, -1),      # (312) lower right
        5: (0, -2)           # (321) bottom
    }

    # Node colors: green for valid (h <= K), gray for invalid
    node_colors = ['#2ecc71' if G.nodes[i]['valid'] else '#bdc3c7'
                   for i in G.nodes()]

    # Edge colors: blue for edges within V_K, gray otherwise
    edge_colors = []
    for u, v in G.edges():
        if G.nodes[u]['valid'] and G.nodes[v]['valid']:
            edge_colors.append('#3498db')  # Blue
        else:
            edge_colors.append('#ecf0f1')  # Light gray

    # Create figure
    fig, ax = plt.subplots(figsize=(8, 8))

    # Draw graph
    nx.draw_networkx_edges(G, pos, edge_color=edge_colors,
                          width=3, ax=ax)
    nx.draw_networkx_nodes(G, pos, node_color=node_colors,
                          node_size=1500, ax=ax)

    # Add labels (permutation + inversion count)
    for i in G.nodes():
        perm_str = ''.join(map(str, perms[i]))
        h = h_vals[i]
        label = f"({perm_str})\nh={h}"

        # Text color: black for valid, dark gray for invalid
        text_color = 'black' if G.nodes[i]['valid'] else '#7f8c8d'
        weight = 'bold' if G.nodes[i]['valid'] else 'normal'

        ax.text(pos[i][0], pos[i][1], label,
               ha='center', va='center',
               fontsize=11, weight=weight, color=text_color)

    # Title and annotations
    ax.text(0, 2.8, 'N=3 Permutohedron',
           ha='center', fontsize=16, weight='bold')
    ax.text(0, 2.5, r'Valid space $V_1 = \{\sigma : h(\sigma) \leq 1\}$ (3 states)',
           ha='center', fontsize=12)

    # Legend
    legend_x = -2.5
    legend_y = -2.8
    ax.scatter([legend_x], [legend_y], c='#2ecc71', s=150, label='Valid (h ≤ 1)')
    ax.scatter([legend_x + 1.2], [legend_y], c='#bdc3c7', s=150, label='Excluded (h > 1)')
    ax.legend(loc='lower right', frameon=True, fontsize=10)

    ax.set_xlim(-3, 3)
    ax.set_ylim(-3.5, 3.5)
    ax.axis('off')

    plt.tight_layout()
    plt.savefig('paper/permutohedron_N3.png', dpi=300, bbox_inches='tight')
    print("Saved: paper/permutohedron_N3.png")
    plt.close()

def generate_N4_figure():
    """Generate N=4 permutohedron figure (layered view)."""
    print("Generating N=4 permutohedron...")

    N = 4
    K = N - 2  # K = 2
    G, perms, h_vals = build_cayley_graph(N, K)

    # Group vertices by inversion count (layered layout)
    layers = {h: [] for h in range(7)}  # Max h for N=4 is 6
    for i in G.nodes():
        layers[h_vals[i]].append(i)

    # Position nodes in layers
    pos = {}
    y_spacing = 1.5

    for h in sorted(layers.keys()):
        nodes_in_layer = layers[h]
        n_nodes = len(nodes_in_layer)

        if n_nodes == 1:
            x_positions = [0]
        else:
            x_positions = np.linspace(-2, 2, n_nodes)

        for i, node in enumerate(nodes_in_layer):
            pos[node] = (x_positions[i], -h * y_spacing)

    # Node colors: green for valid (h <= K=2), gray for invalid
    node_colors = ['#2ecc71' if G.nodes[i]['valid'] else '#bdc3c7'
                   for i in G.nodes()]

    # Node sizes: larger for valid states
    node_sizes = [800 if G.nodes[i]['valid'] else 400
                  for i in G.nodes()]

    # Edge colors
    edge_colors = []
    for u, v in G.edges():
        if G.nodes[u]['valid'] and G.nodes[v]['valid']:
            edge_colors.append('#3498db')  # Blue
        else:
            edge_colors.append('#ecf0f1')  # Very light gray

    # Create figure
    fig, ax = plt.subplots(figsize=(10, 10))

    # Draw edges (gray/faded for clarity)
    nx.draw_networkx_edges(G, pos, edge_color=edge_colors,
                          width=1, alpha=0.4, ax=ax)

    # Draw nodes
    nx.draw_networkx_nodes(G, pos, node_color=node_colors,
                          node_size=node_sizes, ax=ax)

    # Add labels only for valid states
    for i in G.nodes():
        if G.nodes[i]['valid']:
            perm_str = ''.join(map(str, perms[i]))
            h = h_vals[i]
            label = f"({perm_str})\nh={h}"
            ax.text(pos[i][0], pos[i][1], label,
                   ha='center', va='center',
                   fontsize=9, weight='bold')

    # Layer labels
    for h in range(3):  # Only show h=0,1,2 (valid layers)
        if layers[h]:
            ax.text(-2.8, -h * y_spacing, f'h={h}',
                   ha='right', va='center', fontsize=11,
                   weight='bold', color='#34495e')

    # Title and annotations
    ax.text(0, 0.8, 'N=4 Permutohedron (Layered View)',
           ha='center', fontsize=16, weight='bold')
    ax.text(0, 0.4, r'Valid space $V_2 = \{\sigma : h(\sigma) \leq 2\}$ (9 states shown)',
           ha='center', fontsize=12)
    ax.text(0, 0, 'Full $S_4$ has 24 states (only 9 valid states labeled)',
           ha='center', fontsize=10, style='italic', color='#7f8c8d')

    # Legend
    legend_x = -3
    legend_y = -8
    ax.scatter([legend_x], [legend_y], c='#2ecc71', s=200, label='Valid (h ≤ 2)')
    ax.scatter([legend_x + 1.5], [legend_y], c='#bdc3c7', s=100, label='Excluded (h > 2)')
    ax.legend(loc='lower right', frameon=True, fontsize=10)

    ax.set_xlim(-3.5, 3.5)
    ax.set_ylim(-9, 1.2)
    ax.axis('off')

    plt.tight_layout()
    plt.savefig('paper/permutohedron_N4.png', dpi=300, bbox_inches='tight')
    print("Saved: paper/permutohedron_N4.png")
    plt.close()

def generate_combined_figure():
    """Generate combined two-panel figure."""
    print("Generating combined figure...")

    # This would create a side-by-side layout
    # For now, generate separately and combine manually
    # Or use matplotlib subplots

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 8))

    # Generate N=3 on ax1
    N = 3
    K = 1
    G3, perms3, h_vals3 = build_cayley_graph(N, K)

    pos3 = {
        0: (0, 2),
        1: (1.732, 1),
        2: (-1.732, 1),
        3: (-1.732, -1),
        4: (1.732, -1),
        5: (0, -2)
    }

    node_colors3 = ['#2ecc71' if G3.nodes[i]['valid'] else '#bdc3c7'
                    for i in G3.nodes()]
    edge_colors3 = ['#3498db' if G3.nodes[u]['valid'] and G3.nodes[v]['valid']
                    else '#ecf0f1' for u,v in G3.edges()]

    nx.draw_networkx_edges(G3, pos3, edge_color=edge_colors3, width=3, ax=ax1)
    nx.draw_networkx_nodes(G3, pos3, node_color=node_colors3,
                          node_size=1500, ax=ax1)

    for i in G3.nodes():
        perm_str = ''.join(map(str, perms3[i]))
        label = f"({perm_str})\nh={h_vals3[i]}"
        text_color = 'black' if G3.nodes[i]['valid'] else '#7f8c8d'
        weight = 'bold' if G3.nodes[i]['valid'] else 'normal'
        ax1.text(pos3[i][0], pos3[i][1], label,
                ha='center', va='center', fontsize=10,
                weight=weight, color=text_color)

    ax1.text(0, 2.8, '(A) N=3 Permutohedron', ha='center', fontsize=14, weight='bold')
    ax1.text(0, 2.5, r'$V_1$ (3 valid states)', ha='center', fontsize=11)
    ax1.set_xlim(-3, 3)
    ax1.set_ylim(-3, 3.5)
    ax1.axis('off')

    # Generate simplified N=4 on ax2 (just show valid states)
    N = 4
    K = 2
    G4, perms4, h_vals4 = build_cayley_graph(N, K)

    # Extract subgraph of valid states only
    valid_nodes = [i for i in G4.nodes() if G4.nodes[i]['valid']]
    G4_valid = G4.subgraph(valid_nodes).copy()

    # Use spring layout for valid subgraph
    pos4 = nx.spring_layout(G4_valid, k=1.5, iterations=50, seed=42)

    nx.draw_networkx_edges(G4_valid, pos4, edge_color='#3498db', width=2, ax=ax2)
    nx.draw_networkx_nodes(G4_valid, pos4, node_color='#2ecc71',
                          node_size=800, ax=ax2)

    for i in G4_valid.nodes():
        perm_str = ''.join(map(str, perms4[i]))
        label = f"{perm_str}\nh={h_vals4[i]}"
        ax2.text(pos4[i][0], pos4[i][1], label,
                ha='center', va='center', fontsize=9, weight='bold')

    ax2.text(0, 1.3, '(B) N=4 Permutohedron', ha='center', fontsize=14, weight='bold',
            transform=ax2.transAxes)
    ax2.text(0.5, 1.2, r'$V_2$ (9 valid states shown)', ha='center', fontsize=11,
            transform=ax2.transAxes)
    ax2.axis('off')

    plt.tight_layout()
    plt.savefig('paper/permutohedron_combined.png', dpi=300, bbox_inches='tight')
    print("Saved: paper/permutohedron_combined.png")
    plt.close()

def main():
    """Generate all permutohedron figures."""
    print("=== Permutohedron Figure Generation ===\n")

    # Generate individual figures
    generate_N3_figure()
    print()

    generate_N4_figure()
    print()

    # Generate combined figure
    generate_combined_figure()
    print()

    print("=== All figures generated successfully ===")
    print("\nFiles created:")
    print("  - paper/permutohedron_N3.png")
    print("  - paper/permutohedron_N4.png")
    print("  - paper/permutohedron_combined.png")

if __name__ == "__main__":
    main()
