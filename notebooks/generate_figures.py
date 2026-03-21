#!/usr/bin/env python3
"""
LRT Visualizations - Generate computed figures for Logic Realism Theory documentation.
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import networkx as nx
import yaml
from pathlib import Path
import warnings
warnings.filterwarnings('ignore')

# Use a compatible style
try:
    plt.style.use('seaborn-v0_8-whitegrid')
except:
    try:
        plt.style.use('seaborn-whitegrid')
    except:
        pass  # Use default

plt.rcParams['figure.figsize'] = (12, 8)
plt.rcParams['font.family'] = 'sans-serif'
plt.rcParams['font.size'] = 11

# Paths
REPO_ROOT = Path('/media/jdlongmire/Macro-Drive-2TB/GitHub_Repos/logic-realism-theory')
TRACEABILITY = REPO_ROOT / 'traceability' / 'claims'
FIGURES = REPO_ROOT / 'theory' / 'figures'

print(f"Repository: {REPO_ROOT}")
print(f"Traceability claims: {TRACEABILITY}")
print(f"Output figures: {FIGURES}")
print()

# ============================================================
# 1. Dependency Graph
# ============================================================

def load_claims():
    """Load all claim YAML files from traceability directory."""
    claims = {}
    if not TRACEABILITY.exists():
        print(f"Warning: {TRACEABILITY} not found")
        return claims

    for yaml_file in TRACEABILITY.glob('*.yaml'):
        try:
            with open(yaml_file, 'r') as f:
                data = yaml.safe_load(f)
                if data and 'id' in data:
                    claims[data['id']] = data
        except Exception as e:
            print(f"Error loading {yaml_file}: {e}")

    return claims

def build_dependency_graph(claims):
    """Build NetworkX graph from claims."""
    G = nx.DiGraph()

    for claim_id, data in claims.items():
        prefix = claim_id.split('-')[0]
        G.add_node(claim_id,
                   title=data.get('title', data.get('name', claim_id)),
                   prefix=prefix,
                   proof_status=data.get('proof_status', 'unknown'))

    for claim_id, data in claims.items():
        for dep in data.get('depends_on', []):
            # Handle both string and dict formats
            if isinstance(dep, dict):
                dep_id = dep.get('claim_id', dep.get('id'))
            else:
                dep_id = dep
            if dep_id and dep_id in claims:
                G.add_edge(dep_id, claim_id)

    return G

def plot_dependency_graph(G, save_path=None):
    """Plot the dependency graph with color-coded categories."""
    if not G or G.number_of_nodes() == 0:
        print("No graph data to plot - skipping dependency graph")
        return

    fig, ax = plt.subplots(figsize=(16, 12))

    color_map = {
        'ONT': '#2563eb',
        'LOG': '#7c3aed',
        'ACT': '#d97706',
        'QM': '#059669',
        'PHY': '#dc2626',
        'PRD': '#0891b2',
        'OPN': '#6b7280',
        'EXT': '#f59e0b',
    }

    node_colors = [color_map.get(G.nodes[n].get('prefix', ''), '#9ca3af') for n in G.nodes()]

    try:
        pos = nx.spring_layout(G, k=2, iterations=50, seed=42)
    except:
        pos = nx.kamada_kawai_layout(G)

    nx.draw_networkx_edges(G, pos, ax=ax, alpha=0.3, edge_color='gray',
                           arrows=True, arrowsize=15, connectionstyle='arc3,rad=0.1')
    nx.draw_networkx_nodes(G, pos, ax=ax, node_color=node_colors,
                           node_size=800, alpha=0.9)
    nx.draw_networkx_labels(G, pos, ax=ax, font_size=8, font_weight='bold')

    legend_elements = [plt.Line2D([0], [0], marker='o', color='w',
                                   markerfacecolor=color, markersize=10, label=prefix)
                       for prefix, color in color_map.items()]
    ax.legend(handles=legend_elements, loc='upper left', title='Claim Type')

    ax.set_title('LRT Traceability Dependency Graph', fontsize=16, fontweight='bold')
    ax.axis('off')

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {save_path}")

    plt.close()

# ============================================================
# 2. Axiom Reduction Timeline
# ============================================================

def plot_axiom_timeline(save_path=None):
    """Plot axiom reduction history."""
    axiom_history = [
        {'date': '2025-12-01', 'axioms': 55, 'sorries': 12, 'event': 'Initial formalization'},
        {'date': '2026-01-15', 'axioms': 50, 'sorries': 10, 'event': 'Step 1-3 cleanup'},
        {'date': '2026-02-01', 'axioms': 48, 'sorries': 8, 'event': 'Boolean bridge'},
        {'date': '2026-02-15', 'axioms': 45, 'sorries': 6, 'event': 'Step 4-5 integration'},
        {'date': '2026-03-01', 'axioms': 44, 'sorries': 5, 'event': 'Born rule completion'},
        {'date': '2026-03-15', 'axioms': 35, 'sorries': 2, 'event': 'Major audit'},
        {'date': '2026-03-17', 'axioms': 31, 'sorries': 0, 'event': 'Sorry elimination'},
        {'date': '2026-03-20', 'axioms': 31, 'sorries': 0, 'event': 'Current state'},
    ]

    dates = [d['date'] for d in axiom_history]
    axioms = [d['axioms'] for d in axiom_history]
    sorries = [d['sorries'] for d in axiom_history]
    events = [d['event'] for d in axiom_history]

    fig, ax1 = plt.subplots(figsize=(14, 7))

    color1 = '#2563eb'
    ax1.set_xlabel('Date', fontsize=12)
    ax1.set_ylabel('Total Axioms', color=color1, fontsize=12)
    line1 = ax1.plot(dates, axioms, 'o-', color=color1, linewidth=2, markersize=10, label='Axioms')
    ax1.tick_params(axis='y', labelcolor=color1)
    ax1.set_ylim(0, 60)
    ax1.fill_between(dates, axioms, alpha=0.2, color=color1)

    ax2 = ax1.twinx()
    color2 = '#dc2626'
    ax2.set_ylabel('Sorries', color=color2, fontsize=12)
    line2 = ax2.plot(dates, sorries, 's--', color=color2, linewidth=2, markersize=8, label='Sorries')
    ax2.tick_params(axis='y', labelcolor=color2)
    ax2.set_ylim(0, 15)

    for i, (date, ax_count, event) in enumerate(zip(dates, axioms, events)):
        if i in [0, 3, 5, 7]:
            ax1.annotate(event, (date, ax_count), textcoords="offset points",
                         xytext=(0, 15), ha='center', fontsize=9,
                         bbox=dict(boxstyle='round,pad=0.3', facecolor='white', edgecolor='gray', alpha=0.8))

    ax1.axhline(y=24, color='#059669', linestyle=':', linewidth=2, alpha=0.7)
    ax1.text(dates[-1], 25, 'Target: ~24', color='#059669', fontsize=10, ha='right')
    ax1.axhspan(0, 31, xmin=0.85, xmax=1.0, alpha=0.1, color='#059669')
    ax1.text(dates[-1], 33, '0 sorries!', color='#059669', fontsize=11, ha='right', fontweight='bold')

    lines = line1 + line2
    labels = ['Axioms', 'Sorries']
    ax1.legend(lines, labels, loc='upper right')

    ax1.set_title('LRT Axiom Reduction Timeline', fontsize=16, fontweight='bold', pad=20)
    ax1.tick_params(axis='x', rotation=45)
    fig.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {save_path}")

    plt.close()

# ============================================================
# 3. Born Rule Emergence
# ============================================================

def plot_probability_simplex(save_path=None):
    """Plot the 2D probability simplex with Gleason constraint visualization."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    ax1 = axes[0]
    ax1.plot([0, 1], [1, 0], 'k-', linewidth=2, label='Probability simplex')
    ax1.scatter([0, 1], [1, 0], s=200, c='#2563eb', zorder=5, edgecolors='black')
    ax1.annotate('|0⟩', (0, 1), textcoords="offset points", xytext=(-15, 10), fontsize=12)
    ax1.annotate('|1⟩', (1, 0), textcoords="offset points", xytext=(10, -10), fontsize=12)

    theta = np.linspace(0, np.pi/2, 50)
    p0 = np.cos(theta)**2
    p1 = np.sin(theta)**2
    ax1.plot(p0, p1, '--', color='#059669', linewidth=2, label='Born rule states')

    ax1.scatter([0.5], [0.5], s=150, c='#d97706', zorder=5, marker='D', edgecolors='black')
    ax1.annotate('|+⟩ = (|0⟩+|1⟩)/√2', (0.5, 0.5), textcoords="offset points",
                 xytext=(20, 20), fontsize=10,
                 arrowprops=dict(arrowstyle='->', color='gray'))

    ax1.set_xlabel('p(|0⟩)', fontsize=12)
    ax1.set_ylabel('p(|1⟩)', fontsize=12)
    ax1.set_title('Qubit: Born Rule on Probability Simplex', fontsize=14, fontweight='bold')
    ax1.set_xlim(-0.1, 1.1)
    ax1.set_ylim(-0.1, 1.1)
    ax1.set_aspect('equal')
    ax1.legend(loc='upper right')
    ax1.grid(True, alpha=0.3)

    ax2 = axes[1]
    theta = np.linspace(0, 2*np.pi, 100)
    ax2.plot(np.cos(theta), np.sin(theta), 'k-', linewidth=1, alpha=0.5)

    ax2.arrow(0, 0, 0, 0.9, head_width=0.08, head_length=0.08, fc='#2563eb', ec='#2563eb')
    ax2.arrow(0, 0, 0, -0.9, head_width=0.08, head_length=0.08, fc='#dc2626', ec='#dc2626')
    ax2.annotate('|0⟩', (0, 1), textcoords="offset points", xytext=(10, 5), fontsize=12, color='#2563eb')
    ax2.annotate('|1⟩', (0, -1), textcoords="offset points", xytext=(10, -10), fontsize=12, color='#dc2626')

    ax2.scatter([1, -1], [0, 0], s=100, c='#d97706', marker='D', edgecolors='black')
    ax2.annotate('|+⟩', (1, 0), textcoords="offset points", xytext=(10, 5), fontsize=11)
    ax2.annotate('|−⟩', (-1, 0), textcoords="offset points", xytext=(-25, 5), fontsize=11)

    psi_theta = np.pi/3
    psi_x, psi_y = np.sin(psi_theta), np.cos(psi_theta)
    ax2.arrow(0, 0, psi_x*0.85, psi_y*0.85, head_width=0.06, head_length=0.06,
              fc='#059669', ec='#059669', linewidth=2)
    ax2.annotate('|ψ⟩', (psi_x, psi_y), textcoords="offset points", xytext=(10, 5),
                 fontsize=11, color='#059669', fontweight='bold')

    ax2.text(0.5, -0.5, f'p(0|ψ) = cos²(θ/2) = {np.cos(psi_theta/2)**2:.3f}',
             fontsize=10, style='italic')

    ax2.set_xlim(-1.3, 1.3)
    ax2.set_ylim(-1.3, 1.3)
    ax2.set_aspect('equal')
    ax2.set_title('Bloch Sphere: Measurement Probabilities', fontsize=14, fontweight='bold')
    ax2.axis('off')

    textstr = 'LRT: Boolean A constrains\neigenvalues to {0,1}\n→ Gleason forces Born rule'
    props = dict(boxstyle='round', facecolor='#ecfdf5', edgecolor='#059669', alpha=0.9)
    ax2.text(0.95, 0.05, textstr, transform=ax2.transAxes, fontsize=10,
             verticalalignment='bottom', horizontalalignment='right', bbox=props)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {save_path}")

    plt.close()

# ============================================================
# 4. Dimension Scaling
# ============================================================

def plot_dimension_scaling(save_path=None):
    """Plot dimension scaling for different K values."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    ax1 = axes[0]
    n_values = np.arange(1, 8)

    for K, color, label in [(2, '#2563eb', 'K=2 (Complex/Quantum)'),
                             (3, '#d97706', 'K=3 (Quaternionic)'),
                             (4, '#dc2626', 'K=4 (Octonionic)')]:
        dims = K ** n_values
        ax1.plot(n_values, dims, 'o-', color=color, linewidth=2, markersize=10, label=label)

    ax1.fill_between(n_values, 2**n_values, alpha=0.15, color='#2563eb')

    ax1.set_xlabel('Number of subsystems (n)', fontsize=12)
    ax1.set_ylabel('State space dimension (K^n)', fontsize=12)
    ax1.set_title('Dimension Scaling: K^n Growth', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper left')
    ax1.set_xticks(n_values)
    ax1.grid(True, alpha=0.3)

    ax1.annotate('LRT derives K=2\n(via 3 routes)', xy=(3, 8), xytext=(5, 50),
                 fontsize=10, color='#2563eb',
                 arrowprops=dict(arrowstyle='->', color='#2563eb', lw=1.5),
                 bbox=dict(boxstyle='round,pad=0.3', facecolor='white', edgecolor='#2563eb'))

    ax2 = axes[1]
    n_large = np.arange(1, 20)

    ax2.semilogy(n_large, 2**n_large, '-', color='#2563eb', linewidth=3, label='K=2 (QM)')
    ax2.semilogy(n_large, 3**n_large, '--', color='#d97706', linewidth=2, label='K=3')
    ax2.semilogy(n_large, 4**n_large, ':', color='#dc2626', linewidth=2, label='K=4')

    ax2.axhspan(1, 2**10, alpha=0.1, color='#059669')
    ax2.text(15, 500, 'Physically\nrealizable', fontsize=10, color='#059669',
             ha='center', style='italic')

    ax2.set_xlabel('Number of qubits/subsystems', fontsize=12)
    ax2.set_ylabel('State space dimension (log scale)', fontsize=12)
    ax2.set_title('Why K=2: Exponential Efficiency', fontsize=14, fontweight='bold')
    ax2.legend(loc='upper left')
    ax2.grid(True, alpha=0.3)

    textstr = 'H2: dim(AB) = dim(A) × dim(B)\n\nI∞ product structure\n→ multiplicative dimension\n→ K^n scaling'
    props = dict(boxstyle='round', facecolor='#fef3c7', edgecolor='#d97706', alpha=0.9)
    ax2.text(0.98, 0.4, textstr, transform=ax2.transAxes, fontsize=10,
             verticalalignment='center', horizontalalignment='right', bbox=props)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {save_path}")

    plt.close()

# ============================================================
# 5. Entanglement Constraints
# ============================================================

def plot_entanglement_constraints(save_path=None):
    """Plot 3D surface showing L3 constraints on entanglement correlations."""
    fig = plt.figure(figsize=(14, 6))

    ax1 = fig.add_subplot(121, projection='3d')

    a = np.linspace(0, np.pi, 30)
    b = np.linspace(0, np.pi, 30)
    A, B = np.meshgrid(a, b)
    E = -np.cos(A - B)

    surf = ax1.plot_surface(A, B, E, cmap='coolwarm', alpha=0.8,
                            linewidth=0, antialiased=True)

    ax1.set_xlabel('Alice angle (a)', fontsize=10)
    ax1.set_ylabel('Bob angle (b)', fontsize=10)
    ax1.set_zlabel('E(a,b)', fontsize=10)
    ax1.set_title('Quantum Correlations: E(a,b) = −cos(a−b)', fontsize=12, fontweight='bold')

    fig.colorbar(surf, ax=ax1, shrink=0.5, aspect=10, label='Correlation')

    ax2 = fig.add_subplot(122)

    theta = np.linspace(0, np.pi/2, 100)
    S_quantum = 2 * np.sqrt(2) * np.cos(theta)

    ax2.fill_between(theta, 0, 2, alpha=0.2, color='gray', label='Classical region (|S| ≤ 2)')
    ax2.fill_between(theta, 2, 2*np.sqrt(2), alpha=0.2, color='#059669', label='Quantum advantage')

    ax2.plot(theta, S_quantum, '-', color='#2563eb', linewidth=3, label='Quantum (Tsirelson)')
    ax2.axhline(y=2, color='#dc2626', linestyle='--', linewidth=2, label='Classical bound')
    ax2.axhline(y=2*np.sqrt(2), color='#059669', linestyle=':', linewidth=2, label='Tsirelson bound')

    ax2.scatter([0], [2*np.sqrt(2)], s=150, c='#d97706', marker='*', zorder=5, edgecolors='black')
    ax2.annotate(f'S = 2√2 ≈ {2*np.sqrt(2):.3f}', (0, 2*np.sqrt(2)),
                 textcoords="offset points", xytext=(20, 10), fontsize=11,
                 arrowprops=dict(arrowstyle='->', color='gray'))

    ax2.set_xlabel('Measurement angle θ', fontsize=12)
    ax2.set_ylabel('CHSH quantity S', fontsize=12)
    ax2.set_title('Bell Inequality: L₃ Constraints', fontsize=14, fontweight='bold')
    ax2.legend(loc='upper right')
    ax2.set_xlim(0, np.pi/2)
    ax2.set_ylim(0, 3)
    ax2.grid(True, alpha=0.3)

    textstr = 'LRT: Correlations are L₃ constraints\non joint configurations in I∞\n\nNo nonlocal causation\nA evaluates globally'
    props = dict(boxstyle='round', facecolor='#ecfdf5', edgecolor='#059669', alpha=0.9)
    ax2.text(0.02, 0.35, textstr, transform=ax2.transAxes, fontsize=9,
             verticalalignment='center', bbox=props)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {save_path}")

    plt.close()

# ============================================================
# Main
# ============================================================

if __name__ == '__main__':
    print("Generating LRT visualizations...\n")

    # 1. Dependency Graph
    print("1. Dependency Graph")
    claims = load_claims()
    print(f"   Loaded {len(claims)} claims")
    if claims:
        G = build_dependency_graph(claims)
        print(f"   Graph: {G.number_of_nodes()} nodes, {G.number_of_edges()} edges")
        plot_dependency_graph(G, FIGURES / 'dependency-graph.png')
    else:
        print("   Skipped (no claims found)")

    # 2. Axiom Timeline
    print("\n2. Axiom Reduction Timeline")
    plot_axiom_timeline(FIGURES / 'axiom-timeline.png')

    # 3. Born Rule
    print("\n3. Born Rule Emergence")
    plot_probability_simplex(FIGURES / 'born-rule-simplex.png')

    # 4. Dimension Scaling
    print("\n4. Dimension Scaling")
    plot_dimension_scaling(FIGURES / 'dimension-scaling.png')

    # 5. Entanglement
    print("\n5. Entanglement Constraints")
    plot_entanglement_constraints(FIGURES / 'entanglement-constraints.png')

    # Summary
    print("\n" + "=" * 60)
    print("LRT Visualization - Generated Figures")
    print("=" * 60)
    print(f"\nOutput directory: {FIGURES}")
    print("\nGenerated files:")

    generated = [
        'dependency-graph.png',
        'axiom-timeline.png',
        'born-rule-simplex.png',
        'dimension-scaling.png',
        'entanglement-constraints.png',
    ]

    for fig in generated:
        path = FIGURES / fig
        status = "✓" if path.exists() else "✗"
        print(f"  {status} {fig}")

    print("\nStatic figures (created separately):")
    static = ['axiom-treemap.svg', 'axiom-treemap.png',
              'competitor-matrix.svg', 'competitor-matrix.png',
              'epr-dissolution.svg', 'epr-dissolution.png',
              'LRT-derivation-chain-v2.svg', 'LRT-derivation-chain-v2.png']
    for fig in static:
        path = FIGURES / fig
        status = "✓" if path.exists() else "✗"
        print(f"  {status} {fig}")

    print("\nDone!")
