#!/usr/bin/env python3
"""
Generate Family Tree of Physical Theories
Shows how LFT derives/encompasses other theories
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Rectangle
import numpy as np

def generate_family_tree():
    """Generate theory relationship diagram with LFT as foundation"""

    fig, ax = plt.subplots(figsize=(16, 12))

    # Define theory nodes (tree structure)
    # Root: LFT
    root = {
        'name': 'Logic Field Theory (LFT)',
        'subtitle': 'A = L(I)',
        'x': 0.5,
        'y': 0.15,
        'width': 0.30,
        'height': 0.12,
        'color': 'lightgreen',
        'desc': 'Logical filtering\nof information space'
    }

    # First tier: Core derivations
    tier1 = [
        {
            'name': 'Quantum\nMechanics',
            'x': 0.25,
            'y': 0.40,
            'width': 0.18,
            'height': 0.10,
            'color': 'lightblue',
            'desc': 'Born rule from\ngeometric constraints',
            'status': '✓ Derived'
        },
        {
            'name': 'Statistical\nMechanics',
            'x': 0.50,
            'y': 0.40,
            'width': 0.18,
            'height': 0.10,
            'color': 'lightyellow',
            'desc': 'Mahonian distribution\nfrom permutations',
            'status': '✓ Derived'
        },
        {
            'name': 'Thermodynamics',
            'x': 0.75,
            'y': 0.40,
            'width': 0.18,
            'height': 0.10,
            'color': 'lightcoral',
            'desc': 'Arrow of time\nfrom L-Flow',
            'status': '✓ Derived'
        }
    ]

    # Second tier: Emergent phenomena
    tier2 = [
        {
            'name': 'Wave-Particle\nDuality',
            'x': 0.17,
            'y': 0.62,
            'width': 0.14,
            'height': 0.08,
            'color': 'aliceblue',
            'parent_idx': 0,
            'status': '✓ Explained'
        },
        {
            'name': 'Measurement\nProblem',
            'x': 0.33,
            'y': 0.62,
            'width': 0.14,
            'height': 0.08,
            'color': 'aliceblue',
            'parent_idx': 0,
            'status': '✓ Resolved'
        },
        {
            'name': 'Entropy\nIncrease',
            'x': 0.67,
            'y': 0.62,
            'width': 0.14,
            'height': 0.08,
            'color': 'mistyrose',
            'parent_idx': 2,
            'status': '✓ Explained'
        },
        {
            'name': 'Time\nAsymmetry',
            'x': 0.83,
            'y': 0.62,
            'width': 0.14,
            'height': 0.08,
            'color': 'mistyrose',
            'parent_idx': 2,
            'status': '✓ Derived'
        }
    ]

    # Third tier: Future extensions
    tier3 = [
        {
            'name': 'General\nRelativity',
            'x': 0.35,
            'y': 0.82,
            'width': 0.14,
            'height': 0.08,
            'color': 'lavender',
            'status': 'In Progress'
        },
        {
            'name': 'Quantum\nField Theory',
            'x': 0.51,
            'y': 0.82,
            'width': 0.14,
            'height': 0.08,
            'color': 'lavender',
            'status': 'Future Work'
        },
        {
            'name': 'Quantum\nGravity',
            'x': 0.67,
            'y': 0.82,
            'width': 0.14,
            'height': 0.08,
            'color': 'lavender',
            'status': 'Future Work'
        }
    ]

    # Draw root node
    draw_theory_box(ax, root, fontsize=13, title_offset=0.045)

    # Draw tier 1 nodes
    for theory in tier1:
        draw_theory_box(ax, theory, fontsize=11, title_offset=0.035)
        # Connect to root
        draw_connection(ax, root, theory, label='derives', color='navy')

    # Draw tier 2 nodes
    for theory in tier2:
        draw_theory_box(ax, theory, fontsize=9, title_offset=0.028)
        # Connect to parent in tier 1
        parent = tier1[theory['parent_idx']]
        draw_connection(ax, parent, theory, label='', color='darkblue')

    # Draw tier 3 nodes
    for theory in tier3:
        draw_theory_box(ax, theory, fontsize=9, title_offset=0.028)
        # Connect to multiple tier 1 parents
        for parent in tier1[:2]:  # QM and StatMech
            draw_connection(ax, parent, theory, label='', color='gray',
                          linestyle='dashed', alpha=0.5)

    # Add tier labels
    ax.text(0.02, 0.15, 'Foundation', fontsize=11, fontweight='bold',
           rotation=90, ha='center', va='center', color='darkgreen',
           transform=ax.transAxes)
    ax.text(0.02, 0.40, 'Core Theories', fontsize=11, fontweight='bold',
           rotation=90, ha='center', va='center', color='darkblue',
           transform=ax.transAxes)
    ax.text(0.02, 0.62, 'Phenomena', fontsize=11, fontweight='bold',
           rotation=90, ha='center', va='center', color='navy',
           transform=ax.transAxes)
    ax.text(0.02, 0.82, 'Extensions', fontsize=11, fontweight='bold',
           rotation=90, ha='center', va='center', color='purple',
           transform=ax.transAxes)

    # Title
    ax.text(0.5, 0.96, 'Family Tree: Physical Theories Derived from LFT',
           fontsize=16, fontweight='bold', ha='center', va='top',
           transform=ax.transAxes)

    # Legend
    legend_elements = [
        mpatches.Patch(facecolor='lightgreen', edgecolor='black',
                      label='LFT Foundation'),
        mpatches.Patch(facecolor='lightblue', edgecolor='black',
                      label='Quantum theory'),
        mpatches.Patch(facecolor='lightyellow', edgecolor='black',
                      label='Statistical theory'),
        mpatches.Patch(facecolor='lightcoral', edgecolor='black',
                      label='Thermodynamic theory'),
        mpatches.Patch(facecolor='lavender', edgecolor='black',
                      label='Future extensions')
    ]
    ax.legend(handles=legend_elements, loc='lower right', fontsize=9,
             framealpha=0.9, ncol=2)

    # Add summary box
    summary_text = (
        "Derivational Hierarchy:\n"
        "LFT provides first-principles derivation of quantum mechanics,\n"
        "statistical mechanics, and thermodynamics from pure logic.\n"
        "All physical laws emerge from A = L(I)."
    )
    ax.text(0.5, 0.03, summary_text, fontsize=9, ha='center', va='bottom',
           linespacing=1.5,
           bbox=dict(boxstyle='round,pad=0.8', facecolor='lightyellow',
                    edgecolor='black', linewidth=2),
           transform=ax.transAxes)

    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis('off')

    plt.tight_layout()

    # Save
    plt.savefig('outputs/figure_family_tree.png', dpi=300, bbox_inches='tight')
    plt.savefig('outputs/figure_family_tree.svg', format='svg', bbox_inches='tight')
    plt.close()

    print("[OK] Generated Family Tree: outputs/figure_family_tree.[png|svg]")

def draw_theory_box(ax, theory, fontsize=10, title_offset=0.03):
    """Draw a theory box with title, subtitle, and description"""
    # Main box
    box = FancyBboxPatch(
        (theory['x'] - theory['width']/2, theory['y'] - theory['height']/2),
        theory['width'], theory['height'],
        boxstyle="round,pad=0.008",
        edgecolor='black',
        facecolor=theory['color'],
        linewidth=2,
        transform=ax.transAxes
    )
    ax.add_patch(box)

    # Title
    ax.text(theory['x'], theory['y'] + title_offset,
           theory['name'],
           fontsize=fontsize, fontweight='bold', ha='center', va='center',
           transform=ax.transAxes)

    # Subtitle (if exists)
    if 'subtitle' in theory:
        ax.text(theory['x'], theory['y'] + title_offset - 0.02,
               theory['subtitle'],
               fontsize=fontsize-2, style='italic', ha='center', va='center',
               color='darkblue', transform=ax.transAxes)

    # Description (if exists)
    if 'desc' in theory:
        ax.text(theory['x'], theory['y'] - 0.01,
               theory['desc'],
               fontsize=fontsize-2, ha='center', va='center',
               transform=ax.transAxes, linespacing=1.4)

    # Status
    if 'status' in theory:
        status_color = 'darkgreen' if '✓' in theory['status'] else 'darkred'
        ax.text(theory['x'], theory['y'] - theory['height']/2 - 0.015,
               theory['status'],
               fontsize=fontsize-2, ha='center', va='top',
               fontweight='bold', color=status_color,
               transform=ax.transAxes)

def draw_connection(ax, parent, child, label='', color='navy',
                   linestyle='solid', alpha=1.0):
    """Draw arrow from parent to child node"""
    arrow = FancyArrowPatch(
        (parent['x'], parent['y'] + parent['height']/2),
        (child['x'], child['y'] - child['height']/2),
        arrowstyle='-|>',
        mutation_scale=20,
        linewidth=2,
        color=color,
        linestyle=linestyle,
        alpha=alpha,
        transform=ax.transAxes
    )
    ax.add_patch(arrow)

    # Label (if provided)
    if label:
        mid_x = (parent['x'] + child['x']) / 2
        mid_y = (parent['y'] + parent['height']/2 + child['y'] - child['height']/2) / 2
        ax.text(mid_x + 0.03, mid_y, label,
               fontsize=8, style='italic', color=color,
               ha='left', va='center', transform=ax.transAxes)

if __name__ == "__main__":
    generate_family_tree()
