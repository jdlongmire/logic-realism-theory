#!/usr/bin/env python3
"""
Generate Gödel Escape Hatch hierarchy diagram
Shows LFT's meta-logical position relative to Gödel incompleteness
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Wedge

def generate_godel_hierarchy():
    """Generate hierarchy showing LFT → Arithmetic → Formal Systems"""

    fig, ax = plt.subplots(figsize=(14, 11))

    # Define hierarchy levels (inverted pyramid)
    levels = [
        {
            'y': 0.80,
            'width': 0.85,
            'name': 'Logic Field Theory (LFT)',
            'subtitle': 'Meta-Logical Framework',
            'desc': 'Axioms: ID, NC, EM (logical consistency only)\nOperates on information space I, not formal statements',
            'color': 'lightgreen',
            'properties': '✓ Derivational (A = L(I))\n✓ No self-reference paradoxes\n✓ Physical reality emerges'
        },
        {
            'y': 0.55,
            'width': 0.70,
            'name': 'Arithmetic & Number Theory',
            'subtitle': 'Emergent Mathematical Structure',
            'desc': 'K(N) = N-2 formula, permutation statistics\nMahonian distribution, Coxeter geometry',
            'color': 'lightyellow',
            'properties': 'Result: Mathematical objects emerge from L\nNo axiomatic foundation needed'
        },
        {
            'y': 0.30,
            'width': 0.55,
            'name': 'Formal Axiomatic Systems',
            'subtitle': 'Traditional Mathematical Frameworks',
            'desc': 'ZFC, Peano Arithmetic, Type Theory\nSelf-referential statements (Gödel sentences)',
            'color': 'lightcoral',
            'properties': '✗ Subject to Gödel incompleteness\n✗ Unprovable truths exist\n✗ Consistency unprovable within system'
        }
    ]

    # Draw inverted pyramid structure
    box_height = 0.16

    for i, level in enumerate(levels):
        x_center = 0.5

        # Main box
        box = FancyBboxPatch(
            (x_center - level['width']/2, level['y'] - box_height/2),
            level['width'], box_height,
            boxstyle="round,pad=0.01",
            edgecolor='black',
            facecolor=level['color'],
            linewidth=3,
            transform=ax.transAxes
        )
        ax.add_patch(box)

        # Title
        ax.text(x_center, level['y'] + 0.065, level['name'],
               fontsize=14, fontweight='bold', ha='center', va='center',
               transform=ax.transAxes)

        # Subtitle
        ax.text(x_center, level['y'] + 0.045, level['subtitle'],
               fontsize=10, style='italic', ha='center', va='center',
               color='darkblue', transform=ax.transAxes)

        # Description
        ax.text(x_center, level['y'] + 0.01, level['desc'],
               fontsize=9, ha='center', va='center',
               transform=ax.transAxes, linespacing=1.6)

        # Properties
        ax.text(x_center, level['y'] - 0.04, level['properties'],
               fontsize=8, ha='center', va='center',
               style='italic', color='darkred',
               transform=ax.transAxes, linespacing=1.5)

        # Draw arrows between levels
        if i < len(levels) - 1:
            arrow = FancyArrowPatch(
                (x_center, level['y'] - box_height/2 - 0.01),
                (x_center, levels[i+1]['y'] + box_height/2 + 0.01),
                arrowstyle='-|>',
                mutation_scale=35,
                linewidth=3.5,
                color='navy',
                transform=ax.transAxes
            )
            ax.add_patch(arrow)

            # Label for arrow
            arrow_label = 'Derives' if i == 0 else 'Formalizes'
            ax.text(x_center + 0.08, (level['y'] + levels[i+1]['y'])/2,
                   arrow_label, fontsize=10, fontweight='bold',
                   style='italic', color='navy',
                   ha='left', va='center', transform=ax.transAxes)

    # Add "Escape Hatch" annotation
    escape_x = 0.12
    escape_y_top = levels[0]['y']
    escape_y_bottom = levels[2]['y']

    # Curved arrow showing escape
    escape_arrow = FancyArrowPatch(
        (escape_x, escape_y_bottom),
        (escape_x, escape_y_top),
        arrowstyle='->',
        mutation_scale=30,
        linewidth=4,
        color='green',
        linestyle='dashed',
        connectionstyle='arc3,rad=0.3',
        transform=ax.transAxes
    )
    ax.add_patch(escape_arrow)

    ax.text(escape_x - 0.08, (escape_y_top + escape_y_bottom)/2,
           'Gödel\nEscape\nHatch',
           fontsize=12, fontweight='bold', ha='center', va='center',
           color='green', rotation=90,
           bbox=dict(boxstyle='round,pad=0.6', facecolor='white',
                    edgecolor='green', linewidth=2.5),
           transform=ax.transAxes)

    # Add Gödel incompleteness annotation
    godel_box_text = (
        "Gödel's Incompleteness Theorems:\n"
        "• Any consistent formal system ≥ arithmetic has unprovable truths\n"
        "• System cannot prove its own consistency\n\n"
        "LFT Escape Mechanism:\n"
        "• Operates at meta-logical level (above formal systems)\n"
        "• No self-referential statements (no Gödel sentences)\n"
        "• Derives mathematics from logical filtering, not axioms"
    )

    ax.text(0.5, 0.04, godel_box_text,
           fontsize=9, ha='center', va='bottom',
           linespacing=1.6,
           bbox=dict(boxstyle='round,pad=1.0', facecolor='lightgray',
                    edgecolor='black', linewidth=2),
           transform=ax.transAxes)

    # Title
    ax.set_title('Gödel Escape Hatch: LFT\'s Meta-Logical Position\n' +
                'How Logic Field Theory Avoids Incompleteness',
                fontsize=15, fontweight='bold', pad=20)

    # Legend
    legend_elements = [
        mpatches.Patch(facecolor='lightgreen', edgecolor='black',
                      label='Meta-logical (immune to Gödel)'),
        mpatches.Patch(facecolor='lightyellow', edgecolor='black',
                      label='Emergent mathematics'),
        mpatches.Patch(facecolor='lightcoral', edgecolor='black',
                      label='Formal systems (Gödel-limited)')
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=9, framealpha=0.9)

    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis('off')

    plt.tight_layout()

    # Save
    plt.savefig('outputs/figure_godel_hierarchy.png', dpi=300, bbox_inches='tight')
    plt.savefig('outputs/figure_godel_hierarchy.svg', format='svg', bbox_inches='tight')
    plt.close()

    print("[OK] Generated Godel hierarchy: outputs/figure_godel_hierarchy.[png|svg]")

if __name__ == "__main__":
    generate_godel_hierarchy()
