#!/usr/bin/env python3
"""
Generate Logical Operator Breakdown diagram
Shows sequential application: L = EM ∘ NC ∘ ID
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

def generate_logical_operator_diagram():
    """Generate flowchart showing L = EM ∘ NC ∘ ID composition"""

    fig, ax = plt.subplots(figsize=(14, 10))

    # Define positions for stages (vertical flow)
    stages = [
        {
            'y': 0.85,
            'name': 'Information Space I',
            'desc': 'All directed graphs on N elements\n(N! × 2^(N(N-1)/2) configurations)',
            'color': 'lightgray',
            'example': 'Includes: self-loops, cycles, partial orderings'
        },
        {
            'y': 0.65,
            'name': 'ID(I): Identity Filter',
            'desc': 'Axiom: a = a (eliminate self-loops)\nRemoves self-referential edges',
            'color': 'lightblue',
            'example': 'Result: Simple directed graphs'
        },
        {
            'y': 0.45,
            'name': 'NC(ID(I)): Non-Contradiction',
            'desc': 'Axiom: ¬(P ∧ ¬P) (eliminate cycles)\nRemoves circular orderings',
            'color': 'lightgreen',
            'example': 'Result: DAGs (directed acyclic graphs)'
        },
        {
            'y': 0.25,
            'name': 'EM(NC(ID(I))): Excluded Middle',
            'desc': 'Axiom: P ∨ ¬P (complete all pairs)\nRequires total ordering',
            'color': 'lightyellow',
            'example': 'Result: Linear orderings = Permutations'
        },
        {
            'y': 0.05,
            'name': 'Physical Space A = L(I)',
            'desc': 'N! permutations (symmetric group S_N)\nGeometric: (N-1)-dimensional permutohedron',
            'color': 'lightcoral',
            'example': 'Dynamics: L-Flow on this manifold'
        }
    ]

    # Draw boxes for each stage
    box_width = 0.85
    box_height = 0.12

    for i, stage in enumerate(stages):
        # Main box
        x_center = 0.5
        box = FancyBboxPatch(
            (x_center - box_width/2, stage['y'] - box_height/2),
            box_width, box_height,
            boxstyle="round,pad=0.01",
            edgecolor='black',
            facecolor=stage['color'],
            linewidth=2.5,
            transform=ax.transAxes
        )
        ax.add_patch(box)

        # Title
        ax.text(x_center, stage['y'] + 0.04, stage['name'],
               fontsize=13, fontweight='bold', ha='center', va='center',
               transform=ax.transAxes)

        # Description
        ax.text(x_center, stage['y'], stage['desc'],
               fontsize=10, ha='center', va='center',
               transform=ax.transAxes, linespacing=1.5)

        # Example/Result
        ax.text(x_center, stage['y'] - 0.04, stage['example'],
               fontsize=9, ha='center', va='center', style='italic',
               color='darkred', transform=ax.transAxes)

        # Draw arrows between stages (except for last stage)
        if i < len(stages) - 1:
            arrow = FancyArrowPatch(
                (x_center, stage['y'] - box_height/2 - 0.01),
                (x_center, stages[i+1]['y'] + box_height/2 + 0.01),
                arrowstyle='-|>',
                mutation_scale=30,
                linewidth=3,
                color='navy',
                transform=ax.transAxes
            )
            ax.add_patch(arrow)

    # Add side annotation showing composition
    annotation_x = 0.92
    ax.text(annotation_x, 0.55, 'L = EM ∘ NC ∘ ID',
           fontsize=16, fontweight='bold', ha='center', va='center',
           rotation=270, transform=ax.transAxes,
           bbox=dict(boxstyle='round,pad=0.8', facecolor='white',
                    edgecolor='black', linewidth=2))

    # Add legend explaining operator composition
    legend_elements = [
        mpatches.Patch(facecolor='lightgray', edgecolor='black', label='Unrestricted space'),
        mpatches.Patch(facecolor='lightblue', edgecolor='black', label='After Identity'),
        mpatches.Patch(facecolor='lightgreen', edgecolor='black', label='After Non-Contradiction'),
        mpatches.Patch(facecolor='lightyellow', edgecolor='black', label='After Excluded Middle'),
        mpatches.Patch(facecolor='lightcoral', edgecolor='black', label='Physical manifold')
    ]
    ax.legend(handles=legend_elements, loc='upper left', fontsize=9, framealpha=0.9)

    # Title
    ax.set_title('Logical Operator Breakdown: L = EM ∘ NC ∘ ID\n' +
                'Sequential Filtering from Information Space to Physical Space',
                fontsize=15, fontweight='bold', pad=20)

    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis('off')

    plt.tight_layout()

    # Save
    plt.savefig('outputs/figure_logical_operator.png', dpi=300, bbox_inches='tight')
    plt.savefig('outputs/figure_logical_operator.svg', format='svg', bbox_inches='tight')
    plt.close()

    print("[OK] Generated Logical Operator diagram: outputs/figure_logical_operator.[png|svg]")

if __name__ == "__main__":
    generate_logical_operator_diagram()
