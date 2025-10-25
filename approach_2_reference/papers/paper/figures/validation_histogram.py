#!/usr/bin/env python3
"""
Generate validation histogram showing |V_K| decay across N=3-10
Visualizes the exponential decay of feasibility ratio ρ_N
"""

import matplotlib.pyplot as plt
import pandas as pd
import numpy as np

def generate_validation_histogram():
    """Generate histogram of validation data showing exponential decay"""

    # Load data
    df = pd.read_csv('data/validation_data.csv')

    # Create figure with two subplots
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

    # Subplot 1: |V_K| vs N (log scale)
    ax1.bar(df['N'], df['V_K'], color='skyblue', edgecolor='navy', alpha=0.8)
    ax1.set_xlabel('N (System Size)', fontsize=12, fontweight='bold')
    ax1.set_ylabel('|V_K| (Valid States)', fontsize=12, fontweight='bold')
    ax1.set_title('Valid State Space Size: |V_{N-2}|', fontsize=14, fontweight='bold')
    ax1.set_yscale('log')
    ax1.grid(alpha=0.3, axis='y')
    ax1.set_xticks(df['N'])

    # Add data labels
    for _, row in df.iterrows():
        ax1.text(row['N'], row['V_K'], f"{row['V_K']:,}",
                ha='center', va='bottom', fontsize=8)

    # Subplot 2: Feasibility ratio ρ_N (percentage)
    ax2.bar(df['N'], df['rho_percent'], color='coral', edgecolor='darkred', alpha=0.8)
    ax2.set_xlabel('N (System Size)', fontsize=12, fontweight='bold')
    ax2.set_ylabel('ρ_N = |V_K|/N! (%)', fontsize=12, fontweight='bold')
    ax2.set_title('Feasibility Ratio: Exponential Decay', fontsize=14, fontweight='bold')
    ax2.grid(alpha=0.3, axis='y')
    ax2.set_xticks(df['N'])

    # Fit exponential decay: ρ_N ≈ A * exp(-B*N)
    from scipy.optimize import curve_fit
    def exp_decay(x, a, b):
        return a * np.exp(-b * x)

    popt, _ = curve_fit(exp_decay, df['N'], df['rho_percent'])
    N_fit = np.linspace(3, 10, 100)
    ax2.plot(N_fit, exp_decay(N_fit, *popt), 'r--', linewidth=2,
            label=f'Fit: {popt[0]:.2f}·exp(-{popt[1]:.2f}N)')
    ax2.legend(fontsize=10)

    # Add data labels
    for _, row in df.iterrows():
        ax2.text(row['N'], row['rho_percent'], f"{row['rho_percent']:.2f}%",
                ha='center', va='bottom', fontsize=8)

    plt.tight_layout()

    # Save
    plt.savefig('outputs/figure_validation_data.png', dpi=300, bbox_inches='tight')
    plt.savefig('outputs/figure_validation_data.svg', format='svg', bbox_inches='tight')
    plt.close()

    print("[OK] Generated validation histogram: outputs/figure_validation_data.[png|svg]")

if __name__ == "__main__":
    generate_validation_histogram()
