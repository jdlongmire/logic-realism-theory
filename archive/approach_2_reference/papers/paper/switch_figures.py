#!/usr/bin/env python3
"""
Switch figure formats in paper between SVG (web) and PNG (PDF)
Usage:
  python switch_figures.py svg   # Use SVG for GitHub/web
  python switch_figures.py png   # Use PNG for PDF generation
"""

import sys
import re

def switch_format(target_format):
    """Switch all figure references to target format (svg or png)"""

    if target_format not in ['svg', 'png']:
        print(f"Error: Format must be 'svg' or 'png', got '{target_format}'")
        sys.exit(1)

    paper_file = 'Logic_Field_Theory_I_Quantum_Probability.md'

    # Read paper
    with open(paper_file, 'r', encoding='utf-8') as f:
        content = f.read()

    # Find opposite format
    old_format = 'png' if target_format == 'svg' else 'svg'

    # Replace figure extensions
    pattern = rf'(figures/outputs/figure_[^)]+)\.{old_format}'
    replacement = rf'\1.{target_format}'

    new_content = re.sub(pattern, replacement, content)

    # Count replacements
    count = len(re.findall(pattern, content))

    if count == 0:
        print(f"No changes needed - already using .{target_format} format")
        return

    # Write back
    with open(paper_file, 'w', encoding='utf-8') as f:
        f.write(new_content)

    print(f"[OK] Switched {count} figures from .{old_format} -> .{target_format}")
    print(f"  Format: {target_format.upper()}")
    print(f"  Purpose: {'GitHub/web' if target_format == 'svg' else 'PDF generation'}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(1)

    switch_format(sys.argv[1].lower())
