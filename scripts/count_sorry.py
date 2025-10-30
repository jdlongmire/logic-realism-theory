#!/usr/bin/env python3
"""
Count actual sorry statements in Lean files (not in comments or strings).
"""

import re
import sys
from pathlib import Path

def count_sorry_in_file(filepath):
    """Count sorry statements, excluding comments."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    # Remove single-line comments (-- ...)
    content = re.sub(r'--[^\n]*', '', content)

    # Remove multi-line comments (/-  ... -/)
    content = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)

    # Count 'sorry' as standalone word (not in identifiers like "sorry_count")
    sorry_matches = re.findall(r'\bsorry\b', content)

    return len(sorry_matches)

def main():
    lean_dir = Path('lean/LogicRealismTheory')

    total = 0
    files_with_sorry = []

    for lean_file in sorted(lean_dir.rglob('*.lean')):
        count = count_sorry_in_file(lean_file)
        if count > 0:
            rel_path = lean_file.relative_to(lean_dir)
            files_with_sorry.append((str(rel_path), count))
            total += count

    print(f"Total sorry statements: {total}\n")

    if files_with_sorry:
        print("Breakdown by file:")
        for filepath, count in files_with_sorry:
            print(f"  {filepath}: {count} sorry")
    else:
        print("No sorry statements found!")

if __name__ == '__main__':
    main()
