#!/usr/bin/env python3
"""
Add philosophical framing to Section 1.2 (from Branch-2).
Emphasize prescriptive vs descriptive logic.
"""

with open('theory/papers/Logic-realism-theory-v3.md', 'r', encoding='utf-8') as f:
    content = f.read()

# Find insertion point (after Section 1.2 "The Proposal: Logic as Bootstrap Constraint")
# We want to add after the existing 1.2 content, before 1.3
insertion_marker = '### 1.3 Key Result: A First-Principles Prediction'
insertion_idx = content.find(insertion_marker)

if insertion_idx == -1:
    print('ERROR: Could not find Section 1.3 Scope')
    exit(1)

print(f'Found insertion point at character {insertion_idx}')

# Define new philosophical framing paragraphs (to add to end of Section 1.2)
# Based on Branch-2 lines 25-35 (prescriptive logic emphasis)
new_philosophy = '''
**Prescriptive vs Descriptive Logic**: A critical distinction underpins this work. Traditional philosophy treats logic as **descriptive**—rules that govern valid reasoning about an independent reality. LRT proposes logic is **prescriptive and ontological**—the fundamental laws (Identity, Non-Contradiction, Excluded Middle) are **operators** that actively actualize reality from information space. This is not a semantic shift but a foundational claim: logic does not merely describe "what can be"; it **enforces what is**.

This approach builds on Wheeler's (1990) information-theoretic program ("it from bit") while providing novel testable predictions. Where Wheeler proposed information as foundational, LRT specifies the mechanism: logical constraints filter infinite information space I into finite actuality A. The result is a parsimonious framework grounding physics in a single axiom $\\mathcal{A} = \\mathfrak{L}(\\mathcal{I})$ rather than QM's multiple postulates (Hilbert space, Born rule, unitary evolution, measurement collapse).

'''

# Insert new paragraphs (before Section 1.3)
content_new = content[:insertion_idx] + new_philosophy + content[insertion_idx:]

print(f'Inserted philosophical framing ({len(new_philosophy)} characters)')

# Write back
with open('theory/papers/Logic-realism-theory-v3.md', 'w', encoding='utf-8') as f:
    f.write(content_new)

print(f'File size change: {len(content_new) - len(content):+d} characters')
print('\nSUCCESS: Section 1 philosophical framing added (prescriptive logic emphasis from Branch-2)')
