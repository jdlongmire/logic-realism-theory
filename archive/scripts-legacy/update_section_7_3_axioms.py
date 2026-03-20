#!/usr/bin/env python3
"""
Update Section 7.3 to reference lean/AXIOMS.md and the axiom transparency approach.
"""

with open('theory/papers/Logic-realism-theory-v3.md', 'r', encoding='utf-8') as f:
    content = f.read()

# Find Section 7.3
section_start = '### 7.3 Axiom Status: No LRT-Specific Axioms'
section_end = '### 7.4 Key Verified Results'

start_idx = content.find(section_start)
end_idx = content.find(section_end)

if start_idx == -1 or end_idx == -1:
    print('ERROR: Could not find Section 7.3 boundaries')
    exit(1)

# Extract current section (for verification)
old_section = content[start_idx:end_idx]
print(f'Found Section 7.3: {len(old_section)} characters')

# Define new Section 7.3 with axiom transparency approach
new_section = '''### 7.3 Axiom Transparency and Documentation

**Comprehensive axiom documentation**: All axioms used in the Lean formalization are documented in `lean/AXIOMS.md` with full justification, and each Lean file declares its axiom count in the header (e.g., "**Axiom Count**: 1 (energy additivity)").

**Axiom categories**:

1. **Foundational postulates** (3 axioms):
   - Information space I exists
   - Information space I is infinite
   - Actualization function L: I → A is well-defined

   *Status*: Theory-defining assumptions (analogous to QM's Hilbert space postulate)

2. **Established mathematical results** (axiomatized for practicality):
   - Stone's theorem (unitary groups ↔ self-adjoint generators)
   - Jaynes Maximum Entropy Principle
   - Spohn's inequality (entropy change bounds)

   *Status*: Well-known results whose full proofs would require extensive Mathlib infrastructure without adding physical insight

3. **Physical postulates** (1 axiom):
   - Energy additivity for independent systems (E_total = E₁ + E₂)

   *Status*: Fundamental physical principle (analogous to entropy extensivity, cannot be proven from mathematical structure alone)

**Total axiom count**: ~7 axioms across the formalization

**Critical distinction**: We claim "**no novel LRT-specific axioms**" in the sense that:
- Foundational postulates define what LRT *is* (like QM's postulates)
- Established results are standard in physics/mathematics literature
- Physical postulates are domain-standard (energy additivity used universally)

**What we do NOT axiomatize**:
- The 3 Fundamental Laws of Logic (proven from Lean's `Classical.em`)
- Born rule (derived from MaxEnt + Non-Contradiction, Section 5.1)
- Hilbert space structure (emergent from information geometry, Section 5.2)
- Time evolution (derived from Identity constraint, Section 5.3)

**Transparency approach**:

Every Lean file includes a header documenting:
```lean
**Axiom Count**: X (description)
**AXIOM INVENTORY**: For complete axiom documentation, see: lean/AXIOMS.md
This module uses X axioms:
- [List specific axioms used]
```

This ensures reviewers can immediately identify what is assumed versus what is proven in each module. Full justification and references are provided in `lean/AXIOMS.md`.

**Peer review response** (Section 9.1): The claim "LRT derives QM" is accurate in the sense that we derive the Born rule, Hilbert space structure, and time evolution from logical constraints plus well-established principles (MaxEnt, Stone's theorem). We do not introduce *novel* physical postulates beyond the core ontological claim $\\mathcal{A} = \\mathfrak{L}(\\mathcal{I})$ and standard domain assumptions (energy additivity).

**Comparison to quantum mechanics axiomatization**:

| Framework | Axiom Count | Nature |
|-----------|-------------|--------|
| **QM (Dirac)** | 4-5 | Hilbert space, operators, Born rule, unitary evolution, measurement collapse |
| **LRT (this work)** | 7 | Foundational (3) + established results (3) + physical (1) |

**Key difference**: QM *postulates* Born rule and Hilbert space. LRT *derives* them from MaxEnt + logical constraints. Our axioms are more foundational (ontological level) rather than phenomenological (QM's observable-focused postulates).

'''

# Replace section
content_new = content[:start_idx] + new_section + content[end_idx:]

print(f'Replaced Section 7.3: {len(new_section)} characters')

# Write back
with open('theory/papers/Logic-realism-theory-v3.md', 'w', encoding='utf-8') as f:
    f.write(content_new)

print(f'File size change: {len(content_new) - len(content):+d} characters')
print('\\nSUCCESS: Section 7.3 updated with axiom transparency approach')
