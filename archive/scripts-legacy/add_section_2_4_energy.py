#!/usr/bin/env python3
"""
Add Section 2.4: Energy as Work of Instantiation (from Branch-2).
Renumber existing 2.4-2.6 to 2.5-2.7.
"""

with open('theory/papers/Logic-realism-theory-v3.md', 'r', encoding='utf-8') as f:
    content = f.read()

# Find insertion point (between Section 2.3 and current 2.4)
insertion_marker = '### 2.4 Bootstrap Function: Constraints as Enablers'
insertion_idx = content.find(insertion_marker)

if insertion_idx == -1:
    print('ERROR: Could not find Section 2.4 Bootstrap')
    exit(1)

print(f'Found insertion point at character {insertion_idx}')

# Define new Section 2.4 (Energy as Work of Instantiation from Branch-2)
new_section_2_4 = '''### 2.4 Energy as Work of Instantiation

**Intuitive foundation before technical derivation**: While Section 5.2 will provide rigorous derivations via Noether's theorem and Fisher information geometry, this section presents an accessible conceptual framework that grounds energy in the ontological operation $\\mathcal{A} = \\mathfrak{L}(\\mathcal{I})$. This framing makes the subsequent technical apparatus (constraint operators, K-thresholds, entropy reduction) more intuitive.

**Adapted from Branch-2's clear treatment, providing conceptual "why" before Section 5's mathematical "how."**

#### 2.4.1 Information Space to Actuality: A Reduction with Cost

The state of information space $\\mathcal{I}$ contains infinite, ordered potential—not chaos, but the complete set of all logically coherent possibilities. The state of actuality $\\mathcal{A}$ is a single, specific, selected and actualized configuration.

The transition from $\\mathcal{I}$ (all possibilities) to $\\mathcal{A}$ (one actuality) is a profound act of **selection and instantiation**. This act, which reduces the accessible configuration space from "infinite" to "one," has a fundamental thermodynamic cost.

**Key insight**: Information reduction requires energy dissipation.

#### 2.4.2 Landauer's Principle and the Cost of Being

**Landauer's principle** (Landauer, IBM Journal 1961): Erasing one bit of information at temperature T requires minimum energy:

$$E_{\\text{min}} = k_B T \\ln 2$$

This principle, experimentally verified (Bérut et al., Nature 2012), establishes a fundamental connection between information and energy at the physical level.

**LRT application**: The operation $\\mathfrak{L}: \\mathcal{I} \\to \\mathcal{A}$ is precisely this kind of information reduction. Filtering infinite possibilities to finite actuality is an erasure operation. Therefore:

**Energy (E) in LRT is defined as the thermodynamic work of $\\mathfrak{L}$ actualizing $\\mathcal{A}$ from $\\mathcal{I}$.**

This is not merely analogical—it is the fundamental ontological role of energy. Energy is the "cost of being." Physical systems require continuous energy input to maintain their actualized state against the backdrop of infinite possibility.

#### 2.4.3 Rest Energy and the Cost of Upholding Identity

This framework reinterprets Einstein's iconic equation $E = mc^2$ in a new light:

**Mass (m)** is a stable, persistent form of actuality—a localized configuration in $\\mathcal{A}$ that maintains coherent identity across time steps.

**Rest energy (E)** is the **continuous energetic cost** of $\\mathfrak{L}$ upholding that mass's definite, selected existence from one logical moment to the next. It is the work $\\mathfrak{L}$ must do to:
1. **Enforce Identity** ($\\mathfrak{L}_{\\text{Id}}$): m is m (persistence across time)
2. **Enforce Non-Contradiction** ($\\mathfrak{L}_{\\text{NC}}$): m is here, not simultaneously elsewhere
3. **Prevent dissolution**: Maintain the actualized configuration against "evaporation" back into mere potential (I)

The factor $c^2$ is the specific conversion rate for this work of instantiation—a coupling constant relating mass (configuration complexity) to energy (maintenance cost).

**Physical interpretation**:
- A particle at rest is not "doing nothing"—it is actively maintained in existence by $\\mathfrak{L}$
- Mass is "frozen" energy (energy locked into maintaining a persistent identity)
- E = mc² quantifies the minimum energy budget required to sustain that identity

**Connection to Section 5**: This intuitive picture will be formalized via:
- Noether's theorem: Energy conservation emerges from temporal translation symmetry (Identity constraint)
- Fisher information: Energy couples to distinguishability geometry
- Hamiltonian: Energy is the generator of time evolution (Section 5.3)

#### 2.4.4 Why Systems "Need" Energy

This framework explains why physical systems require energy input:

**Thermodynamic perspective**: Maintaining low-entropy configurations (ordered, actualized states) against the tendency toward equilibrium (return to I's possibility space) requires continuous constraint enforcement. Each constraint operation costs energy (Landauer).

**Dynamic systems**: When a system evolves (changes state in $\\mathcal{A}$), $\\mathfrak{L}$ must:
1. Release the old configuration (return constraints to I)
2. Apply new constraints (actualize new configuration)
3. Maintain identity during transition (continuous evolution)

Each step involves information processing → energy transfer.

**Decoherence example** (Section 6): Superposition states have **higher entropy** than definite states (more possibilities coexist in I). When $\\mathfrak{L}_{\\text{EM}}$ forces collapse to definite state:
- Entropy reduced: ΔS = S(superposition) - S(definite) > 0
- Energy dissipated: ΔE = k_B T ΔS (Landauer)
- This is the "cost of collapse" predicted in Section 6.7 (Landauer bounds)

#### 2.4.5 Energy vs. Other Physical Quantities

**Why start with energy?** In LRT's ontological hierarchy, energy is **primary**:

- **Space**: Geometry of relationships within actualized configurations (derivative from constraint structure)
- **Time**: Ordering of sequential applications of $\\mathfrak{L}_{\\text{Id}}$ (emergent from persistence requirement)
- **Mass**: Persistent energy configuration (E = mc²)
- **Force**: Rate of energy transfer (derivative: F = dE/dx)
- **Momentum**: Conserved quantity from spatial translation symmetry (Noether's theorem, assumes energy conservation)

Energy is the "currency" of constraint operations—the fundamental resource required for $\\mathcal{A} = \\mathfrak{L}(\\mathcal{I})$ to operate.

#### 2.4.6 Pedagogical Bridge to Technical Formalism

**Why this section helps**: Students and reviewers often struggle with LRT's constraint operator formalism (Section 4) because it seems abstract. Grounding it in "energy as work of instantiation" provides:

1. **Physical intuition**: Energy is not mysterious—it's the cost of maintaining actuality
2. **Thermodynamic connection**: Landauer principle bridges information theory and physics
3. **Ontological clarity**: Physical quantities emerge from logical operations, not vice versa

**What comes next**:
- Section 3: Hierarchical emergence (how mathematics emerges from proto-primitives)
- Section 4: Constraint operator algebra (mathematical formalization of $\\mathfrak{L}$)
- Section 5: Quantum mechanics derivation (energy as Hamiltonian, time evolution, Born rule)
- Section 6: Empirical predictions (T2/T1, Landauer bounds)

This section provides the conceptual foundation that makes the subsequent technical apparatus intuitive rather than arbitrary.

**Rigorous vs. intuitive**: Section 5.2 will derive energy rigorously via Noether's theorem (time translation symmetry → energy conservation) and entropy reduction formalism (Spohn's inequality). This section is the accessible prelude, not a substitute for rigor.

'''

# Insert new section
content_new = content[:insertion_idx] + new_section_2_4 + '\n' + content[insertion_idx:]

print(f'Inserted Section 2.4: Energy as Work of Instantiation ({len(new_section_2_4)} characters)')

# Renumber existing sections: 2.4 → 2.5, 2.5 → 2.6, 2.6 → 2.7
content_new = content_new.replace('### 2.4 Bootstrap Function: Constraints as Enablers', '### 2.5 Bootstrap Function: Constraints as Enablers')
content_new = content_new.replace('### 2.5 Mind-Independence and Ontological Status', '### 2.6 Mind-Independence and Ontological Status')
content_new = content_new.replace('### 2.6 Necessity, Contingency, and the Physical Laws', '### 2.7 Necessity, Contingency, and the Physical Laws')

print('Renumbered sections: 2.4→2.5, 2.5→2.6, 2.6→2.7')

# Write back
with open('theory/papers/Logic-realism-theory-v3.md', 'w', encoding='utf-8') as f:
    f.write(content_new)

print(f'File size change: {len(content_new) - len(content):+d} characters')
print('\\nSUCCESS: Section 2.4 added (Energy as Work of Instantiation from Branch-2)')
