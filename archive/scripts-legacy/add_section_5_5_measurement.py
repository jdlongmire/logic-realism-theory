#!/usr/bin/env python3
"""
Add Section 5.5: Intuitive Picture of Measurement (from Branch-2).
Renumber existing 5.5-5.7 to 5.6-5.8.
"""

with open('theory/papers/Logic-realism-theory-v3.md', 'r', encoding='utf-8') as f:
    content = f.read()

# Find insertion point (between Section 5.4 and current 5.5)
insertion_marker = '### 5.5 Comparison: LRT Derives What QM Postulates'
insertion_idx = content.find(insertion_marker)

if insertion_idx == -1:
    print('ERROR: Could not find Section 5.5 Comparison')
    exit(1)

print(f'Found insertion point at character {insertion_idx}')

# Define new Section 5.5 (Intuitive Measurement Picture from Branch-2)
new_section_5_5 = '''### 5.5 Intuitive Picture: Measurement as I → A Transition

Before diving into the technical comparison (Section 5.6), we present an intuitive understanding of measurement that makes the formal K-threshold machinery (Section 5.4) accessible to a broader audience. This framing, while informal, captures the essence of LRT's solution to the quantum measurement problem.

**This section is adapted from Branch-2's exceptionally clear treatment, providing the "why" before the "how."**

#### 5.5.1 The Wave Function is Information Space

**Core insight**: The wave function ψ describing a superposition is not a physical object "out there" in spacetime. It is the **representation of information space I** for that system—the ordered set of logical possibilities.

When we write:

$$|\\psi\\rangle = \\frac{1}{\\sqrt{2}}(|\\uparrow\\rangle + |\\downarrow\\rangle)$$

we are describing **both outcomes exist in I** (the possibility space), not that the particle is "spinning both ways" in physical space A.

**Why this matters**: Much of the mystery in quantum mechanics stems from treating ψ as a physical field oscillating in spacetime. In LRT, ψ lives in information space I, which has fundamentally different properties.

#### 5.5.2 Information Space is Non-Spatial

**Key distinction**: The concept of "distance" is a property of actualized reality (A), not information space (I).

When two particles are entangled in the state:

$$|\\psi\\rangle = \\frac{1}{\\sqrt{2}}(|\\uparrow_A \\downarrow_B\\rangle - |\\downarrow_A \\uparrow_B\\rangle)$$

they are **components of a single configuration in I**, not separate objects with "distance between them." The question "how far apart are they in I?" is meaningless—I has no spatial geometry. Space emerges when L actualizes configurations into A.

**Physical analogy**: Think of I as a library catalog. Two books listed together in a catalog entry don't have "distance between them" in the catalog system—distance only exists when the physical books are placed on shelves (actualized into A).

#### 5.5.3 Measurement is the Interface I → A

**What is measurement?** In LRT, measurement is any interaction that forces an I-state system to become part of the wider, existing actuality (A). It is the **forced interface between potential and actuality**.

Before measurement:
- System exists in I (superposition state ψ)
- Multiple outcomes coexist as possibilities
- No definite configuration in A

During measurement:
- Measurement apparatus (already in A) interacts with system
- Interaction adds constraints (Section 5.4: K increases)
- L must resolve I → A (select one outcome)

After measurement:
- System is now part of A (definite state)
- Wave function collapse has occurred
- Only one outcome actualizes

**Why collapse happens**: Because I and A have different ontological status. I contains multiple possibilities; A contains one actuality. When the system joins A, multiplicity cannot persist.

#### 5.5.4 Collapse is Non-Contradiction Applied

**The mechanism**: "Collapse" is the prescriptive force of **L (specifically, Non-Contradiction)** resolving the I-state.

For the system to be actual (join A), it **cannot be "spin up AND spin down."** Non-Contradiction ($\\mathfrak{L}_{\\text{NC}}$) forbids contradictory configurations in A. It must be "spin up OR spin down."

When L selects one coherent outcome (e.g., spin up), this is a **single act of logical selection** from I to A, not a physical process happening "in" spacetime.

**Mathematical connection to Section 5.4**: This intuitive picture corresponds exactly to the K-transition framework:
- Superposition in I: High-K state (many possibilities)
- Measurement interaction: K increases (apparatus constraints)
- Collapse to definite: K decreases to eigenstate (single possibility)
- Non-Contradiction enforces: Only one outcome can actualize

The Born rule probabilities ($p_i = |c_i|^2$, derived in Section 5.1) emerge from maximum entropy principle—L selects outcomes according to the information-theoretic content of each possibility.

#### 5.5.5 Entanglement: No "Spooky Action"

**The EPR "paradox" dissolved**: When two entangled particles are measured and found anticorrelated (e.g., A spin up → B spin down), no faster-than-light signal is sent between them.

**Why?** Particles A and B were never separate objects in I. They are **two components of a single, non-local configuration** in information space:

$$|\\psi\\rangle = \\frac{1}{\\sqrt{2}}(|\\uparrow_A \\downarrow_B\\rangle - |\\downarrow_A \\uparrow_B\\rangle)$$

When measurement forces this configuration into A, **L selects the entire configuration in one logical instant**. Particle B "knows" its state because it was always part of the same I-configuration as particle A—they were never separate in the relevant ontological sense (information space).

**Analogy**: Imagine a library entry: "Book A on Shelf 1, Book B on Shelf 2." When this entry is actualized (books placed on shelves), both books appear simultaneously in their designated locations. No signal travels from Shelf 1 to Shelf 2—the entire configuration was actualized at once. The "correlation" was built into the I-configuration, not created by physical interaction in A.

**Connection to K-threshold**: The entangled state has constraints binding A and B together (conservation laws, total angular momentum). When measurement adds further constraints (K-transition), both particles must satisfy the joint constraint structure. This is why they appear correlated—not because of signals, but because they were always components of one constrained configuration.

#### 5.5.6 Why This Picture Helps

This intuitive framing makes several features of quantum mechanics natural:

1. **Wave-particle duality**: ψ is not "wave" vs "particle"—it's I-representation vs A-manifestation. Different observables (position, momentum) correspond to different constraint structures in I.

2. **Complementarity**: You can't measure position and momentum simultaneously because they impose incompatible constraint structures (different K-configurations). Heisenberg uncertainty emerges from I's geometry (Section 5.2).

3. **Quantum tunneling**: A particle can "tunnel through" a barrier because in I, the trajectory doesn't exist—only boundary conditions exist. When L actualizes the outcome, paths through classically forbidden regions are not forbidden in I.

4. **No-cloning theorem**: You can't duplicate a quantum state because copying requires measuring it (extracting information from I), which collapses it (forces I → A). Information in I cannot be "read" without actualization.

**Pedagogical value**: Students often struggle with quantum mechanics because they try to picture wavefunctions as physical objects in spacetime. The I/A distinction short-circuits this confusion: ψ lives in information space (possibility), measurements extract outcomes into actuality.

**Technical foundation**: Everything in this section has rigorous formalization in Sections 4-5. This intuitive picture is not "hand-waving"—it's the conceptual content of the mathematical framework, presented accessibly before technical details.

'''

# Insert new section
content_new = content[:insertion_idx] + new_section_5_5 + '\n' + content[insertion_idx:]

print(f'Inserted Section 5.5: Intuitive Measurement Picture ({len(new_section_5_5)} characters)')

# Renumber existing sections: 5.5 → 5.6, 5.6 → 5.7, 5.7 → 5.8
content_new = content_new.replace('### 5.5 Comparison: LRT Derives What QM Postulates', '### 5.6 Comparison: LRT Derives What QM Postulates')
content_new = content_new.replace('### 5.6 Quantum Phenomena Explained', '### 5.7 Quantum Phenomena Explained')
content_new = content_new.replace('### 5.7 Summary: Quantum Mechanics is Logical Mechanics', '### 5.8 Summary: Quantum Mechanics is Logical Mechanics')

print('Renumbered sections: 5.5→5.6, 5.6→5.7, 5.7→5.8')

# Write back
with open('theory/papers/Logic-realism-theory-v3.md', 'w', encoding='utf-8') as f:
    f.write(content_new)

print(f'File size change: {len(content_new) - len(content):+d} characters')
print('\\nSUCCESS: Section 5.5 added (Intuitive Measurement Picture from Branch-2)')
