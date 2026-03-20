# Permutohedron Visualization Figure - Specifications

**Purpose**: Illustrate the geometric structure of valid permutation state space V_K
**Target**: Paper figure showing N=3 and N=4 permutohedra with V_K highlighted
**Date**: October 5, 2025 (Week 2 Day 3)

---

## Figure Overview

### Figure Composition

**Two panels side-by-side**:

**Panel A**: N=3 Permutohedron (Hexagon)
- All 6 permutations of S_3
- Valid state space V_1 highlighted (3 states with h≤1)
- Edges showing adjacent transpositions

**Panel B**: N=4 Permutohedron (Truncated Octahedron)
- Select projection of 24 permutations of S_4
- Valid state space V_2 highlighted (9 states with h≤2)
- Cayley graph structure visible

---

## Panel A: N=3 Permutohedron (Detailed Specs)

### Geometric Structure

**Shape**: Regular hexagon (2D projection of permutohedron)

**Vertices** (6 total):
1. (1,2,3) - identity, h=0 [CENTER TOP]
2. (1,3,2) - h=1 [RIGHT]
3. (2,1,3) - h=1 [LEFT]
4. (2,3,1) - h=2 [BOTTOM LEFT]
5. (3,1,2) - h=2 [BOTTOM RIGHT]
6. (3,2,1) - h=3 [CENTER BOTTOM]

**Edges** (9 total):
- (123)-(132): s_2 transposition
- (123)-(213): s_1 transposition
- (132)-(312): s_1 transposition
- (213)-(231): s_2 transposition
- (132)-(321): s_2 transposition
- (213)-(312): s_2 transposition
- (231)-(321): s_1 transposition
- (312)-(321): s_2 transposition
- Self-edges: none (simple graph)

**Valid State Space V_1** (h ≤ 1):
- ✅ (1,2,3): h=0
- ✅ (1,3,2): h=1
- ✅ (2,1,3): h=1
- ❌ (2,3,1): h=2 [excluded]
- ❌ (3,1,2): h=2 [excluded]
- ❌ (3,2,1): h=3 [excluded]

### Visual Encoding

**Vertex Colors**:
- **Green (valid)**: (123), (132), (213) - bold, filled
- **Gray (invalid)**: (231), (312), (321) - faded, hollow

**Edge Colors**:
- **Blue (within V_1)**: Edges between valid states (2 edges)
- **Light gray**: Edges involving invalid states

**Labels**:
- **Permutation**: e.g., "(1,2,3)"
- **Inversion count**: e.g., "h=0"
- **Both** displayed at each vertex

**Annotations**:
- Title: "N=3 Permutohedron"
- Subtitle: "V_1 = {σ : h(σ) ≤ 1} (3 valid states)"
- Legend: "Green = Valid (h≤1), Gray = Excluded (h>1)"

### Layout Coordinates (2D projection)

**Hexagon vertices** (centered at origin):
```
(123): (0, 1)      [top]
(132): (0.866, 0.5)    [upper right]
(213): (-0.866, 0.5)   [upper left]
(231): (-0.866, -0.5)  [lower left]
(312): (0.866, -0.5)   [lower right]
(321): (0, -1)     [bottom]
```

**Scaling**: Radius = 2 units for visibility

---

## Panel B: N=4 Permutohedron (Simplified)

### Geometric Structure

**Shape**: Truncated octahedron (3D, show 2D projection or Schlegel diagram)

**Vertices** (24 total, S_4):
- Too many for full visualization
- **Show subset**: Valid states V_2 + boundary

**Valid State Space V_2** (h ≤ 2):
- |V_2| = 9 states (Mahonian number M(4,0) + M(4,1) + M(4,2))
- Examples:
  - h=0: (1,2,3,4)
  - h=1: (1,2,4,3), (1,3,2,4), (2,1,3,4)
  - h=2: (1,3,4,2), (1,4,2,3), (2,1,4,3), (2,3,1,4), (3,1,2,4)

**Edges**: Cayley graph (adjacent transpositions)

### Visual Encoding

**Vertex Colors** (same as Panel A):
- **Green**: h ≤ 2 (valid)
- **Gray**: h > 2 (excluded)

**Projection**:
- Use Schlegel diagram (project 3D polytope onto 2D)
- OR: Layered view (h=0 top, h=1 middle, h=2 bottom)

**Annotations**:
- Title: "N=4 Permutohedron"
- Subtitle: "V_2 = {σ : h(σ) ≤ 2} (9 valid states)"
- Note: "Showing valid states only (full S_4 has 24 vertices)"

---

## Figure Caption

**Proposed Caption**:

> **Figure [X]: Permutohedron Geometry and Valid State Spaces.** **(A)** The N=3 permutohedron is a hexagon representing all 6 permutations of S_3. Vertices are colored by inversion count h(σ): green indicates valid states (h ≤ K=1), gray indicates excluded states (h > 1). Valid state space V_1 contains 3 states forming a triangle. Edges represent adjacent transpositions (Cayley graph). **(B)** The N=4 permutohedron is a truncated octahedron with 24 vertices (full S_4). Only the 9 valid states V_2 (h ≤ 2) are highlighted. The constraint threshold K(N) = N-2 determines which permutations are logically accessible. The permutohedron structure embeds quantum state space geometrically, with the graph Laplacian H = D - A serving as the natural Hamiltonian on this discrete manifold.

---

## Technical Implementation

### Option 1: Python (NetworkX + Matplotlib)

```python
import networkx as nx
import matplotlib.pyplot as plt
import numpy as np

# N=3 example
perms_N3 = [(1,2,3), (1,3,2), (2,1,3), (2,3,1), (3,1,2), (3,2,1)]
h_values = [0, 1, 1, 2, 2, 3]
valid_N3 = [i for i, h in enumerate(h_values) if h <= 1]

# Create graph
G = nx.Graph()
G.add_nodes_from(range(6))

# Add edges (adjacent transpositions)
edges = [(0,1), (0,2), (1,5), (2,3), (1,4), (2,4), (3,5), (4,5), (3,4)]
G.add_edges_from(edges)

# Layout (hexagon)
pos = {
    0: (0, 1),
    1: (0.866, 0.5),
    2: (-0.866, 0.5),
    3: (-0.866, -0.5),
    4: (0.866, -0.5),
    5: (0, -1)
}

# Colors
colors = ['green' if i in valid_N3 else 'lightgray' for i in range(6)]

# Draw
nx.draw(G, pos, node_color=colors, with_labels=True, node_size=800)
plt.savefig('permutohedron_N3.png', dpi=300)
```

### Option 2: TikZ/LaTeX

```latex
\begin{tikzpicture}
  % Vertices
  \node[circle, fill=green!50, draw] (123) at (0,3) {$(1,2,3)$ \\ $h=0$};
  \node[circle, fill=green!50, draw] (132) at (2.6,1.5) {$(1,3,2)$ \\ $h=1$};
  \node[circle, fill=green!50, draw] (213) at (-2.6,1.5) {$(2,1,3)$ \\ $h=1$};
  \node[circle, fill=gray!30, draw] (231) at (-2.6,-1.5) {$(2,3,1)$ \\ $h=2$};
  \node[circle, fill=gray!30, draw] (312) at (2.6,-1.5) {$(3,1,2)$ \\ $h=2$};
  \node[circle, fill=gray!30, draw] (321) at (0,-3) {$(3,2,1)$ \\ $h=3$};

  % Edges
  \draw[blue, thick] (123) -- (132);
  \draw[blue, thick] (123) -- (213);
  \draw[gray] (132) -- (312);
  \draw[gray] (213) -- (231);
  % ... etc
\end{tikzpicture}
```

### Option 3: Manual (Inkscape/Illustrator)

- Create hexagon shape
- Place permutation labels
- Color vertices (green/gray)
- Draw edges
- Add annotations
- Export as PNG/SVG

---

## Detailed Vertex Data

### N=3 Complete Data

| Vertex | Permutation | h | Valid? | Position | Color |
|--------|-------------|---|--------|----------|-------|
| 0 | (1,2,3) | 0 | ✅ | (0, 1) | Green |
| 1 | (1,3,2) | 1 | ✅ | (0.866, 0.5) | Green |
| 2 | (2,1,3) | 1 | ✅ | (-0.866, 0.5) | Green |
| 3 | (2,3,1) | 2 | ❌ | (-0.866, -0.5) | Gray |
| 4 | (3,1,2) | 2 | ❌ | (0.866, -0.5) | Gray |
| 5 | (3,2,1) | 3 | ❌ | (0, -1) | Gray |

### N=3 Edge Data (Adjacent Transpositions)

| Edge | From | To | Transposition | Within V_1? |
|------|------|----|--------------| ------------|
| e1 | (123) | (132) | s_2 = (2,3) | ✅ Blue |
| e2 | (123) | (213) | s_1 = (1,2) | ✅ Blue |
| e3 | (132) | (321) | s_2 = (2,3) | ❌ Gray |
| e4 | (132) | (312) | s_1 = (1,2) | ❌ Gray |
| e5 | (213) | (231) | s_2 = (2,3) | ❌ Gray |
| e6 | (213) | (312) | s_2 = (2,3) | ❌ Gray |
| e7 | (231) | (321) | s_1 = (1,2) | ❌ Gray |
| e8 | (312) | (321) | s_2 = (2,3) | ❌ Gray |
| e9 | (231) | (312) | s_1 = (1,2) | ❌ Gray |

**Total edges**: 9
**Edges within V_1**: 2 (blue)
**Edges outside V_1**: 7 (gray)

### N=4 Valid States (V_2, h≤2)

| # | Permutation | h | Notes |
|---|-------------|---|-------|
| 1 | (1,2,3,4) | 0 | Identity |
| 2 | (1,2,4,3) | 1 | One inversion |
| 3 | (1,3,2,4) | 1 | |
| 4 | (2,1,3,4) | 1 | |
| 5 | (1,3,4,2) | 2 | Two inversions |
| 6 | (1,4,2,3) | 2 | |
| 7 | (2,1,4,3) | 2 | |
| 8 | (2,3,1,4) | 2 | |
| 9 | (3,1,2,4) | 2 | |

**Total valid states**: 9
**Total S_4 states**: 24
**Fraction**: 9/24 = 37.5%

---

## Figure Dimensions & Format

### Size
- **Width**: 7 inches (two-column format) OR 3.5 inches each panel
- **Height**: 3.5 inches
- **Resolution**: 300 DPI (publication quality)

### Format
- **Primary**: PNG (for paper)
- **Source**: Python script OR TikZ code (for reproducibility)
- **Alternative**: SVG (vector, scalable)

### File Naming
- `permutohedron_N3.png` (Panel A)
- `permutohedron_N4.png` (Panel B)
- `permutohedron_combined.png` (Both panels)

---

## Implementation Priority

### Phase 1 (Immediate - Day 3):
1. ✅ Specifications document (this file)
2. Create N=3 visualization (simple, clear)
3. Draft figure caption

### Phase 2 (Day 4):
1. Create N=4 visualization (may need simplification)
2. Combine into two-panel figure
3. Finalize caption and annotations

### Phase 3 (Day 5):
1. Integrate figure into paper
2. Cross-reference from text
3. Ensure consistency with paper narrative

---

## Code Template (Python)

```python
#!/usr/bin/env python3
"""
Generate permutohedron visualization for N=3 and N=4.
"""

import networkx as nx
import matplotlib.pyplot as plt
import numpy as np
from itertools import permutations

def inversion_count(perm):
    """Count inversions in permutation tuple."""
    count = 0
    for i in range(len(perm)):
        for j in range(i+1, len(perm)):
            if perm[i] > perm[j]:
                count += 1
    return count

def build_cayley_graph(N, K):
    """Build Cayley graph for S_N with constraint K."""
    perms = list(permutations(range(1, N+1)))
    h_vals = [inversion_count(p) for p in perms]

    G = nx.Graph()
    for i, p in enumerate(perms):
        G.add_node(i, perm=p, h=h_vals[i], valid=(h_vals[i] <= K))

    # Add edges (adjacent transpositions)
    for i, p1 in enumerate(perms):
        for j, p2 in enumerate(perms[i+1:], start=i+1):
            if is_adjacent_transposition(p1, p2):
                G.add_edge(i, j)

    return G, perms, h_vals

def is_adjacent_transposition(p1, p2):
    """Check if p1 and p2 differ by one adjacent swap."""
    diffs = [i for i in range(len(p1)) if p1[i] != p2[i]]
    if len(diffs) != 2:
        return False
    i, j = diffs
    return abs(i-j) == 1 and p1[i] == p2[j] and p1[j] == p2[i]

# Generate N=3 figure
G, perms, h_vals = build_cayley_graph(3, 1)

# Hexagon layout
pos = {
    0: (0, 1),
    1: (0.866, 0.5),
    2: (-0.866, 0.5),
    3: (-0.866, -0.5),
    4: (0.866, -0.5),
    5: (0, -1)
}

# Colors
node_colors = ['green' if G.nodes[i]['valid'] else 'lightgray'
               for i in G.nodes()]
edge_colors = ['blue' if G.nodes[u]['valid'] and G.nodes[v]['valid']
               else 'lightgray' for u,v in G.edges()]

# Draw
plt.figure(figsize=(6,6))
nx.draw(G, pos, node_color=node_colors, edge_color=edge_colors,
        with_labels=False, node_size=1000, width=2)

# Add labels
for i in G.nodes():
    perm_str = ''.join(map(str, perms[i]))
    label = f"{perm_str}\nh={h_vals[i]}"
    plt.text(pos[i][0], pos[i][1], label, ha='center', va='center',
             fontsize=10, weight='bold')

plt.title("N=3 Permutohedron\nV_1 = {σ : h(σ) ≤ 1} (3 valid states)",
          fontsize=14)
plt.axis('off')
plt.tight_layout()
plt.savefig('permutohedron_N3.png', dpi=300, bbox_inches='tight')
print("Saved: permutohedron_N3.png")
```

---

## Status

**Specifications**: ✅ Complete
**N=3 code template**: ✅ Ready
**N=4 approach**: ✅ Defined (layered or Schlegel)

**Next**: Generate actual figures using Python script

---

**Figure specifications complete** ✅
**Ready for implementation** ✅
