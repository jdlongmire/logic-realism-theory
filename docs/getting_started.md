# Getting Started with Logic Realism Theory

**Status**: Stub (to be developed)

## Quick Installation

```bash
# Clone repository
git clone https://github.com/jdlongmire/logic-realism-theory
cd logic-realism-theory

# Install Python dependencies
pip install -r notebooks/requirements.txt

# Initialize Lean project (if working with formal proofs)
cd lean
lake update
lake build
```

## First Steps

1. **Read the foundational paper**: `theory/Logic-realism-theory-foundational.md` (30,000 words, publication-ready)
2. **Review Lean formalization**: See `lean/LogicRealismTheory/Foundation/IIS.lean` (2 axioms, 3FLL proven, 0 sorry)
3. **Explore notebooks**: Start with `notebooks/01_IIS_and_3FLL.ipynb` (in development)

## For Researchers Coming from Approach 2

If you're familiar with the Physical Logic Framework (Approach 2):
- See `approach_2_reference/` for complete archive
- LRT is a clean rewrite with 98.6% fewer axioms (140 → 2)
- 3FLL proven from Lean's logic (not axiomatized)
- Notebooks are focused on core derivations only

## Next Steps

(Documentation to be expanded in future sessions)
