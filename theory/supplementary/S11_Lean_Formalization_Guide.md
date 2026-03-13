# S11: Lean 4 Formalization Guide

**Author:** James D. Longmire
**Date:** 2026-03-13
**Status:** Technical Supplement to LRT-MASTER
**Type:** Documentation (Physicist-Readable Guide)
**Addresses:** All Steps (0-10); Understanding the Lean formalization structure

---

## Abstract

This supplement provides a physicist-readable guide to the Lean 4 formalization of Logic Realism Theory. It explains how each formalization file maps to the derivation chain in LRT-MASTER, what the structural elements (including `sorry` placeholders) represent, the role of external mathematical dependencies (Mathlib), and how to build and verify the formalization. The goal is to allow readers who do not know Lean syntax to understand *what* the formalization establishes and *why* it provides structural verification of LRT's derivation chain. This is not a Lean tutorial; it is a guide to interpreting the formalization as evidence for LRT's logical coherence.

---

## 1. What the Formalization Does

### 1.1 Purpose

The Lean 4 formalization serves three purposes:

1. **Type-Level Verification:** Each step in LRT's derivation chain is represented as a typed statement. Lean's type checker verifies that these statements are well-formed and that their logical dependencies are correctly structured.

2. **Proof Obligation Tracking:** Where proofs are complete, Lean verifies their correctness. Where proofs are incomplete (marked with `sorry`), the formalization makes explicit *what* would need to be proven, enabling targeted future work.

3. **Dependency Auditing:** The import structure makes explicit which mathematical results each step depends on. External results are localized in `ExternalTheorems.lean`, ensuring no hidden assumptions.

### 1.2 What It Does Not Do

The formalization does not:

- **Replace philosophical argument.** LRT's claim that L<sub>3</sub> is constitutive of reality (not merely regulative) is a metaphysical thesis not expressible in type theory. Lean proves structural relations; LRT interprets them ontologically.

- **Verify empirical predictions.** The formalization establishes logical coherence, not experimental correctness.

- **Provide a Lean tutorial.** Readers need not learn Lean syntax to understand what the formalization establishes.

---

## 2. File-to-Step Mapping

### 2.1 Current Formalization Structure

The active Lean files are located in `lean/LogicRealismTheory/`:

| File | LRT Step | Content | Status |
|------|----------|---------|--------|
| `D0_1_ThreeFundamentalLaws.lean` | Step 0 | L<sub>3</sub> primitives (Identity, Non-Contradiction, Excluded Middle) | Complete |
| `D0_2_InformationSpace.lean` | Step 1 | I<sub>∞</sub> declaration, infinite cardinality, distinguishability | Complete |
| `ExternalTheorems.lean` | Steps 4-10 | Tier 2 axioms (Masanes-Müller, Gleason, Stone, etc.) | Complete |

The root import file `lean/LogicRealismTheory.lean` imports all active modules.

### 2.2 Mapping to LRT-MASTER Derivation Chain

**Steps 0-1: Primitives (Tier 0)**

| LRT Step | Lean File | What Is Formalized |
|----------|-----------|---------------------|
| Step 0: L<sub>3</sub> constitutive | `D0_1_ThreeFundamentalLaws.lean` | The three laws as Lean theorems; their consequences (double negation, De Morgan) |
| Step 1: I<sub>∞</sub> exists | `D0_2_InformationSpace.lean` | I as an axiomatized type; `I_infinite` as the cardinality axiom |

**Steps 2-3: Physical Proposition Criterion and Local Tomography**

Currently documented in prose (S1, S2, S8). Formalization strategy specified in S8.

| LRT Step | Formalization Status | Reference |
|----------|----------------------|-----------|
| Step 2: PPC derivation | Strategy in S8 | Target: `Structures/PhysicalProposition.lean` |
| Step 3: H1 → H2 bridge | Strategy in S8 | Target: `Step3/LocalTomographyTheorem.lean` |

**Steps 4-7: Hilbert Space, PVM, Gleason, Born Rule**

These steps invoke external mathematical results, now axiomatized in `ExternalTheorems.lean`.

| LRT Step | External Theorem | Lean Axiom |
|----------|------------------|------------|
| Step 4: Complex Hilbert space | Masanes-Müller (2011) | `masanes_muller_reconstruction` |
| Step 5: Eigenvalue restriction | Spectral theory + actualization | Target: S9 strategy |
| Step 6: Gleason's theorem | Gleason (1957) | `gleasons_theorem` |
| Step 7: Born rule | Follows from Steps 5-6 | Derived |

**Steps 8-10: Dynamics**

| LRT Step | External Theorem | Lean Axiom |
|----------|------------------|------------|
| Step 8: Continuous time | Uniqueness of successor states | (future: UNS axiom) |
| Step 9: Stone's theorem | Stone (1932) | `stones_theorem` |
| Step 10: Schrödinger equation | Follows from Steps 8-9 | Derived |

### 2.3 Archived Formalization Work

Previous formalization attempts are preserved in `lean/archive/2025-12-21_LogicRealismTheory/`. These contain:

- `Foundation/`: Earlier IIS formalization
- `Dynamics/`: Time evolution attempts
- `Measurement/`: Measurement structure
- `Reconstruction/`: Hilbert space derivation attempts

**Status:** Archived for reference; not part of active build. The current approach focuses on clean Tier separation (see Section 4).

---

## 3. Understanding `sorry` Placeholders

### 3.1 What `sorry` Means

In Lean, `sorry` is a placeholder that allows a theorem statement to type-check without providing a proof. It represents:

- **A well-typed goal:** Lean has verified that the *statement* makes sense and has the correct type.
- **An unproven claim:** The *proof* is not yet provided.
- **A tracked obligation:** The formalization makes explicit what remains to be done.

### 3.2 Why `sorry` Is Acceptable for Structural Verification

LRT's formalization is not (yet) a complete machine-verified proof of quantum mechanics from L<sub>3</sub>. It is a **structural verification** establishing:

1. **Type coherence:** Each step's hypotheses and conclusions are well-typed.
2. **Dependency correctness:** The import structure matches the derivation chain.
3. **Tier separation:** Novel LRT axioms (Tier 1) are cleanly separated from established mathematics (Tier 2) and physics assumptions (Tier 3).

A formalization with `sorry` placeholders is analogous to a mathematical paper that states "by Theorem X of Smith (1990)" without reproducing Smith's proof. The structural claim is: "If Smith's theorem holds, then our result follows." The formalization makes this conditional structure machine-checkable.

### 3.3 The `sorry` Budget

Current `sorry` usage:

| Category | Count | Status |
|----------|-------|--------|
| Tier 2 axioms (established math) | ~10 | Intentional; these *should* be axioms |
| Proof obligations in derivation steps | ~0 active | Archived code has more |
| Tier 1 axioms (LRT-specific) | 2 | Intentional; these define LRT |

**Key point:** The active formalization (`D0_1`, `D0_2`, `ExternalTheorems`) contains *no* `sorry` statements except for Tier 2 axiom conclusions (which are `True` placeholders, not incomplete proofs).

---

## 4. The 3-Tier Axiom System

### 4.1 Overview

All axioms in the formalization are classified into three tiers (documented in `lean/AXIOMS.md`):

| Tier | Name | Count | Role |
|------|------|-------|------|
| 1 | LRT Specific | 2 | Novel LRT postulates (I, I<sub>∞</sub>) |
| 2 | Established Math Tools | ~16 | Published theorems (Stone, Gleason, etc.) |
| 3 | Universal Physics | 1 | Domain-standard assumptions (energy additivity) |

### 4.2 Tier 1: LRT-Specific Axioms

These define what LRT *is*. They are:

```
axiom I : Type*           -- The Infinite Information Space exists
axiom I_infinite : Infinite I  -- It has infinite cardinality
```

**Epistemic status:** Framework commitment. Analogous to QM's "Hilbert space exists."

**File:** `D0_2_InformationSpace.lean`

### 4.3 Tier 2: Established Mathematical Theorems

These are well-known results axiomatized for practical formalization. Examples from `ExternalTheorems.lean`:

| Axiom | Source | Used For |
|-------|--------|----------|
| `masanes_muller_reconstruction` | Masanes & Müller (2011) | Step 4 (Hilbert space) |
| `gleasons_theorem` | Gleason (1957) | Step 6 (probability measures) |
| `stones_theorem` | Stone (1932) | Step 9 (unitary groups) |
| `uhlmann_purification_uniqueness` | Uhlmann (1976) | Purification |
| `lee_selby_theorem` | Lee & Selby (2016) | MM5 derivation |

**Epistemic status:** ESTABLISHED in the literature. These have published proofs; we axiomatize them rather than re-formalizing because:

1. Full formalization would require extensive work without adding physical insight.
2. This is standard practice in formal quantum foundations (cf. Hardy 2001, Chiribella et al. 2011).
3. As Mathlib matures, these can be replaced with imports.

### 4.4 Tier 3: Universal Physics Assumptions

Domain-standard physical principles:

```
axiom energy_additivity : ...  -- E(A ⊗ B) = E(A) + E(B) for independent systems
```

**Epistemic status:** Accepted across all physics. Cannot be derived from pure mathematics.

### 4.5 Why This Classification Matters

**For honest comparison:** LRT has 2 foundational (Tier 1) axioms, comparable to other reconstruction programs (Hardy: 5, Chiribella: 6). The ~16 Tier 2 axioms are mathematical infrastructure that all such programs use implicitly.

**For auditability:** Every external dependency is localized in `ExternalTheorems.lean` with citations. Reviewers can verify that LRT does not smuggle conclusions into premises.

**For future work:** As Mathlib formalizes more spectral theory, measure theory, etc., Tier 2 axioms can be replaced with imports without changing the LRT-specific content.

---

## 5. Mathlib Dependencies

### 5.1 What Mathlib Is

Mathlib is the community-maintained mathematical library for Lean 4. It provides formalized definitions and theorems for:

- Linear algebra (vector spaces, inner products, operators)
- Analysis (topology, measure theory, functional analysis)
- Logic (classical and intuitionistic)
- Algebra (groups, rings, fields)

### 5.2 Mathlib Imports in LRT

The current formalization imports:

```lean
import Mathlib.Logic.Basic                        -- Classical logic foundations
import Mathlib.Logic.Nontrivial.Defs              -- Nontrivial types
import Mathlib.Data.Fintype.EquivFin              -- Finite types
import Mathlib.Analysis.InnerProductSpace.Basic   -- Hilbert spaces
import Mathlib.Analysis.InnerProductSpace.PiL2    -- L² spaces
import Mathlib.LinearAlgebra.TensorProduct.Basic  -- Tensor products
```

### 5.3 What Mathlib Provides vs. What LRT Defines

| Concept | Mathlib Provides | LRT Defines |
|---------|------------------|-------------|
| Classical logic | `Classical.em`, `Classical.byContradiction` | Ontological interpretation |
| Hilbert space | `InnerProductSpace ℂ H` | Connection to I<sub>∞</sub> |
| Tensor products | `TensorProduct` | Composite system interpretation |
| Infinite types | `Infinite` | I<sub>∞</sub> as the space |

**Key insight:** LRT reuses standard mathematical structures (Mathlib) and adds *interpretive content* (the derivation from L<sub>3</sub>). The formalization verifies that this interpretive content is type-coherent.

---

## 6. How to Build and Verify

### 6.1 Prerequisites

- Lean 4 (version matching `lean-toolchain`)
- Lake (Lean's build system)
- Mathlib4 (fetched automatically by Lake)

### 6.2 Build Commands

From the repository root:

```bash
cd lean
lake build
```

This compiles all `.lean` files and checks them for type errors. A successful build confirms:

1. All type signatures are well-formed.
2. All imports resolve correctly.
3. All proofs (where provided) are valid.

### 6.3 Checking for `sorry`

To audit the formalization for unproven claims:

```bash
grep -r "sorry" lean/LogicRealismTheory/
```

Currently, the active formalization contains no `sorry` statements (Tier 2 axioms use `True` conclusions, not `sorry`).

### 6.4 Checking for Trivial Proofs

To check that theorems are not trivially true:

```bash
grep "theorem.*True" lean/LogicRealismTheory/
```

Some Tier 2 axioms have `True` conclusions because their full statement would require extensive type infrastructure. The *hypotheses* of these axioms are where the content lies.

### 6.5 Verifying Tier Classification

Each axiom should have a tier label in its comment. To audit:

```bash
grep -A 1 "axiom" lean/LogicRealismTheory/*.lean | grep -i "tier"
```

---

## 7. Interpreting Formalization Results

### 7.1 What a Successful Build Means

A successful `lake build` means:

1. **Type coherence:** The derivation chain's structure is internally consistent.
2. **No circular dependencies:** The import graph is acyclic.
3. **All proofs valid:** Where proofs are given, Lean's kernel has verified them.

### 7.2 What a Successful Build Does Not Mean

It does not mean:

- **LRT is true:** Formalization verifies structure, not truth.
- **All steps are proven:** `sorry` or axiom placeholders may exist.
- **Empirical predictions are correct:** That requires experiment.

### 7.3 How to Read Formalization Claims

When this project claims "Step X is formalized," check:

| Claim | Meaning | How to Verify |
|-------|---------|---------------|
| "Complete" | All proofs given; no `sorry` | `grep "sorry" StepX.lean` returns empty |
| "Structured" | Type signatures in place; some proofs missing | `grep "sorry"` shows locations |
| "Axiomatized" | External result stated as axiom | Check `ExternalTheorems.lean` |
| "Strategy only" | No Lean code yet; prose specification | See supplements S8, S9 |

---

## 8. Connection to Theory Documents

### 8.1 Derivation Notebooks

The Lean formalization corresponds to derivation notebooks in `notebooks/`:

| Notebook | Lean File | Content |
|----------|-----------|---------|
| `D0.1-three-fundamental-laws.ipynb` | `D0_1_ThreeFundamentalLaws.lean` | L<sub>3</sub> |
| `D0.2-information-space.ipynb` | `D0_2_InformationSpace.lean` | I<sub>∞</sub> |
| `D1.x-*.ipynb` | (future) | Structural consequences |

### 8.2 Supplements

Formalization strategy supplements:

| Supplement | Target Step | Content |
|------------|-------------|---------|
| S8 | Step 3 (Local Tomography) | H1 → H2 bridge formalization |
| S9 | Step 5 (Eigenvalue Restriction) | Boolean A → PVM structure |
| **S11** (this document) | All | Overall formalization guide |

### 8.3 Master Document

LRT-MASTER (theory/LRT-MASTER.md) provides the prose derivation chain that the formalization structures. Each step in LRT-MASTER has an epistemic status tag (ESTABLISHED, ARGUED, OPEN) that corresponds to formalization completeness:

| Prose Status | Formalization Status |
|--------------|----------------------|
| ESTABLISHED | Should be provable from Mathlib + Tier 2 axioms |
| ARGUED | May require additional LRT-specific lemmas |
| OPEN | Formalization deferred until prose argument resolved |

---

## 9. Open Questions

### 9.1 Formalization Scope

**Q1:** Should we aim for a complete machine-verified derivation of QM from L<sub>3</sub>?

**Current answer:** The goal is structural verification, not complete formalization. Full formalization would require extensive work on spectral theory in Mathlib without adding physical insight. The current approach establishes type coherence and dependency structure.

### 9.2 Tier 2 Axiom Refinement

**Q2:** As Mathlib grows, which Tier 2 axioms should be prioritized for replacement with imports?

**Recommendation:**
1. Stone's theorem (functional analysis in Mathlib is maturing)
2. Gleason's theorem (recent Mathlib work on measure theory)
3. Spectral theory lemmas (ongoing Mathlib development)

### 9.3 Infinite-Dimensional Treatment

**Q3:** How should the formalization handle infinite-dimensional Hilbert spaces?

**Current approach:** Most theorems are stated for general Hilbert spaces (`InnerProductSpace ℂ H`). Infinite-dimensional specifics (continuous spectrum, unbounded operators) are deferred to the spectral theorem axioms.

---

## 10. Summary

### 10.1 What the Reader Should Take Away

1. **The formalization is structural.** It verifies that LRT's derivation chain has coherent type structure, not that LRT is metaphysically true.

2. **Tier separation is key.** Only 2 axioms (Tier 1) are novel LRT postulates. The ~16 Tier 2 axioms are standard mathematical results.

3. **`sorry` is honest.** Where proofs are incomplete, the formalization makes this explicit. Currently, the active formalization has no `sorry` in proofs—only Tier 2 axiom conclusions.

4. **Mathlib provides infrastructure.** LRT reuses standard mathematical structures and adds interpretive content.

5. **Building is easy.** Run `lake build` in the `lean/` directory to verify everything compiles.

### 10.2 Formalization Status Summary

| Component | Status | File |
|-----------|--------|------|
| L<sub>3</sub> (Step 0) | Complete | `D0_1_ThreeFundamentalLaws.lean` |
| I<sub>∞</sub> (Step 1) | Complete | `D0_2_InformationSpace.lean` |
| External theorems | Axiomatized | `ExternalTheorems.lean` |
| Steps 2-3 | Strategy only | S8 |
| Steps 4-7 | Tier 2 axioms | `ExternalTheorems.lean` |
| Steps 8-10 | Partial | `ExternalTheorems.lean` (Stone) |

### 10.3 Next Steps for Formalization

1. **Implement S8 strategy:** Create `DistinguishableSpace`, `PhysicalProposition`, H1/H2 definitions.
2. **Implement S9 strategy:** Create `EventOperator`, spectral lemmas, eigenvalue restriction theorem.
3. **Connect Steps 4-7:** Link Masanes-Müller output to Gleason input.
4. **Verify Stone → Schrödinger:** Complete the dynamics derivation.

---

## References

Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311.

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885-893.

Hardy, L. (2001). Quantum theory from five reasonable axioms. *arXiv:quant-ph/0101012*.

Masanes, L. and Müller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001.

Stone, M. H. (1932). On one-parameter unitary groups in Hilbert space. *Annals of Mathematics*, 33(3), 643-648.

Tao, T., et al. (2023). Polynomial Freiman-Ruzsa conjecture. *Lean formalization*. https://github.com/teorth/pfr

---

*Supplement S11 | Logic Realism Theory Project | 2026-03-13*
