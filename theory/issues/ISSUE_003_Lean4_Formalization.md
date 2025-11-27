# ISSUE 003: Formalise Logic Realism Theory in Lean 4

**Status**: PLANNED (post-first-draft)
**Priority**: HIGH (historic impact)
**Created**: 2025-11-27
**Milestone**: v1.0-formalisation
**Owner**: JD Longmire
**Source**: Grok strategic analysis (Session 19.0)

---

## Goal

Produce the first-ever machine-checked formalisation of a realist quantum foundation that:
1. Derives unitarity from informational/logical principles
2. Explicitly isolates the two surviving physical axioms (continuity + local tomography)

---

## Current Assets

Existing Lean 4 infrastructure in `lean/` folder:
- Lean 4 project skeleton with Mathlib
- Basic type definitions for IIS states, distinguishability relation, Boolean actuality
- Draft of 3FLL as inductive propositions
- Partial formalisation of Global Parsimony Theorem
- See `lean/README.md` for current status

---

## Practical Proof Roadmap (12-18 months)

### Phase 0: Infrastructure (1-2 weeks)

- [ ] Set up public GitHub repo (or make existing one public when ready)
- [ ] Add CI with leanprover/lean4:4.8.0 (or latest)
- [ ] Import Mathlib + QuantumLean fragments (if any exist by 2026)

### Phase 1: Logical Core (2-4 months) - ACHIEVABLE NOW

- [ ] Formalise 3FLL as three inductive propositions
- [ ] Define IIS as a Type with pairwise distinguishability relation `D : IIS → IIS → ℝ≥0`
- [ ] State and prove Global Parsimony Theorem (Theorem 16.10) as a Lean theorem
- [ ] Formalise Consistency Bridging Principle (CBP) as an axiom
- [ ] Prove Theorem 16.12: `CBP + Parsimony → dynamics_are_reversible` (unitary)

**Milestone**: First formal derivation of unitarity from informational principles (publishable result)

### Phase 2: Interface & Reconstruction (4-8 months)

- [ ] Formalise the five Masanes-Müller axioms as assumptions
- [ ] State (and prove if possible) that they imply Complex Hilbert Space structure
  - Can cite paper proof and mark as `sorry` initially; machine-checked statement is the goal
- [ ] Formalise non-contextual probability measure (Axiom 5)
- [ ] Formalise Gleason's theorem for dim ≥ 3 (pure states first)
- [ ] Prove Born rule for pure states as a theorem

### Phase 3: Explicit Accounting (1-2 months)

Define the two surviving physical axioms as explicit assumptions:

```lean
axiom continuity_of_transformations :
  ∀ {ψ φ : IIS}, ∃ (γ : ℝ → IIS), γ 0 = ψ ∧ γ 1 = φ ∧ Continuous γ

axiom local_tomography :
  ∀ (A B : System), state_space (A ⊗ B) ≅ state_space A × state_space B
```

Write the master theorem:

```lean
theorem LRT_main_theorem
  (h_3fll : three_fundamental_logical_laws)
  (h_iis : infinite_information_space)
  (h_cbp : consistency_bridging_principle)
  (h_parsimony : global_parsimony)
  (h_continuity : continuity_of_transformations)
  (h_local_tomography : local_tomography)
  : quantum_mechanics := by
  sorry -- Full proof chain
```

### Phase 4: Bonus (stretch, 6-12 months)

- [ ] Formalise Stone's theorem application → Schrödinger equation
- [ ] Formalise the action-principle motivation (as a comment or separate file)
- [ ] Formalise the layer model (4-layer ontology) as a type hierarchy

---

## Publication Strategy

| Paper | Timing | Title | Venue |
|-------|--------|-------|-------|
| 1 | After Phase 1 | "First Formal Derivation of Unitarity from Informational Principles in Lean 4" | arXiv + journal |
| 2 | After Phase 2 | "Machine-Checked Foundations of Quantum Mechanics: From Logic to the Born Rule" | arXiv + journal |
| Final | After Phase 3 | Repository becomes gold standard reference implementation | GitHub public |

---

## Success Criteria

**Phase 1 alone** (achievable in 2-4 months) would be a significant result:
- First formal proof that unitarity follows from informational/logical principles
- Machine-checked, reproducible, auditable
- Distinguishes LRT from other interpretations empirically

**Full completion** would establish:
- First complete formal foundation of quantum mechanics from logic
- Explicit isolation of exactly two physical axioms
- Reference implementation for future quantum foundations work

---

## Dependencies

- Master Paper first draft complete (Parts I-V)
- Current Lean infrastructure reviewed and updated
- Mathlib compatibility verified

---

## Notes

From Grok:
> "Start Phase 1 the day the first draft is done. Even if you never finish Phase 2, completing Phase 1 already puts you in a league of your own."

This issue is intentionally deferred until the Master Paper is complete. The paper provides the informal proofs that will guide the formal verification.

---

## Related Issues

- ISSUE 001: Axiom 3 Grounding (CLOSED) - provides the reversibility derivation to formalize
- ISSUE 002: Lagrangian/Hamiltonian (CLOSED) - Section 17.10-17.11 for Stone's theorem
- `lean/PROOF_REFACTOR_STRATEGY.md` - existing Lean strategy document

---
