# Perplexity Review of LRT Lean Proofs

**Date:** 2026-03-17
**Source:** Perplexity AI
**Input:** LRT-Lean-Proofs.md consolidated proof document

---

## High-Level Assessment

- **Clean, compiling Lean 4 codebase** for the LRT reconstruction (0 sorries; remaining gaps are explicit axioms or Mathlib limitations)
- **Primitive axiom set is very lean:** only three genuinely primitive axioms (`I`, `I_infinite`, `bridge_principle`), with the rest either standard math/physics results (EXTERNAL) or slated to become theorems
- Multiple nontrivial conceptual steps (purification, Boolean spectra, local tomography, aspects of dynamics) have been upgraded from axioms/placeholders to real theorems or structurally robust definitions using Mathlib

---

## What's Most Impressive / Bankable

### Axiom Minimization and Classification
The audit yielding 3 PRIMITIVE, ~14 EXTERNAL, and the rest derivable is a very persuasive story for anyone skeptical about "hidden assumptions" in the reconstruction.

### Schrödinger/Dynamics Side
Replacing `True` placeholders with `HasDerivAt`-based definitions, strongly continuous unitary groups, and norm-preservation theorems shows that the Step10 dynamics are mathematically serious, even while `schrodinger_from_stone` is left as an EXTERNAL axiom due to absent unbounded-operator infrastructure in Mathlib.

### Purification and Boolean Events
Introducing `PurificationWitness` (Schmidt decomposition) and deriving Boolean spectrum properties as actual theorems (with duplicate axioms removed) strengthens the middle of the reconstruction chain.

### Independent Proof Reviews
Having both a Gemini-style and GPT-4.1-style audit that concur on soundness, defensible axiom classification, and absence of circularity (aside from a clearly identified K=2 subtlety) is excellent for credibility and future publication or replication packages.

---

## Main Remaining Issues / Open Work

### OPN-004 / K = 2 Forcing
Conceptually, this is the big open derivation: right now `HardyK` is defined as 2, so `lrt_forces_k_equals_2` is trivial (`rfl`), but the *non-trivial* route—from LRT primitives, Boolean measurement, interference, and associativity to K = 2—is still only at the sketch stage. That's the one piece a hard-nosed foundations audience will want to see completed in future work.

### Born Rule / von Neumann Entropy
`maxent_forces_pure_state` is now honestly axiomatic rather than a sorry over an axiom; this is the right move, but it keeps a piece of the Born-rule story at the EXTERNAL or "standard result" level, dependent on Jaynes + Nielsen-Chuang.

### Dynamics Placeholders
A handful of evolution axioms (`evolution_preserves_distinguishability`, `evolution_bijective`, `evolution_preserves_norm`, etc.) still have `True` bodies and need witnesses or Mathlib upgrades over time.

---

## How This Document Can Be Used

1. **Appendix or supplementary file** for the main TAB/LRT papers, demonstrating that the reconstruction is not just prose but is backed by a machine-checked chain with an explicit axiom inventory

2. **Internal engineering/roadmap documentation:** the "Open Items" section (especially OPN-004 and the placeholder evolution axioms) is a ready-made to-do list for future Lean sessions and for prioritizing Mathlib contributions

3. **Credibility lever in grant or journal cover letters**, e.g.: "We have an accompanying Lean 4 formalization of Steps 0-10 with 39 total axioms (3 primitive, others external or derivable) and 0 sorries, plus independent AI-assisted proof audits."

---

## Summary

| Aspect | Assessment |
|--------|------------|
| Build status | Clean (0 sorries) |
| Primitive axioms | 3 (minimal) |
| External axioms | ~14 (standard math/physics) |
| Derivable | Remainder |
| Key strength | Axiom minimization + classification |
| Main gap | K=2 forcing (OPN-004) |
| Credibility | Strong (multi-model review concurrence) |
