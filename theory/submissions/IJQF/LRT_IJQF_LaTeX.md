---
title: "Logic Realism Theory and Quantum Foundations: A Co-Constitutive Framework"
author: |
  James D. Longmire
  ORCID: 0009-0009-1383-7698
  jdlongmire@outlook.com
date: December 2025
abstract: |
  We present Logic Realism Theory (LRT), a framework in which physical reality is co-constituted by logical constraint operating on information space. The central thesis, $\mathfrak{A} = \mathfrak{L}(\mathfrak{I})$, decomposes into an empirically supported theorem ($\mathfrak{A} \subseteq \mathfrak{L}(\mathfrak{I})$: no measurement outcome violates the Three Fundamental Laws of Logic) and an open completeness conjecture ($\mathfrak{L}(\mathfrak{I}) \subseteq \mathfrak{A}$: logical constraint on information suffices for physical actualization). We show how this framework connects to quantum reconstruction programs, particularly the Masanes-Müller derivation, while avoiding the over-generation problem that afflicts Many-Worlds interpretations. The co-constitutive framing---in which neither logic nor information alone generates reality, but their interaction does---provides a principled selection criterion absent from interpretations where "all branches exist." We articulate precise falsification conditions and note that no violation of 3FLL has ever been observed in any completed physical measurement.
keywords: quantum foundations, logic realism, quantum reconstruction, information space, co-constitution, Many-Worlds, measurement problem
geometry: margin=1in
fontsize: 11pt
---

# 1. Introduction

The foundations of quantum mechanics remain contested territory. Reconstruction programs (Hardy 2001; Chiribella et al. 2011; Masanes and Müller 2011) have shown that quantum theory can be derived from operational axioms, but these programs typically do not ask what grounds the operational axioms themselves. Meanwhile, interpretations like Many-Worlds face the over-generation problem: if all branches exist, what selects the one we observe?

Logic Realism Theory (LRT) proposes a different starting point. Rather than treating logical consistency as a metalevel constraint on our theories, LRT treats the Three Fundamental Laws of Logic (3FLL) as constraints on physical reality itself. The result is a framework that:

1. Connects to quantum reconstruction via distinguishability and information
2. Provides a principled selection criterion (logical coherence) absent from Many-Worlds
3. Makes clear empirical predictions (no 3FLL violation in completed measurements)
4. Decomposes into proved and open components, avoiding overclaiming

# 2. The Formal Framework

## 2.1 The Three Fundamental Laws of Logic

The 3FLL are:

- **$L_1$ (Identity):** $\forall A: A = A$ --- States are self-identical
- **$L_2$ (Non-Contradiction):** $\forall A: \neg(A \land \neg A)$ --- No outcome is both $P$ and $\neg P$
- **$L_3$ (Excluded Middle):** $\forall A: A \lor \neg A$ --- Every outcome is $P$ or $\neg P$

These are self-grounding: any attempt to deny them presupposes what it denies. To argue "Non-Contradiction is false" requires that this assertion be true and not false.

## 2.2 Formal Definitions

Let $\mathfrak{I}$ (information space) be the set of all total truth-value assignments to a $\sigma$-algebra of propositions about physical measurement outcomes.

Let $\mathfrak{L}$ (the logic constraint operator) filter $\mathfrak{I}$:
$$\mathfrak{L}(\mathfrak{I}) := \{ s \in \mathfrak{I} \mid s \text{ satisfies } L_1, L_2, L_3 \text{ on all outcome propositions} \}$$

Let $\mathfrak{A}$ (the actualization set) be:
$$\mathfrak{A} := \{ s \in \mathfrak{I} \mid s \text{ is a physically realizable history} \}$$

## 2.3 The Central Thesis

**Theorem 1 (3FLL Constraint).** *Given that no completed measurement or physical observation violates 3FLL:*
$$\mathfrak{A} \subseteq \mathfrak{L}(\mathfrak{I})$$

*Proof sketch.* Any $s \in \mathfrak{A}$ encodes outcomes in a physically realizable history. No such outcome is both $P$ and $\neg P$ ($L_2$ violation), neither $P$ nor $\neg P$ ($L_3$ violation), or non-self-identical ($L_1$ violation). Therefore $s \in \mathfrak{L}(\mathfrak{I})$. $\square$

**Status:** Empirically supported. No violation has ever been observed.

**Conjecture 1 (Completeness).** *For any $s \in \mathfrak{L}(\mathfrak{I})$, there exists a physically realizable history:*
$$\mathfrak{L}(\mathfrak{I}) \subseteq \mathfrak{A}$$

**Status:** Open. This is the ambitious core of the research program.

If Conjecture 1 holds, then $\mathfrak{A} = \mathfrak{L}(\mathfrak{I})$: physical reality is exactly the logically constrained information space.

# 3. The Co-Constitutive Thesis

Neither $\mathfrak{L}$ nor $\mathfrak{I}$ alone constitutes physical reality:

- $\mathfrak{I}$ provides the substrate---possible information configurations
- $\mathfrak{L}$ provides the structure---filtering coherent from incoherent
- $\mathfrak{A}$ emerges from their interaction

This is not "logic generates reality" (strong idealism). It is the claim that $\mathfrak{L}$ and $\mathfrak{I}$ are *co-constitutive* of physical actualization.

## 3.1 Resolution of Over-Generation

One might worry that $\mathfrak{L}(\mathfrak{I})$ is "too large"---that physical constraints beyond 3FLL forbid certain logically coherent states. The co-constitutive framing dissolves this concern:

If physical reality IS $\mathfrak{L}(\mathfrak{I})$, there is no external standpoint from which $\mathfrak{L}(\mathfrak{I})$ could be measured as "too large." The completeness question becomes definitional rather than contingent.

# 4. Connection to Quantum Reconstruction

LRT connects to quantum reconstruction programs through the following chain:

1. **Binary distinctions** (from $L_3$): Properties partition into $P$ and $\neg P$
2. **Distinguishability metric** (from 3FLL + information space): States can be told apart
3. **Continuity** (from parsimony): Discontinuity requires extra specification
4. **Reversibility** (from parsimony): Information-preserving transformations are invertible
5. **Inner product structure** (via Masanes-Müller): The above conditions yield quantum state space

The Masanes-Müller reconstruction (2011) shows that operational axioms---tomographic locality, continuous reversibility, subspace structure, composite systems---uniquely determine quantum theory. LRT provides a framework for asking: are these axioms themselves downstream of 3FLL, or genuinely independent?

**Current status:**

- Continuity and reversibility: derived from 3FLL + parsimony
- Tomographic locality, subspace axiom: remain as Tier 2 inputs

# 5. Contrast with Many-Worlds

The Many-Worlds Interpretation (MWI) suffers from over-generation: all branches of the wave function exist, with no principled selection mechanism.

| Problem | MWI | LRT |
|---------|-----|-----|
| Over-generation | All branches exist | Only $\mathfrak{L}(\mathfrak{I})$ exists |
| Selection mechanism | None | $\mathfrak{L}$ constrains $\mathfrak{I}$ |
| Born rule | Unexplained add-on | Emerges from distinguishability |
| Ontological cost | Infinite worlds | Single co-constituted reality |

MWI generates everything consistent with unitary evolution, then struggles to recover observed physics. LRT begins with logical constraint---there is no "everything exists, then we pick."

# 6. Empirical Status

## 6.1 Falsifiability

LRT forbids:

1. A completed measurement recording $P \land \neg P$
2. A completed measurement yielding neither $P$ nor $\neg P$ (genuine gap, not mere indeterminacy)
3. A physical state failing self-identity across observation

## 6.2 Current Evidence

No violation of 3FLL has ever been observed in any completed physical measurement across all domains of physics---classical, quantum, relativistic, or cosmological. Every detector record is Boolean at the outcome level, even when the underlying formalism involves superposition.

## 6.3 Status of Non-Classical Logics

Paraconsistent and dialetheist approaches in physics have not produced distinctive, confirmed predictions differing from standard quantum theory. They remain formal options and thought experiments, not empirically established competitors to the 3FLL-constrained structure LRT codifies.

# 7. Discussion

## 7.1 Scope

LRT concerns *physical reality*---measurement outcomes and actualized states. It is agnostic about mathematical reality, the ontological status of 3FLL themselves, and domains beyond physics.

## 7.2 What LRT Claims

1. **Empirical:** No completed measurement violates 3FLL (Theorem 1---supported)
2. **Structural:** The tier system clarifies presupposition dependencies in foundational physics
3. **Conjectural:** 3FLL + information space suffice for physical actualization (Conjecture 1---open)

## 7.3 What LRT Does Not Claim

- That physics reduces to pure logic
- That all reconstruction axioms have been derived from 3FLL
- That the completeness conjecture is proven

# 8. Conclusion

Logic Realism Theory offers a framework in which physical reality is co-constituted by logical constraint operating on information space. The empirically supported component ($\mathfrak{A} \subseteq \mathfrak{L}(\mathfrak{I})$) states that no actualized outcome violates 3FLL. The open conjecture ($\mathfrak{L}(\mathfrak{I}) \subseteq \mathfrak{A}$) proposes that this constraint, together with the information space structure, suffices for physical actualization.

The co-constitutive framing provides what Many-Worlds lacks: a principled selection criterion. Rather than generating all possibilities and struggling to explain why we observe one, LRT identifies what can be actualized from the start.

The framework connects naturally to quantum reconstruction programs while maintaining clear empirical content and honest separation of proved from conjectured components. It is offered as an ambitious research program for quantum foundations, not established truth.

# References

Chiribella, G., D'Ariano, G.M. and Perinotti, P. (2011) 'Informational derivation of quantum theory', *Physical Review A*, 84(1), 012311.

Hardy, L. (2001) 'Quantum Theory From Five Reasonable Axioms', arXiv:quant-ph/0101012.

Masanes, L. and Müller, M.P. (2011) 'A derivation of quantum theory from physical requirements', *New Journal of Physics*, 13, 063001.
