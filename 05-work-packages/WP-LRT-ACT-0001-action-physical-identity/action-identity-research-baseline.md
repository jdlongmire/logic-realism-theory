# Fundamental Action and Physical Identity: baseline and discrimination tests

Status: RESEARCH / CANDIDATE PRINCIPLES, NOT CANONICAL THEOREMS
Date: 2026-11-08
Work package: WP-LRT-ACT-0001

## Research question

If two physically admissible configurations differ, must that difference have consequences for possible Action? And, if so, must those consequences be measurable, globally or locally?

LRT primitives are `χ=[L3:I∞:A]`. 3FLL are ontologically prior to mathematical representation. A is the fundamental ontological operation making transitions possible; it is **not** defined as a state function. This document uses mathematical traces of Action only as explicitly provisional representations.

## Four inequivalent notions of identity

1. **Logical identity:** `x=y`, equality in the representation. Logical nonidentity `x≠y` does not entail a particular empirical test.
2. **Ontic identity:** whether two representations refer to the same actual physical configuration. A quotient by representational redundancy may be required.
3. **Action-profile equivalence:** configurations have matching possibilities of licensed transitions and their compositions, relative to a specified class of interactions and outcome labels.
4. **Operational equivalence:** all permitted observations produce identical records/statistics; define separately for global and subsystem-local operations.

These are not interchangeable. A mathematical difference can be a gauge redundancy; an ontic difference can be operationally inaccessible under restricted tests.

## Candidate principles

Let C be an admissible configuration set, `T` a specified class of licensed tests or action protocols, and `o_t(x)` the observable outcome distribution (if probabilities are justified) or outcome-set (without probabilities) for protocol t applied to x. This notation represents a proposed operational manifestation of A, not A itself.

**AI-0 (Action relevance):** for any distinct *ontic* configurations x,y, some admissible action context differs in its possible transition consequences. This is a proposed metaphysical individuation law; no proof from 3FLL alone.

**AI-1 (Global operational separation):** `x≠_ont y ⇒ ∃t∈T_global, o_t(x)≠o_t(y)`. Stronger than AI-0: action differences must be convertible to records. It requires an independently justified bridge from transition possibility to measurement.

**AI-2 (Local operational separation):** for composite x,y, `x≠_ont y ⇒ ∃t∈T_local-product, o_t(x)≠o_t(y)`. This closely resembles local tomography and **must not be assumed** in a purported derivation of local tomography.

**AI-3 (Compositional discrimination):** an admissible interaction can turn every ontic distinction into a persistent, readable record in some auxiliary system. Even AI-3 does not establish AI-2 when global coupling is allowed; see the pointer-isometry counterexample in WP-LRT-ONTO-0001.

**Provisional status:** AI-0 through AI-3 are conjectural principles, not entailed results. They form a hierarchy only after specifying the protocol classes and the bridge between possible transitions and records. AI-2 implies AI-1 if local tests are a subset of global tests. AI-1 does not imply AI-2.

## Separating countermodels

### Model A: different states, identical Action profiles

Let C={p,q}. Define a directed licensed-action graph with only identity loops at p and q. Treat state names as distinct ontic labels and compare action profiles up to relabeling. Their structural possibilities are isomorphic, although p≠q. Classical identity, noncontradiction and excluded middle hold, and an action-enabling relation exists. Therefore 3FLL plus the bare existence of licensed Actions does not imply AI-0.

**Important qualification:** identity actions in the mathematical calculus need not correspond to actual physical events. If a proposed ontology prohibits this model, it must supply an independent reason why a nontrivial transition or an individuating Action is necessary. A second model with p↔q transitions and symmetric labels also has indistinguishable unlabeled action profiles.

### Model B: globally distinguishable yet locally indistinguishable

In real two-rebit quantum theory, let `J=[[0,-1],[1,0]]`, `K=J⊗J`, and `ρ±=(I₄±tK)/4` for 0<t≤1. These are distinct physical states, separable by a global effect, while every real-symmetric product effect has identical statistics on the pair. Real-quantum processes compose sequentially and in parallel, so the existing M0/M1 action calculus does not force AI-2. This is an explicit model of global separation without local tomography, **not** a refutation of the still-unformalized primitive A.

### Model C: mathematical nonidentity without ontic difference

Take two labels `(s,0)` and `(s,1)` that denote the same physical state s under a stipulated gauge equivalence. Their syntactic inequality does not establish distinct ontology or distinguishability. Any proposed AI principle must quantify over ontic equivalence classes, or it risks treating redundant mathematical coordinates as reality.

## Candidate derivation chain and gaps

`3FLL + I∞ + A`
→ [**OPEN**: characterize ontic individuation]
`AI-0`
→ [**OPEN**: action-to-record bridge]
`AI-1`
→ [**NOT VALID WITHOUT MORE PREMISES**: global-to-local reduction]
`AI-2 / local tomography`
→ [**EXTERNAL RECONSTRUCTION PREMISES STILL REQUIRED**] complex Hilbert-space reconstruction.

The logical laws constrain consistency of each candidate; they do not independently supply the missing arrows.

## First formal proof obligations

- **PO-1 (type discipline):** define ontic equivalence, Action-context equivalence and observational equivalence without presupposing complex amplitudes, probabilities or time.
- **PO-2 (AI-0 independence):** formally construct symmetric action graphs and prove distinct nodes can have identical unlabeled Action profiles.
- **PO-3 (separation bridge):** propose a noncircular rule by which a difference in licensed transitions yields a stable record.
- **PO-4 (locality bridge):** derive or independently justify a decomposition theorem for records of composite configurations. Test against the rebit `J⊗J` direction.
- **PO-5 (gauge invariance):** show the principles are invariant under representational renaming and ontic equivalence.
- **PO-6 (Lean):** after approval of precise definitions, build a parallel research namespace with explicit axioms and theorem dependency audits; do not replace Step0 or Step1 by fiat.

## Falsification and decisions

AI-0 fails in any accepted LRT model with two genuinely distinct ontic configurations but identical Action possibilities. AI-1 fails if such differences are Action-relevant but no permitted global record can separate them. AI-2 fails in a model that meets all independently justified LRT premises yet retains globally distinguishable, locally indistinguishable composites. The real-rebit example currently refutes AI-2 as a consequence of M0/M1 alone.

**Owner decision required before promotion:** Does ontic distinctness *constitutively require* Action-relevant differences (AI-0), or should that be a theorem derived from a more basic account of individuation? Choosing the former adds a substantive constraint, not a deduction from 3FLL.

## Traceability and validation

Inputs: `WP-LRT-ONTO-0001/action-ontological-operation-research-semantics.md`, `logic-priority-mathematics-dependency-protocol.md`, `minimal-action-composition-calculus.md`, and `ca3-global-interaction-local-record-counterexample.md`.

Confidence: HIGH for elementary logical countermodels conditional on stated definitions; HIGH for the previously derived two-rebit product-effect calculation; UNCERTAIN for the metaphysical AI-0 claim and all unproved bridges. No Lean build, physical experiment or new quantum derivation performed.
