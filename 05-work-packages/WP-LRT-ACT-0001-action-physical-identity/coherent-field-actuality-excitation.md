# Coherent field information, actuality, and excitation: an LRT ontological distinction

Status: RESEARCH / CONCEPTUAL REFINEMENT, NOT CANONICAL THEORY
Date: 2026-11-08
Work package: WP-LRT-ACT-0001
Scope: preserve the three primitives and their logical priority; no canonical equation or Lean modification.

## Thesis under investigation

The user's proposed intuition is that a quantum field is already a coherent information structure, whether or not a particular excitation is present. An excitation is a possible change of the field's state. The coherence of a structure is logically prior to its particular transitions, but explanatory priority must not be mistaken for a temporal sequence.

This requires three separations:

1. **Admissible informational structure:** a possible coherent specification constrained by 3FLL within I∞. Admissibility alone does not entail physical obtaining.
2. **Actual physical field:** an instantiated structure with physical significance, whose obtaining is an ontological question.
3. **Field-state transition/excitation:** a particular possible or obtaining change of the instantiated field, grounded in fundamental Action A.

The coherent informational *description* of a field and the *actual* field must not be identified without an explicit actuality bridge. Likewise, a field and its state are not interchangeable in standard QFT.

## Two candidate ontologies to discriminate

**H1: Identity ontology.** An actual physical field just is a coherent information structure that obtains. The phrase “that obtains” is indispensable; a merely admissible structure in I∞ is not automatically an actual field. Research obligation: explain how obtaining is grounded in the co-constitutive triad without treating a Boolean selection predicate as the full meaning of A.

**H2: Instantiation ontology.** A coherent information structure is a possibility in I∞, and the physical field is its instantiation. Research obligation: specify the instantiation relation, its relata, and why it is not an unacknowledged fourth primitive or an infinite regress of instantiations.

These may differ terminologically rather than ontologically unless a model distinguishes their truth conditions. A discriminating test is whether one admissible structure may have multiple physical instances, or whether two isomorphic field structures can be numerically distinct physical fields. Any claim here requires an account of identity and multiplicity.

## QFT anchor and its limits

In a simple free-field Fock representation, `a†_k |0⟩ = |1_k⟩` is a mathematical construction of a one-particle excitation from a vacuum vector. It does **not** assert that an operator application is itself an ontological event or that an excitation physically occurred. Vacuum states can have nontrivial correlations, and field observables and state functionals are conceptually distinct.

Interacting QFT, inequivalent representations, and curved-spacetime settings complicate a universal particle-number description. Consequently the LRT proposal must be stated in terms of admissible field-state structure and change, not a universal assumption that all events are particle creation or that all fields possess a unique preferred vacuum.

## Dependency ledger

| Statement | Status |
|---|---|
| Logical identity, noncontradiction, and excluded middle constrain coherent descriptions | Foundational LRT commitment |
| 3FLL uniquely determine the QFT field algebra or vacuum | NOT DERIVED |
| A coherent possibility in I∞ is automatically actual | NOT LICENSED |
| A field may be actual without a particular excitation occurring | Conceptual hypothesis compatible with simple QFT examples |
| Fundamental A grounds the possibility of transition | Owner's intended ontology |
| An excitation is a field-state change in every QFT context | Too strong; terminology and representation dependent |
| A is identical to a QFT creation operator | REJECTED as a category mistake |
| Physical obtaining and transition occurrence are both accounted for by the same primitive A | Open bridge obligation |

## Non-regress condition

“Before excitation” here means a **condition of intelligibility or dependence**, not necessarily an earlier instant. If every event must have a prior actual excitation, an unsupported regress is introduced. A must be characterized as enabling transition without being stipulated to be an earlier physical transition.

## Minimal illustrative model, not a derivation

Let `S` be a class of admissible field-state descriptions, `ActualField(F)` a provisional obtaining judgment, and `Licensed_F(s,t)` a provisional trace of A-grounded transition possibility. Distinguish:

- `Coherent(F,s)`: the description is logically admissible;
- `ActualField(F)`: the field obtains;
- `Licensed_F(s,t)`: a transition is possible;
- `Occurs_F(s,t)`: a transition obtains, requiring `Licensed_F(s,t)`.

None of these predicates *defines* fundamental A. In particular, `Coherent(F,s) ⇏ ActualField(F)` and `Licensed_F(s,t) ⇏ Occurs_F(s,t)`. A coherent, actual field with no presently obtaining excitation is consistent with this representation.

## Proposed next proof obligations

- **FI-1:** Provide a noncircular ontological account of physical obtaining consistent with the single primitive A and the existing triad.
- **FI-2:** Determine whether H1 and H2 have different identity or multiplicity consequences; otherwise collapse redundant vocabulary.
- **FI-3:** Define coherence without importing the Hilbert-space/QFT structures intended for reconstruction; distinguish mere logical consistency from sufficient physical constitution.
- **FI-4:** Specify the relationship between actual field identity, possible Action profiles, and occurrence without a preexisting time coordinate.
- **FI-5:** Test whether the proposed field ontology constrains observable distinctions beyond what the existing Action calculus M0/M1 allows.
- **FI-6:** After owner approval, implement only well-typed representations in a parallel Lean research namespace with explicit axioms and countermodels.

## Recommended conceptual choice

Provisional preference: describe an **actual field as an obtaining coherent information structure** (H1), while preserving the distinction between its admissible informational specification and its physical obtaining. This avoids adding an unexplained instantiation entity, but it does not solve the actuality bridge. Do not promote this preference to canonical theory without resolving FI-1 and FI-2.

## Traceability

Related: `action-identity-research-baseline.md` in this work package; `WP-LRT-ONTO-0001/action-ontological-operation-research-semantics.md`, `logic-priority-mathematics-dependency-protocol.md`, and `minimal-action-composition-calculus.md`. Standard free-field Fock notation is used as an illustration only, not a primary-source historical claim or a derivation.

Verification: internal consistency and conceptual separation only. No Lean build, experimental test, or proof of the field ontology is claimed.
