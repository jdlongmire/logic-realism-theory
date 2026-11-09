# Minimal composition of fundamental Actions: axioms, consequences, and countermodels

Status: RESEARCH / PROVISIONAL REPRESENTATIONAL ALGEBRA
Date: 2026-11-08
Scope: WP-LRT-ONTO-0001. No canonical ontology or Lean modifications.

## Ontological boundary

LRT's primitive A is the ontological operation making state transitions possible. It is **not** defined to be a function, relation, morphism, or linear operator. The algebra below represents *licensed transitions grounded in A*, rather than reducing A to mathematics. The 3FLL govern admissibility; mathematical apparatus is downstream as a proposed description. The model does not derive category theory from 3FLL.

## Minimal typed action calculus M0

Choose a class C of admissible configurations. For x,y∈C let Act(x,y) be a collection of **licensed transition descriptions**. Add:

- **Typing:** a∈Act(x,y) has source x and target y.
- **Sequential closure (S):** for a∈Act(x,y), b∈Act(y,z), a composite b∘a∈Act(x,z).
- **Associativity (Assoc):** c∘(b∘a)=(c∘b)∘a whenever typed.
- **Identity availability (Id):** 1_x∈Act(x,x), with a∘1_x=a=1_y∘a.

These are independent structural postulates defining a category-like representation. Neither Assoc nor Id is a theorem of identity/noncontradiction/excluded middle alone. A different physical ontology might not license an identity *action*, although mathematical identity arrows can represent an empty protocol.

**Consequences conditional on M0:** well-typed finite action chains have a unique composite independent of parenthesization; identities are unique at each object. Neither a total order on configurations, reversibility, nontrivial change, probability, nor time follows.

## Parallel composition M1 (optional, strictly stronger)

For independent subsystems, introduce x⊗u and actions a⊗b with source x⊗u and target y⊗v. Require functorial interchange:

`(b∘a)⊗(d∘c)=(b⊗d)∘(a⊗c)`

for matching types, plus identity preservation `1_x⊗1_u=1_(x⊗u)`. Optional associator/unit and symmetry constraints must be explicit. This is a monoidal-category-like representation, **not** a proof that physical composition is locally tomographic, reversible, symmetric, or linear. Physical interactions that couple subsystems need not factor as a⊗b.

**Important:** sequential composition and independent parallel composition alone do not supply measurement effects, distinguishability, or numerical probabilities.

## Occurrence and emergent order

Introduce an obtaining predicate Occ(a) on licensed actions. The implication Occ(a)⇒a licensed is definitional. If occurrence is to be closed under sequential composition, `Occ(a)∧Occ(b)⇒Occ(b∘a)` is a further premise; this may be inappropriate when actions are alternative histories rather than jointly realized events.

A reachability relation `x≼y ⇔ ∃a∈Act(x,y)` is reflexive and transitive under M0, hence a **preorder**. Antisymmetry need not hold. Example: two distinct configurations x,y with licensed arrows both ways produce x≼y and y≼x. Consequently a physical partial order or directed time does not follow without a no-cycle/antisymmetry condition or a quotient by mutual reachability. Quotienting does not establish a physical arrow of time.

## Countermodel 1: free path category

Start with a directed graph whose vertices are configurations and whose arrows are primitive licensed transitions. Act(x,y) consists of finite directed paths x→y, including empty paths; sequential composition is path concatenation. Associativity and identities hold. This supplies a concrete M0 model with no preexisting physical time, numerical probability, or inner-product structure. Its combinatorial path length is a mathematical count, not yet physical duration.

It also demonstrates underdetermination: different directed graphs satisfying M0 have different reachable-state patterns. No unique dynamics follows from M0.

## Countermodel 2: entanglement-compatible, nonlocally tomographic M1

Finite-dimensional **real quantum theory** supplies a richer mathematical model: systems are finite-dimensional real Hilbert spaces, states real symmetric positive trace-one matrices, and licensed processes can be taken as real completely positive trace-preserving maps, with composition and independent tensor products. Identity maps, associativity (up to standard tensor identifications), and interchange hold. Entangled composite states are admitted.

For two rebits `J=[[0,-1],[1,0]]`, `K=J⊗J`, `ρ±=(I₄±tK)/4` (0<t≤1) have the same statistics for all product effects `E⊗F` with E,F real symmetric, but a global measurement separates them. Thus M0+M1 are consistent with **failure of local tomography**, even in an entanglement-compatible theory.

This is a countermodel to any claim that the bare laws of sequential/parallel action composition entail tomography. It does not show that the full, still-unformalized ontological A is exhausted by real quantum processes.

## Assumption ledger

| Ingredient | Classification | Grounding |
|---|---|---|
| 3FLL | LRT primitive constraints | Owner commitment |
| I∞ | LRT primitive | Owner commitment |
| A transition-enabling operation | LRT primitive | Owner clarification |
| Collections of objects/actions | Mathematical representation | Imported set/type language |
| S, Assoc, Id | Candidate action laws | Independent postulates |
| Tensor and interchange | Candidate independent-composition laws | Independent postulates |
| Occurrence and closure | Candidate actuality laws | Not derived |
| Reachability preorder | Conditional theorem | Follows from S and Id |
| Physical temporal order | Open | Requires extra structure |
| Local tomography | Open | Not entailed by M0/M1 |

## Research decision

M0 is a useful *minimal representational calculus* and M1 a useful *candidate composition calculus*. Neither is yet an ontological derivation from 3FLL. Do not adopt these as new LRT axioms without owner review.

**Next discriminating test:** define a substantive, independently motivated **interaction-identity law** connecting ontic individuation to composable Actions. Prove what effects/records it generates and check whether a real-quantum model satisfies that law. Do not merely assert that every distinct composite is locally distinguishable; that would repackage local tomography.

## Verification status

Associativity of path concatenation and preorder derivation are standard direct proofs. The two-rebit countermodel is established analytically in preceding research documents. No Lean implementation, new numerical run, or experimental confirmation is claimed.

Related: `logic-priority-mathematics-dependency-protocol.md`, `action-ontological-operation-research-semantics.md`, `compositional-interaction-separation-theorem.md`.
