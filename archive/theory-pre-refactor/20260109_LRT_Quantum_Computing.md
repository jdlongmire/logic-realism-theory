# Quantum Computing from Determinate Identity: Gates as Logical Transformers

**Working Paper v0.1**

**James D. (JD) Longmire**
ORCID: 0009-0009-1383-7698
jdlongmire@outlook.com

---

## Abstract

Logic Realism Theory (LRT) provides a principled framework for understanding quantum computation. Rather than treating quantum gates as mysterious operations on superpositions, LRT interprets them as *logical transformers*: structured mappings from definite input propositions to probability distributions over definite output propositions. Each run realizes exactly one L3-admissible outcome. This paper develops the LRT reading of single-qubit gates (Hadamard), two-qubit gates (CNOT), and quantum error correction (stabilizer codes as logical constraint protection). The framework suggests that decoherence is constraint violation, error correction is constraint restoration, and algorithm design benefits from treating gates as structured logical operations rather than physical manipulations of indefinite states.

---

## 1. Introduction: Computing with Logic

Quantum computation is typically framed as exploiting superposition and entanglement to achieve computational advantages. The quantum state evolves unitarily through gates, with measurement collapsing the superposition to yield classical output. This framing, while operationally successful, leaves conceptual gaps: what *is* a superposition during computation? How does measurement differ from gate application?

Logic Realism Theory offers a clarifying perspective. The core thesis (Longmire, 2025) holds that the Three Fundamental Laws of Logic (L3: Identity, Non-Contradiction, Excluded Middle) are constraints on physical instantiation, not merely rules of inference. Physical records are always L3-admissible; quantum states are representational vehicles encoding outcome-possibilities.

Applied to quantum computing, this means:

- **Input states** are definite classical propositions (e.g., "qubit is |0>")
- **Gates** are logical transformers that map input propositions to structured probability distributions over output propositions
- **Output records** are always L3-admissible: exactly one definite outcome per run
- **The quantum state** during computation encodes correlation structure between potential outcomes, not "indefinite reality"

This paper develops this framework for understanding quantum gates, entanglement, and error correction.

---

## 2. Gates as Logical Transformers

### 2.1 Single-Qubit Example: Hadamard Gate

Consider a Hadamard gate H followed by Z-basis measurement. The standard description: H transforms |0> into (|0> + |1>)/sqrt(2), creating a superposition that measurement collapses.

**LRT Blueprint:**

Define input propositions:
- I0: "input is |0>"
- I1: "input is |1>"

Define output propositions:
- O0: "detector reads 0"
- O1: "detector reads 1"

The gate+measurement defines a probability map determined by the Hadamard matrix and Born rule:
- P(O0 | I0) = 1/2
- P(O1 | I0) = 1/2
- P(O0 | I1) = 1/2
- P(O1 | I1) = 1/2

**LRT Reading:**

Each run of this circuit satisfies the Three Fundamental Laws:

- **Identity:** Each run realizes exactly one output (O0 or O1). The outcome is determinately what it is.
- **Non-Contradiction:** No run has both O0 and O1 true. The detector never reads "0 and 1."
- **Excluded Middle:** For the performed measurement, exactly one of {O0, O1} is true. There is no "neither" outcome.

The gate is a *logical transformer*: it maps a definite input fact to a probability distribution over definite output facts. The superposition (|0> + |1>)/sqrt(2) is the representational vehicle encoding this distribution, not a description of an "indefinite" physical situation.

### 2.2 Two-Qubit Example: CNOT Gate

The CNOT gate entangles control qubit C with target qubit T. Standard description: CNOT flips the target if and only if the control is |1>.

**LRT Blueprint:**

Define input propositions for the pair (C, T):
- I00: "CT starts as |00>"
- I01: "CT starts as |01>"
- I10: "CT starts as |10>"
- I11: "CT starts as |11>"

Define output propositions:
- Oab: "C measures a, T measures b" for a, b in {0, 1}

The CNOT transformation (followed by measurement) gives:
- P(O00 | I00) = 1, P(O01 | I01) = 1
- P(O11 | I10) = 1, P(O10 | I11) = 1

**Entangled Input:**

Apply H to the control before CNOT, starting from |00>. This creates the entangled state (|00> + |11>)/sqrt(2).

**LRT Reading:**

- Every run yields one sharp pair (a, b)
- The entangled state encodes a *correlation pattern*: only outcomes 00 or 11 occur, never 01 or 10
- This is not "both 00 and 11 realized simultaneously" but a constraint on which output pairs are possible

An entangling gate is thus a *structured logical constraint on pairs of outcomes*. The correlation is encoded in the representational vehicle (the entangled state) and manifests as restricted outcome possibilities. Each individual run remains L3-admissible: one definite pair, not a superposition of pairs.

---

## 3. Error Correction as Logical Constraint Protection

### 3.1 Stabilizer Codes as Logical Constraints

Quantum error correction protects quantum information from decoherence. In the stabilizer formalism, a logical qubit is encoded in a subspace defined by stabilizer operators. A codeword satisfies all stabilizer constraints: S|psi> = |psi> for each stabilizer S.

**LRT Interpretation:**

Stabilizer conditions are *logical constraints* that valid code states must satisfy. Each stabilizer equation is a proposition that must hold for the encoded information to remain intact:

- S1 = +1 (constraint 1 satisfied)
- S2 = +1 (constraint 2 satisfied)
- ...

A valid logical qubit is an equivalence class of physical configurations that all satisfy these constraints. The logical information resides not in any particular physical configuration but in which constraint-satisfying equivalence class the system occupies.

### 3.2 Decoherence as Constraint Violation

Environmental noise perturbs the physical system. In the LRT framework, this produces histories that *violate the stabilizer constraints*:

- Error E occurs: now S_k|psi_error> = -|psi_error> for some k
- The constraint S_k = +1 is violated
- The system has left the logical code space

Decoherence is thus *logical constraint failure*. The physical configuration no longer satisfies the propositions defining the logical qubit.

### 3.3 Error Correction as Constraint Restoration

Syndrome measurement identifies which constraints are violated. The syndrome is a classical bit string recording the signs of stabilizer measurements: +1 (satisfied) or -1 (violated).

**LRT Reading:**

- Syndrome measurement produces L3-admissible classical records (each stabilizer definitively reads +1 or -1)
- The syndrome identifies the pattern of constraint violation
- Correction operations restore all constraints to S_k = +1

Error correction is therefore *logical constraint restoration*: identifying which L3-constraints on the encoded information have been violated and applying operations that restore satisfaction.

A protected logical qubit persists because its defining constraints are maintained, not because any particular physical configuration is preserved. This aligns with LRT's emphasis on logical structure over physical substrate.

---

## 4. Implications for Quantum Algorithm Design

The LRT framework suggests a distinctive approach to quantum algorithm design:

### 4.1 Gates as Constraint Engineering

Rather than thinking of gates as "rotating qubits on the Bloch sphere," consider them as engineering the correlation structure between input and output propositions. Algorithm design becomes:

1. **Specify desired output distribution:** What probabilities should each output have?
2. **Identify constraint structure:** What correlations between qubits enable this distribution?
3. **Construct gate sequence:** Build transformers that create the required correlation structure

### 4.2 Entanglement as Structured Correlation

Entanglement is not mysterious "spooky action" but structured correlation encoded in the representational vehicle. When designing algorithms:

- Entangling gates create logical constraints between qubit outcomes
- Measurement on one qubit updates the probability distribution for others *because the correlation was already encoded*
- No information propagates; the constraint structure is revealed, not created

### 4.3 Measurement as Constraint Satisfaction

Measurement is not "collapse" but the transition from representational vehicle to L3-admissible record. In algorithm design:

- Intermediate measurements produce classical information that can condition subsequent operations
- Final measurement extracts the L3-admissible answer the algorithm was designed to produce
- The algorithm succeeds when the encoded correlation structure makes the desired outcome highly probable

---

## 5. Conclusion

Logic Realism Theory provides a principled framework for understanding quantum computation:

- **Gates are logical transformers:** They map definite inputs to probability distributions over definite outputs
- **Entanglement is structured correlation:** Constraints on which outcome pairs are possible
- **Error correction protects logical constraints:** Decoherence violates constraints; correction restores them
- **Each run is L3-admissible:** Every outcome is definite, non-contradictory, and satisfies excluded middle

This framework does not change the mathematics of quantum computing but clarifies its interpretation. The quantum state during computation is a representational vehicle encoding outcome possibilities; the physical record at every stage remains L3-consistent. Quantum advantage arises from the expressiveness of the correlation structures that quantum vehicles can encode, not from computing with "indefinite" or "contradictory" states.

The practical implication: algorithm design benefits from thinking in terms of constraint engineering rather than state manipulation. What correlation structure will make the desired answer probable? What logical constraints define the problem? How do gates create and transform these constraints?

Future work should develop this perspective for specific algorithmic primitives (Grover search, quantum Fourier transform, variational circuits) and explore whether the constraint-focused viewpoint suggests new algorithmic strategies.

---

## References

Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885-893.

Gottesman, D. (1997). Stabilizer codes and quantum error correction. PhD thesis, Caltech. arXiv:quant-ph/9705052.

Longmire, J. D. (2025). Logic Realism Theory: Position Paper. Zenodo.

Longmire, J. D. (2025). The Minimal Viable Set: Measurement as Logical Selection. Working Paper.

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information*. Cambridge University Press.

---

## Revision History

| Version | Date | Changes |
|---------|------|---------|
| 0.1 | 2026-01-09 | Initial draft |

---

*Working paper. Comments welcome: jdlongmire@outlook.com*
