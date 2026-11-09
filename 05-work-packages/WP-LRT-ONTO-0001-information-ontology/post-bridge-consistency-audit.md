# Post-bridge consistency and entailment audit

Status: RESEARCH AUDIT, not a canonical theory amendment
Date: 2026-11-08
Baseline: PR #100, merge `6d8b3cdb9f0294a3ad9db2778e15baad8496e6b6`
Scope: Source inspection of current `master`, independent of Muse's Lean assignment.

## Accepted bridge and its logical content

The canonical README and `theory/100-LRT-CORE-PHYSICS.md` §1.2 now distinguish `C = L3(I∞)` and `AΩ = {i ∈ C | A(i)=actual}`. Thus `AΩ ⊆ C` follows by definition. The converse `C ⊆ AΩ` is not implied and is false in the compiled infinite-domain countermodel (`formalization/LrtFormalization/BridgeSelectionCountermodel.lean`; successful CI run 42535685668). This does not establish that any particular physical possibility is actual, or derive a selection law.

## Traceability inventory and recommended dispositions

| Location | Observed language | Finding | Disposition |
|---|---|---|---|
| `README.md`, core thesis | New typed selection bridge | Consistent with selection semantics | Retain |
| `theory/100-LRT-CORE-PHYSICS.md` §1.2, near line 55 | New typed selection bridge | Corrected canonical definition | Retain |
| Same, §2.2, near lines 190-200 | `AΩ := L3(I∞)`; all admissible configurations identified with actuality | **Direct contradiction** with §1.2 when A selects a proper subset | Priority 1: replace old identity and explanatory paragraph; preserve vehicle/content distinction |
| Same, near lines 144-166 | Imports and advertises `AΩ = L3(I∞)` as foundation | Stale downstream summary and scope claims | Priority 1: replace equality with conditional selection statement |
| Same, §2.5, near lines 234-240 | Step 1 marked ESTABLISHED with old identity; foundation described as gap-free | Inconsistent with new semantics and existing entailment audit | Priority 1: separate definitional, axiomatic, and argued components; owner review of epistemic status |
| Same, §3.1, near lines 248-296 | Operational local tomography from Determinate Identity | Entailment audit says H1→H2 requires a locality/operational accessibility premise | Priority 2: explicitly conditionalize; avoid presenting H1 alone as sufficient |
| Same, §3.2, near lines 302-308 | Complex Hilbert space via Masanes–Müller with additional physical axioms | Text already acknowledges imported physical premises; no implication from L3 alone | Retain caveat; verify precise published theorem hypothesis list separately before treating shorthand as authoritative |
| `theory/104-LRT-ENTANGLEMENT.md` §§3.4, 5 | Tsirelson bound and no-signaling follow from Hilbert-space structure | Mathematical consequence is conditional on the quantum formalism; ontological grounding inherits unresolved reconstruction premises | Priority 2: distinguish imported mathematical results from independent LRT entailment; do not erase existing entanglement treatment |
| `05-work-packages/WP-LRT-ENT-0001-entailment-audit/entailment-matrix.md` | Step 0 revised; Step 3 requires locality premise | Audit is more conservative than core physics rhetoric | Retain as controlling open-obligation tracker; reconcile canonical prose |

Line references are approximate anchors to the inspected 2026-11-08 master; use headings and literal text to apply future edits.

## Dependency and proof-obligation matrix

| Claim | What is established | Additional requirement | Epistemic disposition |
|---|---|---|---|
| `AΩ ⊆ C` | Definitional set inclusion | None beyond stated definitions | FORMAL/DEFINITIONAL |
| `AΩ ≠ C` is possible | Infinite `Nat` witness compiled in CI | Does not model all LRT physics | FORMAL COUNTERMODEL |
| `AΩ` nonempty for native Step1 | `bridge_principle` assumed in Lean | A nonemptiness premise, not derived from L3 | AXIOM-DEPENDENT |
| Determinate identity | Lean Step2 includes `all_configs_determinate` for arbitrary configurations | Show what physically meaningful determinacy adds beyond classical reflexivity/LEM | FORMAL / EXPLANATORY GAP |
| Operational distinguishability | Philosophical bridge from instantiated distinctions to measurements | Definition of accessible measurement interactions and justification of operational effect | ARGUED |
| Local tomography | Existing entailment audit rejects H1→H2 as strict consequence | Local operational decomposability / accessibility premise | REQUIRES NEW PREMISE |
| Complex Hilbert space | Imported reconstruction route | Full independent hypotheses of selected reconstruction theorem | CONDITIONAL IMPORT |
| Born probabilities | Gleason-family mathematics under probability-measure assumptions | Noncontextuality, additivity, dimension, and operational applicability | CONDITIONAL IMPORT |
| Tsirelson / no-signaling | Standard quantum structural consequences | Validity of Hilbert/tensor-product and measurement assumptions | CONDITIONAL IMPORT |

## Controlled follow-on proposal

1. Canonical editorial PR, restricted to explicit legacy bridge expressions in core physics and stale summary rows. Preserve historical citations and explain the revision.
2. Separate epistemic-status PR for claims marked ESTABLISHED that are presently conditional or argued; obtain theory-owner approval for status promotions/demotions.
3. Independent theorem-hypothesis audit for the reconstruction literature using primary papers.
4. Keep Muse's native Lean Step0/Step1 witness and `#print axioms` work separate to avoid branch conflicts.

## Validation performed

- Read current master of `README.md`, `theory/100-LRT-CORE-PHYSICS.md`, `theory/104-LRT-ENTANGLEMENT.md`, `WP-LRT-ENT-0001/entailment-matrix.md`, and this package's `package.yaml`.
- Compared old and new bridge expressions by source line and section.
- Did not run a new Lean build; prior CI success is linked above.
- Did not inspect primary reconstruction papers in this audit. Claims about their exact theorem hypotheses require a separate source check.
- Did not change canonical equations, epistemic labels, or Lean files.
