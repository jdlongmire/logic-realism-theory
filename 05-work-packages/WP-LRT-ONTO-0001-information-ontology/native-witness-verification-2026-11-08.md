# Native Step0/Step1 Witness: Independent Verification Record

Work package: WP-LRT-ONTO-0001 (information ontology)
Verification date: 2026-11-08
Repository: jdlongmire/logic-realism-theory
Baseline commit: 6d8b3cdb9f0294a3ad9db2778e15baad8496e6b6 (master HEAD at verification time; merge of PR #100)
Base note: before this record was filed, master advanced 19 commits to be1fed89c55c2db82b02c978345d274f5f45e263 (PRs #101 to #119, research notes and one theory document). The formalization subtree is byte-identical between the two commits (git tree cc7b3a7926e654780475e6f1965065f1801b6ec6 in both), so every result below holds unchanged against current master.

## Build environment

- Lean 4.28.0 (commit 7e01a1bf5c70fc6167d49c345d3bf80596e9a79b, x86_64-unknown-linux-gnu), via elan; toolchain pin in formalization/lean-toolchain is leanprover/lean4:v4.28.0.
- Lake 5.0.0-src+7e01a1b.
- Mathlib pinned by formalization/lake-manifest.json at rev 8f9d9cff6bd728b17a24e163c9402775d9e6a365 (v4.28.0 tag line); prebuilt cache used (7,655 oleans), Mathlib not compiled from source.
- Host: Linux VM, user-namespace sandbox; the cache fetch required TAR_OPTIONS=--no-same-owner (tar cannot chown extracted files in the namespace). This is an environment property, not a repository defect.

## Item 1 and 2: rebuild from the pinned toolchain

Commands run in formalization/:

- `lake exe cache get` : exit 0 (after dependency clones completed; see incident note).
- `lake build` : exit 0. "Build completed successfully (2492 jobs)."

Incident note, for the record: the first two attempts failed during dependency cloning with `error: external command 'git' exited with code 128` (a transient network failure on this host; the same clone run manually succeeded immediately), and a third attempt was interrupted by a host restart after dependencies were cloned and compilation had begun. The successful run resumed incrementally from that state. At no point did a Lean compilation error occur.

Sorry audit:

- The successful build log contains zero `sorry` occurrences and zero "declaration uses 'sorry'" warnings across all 2,492 jobs.
- A source scan of the project's own Lean files (formalization/LrtFormalization/**, the root module, and the work-package Lean file) finds no `sorry` in tactic position; every match is prose in comments or status lists.
- The formalization README status table (dated 2026-03-27) reports "3 sorries (technical, not conceptual)" somewhere in the full formalization. That statement appears stale against current master: it is not reproduced by the build or by source scan. One divergence to resolve: Step6_BornRule.lean's internal status list describes `maxent_forces_pure_state` as "(sorry)", while no sorry tactic exists in that file. The file is outside the build target (see coverage note), so the compiler does not adjudicate its status list.

Build coverage note (affects how far the green build reaches):

- The default target (lakefile.toml: defaultTargets = ["LrtFormalization"]) compiles 12 project modules: the root module and, transitively, Basic, BridgeSelectionCountermodel, Steps 0, 1, 2, 3, Step4 (Boolean, Hardy, Purification), and Step5.EigenvalueRestriction.
- Six source files in the tree are not imported by the root module and are therefore not compiled by `lake build` or by the Lean Build CI workflow: Step5/EigenvalueOutcome.lean, Step6_BornRule.lean, Step7_Unitarity.lean, Step8_TemporalEmergence.lean, Step9_EnergyAction.lean, Step10_Schrodinger.lean. The derivation chain in the root module header runs to Step 10; the verified portion of the chain ends at Step 5 EigenvalueRestriction.

## Item 3: axiom-dependency audit

Method: a scratch file importing LrtFormalization, run with `lake env lean`, using `#print axioms`. Outputs verbatim:

- `LRT.BridgeSelectionCountermodel.actual_ne_admissible` depends on axioms: [propext]
- `LRT.BridgeSelectionCountermodel.actual_nonempty` depends on axioms: [propext]
- `LRT.BridgeSelectionCountermodel.actual_subset_admissible` depends on axioms: [propext]
- `LRT.Step1.bridge_principle` depends on axioms: [LRT.Step0.I, LRT.Step1.bridge_principle]
- `LRT.Step1.step1_constitution` depends on axioms: [LRT.Step0.I, LRT.Step1.bridge_principle]
- `LRT.Step0.all_configs_admissible` depends on axioms: [propext, Classical.choice, Quot.sound, LRT.Step0.I]

Reading: the standalone Nat countermodel's three theorems rest on propext alone: no LRT axiom, no classical choice, no sorryAx. They are pure-logic results about the chosen Nat sets, exactly as the file header claims ("No additional axioms or sorry are introduced"). The native constitution theorem step1_constitution depends on precisely the existence axiom for I and the bridge_principle axiom itself, as expected.

## Item 4: native Step0/Step1 witness

New file: formalization/LrtFormalization/NativeBridgeWitness.lean (imported by the root module in this change). It builds the witness from the native primitives only (Step0 `I`, `ActionPrimitive.mk_default`, `X.standard`; Step1 `A_Omega`).

Construction: for a configuration a0, `singletonAction a0` maps a0 to `actual` and every other configuration to `nonActual` (decidability by classical instance, local to the file). `singletonX a0 = X.standard (singletonAction a0)`.

Results:

- `aOmega_singletonX`: A_Omega (singletonX a0) = {a0}.
- `exists_native_proper_nonempty_actual`: there exists a native state X0 with A_Omega X0 nonempty, A_Omega X0 not equal to the full configuration set, and every configuration Admissible (Step0.all_configs_admissible).
- `aOmega_noneX`: the constant-nonActual action gives A_Omega = empty set.

Axiom audit of the new theorems (`#print axioms`):

- `exists_native_proper_nonempty_actual` depends on axioms: [propext, Classical.choice, Quot.sound, LRT.Step0.I, LRT.Step0.I_infinite]
- `aOmega_singletonX` and `aOmega_noneX`: identical dependency set.

The decisive point: **bridge_principle does not appear**. The singleton state's nonemptiness is witnessed constructively from the Step0 existence and infinitude axioms; it is not borrowed from the bridge axiom.

Interpretation, with the three levels kept separate:

1. Syntactic: the native Step0/Step1 definitions are consistent with a proper nonempty actualized subset; nothing in the definitions forces A_Omega to be everything or to be inhabited for every state.
2. Semantic: a model of the native Step0/Step1 assumptions exhibiting a nonempty proper A_Omega now exists inside the formalization itself, complementing the standalone Nat countermodel (which models the same distinction outside the native primitives, over Nat, with propext only). Compatibility with bridge_principle holds in the precise sense that this state's A_Omega is nonempty, as the principle requires of every state.
3. The empty-A_Omega state shows bridge_principle carries real content as a universal claim over all states: it is not derivable from the Step0/Step1 definitions, because a definitional consequence could not fail in a native state, and it does fail for the constant-nonActual action. The principle therefore remains an axiom (Tier 2, as Step1_Constitution.lean already labels it), not a theorem-in-waiting.
4. Not claimed: this is a model of the Step0/Step1 assumptions, not of the full LRT physics programme. Steps 2 and beyond impose further structure, and the physical eligibility question (whether a further predicate K restricts which configurations can be actual) is untouched by this witness. No fourth primitive is introduced or implied.

## Item 5: Step2 dependency check

- `LRT.Step2.step2_determinate_identity` depends on axioms: [propext, Classical.choice, Quot.sound, LRT.Step0.I]
- `LRT.Step2.all_configs_determinate` depends on axioms: [propext, Classical.choice, Quot.sound, LRT.Step0.I]

The dependency sets are identical. The source already shows why: the proof term of step2_determinate_identity does not use its actualization hypothesis (the hypothesis is named with an underscore prefix) and is textually the same construction as all_configs_determinate. Precise claim: for the theorem step2_determinate_identity as formalized, the actualization hypothesis is logically idle; determinate identity for a configuration follows from the Step0 basis (existence of I plus classical logic) for every configuration, actualized or not. This is a statement about this theorem's dependency structure. It does not by itself settle what role actualization plays elsewhere in the programme (for example in Step3 and later, which were outside this check's scope).

## Outstanding obligations and notes for the owner

1. README status table: the "3 sorries" line and the Step6 status list divergence (above) are documentation questions for the owner; this change does not edit them.
2. Build coverage: whether the six uncompiled step files should be brought into the root module (and so under CI) is an owner decision; several may be drafts by design.
3. No canonical ontology, axiom, or existing proof was changed. The change is strictly additive: one new file, one import line, and this record.
4. Physical eligibility (K) remains unresolved and untouched, per the work package authority boundary.

Human-Curated, AI-Enabled (HCAE)
