# LRT Physics Agent Task Queue

Tasks are processed sequentially. Mark completed tasks with `[x]` prefix.

## Task Format

```markdown
- [ ] **S8**: Description of next supplement
  - Type: supplement | derivation | formalization
  - Target: supplementary/S8_Filename.md
  - Supports: Step N
  - Details: Specific requirements for the supplement.
```

## Active Tasks

- [ ] **LEAN-PROOF-CPH001**: Prove QuantumStateSpace.ofCPH from CPHStructure
  - Type: lean_proof
  - Target: formalization/LrtFormalization/Step4/Hardy.lean
  - Supports: QM-003 / step4_hilbert_space reduction
  - Details: Replace axiom `QuantumStateSpace.ofCPH`. The CPHStructure from Step3 already
    contains the Hilbert space data — this should be a straightforward type construction.
    Replace: `QuantumStateSpace.ofCPH`
    ```lean
    def QuantumStateSpace.ofCPH (cph : CPHStructure) : QuantumStateSpace where
      H := cph.H
    ```
    If CPHStructure contains the InnerProductSpace/CompleteSpace instances, this may
    resolve immediately. Check what fields CPHStructure has first. Issue: #54.

- [ ] **LEAN-ISSUE-003**: Assess remaining 4 HARD axioms for Mathlib unbounded operator support
  - Type: lean_build
  - Target: docs/formalization/build-reports/mathlib-assessment-20260323.md
  - Supports: hamiltonian_generates_unitary, hamiltonian_generates_group_mul, schrodinger_from_stone, step4_hilbert_space
  - Details: Search Mathlib for: (1) SelfAdjoint unbounded operator theory, (2) StronglyMeasurable
    unitary groups, (3) Stone's theorem statement in Mathlib (look for `isSelfAdjoint_generator`
    or similar). Report what exists vs what is missing. This will determine whether the 4 HARD
    axioms are reducible or should be reclassified as EXTERNAL. Issue: #54.





## Completed Tasks
- [x] **LEAN-PROOF-SEP001**: Analysis of product_effects_separate_states *(completed 2026-03-23)*
  - Result: **NOT DERIVABLE** — circular dependency detected
  - Analysis: The suggested approach using `gleason_uniqueness_states` won't work because:
    1. `gleason_uniqueness_states` signature: `∀ (P : State → ℝ), P ρ = P σ` → `ρ = σ`
    2. `product_effects_separate_states` signature: `∀ (e : ProductEffect), prob ρ e = prob σ e` → `ρ = σ`
    3. To bridge these, we need: product effect agreement → all-function agreement
    4. But `product_effects_generate_projectors` proves that direction **using** `product_effects_separate_states` itself
  - Verdict: This is a Tier 2 axiom (external physics import). It represents the **content** of tomographic completeness — the claim that local measurements are informationally complete. This is the core result from Hardy/CDP/Masanes-Müller that cannot be derived from LRT primitives alone.
  - Recommendation: Retain as EXTERNAL axiom with clear documentation

- [x] **LEAN-PROOF-HSA001**: Analysis of hamiltonian_isSelfAdjoint *(completed 2026-03-23)*
  - Result: **NOT DERIVABLE** as suggested — `hamiltonian` is an axiom, not a structure
  - Analysis: The suggested proof `exact hamiltonian.self_adjoint` assumes `hamiltonian` has a `.self_adjoint` field, but `hamiltonian` is declared as:
    ```lean
    axiom hamiltonian : H →L[ℂ] H
    ```
    It has no fields — it's a pure axiom.
  - Options:
    1. **Refactor:** Define `SelfAdjointOperator` structure, make `hamiltonian` of that type → significant architecture change
    2. **Stone's theorem approach:** Add axiom that the unitary group has a self-adjoint generator → still requires axiom
    3. **Accept as physical input:** Hamiltonian self-adjointness (energy eigenvalues are real) is a physical constraint, not derivable from logic
  - Verdict: This is a root axiom for QM dynamics. Self-adjointness ensures unitary evolution and real energy spectrum. It should remain as axiom with clear physics justification.
  - Recommendation: Retain as ROOT axiom (physical input)

- [x] **LEAN-BUILD-001**: Full Lean build report *(completed 2026-03-23)*
  - Result: SUCCESS (2491 jobs, 22 axioms, 0 sorries)
  - Report: docs/formalization/build-reports/build-report-20260323.md
  - Comment: https://github.com/jdlongmire/logic-realism-theory/issues/55#issuecomment-4112797909

- [x] **LEAN-PROOF-OPN006**: Projection contraction proof *(completed 2026-03-23)*
  - Result: ALREADY COMPLETE — `proj_norm_le` proven in Step6_BornRule.lean:364-389
  - The requested axiom `projection_contraction` does not exist; equivalent theorem already proven via Cauchy-Schwarz

- [x] **S14**: Boolean Spectrum — Derive eigenvalue restriction from actualization semantics *(completed 2026-03-13)*
- [x] **S14**: Boolean Spectrum — Derive eigenvalue restriction from actualization semantics *(completed 2026-03-13)*
- [x] **S13**: Field Selection (K=2) — Derive complex numbers from Hardy axioms and L₃ *(completed 2026-03-13)*
- [x] **S13**: Field Selection (K=2) — Derive complex numbers from Hardy axioms and L₃ *(completed 2026-03-13)*
- [x] **S12**: Product Effects (H1) — Derive composite system product structure from L₃ *(completed 2026-03-13)*
- [x] **S12**: Product Effects (H1) — Derive composite system product structure from L₃ *(completed 2026-03-13)*
- [x] **S11**: Lean formalization companion document *(completed 2026-03-13)*
- [x] **S11**: Lean formalization companion document *(completed 2026-03-13)*
- [x] **S10**: Lorentz covariance derivation from L₃ symmetry structure *(completed 2026-03-13)*
- [x] **S9**: Lean 4 formalization strategy for Step 5 (eigenvalue restriction) *(completed 2026-03-13)*
- [x] **S8**: Lean 4 formalization strategy for Step 3 (local tomography) *(completed 2026-03-13)*

- [x] **S7**: G-equivariance derivation from L₃ symmetry constraints *(2026-03-13)*
- [x] **S6**: Formalize the Unique Next State (UNS) theorem *(2026-03-13)*
- [x] **S5**: D_sing and Bekenstein-Hawking entropy connection *(2026-03-13)*
- [x] **S4**: Debreu-Nachbin conditions from A_Omega structure *(2026-03-13)*
- [x] **S3**: Eigenvalue Restriction Lemma *(2026-03-13)*
- [x] **S2**: H1-H2 Bridge argument *(2026-03-13)*
- [x] **S1**: PPC Derivation from L₃ *(2026-03-13)*

---

## Notes

- Agent commits and pushes after each task completion
- Email notification sent to longmire.jd@gmail.com on completion
- Physics mode framing applies to all derivations
- Lean 4 tasks produce *strategy* documents, not executable code
