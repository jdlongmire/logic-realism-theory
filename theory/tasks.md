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

- [ ] **LEAN-PROOF-SEP001**: Prove product_effects_separate_states from Operational Determinacy + I∞ structure
  - Type: lean_proof
  - Target: formalization/LrtFormalization/Step3_LocalTomography.lean
  - Supports: QM-001 (separation theorem — critical for MMR #54 PASS)
  - Details: Replace axiom `product_effects_separate_states`. Issue: #54.
    The axiom states: if two bipartite states agree on all local product-effect statistics, they are equal.
    This is the formal separation theorem. Approach: use the distinguishability metric D from I∞ —
    states are identical iff D=0, D is defined as sup over product measurements, so agreement on
    all product effects forces D=0, forces identity. May need to bridge through the `gleason_uniqueness_states`
    theorem already proven in Step3_LocalTomography.lean:425.
    Replace: `product_effects_separate_states`
    ```lean
    theorem product_effects_separate_states (sys : BipartiteSystem) (pep : ProductEffectProb sys) :
        ∀ (ρ σ : sys.AB.State),
          (∀ (e : ProductEffect sys), pep.prob ρ e = pep.prob σ e) → ρ = σ := by
      intro ρ σ h_same_stats
      -- Use gleason_uniqueness_states which already derives state equality
      -- from equal measurement statistics via Gleason's theorem
      exact gleason_uniqueness_states sys pep ρ σ (fun e => h_same_stats ⟨e, rfl⟩)
    ```

- [ ] **LEAN-PROOF-HSA001**: Prove hamiltonian_isSelfAdjoint via construction
  - Type: lean_proof
  - Target: formalization/LrtFormalization/Step9_EnergyAction.lean
  - Supports: QM-042 (Hamiltonian self-adjointness)
  - Details: Replace axiom `hamiltonian_isSelfAdjoint`. The Hamiltonian is defined as the
    generator of the unitary group. In the bounded case, Stone's theorem gives a self-adjoint
    generator directly. Approach: construct H as self-adjoint by definition using Mathlib's
    `IsSelfAdjoint` and the existing `hamiltonian` structure.
    Replace: `hamiltonian_isSelfAdjoint`
    ```lean
    theorem hamiltonian_isSelfAdjoint : IsSelfAdjoint (hamiltonian : H →L[ℂ] H) := by
      exact hamiltonian.self_adjoint
    ```

*No active tasks.*




## Completed Tasks
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
