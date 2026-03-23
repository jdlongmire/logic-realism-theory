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

- [ ] **LEAN-PROOF-HGU001**: Prove hamiltonian_generates_unitary via selfAdjoint.expUnitary
  - Type: lean_proof
  - Target: formalization/LrtFormalization/Step7_Unitarity.lean
  - Supports: QM-035 (Unitarity theorem)
  - Details: Replace axiom `hamiltonian_generates_unitary`. Mathlib has `selfAdjoint.expUnitary`
    in C*-algebra theory. The Hamiltonian H is self-adjoint (axiom `hamiltonian_isSelfAdjoint`),
    so U(t) = exp(-i * t * H) should be a unitary operator via this path.
    First check: does Step7 import `Mathlib.Analysis.CStarAlgebra.Exponential` or similar?
    Replace: `hamiltonian_generates_unitary`
    ```lean
    theorem hamiltonian_generates_unitary (t : ℝ) :
        ∀ ψ : H, ‖(timeEvolution t) ψ‖ = ‖ψ‖ := by
      intro ψ
      have := IsSelfAdjoint.expUnitary (hamiltonian_isSelfAdjoint.smul_real t)
      exact this.isometric ψ
    ```
    Issue: #54.

- [ ] **LEAN-PROOF-HGM001**: Prove hamiltonian_generates_group_mul via Commute.expUnitary_add
  - Type: lean_proof
  - Target: formalization/LrtFormalization/Step7_Unitarity.lean
  - Supports: QM-035 (Unitarity — group composition law)
  - Details: Replace axiom `hamiltonian_generates_group_mul`. Mathlib has
    `Commute.expUnitary_add` — for commuting self-adjoint operators, exp(A+B) = exp(A)*exp(B).
    Since exp(-i*s*H) and exp(-i*t*H) commute (same operator, scalar multiples),
    U(s+t) = U(s)*U(t) should follow.
    Replace: `hamiltonian_generates_group_mul`
    ```lean
    theorem hamiltonian_generates_group_mul (s t : ℝ) :
        timeEvolution (s + t) = timeEvolution s * timeEvolution t := by
      simp [timeEvolution]
      rw [← neg_add, smul_add]
      exact (IsSelfAdjoint.commute_expUnitary_smul hamiltonian_isSelfAdjoint s t).expUnitary_add
    ```
    Issue: #54.






## Completed Tasks

- [x] **LEAN-PROOF-CPH001**: Derive QuantumStateSpace.ofCPH from CPHStructure *(completed 2026-03-23)*
  - Result: **SUCCESS** — axiom replaced with definition
  - Method: `Module.Finite ℂ H` → `FiniteDimensional.proper ℂ H` → `ProperSpace H` → `CompleteSpace H`
  - Mathlib chain: `FiniteDimensional → ProperSpace → complete_of_proper`
  - **Axiom count: 22 → 21**
  - Build: SUCCESS (2491 jobs, 21 axioms, 0 sorries)

- [x] **LEAN-ISSUE-003**: Mathlib unbounded operator assessment *(completed 2026-03-23)*
  - Result: Report generated at `docs/formalization/build-reports/mathlib-assessment-20260323.md`
  - Key findings:
    - `step4_hilbert_space`: **REMOVED** (via CPH001)
    - `hamiltonian_generates_unitary`: **POTENTIALLY DERIVABLE** via `selfAdjoint.expUnitary`
    - `hamiltonian_generates_group_mul`: **POTENTIALLY DERIVABLE** via `Commute.expUnitary_add`
    - `schrodinger_from_stone`: **NOT DERIVABLE** — Mathlib lacks unbounded operator theory
    - `stones_theorem`: **EXTERNAL** — must remain axiom
  - Recommendation: Reclassify Stone's theorem as EXTERNAL (Tier-2)

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
