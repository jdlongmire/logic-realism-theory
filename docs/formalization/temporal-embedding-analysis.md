# Temporal Embedding Axioms: Derivability Analysis

> **HISTORICAL NOTE (2026-03-21):** This analysis led to the decision that LRT adopts discrete time (ℕ-indexed actualizations). The `time_embedding_dense` axiom was removed. Continuous physics interpolates between discrete actualization events.

**Date:** 2026-03-20
**Scope:** Step 8 axioms connecting actualization (ℕ) to continuous time (ℝ)
**Files:** `LrtFormalization/Step8_TemporalEmergence.lean`

---

## Executive Summary

This analysis examined the Step 8 axioms that connect the discrete actualization sequence (ℕ-indexed) to continuous time evolution (ℝ-parameterized):

| Axiom | Status |
|-------|--------|
| `time_embedding` | DEFINITION |
| `time_embedding_strict_mono` | THEOREM |
| `evolution_matches_actualization` | THEOREM |

**Outcome:** LRT holds that time IS the actualization sequencing of events. Actualizations are discrete (ℕ-indexed). Continuous physics describes interpolation between discrete actualization events.

---

## Detailed Analysis

### 1. `time_embedding : ActualizationEvent → Time`

**Current Status:** Tier 2 Axiom (line 90)

**Signature:**
```lean
axiom time_embedding : ActualizationEvent → Time
```

**Analysis:**

The ActualizationEvent structure is:
```lean
structure ActualizationEvent where
  id : ℕ
```

Since `Time := ℝ` (abbreviation), we need a function `ActualizationEvent → ℝ`.

**Construction Options:**

1. **Natural embedding:** `fun e => (e.id : ℝ)`
   - Trivially constructible
   - Strict monotone: yes
   - Dense: NO (ℕ ⊂ ℝ is nowhere dense)

2. **Rational interpolation:** `fun e => q(e.id)` for some ℚ-valued function
   - Still countable image, hence not dense in ℝ

3. **Any countable set embedding:**
   - By cardinality, no injection from ℕ into ℝ can have dense range
   - Image has measure zero

**Derivability Rating:** MEDIUM

**Recommendation:** Convert to definition:
```lean
noncomputable def time_embedding : ActualizationEvent → Time :=
  fun e => (e.id : ℝ)
```

This is the canonical choice and requires no axiom.

---

### 2. `time_embedding_strict_mono : StrictMono time_embedding`

**Current Status:** Tier 2 Axiom (line 101)

**Signature:**
```lean
axiom time_embedding_strict_mono : StrictMono time_embedding
```

**Analysis:**

If `time_embedding` is constructed as `fun e => (e.id : ℝ)`, then strict monotonicity follows from:

```lean
theorem time_embedding_strict_mono : StrictMono time_embedding := by
  intro e₁ e₂ h
  -- h : e₁ < e₂ in ActualizationEvent ordering
  -- Goal: time_embedding e₁ < time_embedding e₂
  -- Since ActualizationEvent ordering is via id: e₁ < e₂ ↔ e₁.id < e₂.id
  -- And time_embedding e = (e.id : ℝ)
  -- We need: (e₁.id : ℝ) < (e₂.id : ℝ)
  exact Nat.cast_lt.mpr h
```

**Derivability Rating:** EASY (once time_embedding is defined)

**Recommendation:** Convert to theorem. The proof is a one-liner using `Nat.cast_lt`.

---

### 3. `time_embedding_dense : DenseRange time_embedding`

**Current Status:** Tier 2 Axiom (line 117)

**Signature:**
```lean
axiom time_embedding_dense : DenseRange time_embedding
```

**Mathematical Status: IMPOSSIBLE**

**Theorem:** No function f : ℕ → ℝ can have dense range.

**Proof:**
- `DenseRange f` means `∀ r : ℝ, ∀ ε > 0, ∃ n : ℕ, |f(n) - r| < ε`
- Equivalently, `closure (range f) = Set.univ`
- But `range f` is countable (image of countable set)
- ℝ is uncountable and not a countable union of closed nowhere-dense sets (Baire category)
- More directly: [0,1] ⊂ ℝ has cardinality continuum, but range f has cardinality ≤ ℵ₀
- A countable set cannot be dense in ℝ... wait, ℚ is countable and dense.

**Correction:** A countable set CAN be dense in ℝ (e.g., ℚ). The question is whether a *monotone* embedding of ℕ can have dense range.

**Revised Analysis:**

For a strictly monotone embedding f : ℕ → ℝ:
- The image {f(0), f(1), f(2), ...} is a strictly increasing sequence
- If bounded above: converges to sup, has limit gaps
- If unbounded: f(n) → ∞, so (−∞, f(0)) has no image points

**Theorem:** No strictly monotone f : ℕ → ℝ has dense range.

**Proof:**
- Either f is bounded above or unbounded
- If bounded: let L = lim f(n). For any ε > 0, only finitely many f(n) in (L-ε, L). The interval (f(N), L) for large N contains no f(n), contradicting density.
- If unbounded: the interval (f(n), f(n+1)) for any n contains no image points, contradicting density.

**Conclusion:** The axiom `time_embedding_dense` combined with `time_embedding_strict_mono` is INCONSISTENT when ActualizationEvent.id : ℕ.

**Derivability Rating:** IMPOSSIBLE (as currently stated)

**Options:**

1. **Remove the axiom:** Accept that actualization times are discrete, not dense.

2. **Change the structure:** Replace `id : ℕ` with `id : ℚ` or `id : ℝ`, representing a dense labeling. This would require architectural changes.

3. **Weaken the claim:** Use "Cauchy-complete" or "order-complete" instead of dense:
   ```lean
   axiom time_embedding_cauchy_complete :
     ∀ s : ℕ → ActualizationEvent, Cauchy (time_embedding ∘ s) →
       ∃ e : ActualizationEvent, ...
   ```
   But this doesn't quite work either since ℕ-indexed sequences can't be Cauchy in a non-trivial way.

4. **Interpret "density" philosophically:** The axiom expresses that time is "filled in" by actualizations, not that the embedding has dense range. This would need reformulation.

**Recommendation:** This axiom should be either REMOVED or RECONCEPTUALIZED. The current formulation is mathematically inconsistent.

---

### 4. `evolution_matches_actualization`

**Current Status:** Tier 2 Axiom (line 139)

**Signature:**
```lean
axiom evolution_matches_actualization
    (U : UnitaryGroup (H := H))
    (e₁ e₂ : ActualizationEvent) :
    U.U (eventTime e₂) = U.U (eventTime e₂ - eventTime e₁) * U.U (eventTime e₁)
```

**Analysis:**

This axiom states that the unitary evolution at time t₂ equals evolution by (t₂ - t₁) composed with evolution at t₁.

This is a DIRECT CONSEQUENCE of the group composition law:
```lean
axiom evolution_group_composition (s t : ℝ) :
    time_evolution_family (H := H) (s + t) = time_evolution_family s * time_evolution_family t
```

**Proof sketch:**
```lean
theorem evolution_matches_actualization
    (U : UnitaryGroup (H := H))
    (e₁ e₂ : ActualizationEvent) :
    U.U (eventTime e₂) = U.U (eventTime e₂ - eventTime e₁) * U.U (eventTime e₁) := by
  -- Note: eventTime eᵢ = time_embedding eᵢ
  -- We want: U(t₂) = U(t₂ - t₁) * U(t₁)
  -- Group law: U(s + t) = U(s) * U(t)
  -- Substitute s = t₂ - t₁, t = t₁:
  -- U((t₂ - t₁) + t₁) = U(t₂ - t₁) * U(t₁)
  -- Simplify: U(t₂) = U(t₂ - t₁) * U(t₁) ✓
  have h := U.group_mul (eventTime e₂ - eventTime e₁) (eventTime e₁)
  simp only [sub_add_cancel] at h
  exact h
```

**Derivability Rating:** EASY

**Recommendation:** Convert to theorem using `UnitaryGroup.group_mul`.

---

## Summary Table

| Axiom | Current | Target | Effort | Blocker |
|-------|---------|--------|--------|---------|
| `time_embedding` | axiom | def | 1 hour | None |
| `time_embedding_strict_mono` | axiom | theorem | 30 min | Needs time_embedding def |
| `time_embedding_dense` | axiom | **REMOVE or RECONCEPTUALIZE** | N/A | Mathematically impossible |
| `evolution_matches_actualization` | axiom | theorem | 30 min | None |

---

## Mathematical Background: Dense Embeddings of ℕ into ℝ

### Key Theorem

**There exists no strictly monotone embedding f : ℕ → ℝ with dense range.**

### Weaker Notions

1. **Order-density:** ∀ a < b in range(f), ∃ c ∈ range(f) with a < c < b.
   - This is impossible for ℕ since ℕ is discrete (no element between n and n+1)

2. **Eventual density:** The closure of range(f) contains [L, ∞) for some L.
   - Possible if f(n) → ∞ and gaps shrink to 0

3. **Completion:** Consider the Cauchy completion of (ℕ, d) where d(m,n) = |f(m) - f(n)|.
   - This embeds into ℝ but doesn't give density

### LRT Interpretation

The LRT claim that "time emerges from actualization" may not require dense embedding. Alternative interpretations:

1. **Discrete time is fundamental:** Time is fundamentally discrete (ℕ-indexed), and the continuum is an idealization.

2. **Uncountable events:** ActualizationEvent should have id : ℝ, representing a continuum of actualizations.

3. **Limit structure:** The continuum emerges as a limit/completion of discrete events, not as a dense embedding.

---

## Recommendations

### Immediate Actions

1. **Remove `time_embedding_dense`** — It is inconsistent with ℕ-indexed events.

2. **Convert `time_embedding` to definition:**
   ```lean
   noncomputable def time_embedding : ActualizationEvent → Time :=
     fun e => (e.id : ℝ)
   ```

3. **Derive `time_embedding_strict_mono`** from the definition.

4. **Derive `evolution_matches_actualization`** from group law.

### Architectural Decision Required

The project needs to decide:

**Option A: Accept discrete time**
- Remove density requirement
- Time is fundamentally discrete, continuum is approximation
- Simpler mathematics

**Option B: Change ActualizationEvent structure**
- Replace `id : ℕ` with `id : ℚ` or `id : ℝ`
- Allows density but requires more philosophical justification
- Why are there ℚ-many or ℝ-many actualizations?

**Option C: Two-level structure**
- Keep discrete actualizations (ℕ)
- Add interpolation/completion layer to get continuum
- Most faithful to "time emerges from discrete events"

---

## Appendix: Lean Code Sketch

```lean
-- Proposed changes to Step8_TemporalEmergence.lean

-- Replace axiom with definition
noncomputable def time_embedding : ActualizationEvent → Time :=
  fun e => (e.id : ℝ)

-- Derive strict monotonicity
theorem time_embedding_strict_mono : StrictMono time_embedding := by
  intro e₁ e₂ h
  simp only [time_embedding]
  exact Nat.cast_lt.mpr (show e₁.id < e₂.id from h)

-- Derive evolution_matches_actualization
theorem evolution_matches_actualization
    (U : UnitaryGroup (H := H))
    (e₁ e₂ : ActualizationEvent) :
    U.U (eventTime e₂) = U.U (eventTime e₂ - eventTime e₁) * U.U (eventTime e₁) := by
  have h := U.group_mul (eventTime e₂ - eventTime e₁) (eventTime e₁)
  simp only [sub_add_cancel] at h
  exact h

-- REMOVE time_embedding_dense entirely
-- It cannot be satisfied with ℕ-indexed events
```

---

## Conclusion

Three of the four Step 8 temporal axioms can be converted to theorems or definitions with straightforward proofs. The fourth (`time_embedding_dense`) is mathematically impossible as stated and requires either removal or reconceptualization.

This analysis reduces the Step 8 axiom count from 4 to potentially 0-1, depending on how the density question is resolved architecturally.
