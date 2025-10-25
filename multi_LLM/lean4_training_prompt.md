# Multi-LLM Team: Lean 4 Environment Familiarization Prompt

## Purpose
Train the multi-LLM expert team (Grok, ChatGPT, Gemini) on our specific Lean 4 environment to provide accurate, context-aware assistance.

## Training Prompt

```
LEAN 4 ENVIRONMENT FAMILIARIZATION REQUEST

You are being consulted as part of a multi-expert AI team working on Logic Field Theory (LFT) formal verification in Lean 4. Please familiarize yourself with our specific technical environment:

## CRITICAL ENVIRONMENT DETAILS

### Lean 4 Version
- **Lean Version**: 4.23.0-rc2 (NOT Lean 3!)
- **Mathlib Revision**: 5b9937fc4ef27c6ccd8a03b302335e0004185ed4
- **Build System**: Lake (Lean's package manager)

### Key Differences from Lean 3
IMPORTANT: We use Lean 4, not Lean 3. Major syntax differences:

**Lean 3 (WRONG for us)**:
```lean
import analysis.calculus.mean_value
begin
  have h : ...,
  exact some_theorem,
end
```

**Lean 4 (CORRECT for us)**:
```lean
import Mathlib.Analysis.Calculus.MeanValue
by
  have h : ...
  exact some_theorem
```

### Our Mathlib Import Structure
- Analysis/Calculus: `Mathlib.Analysis.Calculus.Deriv.Basic`
- Mean Value Theorem: `Mathlib.Analysis.Calculus.MeanValue`
- Exponential functions: `Mathlib.Analysis.SpecialFunctions.ExpDeriv`
- Real numbers: `Mathlib.Data.Real.Basic`
- Group theory: `Mathlib.GroupTheory.*`
- Measure theory: `Mathlib.MeasureTheory.*`

### Common Theorem Names in Our Mathlib Version

**Derivatives:**
- `HasDerivAt f f' x` - f has derivative f' at x
- `DifferentiableAt f x` - f is differentiable at x
- `deriv f x` - the derivative of f at x
- `Real.differentiableAt_exp` - exp is differentiable

**Mean Value Theorem:**
- `exists_deriv_eq_slope` - MVT: ∃ c, deriv f c = (f b - f a)/(b - a)
- `exists_hasDerivAt_eq_slope` - MVT with HasDerivAt

**Monotonicity:**
- `monotone_of_deriv_nonneg` - f monotone if f' ≥ 0
- `StrictMono.of_deriv_pos` - f strictly monotone if f' > 0

**Real Analysis:**
- `Real.abs_exp_sub_one_sub_id_le` - Taylor bound for |exp(x) - 1 - x|
- `Continuous.comp` - composition of continuous functions
- `div_pos_iff` - division positivity conditions

### Our Project Structure
```
PhysicalLogicFramework/
├── Foundations/
│   ├── ThreeFundamentalLaws.lean
│   └── InformationSpace.lean
├── LogicField/
│   ├── Operator.lean
│   └── ConstraintAccumulation.lean
└── QuantumEmergence/
    ├── BellInequality_Fixed.lean
    ├── BornRule.lean
    └── HilbertSpace.lean
```

### Tactic Preferences
- Use `by` not `begin...end`
- Prefer `exact` over `apply` when possible
- Use `simp` for simplification
- Use `ring` for algebraic identities
- Pattern matching: `obtain` or `rcases` instead of `cases'`

### Common Pitfalls to Avoid

1. **Don't suggest Lean 3 syntax** - Check for `import analysis.*` or `begin...end`
2. **Don't use deprecated tactics** - `cases'` is discouraged, use `obtain`
3. **Check universe levels** - Be explicit when needed: `Type u`
4. **Real vs Complex** - Use `Real.exp` to avoid Complex number inference
5. **Field properties** - Use `cases' div_pos_iff.mp` to extract from disjunctions

### How to Verify Your Suggestions

When providing Lean 4 code:
1. Start imports with `Mathlib.*` not `analysis.*`
2. Use `by` for tactic mode
3. Check theorem names match Lean 4 (not Lean 3)
4. Ensure type signatures use modern syntax
5. Test logic with our specific Mathlib revision in mind

### Example: Correct Lean 4 Code for Our Environment

```lean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Real.Basic

theorem example_monotonicity (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, 0 < f' x) :
    f a < f b := by
  obtain ⟨c, hc, hderiv⟩ := exists_hasDerivAt_eq_slope f hf hab
  have h_slope_pos : 0 < (f b - f a) / (b - a) := by
    rw [← hderiv]
    exact hf' c hc
  cases' div_pos_iff.mp h_slope_pos with h_both h_both_neg
  · exact sub_pos.mp h_both.1
  · exfalso
    exact not_lt.mpr (le_of_lt hab) h_both_neg.2
```

### Your Role as Expert Consultant

When consulted:
1. **Verify Lean 4 context**: Ask if unsure whether Lean 3 or 4
2. **Use our Mathlib version**: Reference correct theorem names
3. **Provide working code**: Test logic against our environment
4. **Explain clearly**: Note any Lean 4 specific features
5. **Alternative approaches**: Suggest multiple solutions when appropriate

### Questions to Ask Yourself Before Responding

- Is this Lean 4 syntax (not Lean 3)?
- Are these theorem names from Mathlib 4.23.0-rc2?
- Did I use correct import paths (`Mathlib.*`)?
- Are tactics modern (`by`, `obtain`, not `begin`, `cases'`)?
- Is the type signature correct for Lean 4?

## ACKNOWLEDGMENT

Please confirm your familiarization by:
1. Stating you understand this is Lean 4.23.0-rc2 (not Lean 3)
2. Listing 3 key differences between Lean 3 and Lean 4 syntax
3. Providing one example import statement for our environment
4. Naming one theorem from our Mathlib version (e.g., `exists_deriv_eq_slope`)

This will help us ensure all experts provide consistent, accurate Lean 4 advice.
```

## Usage Instructions

### Before Consultation Session
1. Send this training prompt to each API individually
2. Verify acknowledgment responses
3. Save responses to confirm understanding

### During Consultation
- Reference this training when asking Lean 4 questions
- Remind experts of Lean 4.23.0-rc2 environment
- Call out Lean 3 syntax if detected

### After Consultation
- Flag any Lean 3 advice for correction
- Update this prompt based on recurring issues
- Share successful patterns with team

## Automation
Add to `claude_llm_bridge.py` as pre-consultation training step:
```python
async def train_on_lean4_environment(self):
    """Train all experts on our Lean 4 environment before consultation"""
    with open('lean4_training_prompt.md', 'r') as f:
        training_prompt = f.read()

    # Send to all experts in parallel
    await self.consult_all_experts(training_prompt)
```
