/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IndHyp
public import ElboimSly.Frozen.Defs.IndScale
public import Mathlib

/-!
# The step regime

Step regime (ES22 §4 opening, ES22 §4).

`StepRegime d n₁ β n t₀` is `SR(n₁; β, n, t₀)`: `n₁ ≥ 8d`, `β > 1`, `n ≥ 1`, `t₀ ∈ (1, 4]`,
`t_n = 4ⁿ t₀ > β`, and `H(β, n', t₀')` holds for all integers `n₁ ≤ n' < n` and `t₀' ∈ (1, 4]`.

Also the level `n(s) = ⌈log₄ s⌉ - 1` and `t₀(s) = s / 4^{n(s)}` of a real `s > 1`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper

/-- Step regime. The step regime at base `n₁`. -/
def StepRegime (d n₁ : ℕ) (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ) : Prop :=
  8 * d ≤ n₁ ∧ 1 < β ∧ 1 ≤ n ∧ t₀ ∈ Ioc (1 : ℝ) 4 ∧ β < indScale t₀ n ∧
    ∀ n' : ℕ, n₁ ≤ n' → n' < n → ∀ t₀' ∈ Ioc (1 : ℝ) 4, IndHyp d β n' t₀'

/-- Constants, scales, failure bounds. `n(s) = ⌈log₄ s⌉ - 1`. -/
noncomputable def stepLevel (s : ℝ) : ℕ := ⌈Real.logb 4 s⌉₊ - 1

/-- Constants, scales, failure bounds. `t₀(s) = s / 4^{n(s)}`. -/
noncomputable def stepScale0 (s : ℝ) : ℝ := s / 4 ^ stepLevel s

end ElboimSly.Paper
