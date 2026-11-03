/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.CycWalk
public import Mathlib.Basic.Real.Basic

/-!
# CycMerges

Merging of two walks (ES22 §3).
-/

public section

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The walks `W_1 := W_{u₁,q₁}` and `W_2 := W_{u₂,q₂}` *merge by time* `t'`: there are
`s₁, s₂ ∈ [0, t']` with `(s₁ + q₁) - (s₂ + q₂) ∈ βℤ` and `W₁(s₁) = W₂(s₂)`.
Merging of two walks. -/
@[expose] def cycMerges (ν : MeasureTheory.Measure (RingSpace d β)) (u₁ u₂ : Fin d → ℤ)
    (q₁ q₂ t' : ℝ) : Prop :=
  ∃ s₁ s₂ : ℝ, s₁ ∈ Set.Icc 0 t' ∧ s₂ ∈ Set.Icc 0 t' ∧
    (∃ k : ℤ, (s₁ + q₁) - (s₂ + q₂) = (k : ℝ) * β) ∧ cycWalk ν u₁ q₁ s₁ = cycWalk ν u₂ q₂ s₂

end ElboimSly

end
