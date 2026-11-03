/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.CycClosesBy
public import ElboimSlyChallenges.ElboimSly.Defs.CycMerges
public import Mathlib.Basic.Real.Basic

/-!
# CycOmega

Merging of two walks (the event `Ω(u₁,u₂,q₁,q₂;t')`, ES22 §3).
-/

public section

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The event `Ω(u₁, u₂, q₁, q₂; t')`, as a predicate of the environment `ν`: the walks `W_{u₁,q₁}` and
`W_{u₂,q₂}` do not merge by time `t'` and neither closes by time `t'`. Merging of two walks. -/
@[expose] def cycOmega (ν : MeasureTheory.Measure (RingSpace d β)) (u₁ u₂ : Fin d → ℤ)
    (q₁ q₂ t' : ℝ) : Prop :=
  ¬ cycMerges ν u₁ u₂ q₁ q₂ t' ∧ ¬ cycClosesBy ν u₁ q₁ t' ∧ ¬ cycClosesBy ν u₂ q₂ t'

end ElboimSly

end
