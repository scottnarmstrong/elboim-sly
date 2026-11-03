/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.CycWalk
public import Mathlib.Basic.Real.Basic

/-!
# CycTreg

Closing time (ES22 §2, ES22 §3).
-/

public section

open scoped ENNReal

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The closing time `t_reg := inf {k β : k ∈ ℤ_{≥1}, W(kβ) = 0} ∈ βℤ_{≥1} ∪ {∞}` of the cyclic walk
`W = W^ν_{0,0}`. Closing time. Values in `ℝ≥0∞`; the infimum over the empty set is `∞`. -/
@[expose] noncomputable def cycTreg (ν : MeasureTheory.Measure (RingSpace d β)) : ℝ≥0∞ :=
  ⨅ k : {k : ℕ // 1 ≤ k ∧ cycWalk ν 0 0 ((k : ℝ) * β) = 0}, ENNReal.ofReal ((k.1 : ℝ) * β)

end ElboimSly

end
