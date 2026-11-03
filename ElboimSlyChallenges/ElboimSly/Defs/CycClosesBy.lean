/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.CycWalk
public import Mathlib.Basic.Real.Basic

/-!
# CycClosesBy

Closing time (second sentence; ES22 §3).
-/

public section

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `W_{u,q}` *closes by time* `t'`: `W_{u,q}(s) = u` for some `s ∈ βℤ ∩ (0, t']`.
Closing time; Reading choices (b). -/
@[expose] def cycClosesBy (ν : MeasureTheory.Measure (RingSpace d β)) (u : Fin d → ℤ) (q t' : ℝ) :
    Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) * β ≤ t' ∧ cycWalk ν u q ((k : ℝ) * β) = u

end ElboimSly

end
