/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.IsRelaxedTimeWrt
public import ElboimSlyChallenges.ElboimSly.Defs.RegenWalk
public import Mathlib.Basic.Real.Basic

/-!
# IsRelaxedTime

Relaxed times (regenerated-walk form).
-/

public section

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- For the regenerated walk, `t` is *relaxed* if it is relaxed with respect to `W|[α(t), t]`.
Relaxed times. -/
@[expose] noncomputable def IsRelaxedTime (ν : ℕ → MeasureTheory.Measure (RingSpace d β)) (t : ℝ) :
    Prop :=
  IsRelaxedTimeWrt β (regenWalk ν) (regenStart ν t) t

end ElboimSly

end
