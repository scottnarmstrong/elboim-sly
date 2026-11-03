/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.RegenCount
public import Mathlib.Basic.Real.Basic

/-!
# RegenStart

Regenerated cyclic walk (`α(t) = σ_{𝔑_t}`, ES22 §2).
-/

public section

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `α(t) := σ_{𝔑_t}`, the last regeneration time at or before `t` (real-valued; finite since
`σ_{𝔑_t} ≤ t`). Regenerated cyclic walk. -/
@[expose] noncomputable def regenStart (ν : ℕ → MeasureTheory.Measure (RingSpace d β)) (t : ℝ) : ℝ :=
  (regenSigma ν (regenCount ν t)).toReal

end ElboimSly

end
