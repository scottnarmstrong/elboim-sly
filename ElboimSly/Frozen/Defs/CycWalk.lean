/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSpace
public import ElboimSly.Frozen.Defs.IsBackwardTrajectory
public import ElboimSly.Frozen.Defs.IsForwardTrajectory
public import ElboimSly.Frozen.Defs.RingSpace
public import Mathlib.Basic.Real.Basic

/-!
# CycWalk

Cyclic walk (ES22 §2, ES22 §3, ES22 §5).
-/

public section

open scoped NNReal

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The cyclic walk `W^ν_{u,q}` started at `u` at cyclic time `q`, as a function of `s : ℝ`.
Cyclic walk. In the half-line encoding of the frozen trajectories (`γ s` is the position
at time `q + s`, `η s` the position at time `q - s`):
`W^ν_{u,q}(s) = γ^ν_{u,q}(q+s)` for `s ≥ 0` is `γ s`, and `W^ν_{u,q}(s) = η^ν_{u,q}(q+s)` for `s ≤ 0`
is `η (-s)`. Following D16, `γ` and `η` are the trajectories of `IsForwardTrajectory ν u q`
and `IsBackwardTrajectory ν u q`, chosen with `Classical.epsilon`. On `Good ν` they exist and are
unique (`ElboimSly.existsUnique_trajectories`), so the choice is the trajectory. Off `Good ν`
the value is an arbitrary junk value that no statement uses (the environments are a.s. good). -/
@[expose] noncomputable def cycWalk (ν : MeasureTheory.Measure (RingSpace d β)) (u : Fin d → ℤ)
    (q : ℝ) (s : ℝ) : Fin d → ℤ :=
  if 0 ≤ s then
    Classical.epsilon (fun γ : ℝ≥0 → Fin d → ℤ => IsForwardTrajectory ν u q γ) s.toNNReal
  else
    Classical.epsilon (fun η : ℝ≥0 → Fin d → ℤ => IsBackwardTrajectory ν u q η) (-s).toNNReal

end ElboimSly

end
