/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.EdgeInstMeasurableSpace
public import ElboimSlyChallenges.ElboimSly.Defs.Good
public import ElboimSlyChallenges.ElboimSly.Defs.IsBackwardTrajectory
public import ElboimSlyChallenges.ElboimSly.Defs.IsForwardTrajectory
public import ElboimSlyChallenges.ElboimSly.Defs.RingSpace
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# ExistsUniqueTrajectories

Existence and uniqueness of trajectories.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

/-- Existence and uniqueness of forward and backward trajectories for good configurations: the
well-definedness theorem of D16. In the half-line encoding of `IsForwardPath` and
`IsBackwardPath`, `γ s` is the position at time `a + s` and `η s` the position at time `b - s`.
Existence and uniqueness of trajectories, first two sentences only. The third sentence (a `ν`-path on `[a, b]`
is determined by its value at `a`, and also by its value at `b`) is not part of this statement. -/
theorem existsUnique_trajectories (ν : Measure (RingSpace d β)) (hν : Good ν) :
    (∀ (x : Fin d → ℤ) (a : ℝ), ∃! γ : ℝ≥0 → Fin d → ℤ, IsForwardTrajectory ν x a γ) ∧
    (∀ (y : Fin d → ℤ) (b : ℝ), ∃! η : ℝ≥0 → Fin d → ℤ, IsBackwardTrajectory ν y b η) :=
  sorry

end ElboimSly

end
