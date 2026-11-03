/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSpace
public import ElboimSly.Frozen.Defs.Good
public import ElboimSly.Frozen.Defs.IsBackwardTrajectory
public import ElboimSly.Frozen.Defs.IsForwardTrajectory
public import ElboimSly.Frozen.Defs.RingSpace
public import ElboimSly.Provider.ExistsUniqueTrajectories
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

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- Existence and uniqueness of forward and backward trajectories for good configurations: the
well-definedness theorem of D16. In the half-line encoding of `IsForwardPath` and
`IsBackwardPath`, `γ s` is the position at time `a + s` and `η s` the position at time `b - s`.
Existence and uniqueness of trajectories, first two sentences only. The third sentence (a `ν`-path on `[a, b]`
is determined by its value at `a`, and also by its value at `b`) is not part of this statement. -/
theorem existsUnique_trajectories (ν : Measure (RingSpace d β)) (hν : Good ν) :
    (∀ (x : Fin d → ℤ) (a : ℝ), ∃! γ : ℝ≥0 → Fin d → ℤ, IsForwardTrajectory ν x a γ) ∧
    (∀ (y : Fin d → ℤ) (b : ℝ), ∃! η : ℝ≥0 → Fin d → ℤ, IsBackwardTrajectory ν y b η) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ElboimSly.Provider.existsUniqueTrajectories
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ElboimSly

end
-- FROZEN_ANCHOR_SUFFIX_END
