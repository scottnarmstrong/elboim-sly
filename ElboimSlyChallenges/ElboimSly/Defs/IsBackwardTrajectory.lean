/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.EdgeInstMeasurableSpace
public import ElboimSlyChallenges.ElboimSly.Defs.IsBackwardPath
public import ElboimSlyChallenges.ElboimSly.Defs.RingSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# IsBackwardTrajectory

ν-paths.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

/-- A backward trajectory to `(y, b)`: a backward `ν`-path with `η 0 = y`.
ν-paths. -/
@[expose] def IsBackwardTrajectory (ν : Measure (RingSpace d β)) (y : Fin d → ℤ) (b : ℝ)
    (η : ℝ≥0 → Fin d → ℤ) : Prop :=
  IsBackwardPath ν b η ∧ η 0 = y

end ElboimSly

end
