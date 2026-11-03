/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSpace
public import ElboimSly.Frozen.Defs.IsForwardPath
public import ElboimSly.Frozen.Defs.RingSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# IsForwardTrajectory

ν-paths.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

/-- A forward trajectory from `(x, a)`: a forward `ν`-path with `γ 0 = x`.
ν-paths. -/
@[expose] def IsForwardTrajectory (ν : Measure (RingSpace d β)) (x : Fin d → ℤ) (a : ℝ)
    (γ : ℝ≥0 → Fin d → ℤ) : Prop :=
  IsForwardPath ν a γ ∧ γ 0 = x

end ElboimSly

end
