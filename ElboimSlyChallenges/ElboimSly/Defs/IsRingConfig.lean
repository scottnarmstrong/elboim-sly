/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.EdgeInstMeasurableSpace
public import ElboimSlyChallenges.ElboimSly.Defs.RingSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# IsRingConfig

Ring configurations.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

/-- A *ring configuration*: a measure on `S_β` with values in `ℕ ∪ {∞}`.
Ring configurations. -/
@[expose] def IsRingConfig (ν : Measure (RingSpace d β)) : Prop :=
  ∀ A : Set (RingSpace d β), MeasurableSet A → ν A = ∞ ∨ ∃ n : ℕ, ν A = n

end ElboimSly

end
