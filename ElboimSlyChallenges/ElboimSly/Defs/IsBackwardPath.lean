/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.EdgeInstMeasurableSpace
public import ElboimSlyChallenges.ElboimSly.Defs.IsRightLimit
public import ElboimSlyChallenges.ElboimSly.Defs.RingSpace
public import ElboimSlyChallenges.ElboimSly.Defs.SwapRule
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# IsBackwardPath

ν-paths.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

/-- `η` is a backward `ν`-path from time `b`: `η s` is the position at time `b - s`, `s ≥ 0`.
In the time variable `t = b - s` the path is right-continuous (`s' ↑ s`), has left limits at every
`t ≤ b` (`s' ↓ s`), has finitely many discontinuities on bounded intervals, and obeys the swap
rule at every `t ≤ b`, with `z` the left limit in `t` (the limit of `η` from the right in `s`).
ν-paths for `J = (-∞, b]`. -/
@[expose] def IsBackwardPath (ν : Measure (RingSpace d β)) (b : ℝ) (η : ℝ≥0 → Fin d → ℤ) :
    Prop :=
  (∀ s, ∀ᶠ u in 𝓝[≤] s, η u = η s) ∧
  (∀ s : ℝ≥0, ∃ z, IsRightLimit η s z) ∧
  (∀ T : ℝ≥0, {s : ℝ≥0 | s ≤ T ∧ ∃ z, IsRightLimit η s z ∧ z ≠ η s}.Finite) ∧
  (∀ s : ℝ≥0, ∀ z, IsRightLimit η s z → SwapRule ν (b - s) z (η s))

end ElboimSly

end
