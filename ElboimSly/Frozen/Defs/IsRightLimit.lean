/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# IsRightLimit

ν-paths.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable {d : ℕ}

/-- `z` is the limit of `η` from the right at `s` (the left limit in the reversed time). -/
@[expose] def IsRightLimit (η : ℝ≥0 → Fin d → ℤ) (s : ℝ≥0) (z : Fin d → ℤ) : Prop :=
  ∀ᶠ u in 𝓝[>] s, η u = z

end ElboimSly

end
