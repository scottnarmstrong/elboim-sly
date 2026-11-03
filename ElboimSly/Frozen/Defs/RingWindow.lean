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
# RingWindow

Ring paths.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

/-- The interval `I_j = [jβ/4, jβ/4 + β/2]`. Ring paths. -/
@[expose] def ringWindow (β : ℝ) (j : ℤ) : Set ℝ := Set.Icc (j * β / 4) (j * β / 4 + β / 2)

end ElboimSly

end
