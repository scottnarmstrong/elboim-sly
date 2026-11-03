/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Algebra.Order.Interval.Set.Instances
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# WalkPath

Brownian coupling at a time (path space; D17).
-/

public section

open scoped NNReal

namespace ElboimSly

/-- The walk path space on `[0, T]`: the right-continuous, piecewise-constant paths
`w : [0, T] → ℤ^d` with finitely many jumps, i.e. there is a finite set `F` of jump times such that
`w s = w u` whenever `s ≤ u` and no element of `F` lies in `(s, u]`. The `σ`-algebra is the one induced
from the product (cylinder) `σ`-algebra on `[0,T] → ℤ^d`, as in the source ("law on the cylinder
`σ`-algebra"). Brownian coupling at a time, D17. -/
@[reducible, expose] def WalkPath (d : ℕ) (T : ℝ≥0) : Type :=
  {w : Set.Icc (0 : ℝ≥0) T → Fin d → ℤ //
    ∃ F : Finset ℝ≥0, ∀ s u : Set.Icc (0 : ℝ≥0) T, s ≤ u → (∀ r ∈ F, ¬ ((s : ℝ≥0) < r ∧ r ≤ u)) →
      w s = w u}

end ElboimSly

end
