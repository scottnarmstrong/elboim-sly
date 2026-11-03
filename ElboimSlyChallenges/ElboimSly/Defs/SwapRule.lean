/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.Edge
public import ElboimSlyChallenges.ElboimSly.Defs.EdgeInstMeasurableSpace
public import ElboimSlyChallenges.ElboimSly.Defs.EdgeMem
public import ElboimSlyChallenges.ElboimSly.Defs.RingSpace
public import ElboimSlyChallenges.ElboimSly.Defs.Rings
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# SwapRule

ν-paths.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

/-- The swap rule (S) at the real time `t`, given the pre-jump position `z` and post-jump
position `w`: if an edge containing `z` rings at `t` then `w` is its other endpoint; if no edge
containing `z` rings at `t` then `w = z`. ν-paths. -/
@[expose] def SwapRule (ν : Measure (RingSpace d β)) (t : ℝ) (z w : Fin d → ℤ) : Prop :=
  (∀ e : Edge d, e.Mem z → Rings ν e t → e.1 = s(z, w)) ∧
  ((¬ ∃ e : Edge d, e.Mem z ∧ Rings ν e t) → w = z)

end ElboimSly

end
