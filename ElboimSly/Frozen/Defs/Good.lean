/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.Edge
public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSpace
public import ElboimSly.Frozen.Defs.IsRingConfig
public import ElboimSly.Frozen.Defs.IsRingPath
public import ElboimSly.Frozen.Defs.RingSet
public import ElboimSly.Frozen.Defs.RingSpace
public import ElboimSly.Frozen.Defs.RingWindow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Good

Good configurations.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

/-- Good configurations (G1)–(G3). Good configurations. -/
@[expose] def Good (ν : Measure (RingSpace d β)) : Prop :=
  IsRingConfig ν ∧
  -- (G1)
  (∀ e : Edge d, ν ({e} ×ˢ Set.univ) < ∞) ∧
  -- (G2)
  ((∀ e θ, ν {(e, θ)} ≤ 1) ∧ ∀ e f : Edge d, e ≠ f → Disjoint (ringSet ν e) (ringSet ν f)) ∧
  -- (G3)
  ∀ (y : Fin d → ℤ) (j : ℤ), ∃ n : ℕ,
    (¬ ∃ (v : Fin (n + 1) → (Fin d → ℤ)) (t : Fin n → ℝ),
        v 0 = y ∧ IsRingPath ν (ringWindow β j) n v t) ∧
    (¬ ∃ (v : Fin (n + 1) → (Fin d → ℤ)) (t : Fin n → ℝ),
        v (Fin.last n) = y ∧ IsRingPath ν (ringWindow β j) n v t)

end ElboimSly

end
