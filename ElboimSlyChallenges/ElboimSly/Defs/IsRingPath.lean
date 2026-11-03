/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.Edge
public import ElboimSlyChallenges.ElboimSly.Defs.EdgeInstMeasurableSpace
public import ElboimSlyChallenges.ElboimSly.Defs.RingSpace
public import ElboimSlyChallenges.ElboimSly.Defs.Rings
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# IsRingPath

Ring paths.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

/-- A `ν`-ring path of length `n` in `I`: vertices `v₀, …, vₙ`, strictly increasing times
`t₁ < ⋯ < tₙ` in `I`, such that the edge `{v_{i-1}, v_i}` rings at `t_i`.
Ring paths. -/
@[expose] def IsRingPath (ν : Measure (RingSpace d β)) (I : Set ℝ) (n : ℕ)
    (v : Fin (n + 1) → (Fin d → ℤ)) (t : Fin n → ℝ) : Prop :=
  StrictMono t ∧ (∀ i, t i ∈ I) ∧
    ∀ i : Fin n, ∃ e : Edge d, e.1 = s(v i.castSucc, v i.succ) ∧ Rings ν e (t i)

end ElboimSly

end
