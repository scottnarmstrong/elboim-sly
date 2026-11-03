/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.EdgeInstMeasurableSpace
public import ElboimSlyChallenges.ElboimSly.Defs.IsLeftLimit
public import ElboimSlyChallenges.ElboimSly.Defs.RingSpace
public import ElboimSlyChallenges.ElboimSly.Defs.SwapRule
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# IsForwardPath

ν-paths.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable (d : ℕ) (β : ℝ)
variable [Fact (0 < β)]
variable {d β}

/-- `γ` is a forward `ν`-path from time `a`: `γ s` is the position at time `a + s`, `s ≥ 0`.
It is right-continuous (for the discrete topology on `ℤᵈ`), has left limits at `s > 0`, has
finitely many discontinuities on bounded intervals, and obeys the swap rule (S) at every `s > 0`.
ν-paths for `J = [a, ∞)`. -/
@[expose] def IsForwardPath (ν : Measure (RingSpace d β)) (a : ℝ) (γ : ℝ≥0 → Fin d → ℤ) :
    Prop :=
  (∀ s, ∀ᶠ u in 𝓝[≥] s, γ u = γ s) ∧
  (∀ s : ℝ≥0, 0 < s → ∃ z, IsLeftLimit γ s z) ∧
  (∀ T : ℝ≥0, {s : ℝ≥0 | 0 < s ∧ s ≤ T ∧ ∃ z, IsLeftLimit γ s z ∧ z ≠ γ s}.Finite) ∧
  (∀ s : ℝ≥0, 0 < s → ∀ z, IsLeftLimit γ s z → SwapRule ν (a + s) z (γ s))

end ElboimSly

end
