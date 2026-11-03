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
# IsLeftLimit

ν-paths.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable {d : ℕ}

/-- `z` is the left limit of `γ` at `s` (for the discrete topology on `ℤᵈ`; meaningful for
`s > 0`, where `𝓝[<] s` is nontrivial, hence `z` is unique). -/
@[expose] def IsLeftLimit (γ : ℝ≥0 → Fin d → ℤ) (s : ℝ≥0) (z : Fin d → ℤ) : Prop :=
  ∀ᶠ u in 𝓝[<] s, γ u = z

end ElboimSly

end
