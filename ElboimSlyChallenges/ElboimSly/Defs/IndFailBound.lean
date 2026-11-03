/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.IndScale
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Basic.Real.Basic

/-!
# IndFailBound

Constants, scales, failure bounds (ES22 §3).
-/

public section

namespace ElboimSly

/-- The failure bound `p_n(β, t₀)`: `exp(-n³)` if `t_n < β`, and `exp(-n²)` if `t_n ≥ β`.
Constants, scales, failure bounds. The case split is the source's definition. -/
@[expose] noncomputable def indFailBound (β t₀ : ℝ) (n : ℕ) : ℝ :=
  if indScale t₀ n < β then Real.exp (-((n : ℝ) ^ 3)) else Real.exp (-((n : ℝ) ^ 2))

end ElboimSly

end
