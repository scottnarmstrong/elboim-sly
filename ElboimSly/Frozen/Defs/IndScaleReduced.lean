/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IndScale
public import Mathlib.Basic.Real.Basic

/-!
# IndScaleReduced

Constants, scales, failure bounds.
-/

public section

namespace ElboimSly

/-- The reduced time scale `t'_n := t_n / n⁴` (the written proof uses it for `n ≥ 1`).
Constants, scales, failure bounds. -/
@[expose] noncomputable def indScaleReduced (t₀ : ℝ) (n : ℕ) : ℝ := indScale t₀ n / (n : ℝ) ^ 4

end ElboimSly

end
