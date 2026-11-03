/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Basic.Real.Basic

/-!
# ScaleIndex

Constants, scales, failure bounds (`n(t)`), used by relaxed path.
-/

public section

namespace ElboimSly

/-- The scale index `n(t) := ⌈log₄ t⌉ - 1` of a real `t > 1`, so that `t ∈ (4^{n(t)}, 4^{n(t)+1}]`
and `t_n` has `n(t_n) = n`. Constants, scales, failure bounds. Natural subtraction is harmless: it is
used only for `t > 1`, where `⌈log₄ t⌉ ≥ 1`. -/
@[expose] noncomputable def scaleIndex (t : ℝ) : ℕ := ⌈Real.logb 4 t⌉₊ - 1

end ElboimSly

end
