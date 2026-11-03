/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# IndScale

Constants, scales, failure bounds (ES22 §3).
-/

public section

namespace ElboimSly

/-- The time scale `t_n := 4ⁿ t₀`. Constants, scales, failure bounds. The written proof's restriction
`t₀ ∈ (1, 4]` sits on the quantifier in `IndHyp` and the main theorem, not on this function. -/
@[expose] noncomputable def indScale (t₀ : ℝ) (n : ℕ) : ℝ := 4 ^ n * t₀

end ElboimSly

end
