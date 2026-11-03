/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# IndDelta

Constants, scales, failure bounds (ES22 §3).
-/

public section

namespace ElboimSly

/-- The exponent `δ := 1 / (3000 d²)` (`= ε / (10 d)` with `ε = 1 / (300 d)`).
Constants, scales, failure bounds. The constant `ε` is used by no statement in gate G1 and is not defined. -/
@[expose] noncomputable def indDelta (d : ℕ) : ℝ := 1 / (3000 * (d : ℝ) ^ 2)

end ElboimSly

end
