/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# IndThetaH

Constants, scales, failure bounds; The (H4) exponent.
-/

public section

namespace ElboimSly

/-- The (H4) exponent `θ_H := 41/100`. **Deviation D11:** ES22 (ES22 §3) has `2/5`.
Constants, scales, failure bounds. -/
@[expose] noncomputable def indThetaH : ℝ := 41 / 100

end ElboimSly

end
