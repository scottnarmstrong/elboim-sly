/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.RegenStart
public import Mathlib.Basic.Real.Basic

/-!
# RegenWalk

Regenerated cyclic walk (ES22 §2).
-/

public section

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated cyclic walk built from the environments `ν 0, ν 1, …` (piece `k + 1` uses `ν k`):
`W(s) := W^{(i)}(s - σ_{i-1})` for `s ∈ [σ_{i-1}, σ_i)`. With `𝔑_t = i - 1` this is
`cycWalk (ν 𝔑_t) 0 0 (t - α(t))`. If `t_reg^{(i)} = ∞` then `σ_i = ∞` and `W` follows `W^{(i)}`
forever, as in the source. Only `t ≥ 0` is meaningful. Regenerated cyclic walk (construction (i),
from i.i.d. environments; the constructions of the regenerated walk shows the other constructions have the same law). -/
@[expose] noncomputable def regenWalk (ν : ℕ → MeasureTheory.Measure (RingSpace d β)) (t : ℝ) :
    Fin d → ℤ :=
  cycWalk (ν (regenCount ν t)) 0 0 (t - regenStart ν t)

end ElboimSly

end
