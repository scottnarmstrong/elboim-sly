/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Provider.IndMain
public import ElboimSly.Frozen.Defs.IndHyp
public import Mathlib.Basic.Real.Basic

/-!
# IndMain

ES22 Theorem 3.2 (§3).
-/

public section

namespace ElboimSly

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- Theorem 3.2, with the index range explicit. For every `d ≥ 5` there are `β₀` and `n₀ ≥ 10` such that
`H(β, n, t₀)` holds for all `β ≥ β₀`, all `n ≥ n₀` and all `t₀ ∈ (1, 4]`. (`β > 0` is the instance
`[Fact (0 < β)]`, D19.) **Deviations:** F03 (`n₀ ≥ 10` explicit) and D11 (`θ_H = 41/100` in (H4)).
ES22 Theorem 3.2. -/
theorem ind_main (d : ℕ) (hd : 5 ≤ d) :
    ∃ β₀ : ℝ, ∃ n₀ : ℕ, 10 ≤ n₀ ∧
      ∀ (β : ℝ) [Fact (0 < β)], β₀ ≤ β → ∀ n : ℕ, n₀ ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
        IndHyp d β n t₀ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ElboimSly.Provider.indMain
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ElboimSly

end
-- FROZEN_ANCHOR_SUFFIX_END
