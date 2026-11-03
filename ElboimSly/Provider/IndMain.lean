/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Induction.MainOfClaimJ
public import ElboimSly.Paper.Step.Lemma78ClaimJ
import Mathlib

/-!
# Provider for `IndMain`

Proof of the main theorem `ElboimSly.Frozen.Theorems.IndMain` (ES22 Theorem 3.2,
ES22 Theorem 3.2). The proof is `ElboimSly.Paper.Induction.ind_main_of_claimJ`: the induction base
(`ind_base`, ES22 §8) and the induction step (ES22 §4–§7, with the §5 interface
`heavyEscInterfaceAll_holds`), applied to the excursion claim of Lemma 7.8,
`ElboimSly.Paper.Step.step78_claimJ`.
-/

public section

namespace ElboimSly.Provider

/-- Theorem 3.2, with the index range explicit: for `d ≥ 5` there are `β₀` and `n₀ ≥ 10` such that
`H(β, n, t₀)` holds for all `β ≥ β₀`, `n ≥ n₀` and `t₀ ∈ (1, 4]`. ES22 Theorem 3.2. -/
theorem indMain {d : ℕ} (hd : 5 ≤ d := by assumption) :
    ∃ β₀ : ℝ, ∃ n₀ : ℕ, 10 ≤ n₀ ∧
      ∀ (β : ℝ) [Fact (0 < β)], β₀ ≤ β → ∀ n : ℕ, n₀ ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
        IndHyp d β n t₀ :=
  ElboimSly.Paper.Induction.ind_main_of_claimJ d hd (ElboimSly.Paper.Step.step78_claimJ hd)

end ElboimSly.Provider

end
