/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Induction.MainOfStep
public import ElboimSly.Paper.Step.Lemma78Final
public import ElboimSly.Paper.Escape.Es5IntFinal
public import Mathlib

/-!
# Theorem 3.2 from the excursion claim of Lemma 7.8

Composes `ind_main_of_interface` with the unconditional §5 interface `heavyEscInterfaceAll_holds`
and the assembled Lemma 7.8 `step_lemma78_of_interface_of_J`. The conclusion is the frozen
`ind_main` statement verbatim; the only remaining input is `Step78ClaimJ d`
(one excursion succeeds with probability at least frac12 with the `{J > n³}` form).
-/

@[expose] public section

namespace ElboimSly.Paper.Induction

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Step ElboimSly.Paper.Heavy

/-- **Theorem 3.2 conditional on Lemma 7.8's excursion claim.** The conclusion is the frozen
`ind_main` statement; the hypothesis is `Step78ClaimJ d`. -/
theorem ind_main_of_claimJ (d : ℕ) (hd : 5 ≤ d) (hJ : Step78ClaimJ d) :
    ∃ β₀ : ℝ, ∃ n₀ : ℕ, 10 ≤ n₀ ∧
      ∀ (β : ℝ) [Fact (0 < β)], β₀ ≤ β → ∀ n : ℕ, n₀ ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
        IndHyp d β n t₀ := by
  obtain ⟨E, hI⟩ := heavyEscInterfaceAll_holds hd
  obtain ⟨cPp, βPp, hPp⟩ := step_lemma78_of_interface_of_J hd E hI hJ
  exact ind_main_of_interface d hd E hI hPp

end ElboimSly.Paper.Induction

end
