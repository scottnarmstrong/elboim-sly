/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lem71Main
public import ElboimSly.Paper.Step.Cor72Proof
public import Mathlib

/-!
# Corollary 7.2, conditional on Theorem 6.1

ES22 Corollary 7.2.

`stepCor72_of_es61`: if `StepEs61 d c₆ β₆` (the conclusion of ES22 Theorem 6.1, isolated), then
`StepCor72 d c β_cat` (the statement of `Cor72.lean`) for some `c > 0` and threshold `β_cat`.
Once ES22 Theorem 6.1 is available (`wip/paper-heavy-2`), `StepEs61` is discharged from it by the
translation between relaxed times of the environment and of the driven walk.
-/

@[expose] public section

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

theorem stepCor72_of_es61 {d : ℕ} (hd5 : 5 ≤ d) {c6 : ℝ} (hc6 : 0 < c6) {β6 : ℕ → ℝ}
    (H6 : StepEs61 d c6 β6) : ∃ c : ℝ, 0 < c ∧ ∃ βCat : ℕ → ℝ, StepCor72 d c βCat := by
  obtain ⟨c, hc, βCat, h⟩ := stepLem71_of_es61 hd5 hc6 H6
  exact ⟨c, hc, βCat, stepCor72_of_lem71 h⟩

end ElboimSly.Paper.Step
