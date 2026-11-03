/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.SigmaClaim
public import ElboimSly.Paper.Step.Lemma77
public import ElboimSly.Paper.Step.Cor72Final
public import Mathlib

/-!
# Lemmas 7.3, 7.4, 7.6, 7.7 from Corollary 7.2

ES22 Lemma 7.3; ES22 Lemma 7.4; ES22 Lemma 7.6; ES22 Lemma 7.7. Each is derived from `StepCor72`;
`*_of_es61` chains to `stepCor72_of_es61`, so they depend only on `StepEs61` (Theorem 6.1).
-/

@[expose] public section

namespace ElboimSly.Paper.Step

variable {d : ℕ}

/-- Lemmas 7.3, 7.4, 7.6, 7.7 together, from `StepCor72`. -/
theorem step_lemmas_of_cor72 (hd : 1 ≤ d) {cCat : ℝ} (hc : 0 < cCat) {βCat : ℕ → ℝ}
    (hCor : StepCor72 d cCat βCat) :
    (∃ cTf, 0 < cTf ∧ ∃ βTf, StepTf d cTf βTf) ∧ (∃ cTr, 0 < cTr ∧ ∃ βTr, StepTr d cTr βTr) ∧
    (∃ cBm, 0 < cBm ∧ ∃ βBm, StepBm d cBm βBm) ∧ ∃ βTp, StepTp d βTp := by
  obtain ⟨cTr, hcTr, βTr, hTr⟩ := step_lemma74_of_cor72 hd hc hCor
  obtain ⟨cBm, hcBm, βBm, hBm⟩ :=
    step_lemma76_of_cor72_sigma hd hc hCor hcTr hTr (step_sigma_claim_of_tr hd hcTr hTr)
  exact ⟨step_lemma73_of_cor72 hd hc hCor, ⟨cTr, hcTr, βTr, hTr⟩, ⟨cBm, hcBm, βBm, hBm⟩,
    step_lemma77_of_cor72_bm hd hc hCor hcBm hBm⟩

/-- The same from `StepEs61` (Theorem 6.1 for the driven walk), `d ≥ 5`. -/
theorem step_lemmas_of_es61 (hd5 : 5 ≤ d) {c6 : ℝ} (hc6 : 0 < c6) {β6 : ℕ → ℝ}
    (H6 : StepEs61 d c6 β6) :
    (∃ cTf, 0 < cTf ∧ ∃ βTf, StepTf d cTf βTf) ∧ (∃ cTr, 0 < cTr ∧ ∃ βTr, StepTr d cTr βTr) ∧
    (∃ cBm, 0 < cBm ∧ ∃ βBm, StepBm d cBm βBm) ∧ ∃ βTp, StepTp d βTp := by
  obtain ⟨c, hc, βCat, hCor⟩ := stepCor72_of_es61 hd5 hc6 H6
  exact step_lemmas_of_cor72 (by omega) hc hCor

end ElboimSly.Paper.Step
