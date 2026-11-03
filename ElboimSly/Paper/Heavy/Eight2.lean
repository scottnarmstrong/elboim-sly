/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Eight1
public import ElboimSly.Paper.Heavy.SetsU

/-!
# Lemma 6.8, Step 6: every time in `U₁ ∩ U₂` is relaxed

ES22 Lemma 6.8, Step 6 (ES22 §6).
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} {w : ℝ → Fin d → ℤ}

theorem isHeavy_zero_iff_of_far {tst s r : ℝ} {x : Fin d → ℤ} (hx : x = w s) (_hs0 : tst ≤ s)
    (htst : 0 ≤ tst)
    (hfar : ∀ s' ∈ Ico (0 : ℝ) tst, r < ‖w s - w s'‖) :
    IsHeavy w 0 s x r ↔ IsHeavy w tst s x r := by
  unfold IsHeavy
  refine and_congr Iff.rfl ?_
  have : {v : Fin d → ℤ | ‖v - x‖ ≤ r} ∩ visitedSet w 0 s =
      {v : Fin d → ℤ | ‖v - x‖ ≤ r} ∩ visitedSet w tst s := by
    ext v
    constructor
    · rintro ⟨hv, s', hs', rfl⟩
      refine ⟨hv, s', ⟨?_, hs'.2⟩, rfl⟩
      by_contra hlt
      push Not at hlt
      have := hfar s' ⟨hs'.1, hlt⟩
      rw [hx] at hv
      rw [norm_sub_rev] at this
      exact absurd hv (not_le.2 this)
    · rintro ⟨hv, s', hs', rfl⟩
      exact ⟨hv, s', ⟨htst.trans hs'.1, hs'.2⟩, rfl⟩
  rw [this]

/-- ES22 Lemma 6.8, Step 6. -/
theorem eight_step6 (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 0 < β)
    (hβt : β < indScale t₀ n) (hT : HeavyT d n₀ E n) (hw : IsCyclicPath w) {t tk : ℝ}
    (hjump : ENNReal.ofReal t < pathTjumpCube w n)
    (htau : ENNReal.ofReal t < heavyTauPrime d t₀ n w) (_hr : tk = heavyTkPrime d t₀ n)
    (hCI : heavyTStar β tk t ∈ cycIntTimes β) {s : ℝ}
    (hs1 : s ∈ heavyU1 β tk w t) (hs2 : s ∈ heavyU2 β tk (indScale t₀ n) w t) :
    s ∈ relaxedTimes β w := by
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  have hst : heavyTStar β tk t ≤ s := hs2.1.1
  have hst0 : 0 ≤ heavyTStar β tk t := hCI.1
  have hs0 : 0 ≤ s := hst0.trans hst
  have hst_t : s ≤ t := hs2.1.2
  have htnβ : β ^ indDelta d ≤ indScale t₀ n ^ indDelta d :=
    Real.rpow_le_rpow hβ.le hβt.le hδ.le
  obtain ⟨hR1, hR2⟩ := hs1.2
  refine ⟨hs0, ?_, ?_⟩
  · intro r hr' hheavy
    by_cases hcase : indScale t₀ n ^ indDelta d ≤ r
    · refine es6_four hd ht1 ht4 hT hw hs0 ?_ ?_ (w s) hcase hheavy
      · exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst_t) hjump
      · exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst_t) htau
    · push Not at hcase
      have hfar : ∀ s' ∈ Ico (0 : ℝ) (heavyTStar β tk t), r < ‖w s - w s'‖ :=
        fun s' hs' => lt_trans hcase (hs2.2 s' hs')
      exact hR1 r hr' ((isHeavy_zero_iff_of_far rfl hst hst0 hfar).1 hheavy)
  · intro s'' h0 h1
    by_cases hc : heavyTStar β tk t ≤ s''
    · exact hR2 s'' hc h1
    · push Not at hc
      exact htnβ.trans (hs2.2 s'' ⟨h0, hc⟩).le

end ElboimSly.Paper
