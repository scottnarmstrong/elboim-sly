/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.H1Lag
public import ElboimSly.Paper.Base.H1Det
public import ElboimSly.Paper.Base.Es8Constants
public import Mathlib

/-!
# (H1) at the base: the failure set of (R2) has measure at most `T/20`

ES22 Lemma 8.1, Step 3 (case `t_n ≥ β^{3δ}`).

* `h1LagEvent`: the lag event `{|T(B*)| ≥ t_*^{1-ζ³}}` (empty if `T < b³`).
* `h1_badTimes_volume_le`: outside the lag event, `|{R2 fails}| ≤ T/20`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Brownian

variable {d : ℕ}

/-- The lag event of Step 3, for `b = β^δ`: nonempty only if `T ≥ b³`. -/
def h1LagEvent {Ω : Type*} (d : ℕ) (b T : ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) : Set Ω :=
  {ω | b ^ 3 ≤ T ∧ ENNReal.ofReal ((T / (2 * b ^ 2)) ^ (1 - es8Zeta d ^ 3)) ≤
    nnLebesgue (sepSet (h1Scaled b B) 1 (Real.toNNReal ((T / (2 * b ^ 2)) ^ es8Zeta d))
      (Real.toNNReal (T / (2 * b ^ 2))) ω)}

theorem sepSet_mono_lag {Ω : Type*} {B : ℝ≥0 → Ω → Fin d → ℝ} {σ : ℝ} {L L' t : ℝ≥0}
    (h : L' ≤ L) (ω : Ω) : sepSet B σ L t ω ⊆ sepSet B σ L' t ω := by
  rintro s ⟨hs, s', hs', hn⟩
  exact ⟨hs, s', (add_le_add_right h s').trans hs', hn⟩

theorem rpow_delta_three (β : ℝ) (hβ : 0 < β) :
    β ^ (3 * indDelta d) = (β ^ indDelta d) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hβ.le]
  congr 1; push_cast; ring

theorem h1_badTimes_volume_le {Ω : Type*} (hd : 1 ≤ d) (B : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω)
    (γ : SRW.PathSpace d) (T : ℝ≥0) {n : ℕ} {β : ℝ} (hβ : 0 < β) (hTβ : (T : ℝ) ≤ β)
    (hb4 : 4 ≤ β ^ indDelta d) (hn : 2 * (n : ℝ) ^ 10 ≤ β ^ indDelta d)
    (hB3 : 20 ≤ (β ^ indDelta d / 2) ^ (es8Zeta d ^ 3))
    (hcpl : ∀ s : ℝ≥0, s ≤ T → ‖latR (γ s) - Real.sqrt 2 • B s ω‖ < (n : ℝ) ^ 10)
    (hno : ω ∉ h1LagEvent d (β ^ indDelta d) T B) :
    volume (h1BadTimes β T γ) ≤ ENNReal.ofReal ((T : ℝ) / 20) := by
  set b := β ^ indDelta d with hb
  have hb0 : 0 < b := by linarith
  have hb2 : 0 < 2 * b ^ 2 := by positivity
  have hT0 : (0 : ℝ) ≤ T := T.2
  by_cases hT3 : (T : ℝ) < b ^ 3
  · have : h1BadTimes β T γ = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun t ⟨ht, hfail⟩ => hfail fun s hs0 hs => ?_
      exfalso
      rw [rpow_delta_three β hβ] at hs
      linarith [ht.2]
    rw [this]; simp
  · push Not at hT3
    set ts : ℝ := (T : ℝ) / (2 * b ^ 2) with hts
    have hts_ge : b / 2 ≤ ts := by
      rw [hts, le_div_iff₀ hb2]; nlinarith [sq_nonneg b]
    have hts_pos : 0 < ts := by linarith
    have hts_le : ts ≤ β := by
      rw [hts, div_le_iff₀ hb2]
      have h2b : 1 ≤ 2 * b ^ 2 := by nlinarith
      exact hTβ.trans (le_mul_of_one_le_right hβ.le h2b)
    -- the lag set is small
    have hno' : nnLebesgue (sepSet (h1Scaled b B) 1 (Real.toNNReal (ts ^ es8Zeta d))
        (Real.toNNReal ts) ω) < ENNReal.ofReal (ts ^ (1 - es8Zeta d ^ 3)) := by
      by_contra hcon
      push Not at hcon
      exact hno ⟨hT3, hcon⟩
    -- `t_*^ζ ≤ b/2`
    have hz : 0 ≤ es8Zeta d := (es8Zeta_pos hd).le
    have hzle : ts ^ es8Zeta d ≤ b / 2 := by
      have h1 : ts ^ es8Zeta d ≤ β ^ es8Zeta d := Real.rpow_le_rpow hts_pos.le hts_le hz
      have hx : β ^ es8Zeta d * β ^ es8Zeta d = b := by
        rw [← Real.rpow_add hβ, hb]; congr 1; unfold es8Zeta; ring
      have hx0 : 0 ≤ β ^ es8Zeta d := Real.rpow_nonneg hβ.le _
      have hx2 : 2 ≤ β ^ es8Zeta d := by nlinarith
      nlinarith
    have hmono : sepSet (h1Scaled b B) 1 (b / 2).toNNReal (T / (2 * b ^ 2)).toNNReal ω ⊆
        sepSet (h1Scaled b B) 1 (Real.toNNReal (ts ^ es8Zeta d)) (Real.toNNReal ts) ω :=
      sepSet_mono_lag (Real.toNNReal_le_toNNReal hzle) ω
    -- the bad times
    have hBad : ∀ t ∈ h1BadTimes β T γ, 0 ≤ t ∧ t ≤ T ∧ ∃ s, 0 ≤ s ∧ s ≤ t - b ^ 3 ∧
        ‖γ t.toNNReal - γ s.toNNReal‖ < b := by
      rintro t ⟨ht, hfail⟩
      push Not at hfail
      obtain ⟨s, hs0, hs, hlt⟩ := hfail
      rw [rpow_delta_three β hβ] at hs
      refine ⟨ht.1, ht.2, s, hs0, hs, ?_⟩
      have hsT : s ≤ T := by linarith [pow_pos hb0 3, ht.2]
      have e1 : h1Walk T γ t = γ t.toNNReal := by
        simp only [h1Walk]
        rw [min_eq_left]
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1]; exact ht.2
      have e2 : h1Walk T γ s = γ s.toNNReal := by
        simp only [h1Walk]
        rw [min_eq_left]
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hsT
      rw [e1, e2] at hlt
      exact hlt
    have hvol := h1_bad_volume B ω γ T hb0 hn hcpl hBad
    have hlt : ENNReal.ofReal (2 * b ^ 2) * nnLebesgue (sepSet (h1Scaled b B) 1
        (b / 2).toNNReal (T / (2 * b ^ 2)).toNNReal ω) ≤
        ENNReal.ofReal (2 * b ^ 2) * ENNReal.ofReal (ts ^ (1 - es8Zeta d ^ 3)) :=
      mul_le_mul_right ((measure_mono hmono).trans hno'.le) _
    refine hvol.trans (hlt.trans ?_)
    rw [← ENNReal.ofReal_mul hb2.le]
    refine ENNReal.ofReal_le_ofReal ?_
    -- real arithmetic
    have hz3 : 0 ≤ es8Zeta d ^ 3 := by positivity
    have hge : 20 ≤ ts ^ (es8Zeta d ^ 3) :=
      hB3.trans (Real.rpow_le_rpow (by positivity) hts_ge hz3)
    have hpos : 0 < ts ^ (es8Zeta d ^ 3) := Real.rpow_pos_of_pos hts_pos _
    rw [Real.rpow_sub hts_pos, Real.rpow_one]
    have hmul : 2 * b ^ 2 * ts = T := by rw [hts]; field_simp
    calc 2 * b ^ 2 * (ts / ts ^ (es8Zeta d ^ 3)) = T / ts ^ (es8Zeta d ^ 3) := by
          rw [← hmul]; ring
      _ ≤ T / 20 := div_le_div_of_nonneg_left hT0 (by norm_num) hge

end ElboimSly.Paper

end
