/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Asymp
public import ElboimSly.Paper.Escape.C56Main
public import Mathlib

/-!
# ES22 Claim 5.6: the numerical conditions hold for large `β`

ES22 Claim 5.6, "Choose `β_{56}` such that...".
-/

@[expose] public section

open Filter Topology Real
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.SRW ElboimSly.Brownian

theorem ev_theta : ∀ᶠ ρ : ℝ in atTop, (4864 / 10 * ρ ^ 2) ^ indThetaH ≤ ρ / 240 := by
  have h1 : Tendsto (fun x : ℝ => x ^ (0.18 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [h1.eventually_ge_atTop (240 * (4864 / 10 : ℝ) ^ indThetaH), eventually_gt_atTop 0]
    with ρ hρ hρ0
  have e1 : (4864 / 10 * ρ ^ 2) ^ indThetaH = (4864 / 10 : ℝ) ^ indThetaH * ρ ^ (0.82 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast ρ 2,
      ← Real.rpow_mul hρ0.le]
    congr 2
    unfold indThetaH; norm_num
  have e2 : ρ = ρ ^ (0.82 : ℝ) * ρ ^ (0.18 : ℝ) := by
    rw [← Real.rpow_add hρ0]; norm_num
  rw [e1]
  have hp : 0 < ρ ^ (0.82 : ℝ) := Real.rpow_pos_of_pos hρ0 _
  have : (4864 / 10 : ℝ) ^ indThetaH * ρ ^ (0.82 : ℝ) * 240 ≤ ρ := by
    calc (4864 / 10 : ℝ) ^ indThetaH * ρ ^ (0.82 : ℝ) * 240
        = ρ ^ (0.82 : ℝ) * (240 * (4864 / 10 : ℝ) ^ indThetaH) := by ring
      _ ≤ ρ ^ (0.82 : ℝ) * ρ ^ (0.18 : ℝ) := by gcongr
      _ = ρ := e2.symm
  linarith

theorem avoidLevel_ge {T : ℝ} (hT : 1 < T) : Real.logb 4 T - 1 ≤ (avoidLevel T : ℝ) := by
  obtain ⟨-, h2⟩ := avoidLevel_spec hT
  have : Real.logb 4 T ≤ ((avoidLevel T + 1 : ℕ) : ℝ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith), Real.rpow_natCast]; exact h2
  push_cast at this
  linarith

theorem eta_bound {β : ℝ} (hL : 0 ≤ Real.logb 4 (0.6 * Real.sqrt β) - 1) {T : ℝ}
    (hT : 0.6 * Real.sqrt β ≤ T) :
    Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2) ≤
      Real.exp (-(Real.logb 4 (0.6 * Real.sqrt β) - 1) ^ 2) := by
  have h4 : (1 : ℝ) ≤ Real.logb 4 (0.6 * Real.sqrt β) := by linarith
  have hpos : 0 < 0.6 * Real.sqrt β := by
    have hnn : 0 ≤ 0.6 * Real.sqrt β := by positivity
    rcases hnn.eq_or_lt with h | h
    · rw [← h, Real.logb_zero] at h4; norm_num at h4
    · exact h
  have h1 : 1 < T := by
    have h5 : (4 : ℝ) ≤ 0.6 * Real.sqrt β := by
      have := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 4) hpos).1 h4
      simpa using this
    linarith
  have hlev := avoidLevel_ge h1
  have hmono : Real.logb 4 (0.6 * Real.sqrt β) ≤ Real.logb 4 T :=
    Real.logb_le_logb_of_le (by norm_num) hpos hT
  apply Real.exp_le_exp.2
  have : Real.logb 4 (0.6 * Real.sqrt β) - 1 ≤ (avoidLevel T : ℝ) := by linarith
  nlinarith

theorem min_bound {β R : ℝ} (hβ : 1 ≤ β) (hR : 0 < R) (hR2 : R ≤ 3 * Real.sqrt β) :
    β ^ (0.1 : ℝ) / 24 ≤ min ((β ^ (0.3 : ℝ)) ^ 2 / (8 * R)) (β ^ (0.3 : ℝ) / 2) := by
  have hβ0 : 0 < β := by linarith
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have hid : (β ^ (0.3 : ℝ)) ^ 2 = β ^ (0.1 : ℝ) * Real.sqrt β := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβ0.le, Real.sqrt_eq_rpow, ← Real.rpow_add hβ0]
    norm_num
  have h01 : 0 < β ^ (0.1 : ℝ) := Real.rpow_pos_of_pos hβ0 _
  refine le_min ?_ ?_
  · rw [hid]
    calc β ^ (0.1 : ℝ) / 24 = β ^ (0.1 : ℝ) * Real.sqrt β / (24 * Real.sqrt β) := by
          field_simp
      _ ≤ β ^ (0.1 : ℝ) * Real.sqrt β / (8 * R) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          linarith
  · have : β ^ (0.1 : ℝ) ≤ β ^ (0.3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hβ (by norm_num)
    linarith

theorem sqrt_sqrt_le {β τ : ℝ} (_hβ : 0 < β) (hτ : τ ≤ 4 * Real.sqrt β) :
    Real.sqrt τ ≤ 2 * Real.sqrt (Real.sqrt β) := by
  calc Real.sqrt τ ≤ Real.sqrt (4 * Real.sqrt β) := Real.sqrt_le_sqrt hτ
    _ = 2 * Real.sqrt (Real.sqrt β) := by
      rw [Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [this]

theorem c0_ge (d : ℕ) {β τ : ℝ} (hβ : 0 < β) (hτ0 : 0 < τ) (hτ : τ ≤ 4 * Real.sqrt β) :
    cBox ^ (201 * d) / 4 ^ (201 * d * CBox) / (Real.sqrt (Real.sqrt β)) ^ (201 * d * CBox) / 2 ≤
      cBox ^ (201 * d) / (2 * Real.sqrt τ) ^ (201 * d * CBox) / 2 := by
  have hy : 0 < Real.sqrt (Real.sqrt β) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hβ)
  have hc := cBox_pos
  have h := sqrt_sqrt_le hβ hτ
  have e : cBox ^ (201 * d) / 4 ^ (201 * d * CBox) / (Real.sqrt (Real.sqrt β)) ^ (201 * d * CBox) / 2 =
      cBox ^ (201 * d) / (4 * Real.sqrt (Real.sqrt β)) ^ (201 * d * CBox) / 2 := by
    rw [mul_pow]; field_simp
  rw [e]
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  have : (2 * Real.sqrt τ) ^ (201 * d * CBox) ≤ (4 * Real.sqrt (Real.sqrt β)) ^ (201 * d * CBox) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  gcongr

theorem c1_ge (d : ℕ) {β τ : ℝ} (hβ : 0 < β) (hτ0 : 0 < τ) (hτ : τ ≤ 4 * Real.sqrt β) :
    cBox ^ d / 6 ^ (d * CBox) / (Real.sqrt (Real.sqrt β)) ^ (d * CBox) / 2 ≤
      cBox ^ d / (3 * Real.sqrt τ) ^ (d * CBox) / 2 := by
  have hy : 0 < Real.sqrt (Real.sqrt β) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hβ)
  have hc := cBox_pos
  have h := sqrt_sqrt_le hβ hτ
  have e : cBox ^ d / 6 ^ (d * CBox) / (Real.sqrt (Real.sqrt β)) ^ (d * CBox) / 2 =
      cBox ^ d / (6 * Real.sqrt (Real.sqrt β)) ^ (d * CBox) / 2 := by
    rw [mul_pow]; field_simp
  rw [e]
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  have : (3 * Real.sqrt τ) ^ (d * CBox) ≤ (6 * Real.sqrt (Real.sqrt β)) ^ (d * CBox) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  gcongr

theorem tendsto_yy : Tendsto (fun β : ℝ => Real.sqrt (Real.sqrt β)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop

theorem eta_eq {β : ℝ} (hβ : 0 < β) :
    Real.logb 4 (0.6 * Real.sqrt β) - 1 =
      2 / Real.log 4 * Real.log (Real.sqrt (Real.sqrt β)) + (Real.log 0.6 / Real.log 4 - 1) := by
  have hy : 0 < Real.sqrt (Real.sqrt β) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hβ)
  have hsq : Real.sqrt β = Real.sqrt (Real.sqrt β) ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [Real.logb]
  nth_rewrite 1 [hsq]
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast
  field_simp
  ring

theorem rpow_tenth {β : ℝ} (hβ : 0 < β) :
    β ^ (0.1 : ℝ) = Real.sqrt (Real.sqrt β) ^ (0.4 : ℝ) := by
  have hy : 0 < Real.sqrt (Real.sqrt β) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hβ)
  have h4 : Real.sqrt (Real.sqrt β) ^ 4 = β := by
    rw [show Real.sqrt (Real.sqrt β) ^ 4 = (Real.sqrt (Real.sqrt β) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hβ.le]
  nth_rewrite 1 [← h4]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
  norm_num

theorem asymp_conditions {d : ℕ} (hd : 1 ≤ d) (n₀ : ℕ) (C : ℝ) :
    ∃ B : ℝ, ∀ β : ℝ, B ≤ β →
      (1 ≤ β) ∧ (2 : ℝ) ^ 40 ≤ β ∧ (4 : ℝ) ^ n₀ < 0.6 * Real.sqrt β ∧
      (∀ ρ : ℝ, Real.sqrt (Real.sqrt β) / 16 ≤ ρ → (4864 / 10 * ρ ^ 2) ^ indThetaH ≤ ρ / 240) ∧
      (0 ≤ Real.logb 4 (0.6 * Real.sqrt β) - 1) ∧
      (escCstar d + 2 * Real.exp (-(Real.logb 4 (0.6 * Real.sqrt β) - 1) ^ 2) +
        C * β ^ (-indDelta d / 30) ≤ ctube d escKstar) ∧
      (∀ τ : ℝ, Real.sqrt β ≤ τ → τ ≤ 4 * Real.sqrt β →
        4 * (d : ℝ) * Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 /
          (8 * (((0.6 * τ).toNNReal : ℝ≥0) : ℝ))) (β ^ (0.3 : ℝ) / 2)) +
          Real.exp (-(Real.logb 4 (0.6 * Real.sqrt β) - 1) ^ 2) ≤
          cBox ^ (201 * d) / (2 * Real.sqrt τ) ^ (201 * d * CBox) / 2) ∧
      (∀ τ : ℝ, Real.sqrt β ≤ τ → τ ≤ 4 * Real.sqrt β → ∀ T' : ℝ≥0,
        0.3 * τ ≤ T' → (T' : ℝ) ≤ 0.5 * τ →
        4 * (d : ℝ) * Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 / (8 * (T' : ℝ)))
          (β ^ (0.3 : ℝ) / 2)) ≤ cBox ^ d / (3 * Real.sqrt τ) ^ (d * CBox) / 2) := by
  have hc := cBox_pos
  set A : ℝ := 2 / Real.log 4 with hA
  set B' : ℝ := Real.log 0.6 / Real.log 4 - 1 with hB'
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hApos : 0 < A := by positivity
  set a0 : ℝ := cBox ^ (201 * d) / 4 ^ (201 * d * CBox) with ha0
  set a1 : ℝ := cBox ^ d / 6 ^ (d * CBox) with ha1
  have ha0p : 0 < a0 := by positivity
  have ha1p : 0 < a1 := by positivity
  have hctp : 0 < ctube d escKstar := by
    have := escCstar_pos d; unfold escCstar at this; linarith
  have hd0 : (0 : ℝ) ≤ 4 * (d : ℝ) := by positivity
  -- eventualities in `y`
  have hy0 := evA (a := a0) (D := 4 * (d : ℝ)) ha0p (201 * d * CBox) hd0
  have hy1 := evB (A := A) (B := B') hApos ha0p (201 * d * CBox)
  have hy2 := evA (a := a1) (D := 4 * (d : ℝ)) ha1p (d * CBox) hd0
  have hy3 := evB (A := A) (B := B') hApos hctp 1
  obtain ⟨R, hR⟩ := eventually_atTop.1 ev_theta
  have hlogT : Tendsto (fun y : ℝ => A * Real.log y + B') atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hApos |>.comp Real.tendsto_log_atTop)
  have hyAll : ∀ᶠ y : ℝ in atTop, (4 * (d : ℝ) * Real.exp (-(1 / 24) * y ^ (0.4 : ℝ)) ≤
        a0 / y ^ (201 * d * CBox) / 4) ∧
      (Real.exp (-(A * Real.log y + B') ^ 2) ≤ a0 / y ^ (201 * d * CBox) / 4) ∧
      (4 * (d : ℝ) * Real.exp (-(1 / 24) * y ^ (0.4 : ℝ)) ≤ a1 / y ^ (d * CBox) / 4) ∧
      (Real.exp (-(A * Real.log y + B') ^ 2) ≤ ctube d escKstar / y ^ 1 / 4) ∧ (4 ≤ y) ∧
      (16 * R ≤ y) ∧ (1 ≤ y) ∧ (0 ≤ A * Real.log y + B') :=
    hy0.and (hy1.and (hy2.and (hy3.and ((eventually_ge_atTop 4).and
      ((eventually_ge_atTop (16 * R)).and ((eventually_ge_atTop 1).and
        (hlogT.eventually_ge_atTop 0)))))))
  have hdel : 0 < indDelta d / 30 := by
    have : 0 < indDelta d := by unfold indDelta; positivity
    positivity
  have hβdel : ∀ᶠ β : ℝ in atTop, C * β ^ (-indDelta d / 30) ≤ ctube d escKstar / 4 := by
    have h := (tendsto_rpow_neg_atTop hdel).const_mul C
    have h2 : Tendsto (fun β : ℝ => C * β ^ (-(indDelta d / 30))) atTop (𝓝 0) := by
      simpa using h
    filter_upwards [h2.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ctube d escKstar / 4))]
      with β hβ
    rw [neg_div]; exact hβ
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.1 ((tendsto_yy.eventually hyAll).and
    (hβdel.and ((eventually_ge_atTop (2 ^ 40)).and (eventually_ge_atTop (((4 : ℝ) ^ n₀ / 0.6) ^ 2 + 1)))))
  refine ⟨B₁, fun β hβ => ?_⟩
  obtain ⟨⟨hy_0, hy_1, hy_2, hy_3, hy_4, hy_5, hy_6, hy_7⟩, hCβ, h40, hn0⟩ := hB₁ β hβ
  have hβ1 : 1 ≤ β := le_trans (by norm_num) h40
  have hβ0 : 0 < β := by linarith
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  set y := Real.sqrt (Real.sqrt β) with hy
  have hypos : 0 < y := Real.sqrt_pos.2 hsb
  have hLeq := eta_eq hβ0
  have hL0 : 0 ≤ Real.logb 4 (0.6 * Real.sqrt β) - 1 := by rw [hLeq]; exact hy_7
  have hη : Real.exp (-(Real.logb 4 (0.6 * Real.sqrt β) - 1) ^ 2) =
      Real.exp (-(A * Real.log y + B') ^ 2) := by rw [hLeq]
  have h10 := rpow_tenth hβ0
  refine ⟨hβ1, h40, ?_, fun ρ hρ => hR ρ (by linarith), hL0, ?_, ?_, ?_⟩
  · have h1 : ((4 : ℝ) ^ n₀ / 0.6) ^ 2 < β := by linarith
    have h2 : (4 : ℝ) ^ n₀ / 0.6 < Real.sqrt β := Real.lt_sqrt_of_sq_lt h1
    rw [div_lt_iff₀ (by norm_num)] at h2
    linarith
  · -- the constant condition
    rw [hη]
    have hc1 : escCstar d = ctube d escKstar / 2 := rfl
    have h4 : ctube d escKstar / y ^ 1 / 4 ≤ ctube d escKstar / 16 := by
      rw [pow_one]
      have : ctube d escKstar / y ≤ ctube d escKstar / 4 :=
        div_le_div_of_nonneg_left hctp.le (by norm_num) hy_4
      linarith
    linarith
  · intro τ hτ1 hτ2
    have hτ0 : 0 < τ := lt_of_lt_of_le hsb hτ1
    have hRc : (((0.6 * τ).toNNReal : ℝ≥0) : ℝ) = 0.6 * τ := Real.coe_toNNReal _ (by positivity)
    have hmin := min_bound hβ1 (R := (((0.6 * τ).toNNReal : ℝ≥0) : ℝ)) (by rw [hRc]; positivity)
      (by rw [hRc]; linarith)
    have hexp : Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 / (8 * (((0.6 * τ).toNNReal : ℝ≥0) : ℝ)))
        (β ^ (0.3 : ℝ) / 2)) ≤ Real.exp (-(1 / 24) * y ^ (0.4 : ℝ)) := by
      apply Real.exp_le_exp.2
      rw [← h10]; linarith
    have h1 : 4 * (d : ℝ) * Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 /
        (8 * (((0.6 * τ).toNNReal : ℝ≥0) : ℝ))) (β ^ (0.3 : ℝ) / 2)) ≤
        4 * (d : ℝ) * Real.exp (-(1 / 24) * y ^ (0.4 : ℝ)) := by gcongr
    have h2 := c0_ge d hβ0 hτ0 hτ2
    rw [hη]
    have : a0 / y ^ (201 * d * CBox) / 4 + a0 / y ^ (201 * d * CBox) / 4 =
        a0 / y ^ (201 * d * CBox) / 2 := by ring
    calc _ ≤ a0 / y ^ (201 * d * CBox) / 4 + a0 / y ^ (201 * d * CBox) / 4 :=
          add_le_add (h1.trans hy_0) hy_1
      _ = a0 / y ^ (201 * d * CBox) / 2 := this
      _ ≤ _ := h2
  · intro τ hτ1 hτ2 T' hT1 hT2
    have hτ0 : 0 < τ := lt_of_lt_of_le hsb hτ1
    have hT'pos : 0 < (T' : ℝ) := by linarith
    have hmin := min_bound hβ1 (R := (T' : ℝ)) hT'pos (by linarith)
    have hexp : Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 / (8 * (T' : ℝ))) (β ^ (0.3 : ℝ) / 2)) ≤
        Real.exp (-(1 / 24) * y ^ (0.4 : ℝ)) := by
      apply Real.exp_le_exp.2
      rw [← h10]; linarith
    have h1 : 4 * (d : ℝ) * Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 / (8 * (T' : ℝ)))
        (β ^ (0.3 : ℝ) / 2)) ≤ 4 * (d : ℝ) * Real.exp (-(1 / 24) * y ^ (0.4 : ℝ)) := by gcongr
    have h2 := c1_ge d hβ0 hτ0 hτ2
    calc _ ≤ a1 / y ^ (d * CBox) / 4 := h1.trans hy_2
      _ ≤ a1 / y ^ (d * CBox) / 2 := by
          have : 0 ≤ a1 / y ^ (d * CBox) := by positivity
          linarith
      _ ≤ _ := h2

end ElboimSly.Paper.Escape

end
