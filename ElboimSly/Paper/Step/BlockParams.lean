/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelBlocks
public import ElboimSly.Paper.Step.TravelNum
public import ElboimSly.Paper.Heavy.Scales
public import Mathlib

/-!
# Parameters of the block decomposition of Lemma 7.6

ES22 Lemma 7.6, "Parameters" of the σ-estimate and Step 4. With `a_H = 79/200`,
`ℓ = ⌈t_n^{a_H}⌉`, `T = t_n/ℓ`: `ℓT = t_n`, `√t_n ≤ T ≤ t_n`, and
`ℓ t_n^{2ε} + 4 n² √T ≤ (3/8) t_n^{θ_H}` for `n` large. Everything is a power of `u = t_n^{1/400}`.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

theorem lemma76_params {d n : ℕ} (hd : 1 ≤ d) {tn : ℝ} (ht1 : (4 : ℝ) ^ n < tn)
    (hn : 400 ≤ n) (h16 : (16 * (n : ℝ) ^ 2) ^ 400 ≤ 4 ^ (43 * n)) :
    ∃ (ℓ : ℕ) (T : ℝ≥0), 1 ≤ ℓ ∧ 0 < T ∧ tn ^ ((79 : ℝ) / 200) / 2 ≤ ℓ ∧
      (ℓ : ℝ) ≤ 2 * tn ^ ((79 : ℝ) / 200) ∧ (ℓ : ℝ) * T = tn ∧ Real.sqrt tn ≤ T ∧ (T : ℝ) ≤ tn ∧
      (ℓ : ℝ) * tn ^ (2 * heavyEps d) + 4 * ((n : ℝ) ^ 2 * Real.sqrt T) ≤
        3 / 8 * tn ^ indThetaH ∧
      tn ^ ((121 : ℝ) / 200) / 2 ≤ T ∧ (T : ℝ) ≤ tn ^ ((121 : ℝ) / 200) := by
  have h4n : (4 : ℝ) ^ 400 ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have htn0 : 0 < tn := lt_trans (by positivity) ht1
  have htn1 : 1 ≤ tn :=
    calc (1 : ℝ) ≤ 4 ^ 400 := one_le_pow₀ (by norm_num)
      _ ≤ 4 ^ n := h4n
      _ ≤ tn := ht1.le
  obtain ⟨u, hu⟩ : ∃ u, u = tn ^ ((1 : ℝ) / 400) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact Real.rpow_pos_of_pos htn0 _
  have hu400 : u ^ 400 = tn := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul htn0.le]; norm_num
  have hu3 : 3 ≤ u := by
    have h1 : (3 : ℝ) ^ 400 ≤ u ^ 400 := by
      rw [hu400]
      calc (3 : ℝ) ^ 400 ≤ 4 ^ 400 := pow_le_pow_left₀ (by norm_num) (by norm_num) 400
        _ ≤ 4 ^ n := h4n
        _ ≤ tn := ht1.le
    exact (pow_le_pow_iff_left₀ (by norm_num) hu0.le (by norm_num)).1 h1
  have hu43 : 16 * (n : ℝ) ^ 2 ≤ u ^ 43 := by
    have h1 : (16 * (n : ℝ) ^ 2) ^ 400 ≤ (u ^ 43) ^ 400 := by
      rw [← pow_mul, show 43 * 400 = 400 * 43 by norm_num, pow_mul, hu400]
      calc (16 * (n : ℝ) ^ 2) ^ 400 ≤ 4 ^ (43 * n) := h16
        _ = (4 ^ n) ^ 43 := by rw [pow_mul']
        _ ≤ tn ^ 43 := pow_le_pow_left₀ (by positivity) ht1.le 43
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
  have hpow : ∀ q : ℕ, tn ^ ((q : ℝ) / 400) = u ^ q := fun q => by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul htn0.le]; congr 1; ring
  have ha : tn ^ ((79 : ℝ) / 200) = u ^ 158 := by
    rw [← hpow 158]; norm_num
  have hθ : tn ^ indThetaH = u ^ 164 := by
    have : indThetaH = ((164 : ℕ) : ℝ) / 400 := by unfold indThetaH; norm_num
    rw [this, hpow]
  have hu1 : (1 : ℝ) ≤ u ^ 158 := one_le_pow₀ (by linarith)
  obtain ⟨hk1, hk2, hk3⟩ := blocks_k hu1
  set ℓ : ℕ := ⌈u ^ 158⌉₊ with hℓ
  have hℓ0 : (0 : ℝ) < ℓ := lt_of_lt_of_le (by positivity) hk2
  have hT121 : tn ^ ((121 : ℝ) / 200) = u ^ 242 := by rw [← hpow 242]; norm_num
  refine ⟨ℓ, (tn / ℓ).toNNReal, hk1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.toNNReal_pos.2 (by positivity)
  · rw [ha]; linarith
  · rw [ha]; exact hk3
  · rw [Real.coe_toNNReal _ (by positivity)]; field_simp
  · -- √tn ≤ T
    have hT : tn / ℓ ≥ u ^ 242 / 2 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hℓ0]
      calc u ^ 242 * ℓ ≤ u ^ 242 * (2 * u ^ 158) := by gcongr
        _ = tn * 2 := by rw [← hu400]; ring
    have hs : Real.sqrt tn = u ^ 200 := by
      rw [← hu400, show (400 : ℕ) = 2 * 200 by norm_num, pow_mul', Real.sqrt_sq (by positivity)]
    rw [hs, Real.coe_toNNReal _ (by positivity)] at *
    have hu42 : (2 : ℝ) ≤ u ^ 42 := by
      calc (2 : ℝ) ≤ 3 := by norm_num
        _ ≤ u := hu3
        _ = u ^ 1 := (pow_one u).symm
        _ ≤ u ^ 42 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have : u ^ 242 = u ^ 200 * u ^ 42 := by ring
    have h200 : 0 < u ^ 200 := by positivity
    refine le_trans ?_ hT
    rw [this]; nlinarith
  · rw [Real.coe_toNNReal _ (by positivity)]
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hk1
    calc tn / ℓ ≤ tn / 1 := by gcongr
      _ = tn := div_one tn
  · -- the radius bound
    have hT : ((tn / ℓ).toNNReal : ℝ) = tn / ℓ := Real.coe_toNNReal _ (by positivity)
    rw [hT, hθ]
    have hTle : tn / ℓ ≤ u ^ 242 := by
      rw [div_le_iff₀ hℓ0]
      calc tn = u ^ 242 * u ^ 158 := by rw [← hu400]; ring
        _ ≤ u ^ 242 * ℓ := by gcongr
    have hsq : Real.sqrt (tn / ℓ) ≤ u ^ 121 := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      calc tn / ℓ ≤ u ^ 242 := hTle
        _ = (u ^ 121) ^ 2 := by ring
    have h2 : tn ^ (2 * heavyEps d) ≤ u ^ 3 := by
      have hε : 2 * heavyEps d ≤ 1 / 150 := by
        have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
        unfold heavyEps
        rw [show 2 * (1 / (300 * (d : ℝ))) = 1 / (150 * d) by field_simp; ring]
        exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
      calc tn ^ (2 * heavyEps d) ≤ tn ^ (((3 : ℕ) : ℝ) / 400) :=
            Real.rpow_le_rpow_of_exponent_le htn1 (by push_cast; linarith)
        _ = u ^ 3 := hpow 3
    have hu16 : (16 : ℝ) ≤ u ^ 3 := by
      calc (16 : ℝ) ≤ 3 ^ 3 := by norm_num
        _ ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu3 3
    have e1 : (ℓ : ℝ) * tn ^ (2 * heavyEps d) ≤ u ^ 164 / 8 := by
      calc (ℓ : ℝ) * tn ^ (2 * heavyEps d) ≤ (2 * u ^ 158) * u ^ 3 := by
            apply mul_le_mul hk3 h2 (Real.rpow_nonneg htn0.le _) (by positivity)
        _ = 2 * u ^ 161 := by ring
        _ ≤ u ^ 164 / 8 := by
            have : u ^ 164 = u ^ 161 * u ^ 3 := by ring
            have h161 : 0 < u ^ 161 := by positivity
            rw [this]; nlinarith
    have e2 : 4 * ((n : ℝ) ^ 2 * Real.sqrt (tn / ℓ)) ≤ u ^ 164 / 4 := by
      calc 4 * ((n : ℝ) ^ 2 * Real.sqrt (tn / ℓ)) ≤ 4 * ((n : ℝ) ^ 2 * u ^ 121) := by gcongr
        _ ≤ u ^ 164 / 4 := by
            have : u ^ 164 = u ^ 43 * u ^ 121 := by ring
            have h121 : 0 < u ^ 121 := by positivity
            rw [this]; nlinarith
    linarith
  · rw [Real.coe_toNNReal _ (by positivity), hT121]
    rw [div_le_div_iff₀ (by norm_num) hℓ0]
    calc u ^ 242 * ℓ ≤ u ^ 242 * (2 * u ^ 158) := by gcongr
      _ = tn * 2 := by rw [← hu400]; ring
  · rw [Real.coe_toNNReal _ (by positivity), hT121, div_le_iff₀ hℓ0]
    calc tn = u ^ 242 * u ^ 158 := by rw [← hu400]; ring
      _ ≤ u ^ 242 * ℓ := by gcongr

/-- The final summation of Lemma 7.6:
`(ℓ-1)e^{-c₁n³} + ℓ e^{-c₂n³} + e^{-n³/7} + 4dℓ e^{-n⁴/16} ≤ e^{-c n³}` with `c = c'/2`,
`c' = min (min c₁ c₂) (1/7)`, for `(4d+3) ℓ ≤ exp(c' n³/2)` and `n ≥ 16`. -/
theorem lemma76_sum_le {n d ℓ : ℕ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hn : 16 ≤ n)
    (hℓ : 1 ≤ ℓ)
    (hbig : ((4 * d + 3) * ℓ : ℝ) ≤ Real.exp (min (min c₁ c₂) (1 / 7) / 2 * (n : ℝ) ^ 3)) :
    ((ℓ : ℝ) - 1) * Real.exp (-(c₁ * (n : ℝ) ^ 3)) + ℓ * Real.exp (-(c₂ * (n : ℝ) ^ 3)) +
      Real.exp (-(n : ℝ) ^ 3 / 7) + (4 * d * ℓ : ℝ) * Real.exp (-(((n : ℝ) ^ 2) ^ 2 / 16)) ≤
      Real.exp (-(min (min c₁ c₂) (1 / 7) / 2 * (n : ℝ) ^ 3)) := by
  set c' : ℝ := min (min c₁ c₂) (1 / 7) with hc'
  have hc'0 : 0 < c' := lt_min (lt_min hc₁ hc₂) (by norm_num)
  have h1 : c' ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : c' ≤ c₂ := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : c' ≤ 1 / 7 := min_le_right _ _
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  set E := Real.exp (-(c' * (n : ℝ) ^ 3)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e1 : Real.exp (-(c₁ * (n : ℝ) ^ 3)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-(c₂ * (n : ℝ) ^ 3)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-(n : ℝ) ^ 3 / 7) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have e4 : Real.exp (-(((n : ℝ) ^ 2) ^ 2 / 16)) ≤ E := Real.exp_le_exp.2 (by
    have : ((n : ℝ) ^ 2) ^ 2 / 16 = (n : ℝ) ^ 3 * ((n : ℝ) / 16) := by ring
    rw [this]
    have h4 : 1 ≤ (n : ℝ) / 16 := by rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith)
  have hℓ0 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hsum : ((ℓ : ℝ) - 1) * Real.exp (-(c₁ * (n : ℝ) ^ 3)) + ℓ * Real.exp (-(c₂ * (n : ℝ) ^ 3)) +
      Real.exp (-(n : ℝ) ^ 3 / 7) + (4 * d * ℓ : ℝ) * Real.exp (-(((n : ℝ) ^ 2) ^ 2 / 16)) ≤
      ((4 * d + 3) * ℓ : ℝ) * E := by
    have a1 : ((ℓ : ℝ) - 1) * Real.exp (-(c₁ * (n : ℝ) ^ 3)) ≤ ((ℓ : ℝ) - 1) * E :=
      mul_le_mul_of_nonneg_left e1 (by linarith)
    have a2 : (ℓ : ℝ) * Real.exp (-(c₂ * (n : ℝ) ^ 3)) ≤ ℓ * E :=
      mul_le_mul_of_nonneg_left e2 (by linarith)
    have a4 : (4 * d * ℓ : ℝ) * Real.exp (-(((n : ℝ) ^ 2) ^ 2 / 16)) ≤ (4 * d * ℓ : ℝ) * E :=
      mul_le_mul_of_nonneg_left e4 (by positivity)
    nlinarith
  calc _ ≤ ((4 * d + 3) * ℓ : ℝ) * E := hsum
    _ ≤ Real.exp (c' / 2 * (n : ℝ) ^ 3) * E := mul_le_mul_of_nonneg_right hbig hE0.le
    _ = Real.exp (-(c' / 2 * (n : ℝ) ^ 3)) := by
        rw [hE, ← Real.exp_add]; congr 1; ring

end ElboimSly.Paper.Step
