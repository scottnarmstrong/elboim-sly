/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Numerical bookkeeping (B1)-(B4) of the coupling step of Lemma 7.6, re-tuned

The coupling step of Lemma 7.6, re-tuned.  Throughout `a = 79/200`, `θ_H = 41/100`, `n ≥ 10^4`,
`4^n < t ≤ 4^{n+1}` and `t^a/2 ≤ ℓ ≤ 2 t^a`.
-/

@[expose] public section

open Real

namespace ElboimSly
namespace StrongApprox

theorem log_four_gt : (1.38629436 : ℝ) < Real.log 4 := by
  have h := Real.log_two_gt_d9
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this]; linarith

theorem log_four_lt : Real.log 4 < 1.3862944 := by
  have h := Real.log_two_lt_d9
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this]; linarith

section

variable {n : ℕ} {t ℓ : ℝ}

theorem log_t_bounds (_hn : 1 ≤ n) (ht1 : (4 : ℝ) ^ n < t) (ht2 : t ≤ 4 ^ (n + 1)) :
    n * Real.log 4 < Real.log t ∧ Real.log t ≤ (n + 1) * Real.log 4 := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  constructor
  · have := Real.log_lt_log h4 ht1
    rwa [Real.log_pow] at this
  · have := Real.log_le_log (by linarith) ht2
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this

/-- (B1)-ish: `log ℓ ≥ 0.53 n`. -/
theorem log_ell_ge (hn : 10 ^ 4 ≤ n) (ht1 : (4 : ℝ) ^ n < t) (ht2 : t ≤ 4 ^ (n + 1))
    (hℓ : t ^ ((79 : ℝ) / 200) / 2 ≤ ℓ) : 0.53 * n ≤ Real.log ℓ := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨h1, _⟩ := log_t_bounds hn1 ht1 ht2
  have htpos : 0 < t := lt_trans (by positivity) ht1
  have hpos : 0 < t ^ ((79 : ℝ) / 200) / 2 := by positivity
  have hl := Real.log_le_log hpos hℓ
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow htpos] at hl
  have h2 := Real.log_two_lt_d9
  have h3 := log_four_gt
  nlinarith

/-- `log ℓ ≤ n`. -/
theorem log_ell_le (hn : 10 ^ 4 ≤ n) (ht2 : t ≤ 4 ^ (n + 1)) (ht0 : 0 < t)
    (hℓ : ℓ ≤ 2 * t ^ ((79 : ℝ) / 200)) (hℓ0 : 0 < ℓ) : Real.log ℓ ≤ n := by
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_le_log hℓ0 hℓ
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow ht0] at hl
  have h1 : Real.log t ≤ (n + 1) * Real.log 4 := by
    have := Real.log_le_log ht0 ht2
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
  have h2 := Real.log_two_lt_d9
  have h3 := log_four_lt
  have h4 := log_four_gt
  nlinarith

theorem exp_nine_ge : (8100 : ℝ) ≤ Real.exp 9 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (8100 : ℝ) ≤ 2.7182818283 ^ 9 := by norm_num
    _ ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) h.le 9

theorem pow_gap (hn : 10 ^ 4 ≤ n) : 28 * (n : ℝ) ^ 12 ≤ Real.exp (0.01212 * n) := by
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : Real.log n ≤ 8 + n / 8100 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) / Real.exp 9 by positivity)
    rw [Real.log_div hnpos.ne' (Real.exp_pos 9).ne', Real.log_exp] at h1
    have h2 : (n : ℝ) / Real.exp 9 ≤ n / 8100 :=
      div_le_div_of_nonneg_left hnpos.le (by norm_num) exp_nine_ge
    linarith
  have h28 : Real.log 28 ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.sum_le_exp_of_nonneg (x := (4 : ℝ)) (by norm_num) 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this
    linarith
  have h12 : Real.exp (12 * Real.log n) = (n : ℝ) ^ 12 := by
    have := Real.log_pow (n : ℝ) 12
    rw [show ((12 : ℕ) : ℝ) = 12 by norm_num] at this
    rw [← this, Real.exp_log (by positivity)]
  have : 28 * (n : ℝ) ^ 12 = Real.exp (Real.log 28 + 12 * Real.log n) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), h12]
  rw [this]
  exact Real.exp_le_exp.2 (by nlinarith)

/-- (B4): the threshold in conclusion (b) is below `t^{θ_H}/8`. -/
theorem threshold_le {T σ : ℝ} (hn : 10 ^ 4 ≤ n) (ht1 : (4 : ℝ) ^ n < t) (ht2 : t ≤ 4 ^ (n + 1))
    (hℓ1 : t ^ ((79 : ℝ) / 200) / 2 ≤ ℓ) (hℓ2 : ℓ ≤ 2 * t ^ ((79 : ℝ) / 200)) (hT : 0 < T)
    (hℓT : ℓ * T ≤ 2 * t) (_hσ0 : 0 < σ) (hσ : σ ≤ 2) :
    σ * √T * ℓ ^ ((1 : ℝ) / 4) * (Real.log ℓ) ^ 12 ≤ t ^ ((41 : ℝ) / 100) / 8 := by
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have htpos : 0 < t := lt_trans (by positivity) ht1
  have hta : 0 < t ^ ((79 : ℝ) / 200) := by positivity
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ1
  have hL0 : 0 < Real.log ℓ := lt_of_lt_of_le (by linarith) (log_ell_ge hn ht1 ht2 hℓ1)
  have hL : Real.log ℓ ≤ n := log_ell_le hn ht2 htpos hℓ2 hℓ0
  set u : ℝ := √T * ℓ ^ ((1 : ℝ) / 4) with hu
  have hu0 : 0 ≤ u := by positivity
  -- u^4 ≤ 8 t^(2-a)
  have hu4 : u ^ 4 = T ^ 2 * ℓ := by
    rw [hu, mul_pow]
    have h1 : (√T) ^ 4 = T ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt hT.le]
    have h2 : (ℓ ^ ((1 : ℝ) / 4)) ^ 4 = ℓ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]; norm_num
    rw [h1, h2]
  have hT2 : T ^ 2 * ℓ ≤ 8 * t ^ (2 - (79 : ℝ) / 200) := by
    have h1 : T ^ 2 * ℓ * ℓ = (ℓ * T) ^ 2 := by ring
    have h2 : (ℓ * T) ^ 2 ≤ (2 * t) ^ 2 := pow_le_pow_left₀ (by positivity) hℓT 2
    have h3 : t ^ (2 - (79 : ℝ) / 200) * t ^ ((79 : ℝ) / 200) = t ^ 2 := by
      rw [← Real.rpow_add htpos]; norm_num
    have h4 : 8 * t ^ (2 - (79 : ℝ) / 200) * (t ^ ((79 : ℝ) / 200) / 2) = 4 * t ^ 2 := by
      rw [← h3]; ring
    have h5 : T ^ 2 * ℓ * (t ^ ((79 : ℝ) / 200) / 2) ≤ T ^ 2 * ℓ * ℓ :=
      mul_le_mul_of_nonneg_left hℓ1 (by positivity)
    have : T ^ 2 * ℓ * (t ^ ((79 : ℝ) / 200) / 2) ≤
        8 * t ^ (2 - (79 : ℝ) / 200) * (t ^ ((79 : ℝ) / 200) / 2) := by
      rw [h4]; nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  have hu_le : u ≤ 1.7 * t ^ ((2 - (79 : ℝ) / 200) / 4) := by
    have hq : (t ^ ((2 - (79 : ℝ) / 200) / 4)) ^ 4 = t ^ (2 - (79 : ℝ) / 200) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]; norm_num
    have hq0 : 0 < t ^ ((2 - (79 : ℝ) / 200) / 4) := by positivity
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
    rw [hu4, mul_pow, hq]
    have : (1.7 : ℝ) ^ 4 = 8.3521 := by norm_num
    rw [this]
    have hpos : 0 < t ^ (2 - (79 : ℝ) / 200) := by positivity
    nlinarith
  -- t^(7/800) dominates
  have hgap : 28 * (n : ℝ) ^ 12 ≤ t ^ ((7 : ℝ) / 800) := by
    refine (pow_gap hn).trans ?_
    have h1 : (4 : ℝ) ^ ((7 : ℝ) / 800 * n) ≤ t ^ ((7 : ℝ) / 800) := by
      calc (4 : ℝ) ^ ((7 : ℝ) / 800 * n) = ((4 : ℝ) ^ (n : ℝ)) ^ ((7 : ℝ) / 800) := by
            rw [← Real.rpow_mul (by norm_num)]; ring_nf
        _ ≤ t ^ ((7 : ℝ) / 800) := by
            apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
            rw [Real.rpow_natCast]; exact ht1.le
    refine le_trans ?_ h1
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    have := log_four_gt
    nlinarith
  have hsplit : t ^ ((41 : ℝ) / 100) = t ^ ((2 - (79 : ℝ) / 200) / 4) * t ^ ((7 : ℝ) / 800) := by
    rw [← Real.rpow_add htpos]; norm_num
  have hq0 : 0 < t ^ ((2 - (79 : ℝ) / 200) / 4) := by positivity
  have hLn : (Real.log ℓ) ^ 12 ≤ (n : ℝ) ^ 12 := pow_le_pow_left₀ hL0.le hL 12
  calc σ * √T * ℓ ^ ((1 : ℝ) / 4) * (Real.log ℓ) ^ 12 = σ * u * (Real.log ℓ) ^ 12 := by
        rw [hu]; ring
    _ ≤ 2 * (1.7 * t ^ ((2 - (79 : ℝ) / 200) / 4)) * (n : ℝ) ^ 12 := by
        gcongr
    _ ≤ t ^ ((41 : ℝ) / 100) / 8 := by
        rw [hsplit]
        have hn12 : 0 ≤ (n : ℝ) ^ 12 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hgap hq0.le]

/-- The threshold `n_X(d)` of the coupling step of Lemma 7.6, re-tuned. -/
noncomputable def nX (d : ℕ) : ℕ :=
  max (10 ^ 4) ⌈Real.log (20 * d) / ((79 / 200 : ℝ) * Real.log 4)⌉₊

/-- (B2): `ℓ ≥ max (10^5) (10 d)`. -/
theorem ell_ge_threshold {d : ℕ} (hd : 1 ≤ d) (hn : nX d ≤ n) (ht1 : (4 : ℝ) ^ n < t)
    (ht2 : t ≤ 4 ^ (n + 1)) (hℓ1 : t ^ ((79 : ℝ) / 200) / 2 ≤ ℓ) :
    (10 : ℝ) ^ 5 ≤ ℓ ∧ 10 * (d : ℝ) ≤ ℓ := by
  have hn4 : 10 ^ 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnc : ⌈Real.log (20 * d) / ((79 / 200 : ℝ) * Real.log 4)⌉₊ ≤ n :=
    le_trans (le_max_right _ _) hn
  have htpos : 0 < t := lt_trans (by positivity) ht1
  refine ⟨?_, ?_⟩
  · have h := log_ell_ge hn4 ht1 ht2 hℓ1
    have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn4
    have hℓ0 : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ1
    have h12 : (12 : ℝ) ≤ Real.log ℓ := by linarith
    have he : (10 : ℝ) ^ 5 ≤ Real.exp 12 := by
      have h := Real.exp_one_gt_d9
      have : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc (10 : ℝ) ^ 5 ≤ 2.7182818283 ^ 12 := by norm_num
        _ ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) h.le 12
    have : Real.exp 12 ≤ ℓ := by
      calc Real.exp 12 ≤ Real.exp (Real.log ℓ) := Real.exp_le_exp.2 h12
        _ = ℓ := Real.exp_log hℓ0
    exact he.trans this
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hl4 : 0 < (79 / 200 : ℝ) * Real.log 4 := by
      have := log_four_gt; positivity
    have h1 : Real.log (20 * d) ≤ n * ((79 / 200 : ℝ) * Real.log 4) := by
      have := Nat.le_ceil (Real.log (20 * d) / ((79 / 200 : ℝ) * Real.log 4))
      have h2 : Real.log (20 * d) / ((79 / 200 : ℝ) * Real.log 4) ≤ n :=
        this.trans (by exact_mod_cast hnc)
      rwa [div_le_iff₀ hl4] at h2
    have h2 : (20 : ℝ) * d ≤ t ^ ((79 : ℝ) / 200) := by
      have h3 : Real.log (20 * d) ≤ Real.log (t ^ ((79 : ℝ) / 200)) := by
        rw [Real.log_rpow htpos]
        have := (log_t_bounds (by omega) ht1 ht2).1
        nlinarith [log_four_gt]
      exact (Real.log_le_log_iff (by positivity) (by positivity)).1 h3
    linarith

end

end StrongApprox
end ElboimSly
