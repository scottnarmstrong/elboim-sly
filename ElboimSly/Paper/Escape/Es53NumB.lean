/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IndThetaH
public import Mathlib

/-!
# Analytic estimates for the thresholds of ES22 Lemma 5.3

The exponent `θ = θ_H = 41/100`.
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

open ElboimSly

theorem log_le_div_ten (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 10 + 2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / 10 by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h
  have h10 : Real.log 10 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [this]
    nlinarith [Real.exp_pos 1]
  linarith

theorem log_two_ge : (0.6931 : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- `(4^m)^θ ≤ 2^{m+3} / m` for all `m ≥ 1`. -/
theorem theta_B (m : ℕ) (hm : 1 ≤ m) :
    ((4 : ℝ) ^ m) ^ indThetaH ≤ 2 ^ (m + 3) / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl2 := log_two_ge
  have hlm := log_le_div_ten m hm0
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [le_div_iff₀ hm0]
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) hm0.ne', Real.log_rpow (by positivity), Real.log_pow,
    Real.log_pow, h4]
  unfold indThetaH
  push_cast
  nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

/-- `(j 4^j)^θ ≤ 2^j` for `j ≥ 10`. -/
theorem theta_B' (j : ℕ) (hj : 10 ≤ j) :
    ((j : ℝ) * 4 ^ j) ^ indThetaH ≤ 2 ^ j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hj10 : (10 : ℝ) ≤ j := by exact_mod_cast hj
  have hl2 := log_two_ge
  have hlj := log_le_div_ten j hj0
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  rw [Real.log_rpow (by positivity), Real.log_mul hj0.ne' (by positivity), Real.log_pow,
    Real.log_pow, h4]
  unfold indThetaH
  nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

/-- `80 n^41 ≤ 4^n` for `n ≥ 400`. -/
theorem pow_le_four_pow (n : ℕ) (hn : 400 ≤ n) : (80 : ℝ) * (n : ℝ) ^ 41 ≤ 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h : (80 * 400 ^ 41 : ℕ) ≤ 4 ^ 400 :=
      calc (80 * 400 ^ 41 : ℕ) ≤ 4 ^ 200 * 4 ^ 200 := by norm_num
        _ = 4 ^ 400 := (pow_add 4 200 200).symm
    exact_mod_cast h
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn400 : (400 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : ((n : ℝ) + 1) ≤ (n : ℝ) * (401 / 400) := by nlinarith
    have h2 : ((n : ℝ) + 1) ^ 41 ≤ ((n : ℝ) * (401 / 400)) ^ 41 :=
      pow_le_pow_left₀ (by positivity) h1 41
    have h3 : ((n : ℝ) * (401 / 400)) ^ 41 ≤ 4 * (n : ℝ) ^ 41 := by
      rw [mul_pow]
      have : ((401 : ℝ) / 400) ^ 41 ≤ 4 := by norm_num
      nlinarith [pow_pos hn0 41]
    push_cast
    calc (80 : ℝ) * ((n : ℝ) + 1) ^ 41 ≤ 80 * (4 * (n : ℝ) ^ 41) := by
          gcongr; exact h2.trans h3
      _ = 4 * (80 * (n : ℝ) ^ 41) := by ring
      _ ≤ 4 * 4 ^ n := by gcongr
      _ = 4 ^ (n + 1) := by ring

/-- For `n ≥ 10^18`, `(80 n^41)^θ ≤ n^17 / 30`. -/
theorem theta_n (n : ℕ) (hn : (10 : ℝ) ^ 18 ≤ n) :
    (80 * (n : ℝ) ^ 41) ^ indThetaH ≤ (n : ℝ) ^ 17 / 30 := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have h80 : (80 : ℝ) ^ indThetaH ≤ 9 := by
    have : (80 : ℝ) ^ indThetaH ≤ 80 ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by unfold indThetaH; norm_num)
    refine this.trans ?_
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
    norm_num
  have hbig : (1000 : ℝ) ≤ (n : ℝ) ^ (19 / 100 : ℝ) := by
    have h1 : (1000 : ℝ) ^ (6 : ℝ) ≤ n := by
      calc (1000 : ℝ) ^ (6 : ℝ) = 10 ^ 18 := by norm_num
        _ ≤ n := hn
    calc (1000 : ℝ) = (1000 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1000 : ℝ) ^ ((6 : ℝ) * (19 / 100)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = ((1000 : ℝ) ^ (6 : ℝ)) ^ (19 / 100 : ℝ) := by rw [Real.rpow_mul (by norm_num)]
      _ ≤ (n : ℝ) ^ (19 / 100 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hsplit : (n : ℝ) ^ 17 = ((n : ℝ) ^ (41 * indThetaH)) * (n : ℝ) ^ (19 / 100 : ℝ) := by
    rw [← Real.rpow_add hn0]
    have : (41 * indThetaH + 19 / 100 : ℝ) = (17 : ℕ) := by unfold indThetaH; norm_num
    rw [this, Real.rpow_natCast]
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (n : ℝ) 41,
    ← Real.rpow_mul hn0.le]
  have hpos : 0 < (n : ℝ) ^ (41 * indThetaH) := Real.rpow_pos_of_pos hn0 _
  have e : ((41 : ℕ) : ℝ) * indThetaH = 41 * indThetaH := by push_cast; ring
  rw [e]
  have : (n : ℝ) ^ 17 / 30 ≥ 9 * (n : ℝ) ^ (41 * indThetaH) := by
    rw [hsplit]
    nlinarith
  calc (80 : ℝ) ^ indThetaH * (n : ℝ) ^ (41 * indThetaH) ≤ 9 * (n : ℝ) ^ (41 * indThetaH) := by
        gcongr
    _ ≤ _ := this

end ElboimSly.Paper.Escape
