/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Auxiliary facts for old history is far

* `esc_beta_pow_le`: `β^0.3 ≤ √β / 256` for `β ≥ 2^40`.
* `inv_pow_le_quarter`: `n + 2 ≤ n' → 2^{-n'} ≤ 2^{-n}/4`.
* `quarter_root_le`: `Q ≤ T / 2^n` from `2^m Q ≤ T` and `n ≤ m`.
* `tri_norm`: the four-point triangle inequality.
-/

@[expose] public section

namespace ElboimSly.Paper

lemma esc_beta_pow_le {β : ℝ} (hβ : (2 : ℝ) ^ 40 ≤ β) : β ^ (0.3 : ℝ) ≤ Real.sqrt β / 256 := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have h1 : (256 : ℝ) ≤ β ^ (0.2 : ℝ) := by
    have e : ((2 : ℝ) ^ (40 : ℝ)) ^ (0.2 : ℝ) = 256 := by
      rw [← Real.rpow_mul (by norm_num)]
      rw [show (40 * 0.2 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [← e]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    rw [show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact hβ
  have h2 : β ^ (0.3 : ℝ) * β ^ (0.2 : ℝ) = Real.sqrt β := by
    rw [← Real.rpow_add hβ0, Real.sqrt_eq_rpow]; norm_num
  have h3 : 0 ≤ β ^ (0.3 : ℝ) := by positivity
  nlinarith

lemma inv_pow_le_quarter {n n' : ℕ} (h : n + 2 ≤ n') : 1 / (2 : ℝ) ^ n' ≤ (1 / 2 ^ n) / 4 := by
  have h1 : (2 : ℝ) ^ n * 4 ≤ 2 ^ n' := by
    calc (2 : ℝ) ^ n * 4 = 2 ^ (n + 2) := by rw [pow_add]; norm_num
      _ ≤ 2 ^ n' := pow_le_pow_right₀ (by norm_num) h
  rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
  exact h1

lemma quarter_root_le {Q T : ℝ} {n m : ℕ} (hQ : 0 ≤ Q) (hm : (2 : ℝ) ^ m * Q ≤ T) (hnm : n ≤ m) :
    Q ≤ 1 / 2 ^ n * T := by
  have h1 : (2 : ℝ) ^ n ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hnm
  have h2 : (2 : ℝ) ^ n * Q ≤ T := le_trans (mul_le_mul_of_nonneg_right h1 hQ) hm
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

lemma tri_norm {X : Type*} [NormedAddCommGroup X] (A B C D : X) :
    ‖A - C‖ - ‖B - A‖ - ‖D - C‖ ≤ ‖B - D‖ := by
  have := dist_triangle4 A B D C
  simp only [dist_eq_norm] at this
  rw [norm_sub_rev B A]
  linarith

end ElboimSly.Paper
