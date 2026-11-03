/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Lemma 7.8: the final sum of exponentials

ES22 Lemma 7.8, the displayed estimate
`4A_n e^{-c n³} + e^{-c_bm n³} + e^{-n³} + 2e^{-c n³} + e^{-n³/17} ≤ e^{-c_pp n³}`.
With `m = min(c/2, c_bm)` and `c_pp = m/2`, and (T11) in the form
`e^{-n³} + (n³ + 1) A e^{-c n³} ≤ e^{-(c/2) n³}`, the sum of the five terms (counted with
multiplicity as in `step78_bad` and `step78_H1`) is at most `e^{-(m/2) n³}` once `n ≥ 2/m`.
-/

@[expose] public section

namespace ElboimSly.Paper.Step

theorem step78_arith {A c c' cBm : ℝ} {n : ℕ} (hA0 : 0 ≤ A) (hc : 0 < c) (hc17 : c ≤ 1 / 17)
    (hcc' : c ≤ c') (hcBm : 0 < cBm) (hn : 2 / min (c / 2) cBm ≤ (n : ℝ))
    (ht11 : Real.exp (-(n : ℝ) ^ 3) + ((n : ℝ) ^ 3 + 1) * A * Real.exp (-(c * (n : ℝ) ^ 3)) ≤
      Real.exp (-(c / 2 * (n : ℝ) ^ 3))) :
    (A * Real.exp (-(c * (n : ℝ) ^ 3)) + Real.exp (-(cBm * (n : ℝ) ^ 3)) + Real.exp (-(n : ℝ) ^ 3)) +
      2 * (A * Real.exp (-(c * (n : ℝ) ^ 3))) + 2 * Real.exp (-(c' * (n : ℝ) ^ 3)) +
      Real.exp (-((n : ℝ) ^ 3 / 17)) ≤ Real.exp (-(min (c / 2) cBm / 2 * (n : ℝ) ^ 3)) := by
  set m : ℝ := min (c / 2) cBm with hm
  set x : ℝ := (n : ℝ) ^ 3 with hx
  have hm0 : 0 < m := lt_min (by linarith) hcBm
  have hm1 : m ≤ c / 2 := min_le_left _ _
  have hm2 : m ≤ cBm := min_le_right _ _
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx0 : 0 ≤ x := by positivity
  have hmn : 2 ≤ m * n := by
    rw [div_le_iff₀ hm0] at hn; linarith
  have hn34 : (34 : ℝ) ≤ n := by
    have : 2 / m ≥ 34 := by
      rw [ge_iff_le, le_div_iff₀ hm0]; linarith
    linarith
  have ha : A * Real.exp (-(c * x)) ≤ Real.exp (-(c / 2 * x)) := by
    have h1 : 0 ≤ A * Real.exp (-(c * x)) := by positivity
    have h2 : A * Real.exp (-(c * x)) ≤ (x + 1) * A * Real.exp (-(c * x)) := by nlinarith
    have h3 := Real.exp_pos (-(n : ℝ) ^ 3)
    linarith
  have key : ∀ y : ℝ, m * x ≤ y → Real.exp (-y) ≤ Real.exp (-(m * x)) := fun y hy =>
    Real.exp_le_exp.2 (by linarith)
  have e1 : A * Real.exp (-(c * x)) ≤ Real.exp (-(m * x)) :=
    ha.trans (key _ (by nlinarith))
  have e2 : Real.exp (-(cBm * x)) ≤ Real.exp (-(m * x)) := key _ (by nlinarith)
  have e3 : Real.exp (-x) ≤ Real.exp (-(m * x)) := key _ (by nlinarith)
  have e4 : Real.exp (-(c' * x)) ≤ Real.exp (-(m * x)) := key _ (by nlinarith)
  have e5 : Real.exp (-(x / 17)) ≤ Real.exp (-(m * x)) := key _ (by nlinarith)
  have hsum : (A * Real.exp (-(c * x)) + Real.exp (-(cBm * x)) + Real.exp (-x)) +
      2 * (A * Real.exp (-(c * x))) + 2 * Real.exp (-(c' * x)) + Real.exp (-(x / 17)) ≤
      8 * Real.exp (-(m * x)) := by linarith
  refine hsum.trans ?_
  have h3 : (3 : ℝ) ≤ m / 2 * x := by
    have : x = (n : ℝ) * (n : ℝ) ^ 2 := by rw [hx]; ring
    rw [this]
    nlinarith [mul_nonneg hn0 hn0, sq_nonneg ((n : ℝ) - 34)]
  have h8 : (8 : ℝ) ≤ Real.exp (m / 2 * x) := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h83 : (8 : ℝ) ≤ Real.exp 3 := by
      rw [this]; nlinarith [pow_le_pow_left₀ (by norm_num) h1 3]
    exact h83.trans (Real.exp_le_exp.2 h3)
  have : Real.exp (-(m / 2 * x)) * Real.exp (m / 2 * x) = 1 := by
    rw [← Real.exp_add]; simp
  have e : Real.exp (-(m * x)) = Real.exp (-(m / 2 * x)) * Real.exp (-(m / 2 * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hp := Real.exp_pos (-(m / 2 * x))
  nlinarith [mul_le_mul_of_nonneg_left h8 hp.le]

end ElboimSly.Paper.Step

end
