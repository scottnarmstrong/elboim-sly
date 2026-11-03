/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# The sum of the failure probabilities of Lemma 7.1
-/

@[expose] public section

namespace ElboimSly.Paper.Step

theorem prob_sum_le {c6 cf Cf c T : ℝ} {n : ℕ} (hCf : 0 < Cf) (hc : c = 1 / 2 * min c6 (min cf (1 / 17)))
    (_hc6 : 0 < c6) (_hcf : 0 < cf)
    (hQ : (3 + 32 * Cf) * (16 : ℝ) ^ n ≤ Real.exp (c * (n : ℝ) ^ 3))
    (hT1 : 1 ≤ T) (hT : T ≤ 4 ^ (n + 1)) {p1 p2 p3 p4 p5 : ℝ}
    (h1 : p1 ≤ Real.exp (-((n : ℝ) ^ 3 / 17))) (h2 : p2 ≤ Real.exp (-(c6 * (n : ℝ) ^ 3)))
    (h3 : p3 ≤ Real.exp (-(c6 * (n : ℝ) ^ 3)))
    (h4 : p4 ≤ Cf * T ^ 2 * Real.exp (-(cf * (n : ℝ) ^ 3)))
    (h5 : p5 ≤ Cf * T ^ 2 * Real.exp (-(cf * (n : ℝ) ^ 3))) :
    p1 + p2 + p3 + p4 + p5 ≤ Real.exp (-(c * (n : ℝ) ^ 3)) := by
  set m : ℝ := (n : ℝ) ^ 3 with hm
  have hm0 : 0 ≤ m := by positivity
  have hcmin1 : 2 * c ≤ c6 := by rw [hc]; nlinarith [min_le_left c6 (min cf (1 / 17))]
  have hcmin2 : 2 * c ≤ cf := by
    rw [hc]; nlinarith [min_le_left cf (1 / 17), min_le_right c6 (min cf (1 / 17))]
  have hcmin3 : 2 * c ≤ 1 / 17 := by
    rw [hc]; nlinarith [min_le_right cf (1 / 17), min_le_right c6 (min cf (1 / 17))]
  set E := Real.exp (-(2 * c * m)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e1 : Real.exp (-(m / 17)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-(c6 * m)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-(cf * m)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have hT2 : T ^ 2 ≤ 16 * 16 ^ n := by
    have : T ^ 2 ≤ ((4 : ℝ) ^ (n + 1)) ^ 2 := by gcongr
    calc T ^ 2 ≤ ((4 : ℝ) ^ (n + 1)) ^ 2 := this
      _ = 16 * 16 ^ n := by
        have : ((4 : ℝ) ^ (n + 1)) ^ 2 = (4 ^ 2) ^ (n + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
        rw [this]; norm_num; ring
  have h16 : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
  have hsum : p1 + p2 + p3 + p4 + p5 ≤ (3 + 32 * Cf * 16 ^ n) * E := by
    have a4 : p4 ≤ Cf * (16 * 16 ^ n) * E :=
      h4.trans (mul_le_mul (mul_le_mul_of_nonneg_left hT2 hCf.le) e3 (Real.exp_pos _).le
        (by positivity))
    have a5 : p5 ≤ Cf * (16 * 16 ^ n) * E :=
      h5.trans (mul_le_mul (mul_le_mul_of_nonneg_left hT2 hCf.le) e3 (Real.exp_pos _).le
        (by positivity))
    nlinarith
  have h6 : (3 + 32 * Cf * 16 ^ n) ≤ (3 + 32 * Cf) * 16 ^ n := by nlinarith
  calc p1 + p2 + p3 + p4 + p5 ≤ (3 + 32 * Cf * 16 ^ n) * E := hsum
    _ ≤ (3 + 32 * Cf) * 16 ^ n * E := mul_le_mul_of_nonneg_right h6 hE0.le
    _ ≤ Real.exp (c * m) * E := mul_le_mul_of_nonneg_right hQ hE0.le
    _ = Real.exp (-(c * m)) := by
      rw [hE, ← Real.exp_add]; congr 1; ring

end ElboimSly.Paper.Step
