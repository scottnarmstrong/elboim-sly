/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelNum
public import Mathlib

/-!
# The "`n` large" conditions of Lemmas 7.3 and 7.4

`travel_eventually` bundles every largeness condition on `n` used in the proofs of ES22 Lemma 7.3 and
ES22 Lemma 7.4 (the written proof's "for `n` large", with `4^{N+1}` covering them). They are all
consequences of the decay of `n^m e^{-cn}` and the growth of `e^{c n³}`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Step

/-- `2^n` and `4^n` as exponentials. -/
theorem two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ n = Real.exp (Real.log 2 * n) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem four_pow_eq_exp (n : ℕ) : (4 : ℝ) ^ n = Real.exp (Real.log 4 * n) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- All the largeness conditions on `n` of Lemmas 7.3 and 7.4. -/
theorem travel_eventually (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 200 ≤ n ∧ 1024 * d ≤ n ∧ (64 * (n : ℝ) ^ 6) ^ 15 ≤ 2 ^ n ∧
      (n : ℝ) ^ 6 * Real.exp n * Real.exp (-((n : ℝ) / 6 - 3 / 2) ^ 2) ≤ 1 / 2 ∧
      (5 * (n : ℝ)) ^ 10 ≤ 2 ^ n ∧
      Real.exp (3 * n) * Real.exp (-((n : ℝ) / 3 - 3 / 2) ^ 2) ≤ 1 / 2 ∧
      20 * (4 : ℝ) ^ n ≤ Real.exp (c / 2 * (n : ℝ) ^ 3) := by
  have e1 : ∀ᶠ n : ℕ in atTop, 200 ≤ n := eventually_ge_atTop 200
  have e2 : ∀ᶠ n : ℕ in atTop, 1024 * d ≤ n := eventually_ge_atTop _
  have e3 : ∀ᶠ n : ℕ in atTop, (64 * (n : ℝ) ^ 6) ^ 15 ≤ 2 ^ n := by
    have := eventually_pow_mul_exp_neg_le 90 (c := Real.log 2) (δ := 1 / 64 ^ 15)
      (Real.log_pos (by norm_num)) (by positivity)
    filter_upwards [this] with n hn
    rw [two_pow_eq_exp]
    have h1 : (64 * (n : ℝ) ^ 6) ^ 15 = 64 ^ 15 * (n : ℝ) ^ 90 := by ring
    rw [h1]
    have h2 : Real.exp (-(Real.log 2 * n)) = (Real.exp (Real.log 2 * n))⁻¹ := Real.exp_neg _
    rw [h2] at hn
    have hpos := Real.exp_pos (Real.log 2 * n)
    rw [← div_eq_mul_inv, div_le_iff₀ hpos] at hn
    have : (64 : ℝ) ^ 15 * (n : ℝ) ^ 90 ≤ 64 ^ 15 * (1 / 64 ^ 15 * Real.exp (Real.log 2 * n)) := by
      gcongr
    calc _ ≤ _ := this
      _ = Real.exp (Real.log 2 * n) := by field_simp
  have e4 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 6 * Real.exp n *
      Real.exp (-((n : ℝ) / 6 - 3 / 2) ^ 2) ≤ 1 / 2 := by
    have := eventually_pow_mul_exp_neg_le 6 (c := 1) (δ := 1 / 2) one_pos (by norm_num)
    filter_upwards [this, e1] with n hn h100
    have hn' : (200 : ℝ) ≤ n := by exact_mod_cast h100
    have hq : (n : ℝ) - ((n : ℝ) / 6 - 3 / 2) ^ 2 ≤ -(1 * n) := by nlinarith
    calc (n : ℝ) ^ 6 * Real.exp n * Real.exp (-((n : ℝ) / 6 - 3 / 2) ^ 2)
        = (n : ℝ) ^ 6 * Real.exp ((n : ℝ) - ((n : ℝ) / 6 - 3 / 2) ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ (n : ℝ) ^ 6 * Real.exp (-(1 * n)) := by gcongr
      _ ≤ 1 / 2 := hn
  have e5 : ∀ᶠ n : ℕ in atTop, (5 * (n : ℝ)) ^ 10 ≤ 2 ^ n := by
    have := eventually_pow_mul_exp_neg_le 10 (c := Real.log 2) (δ := 1 / 5 ^ 10)
      (Real.log_pos (by norm_num)) (by positivity)
    filter_upwards [this] with n hn
    rw [two_pow_eq_exp]
    have h2 : Real.exp (-(Real.log 2 * n)) = (Real.exp (Real.log 2 * n))⁻¹ := Real.exp_neg _
    rw [h2] at hn
    have hpos := Real.exp_pos (Real.log 2 * n)
    rw [← div_eq_mul_inv, div_le_iff₀ hpos] at hn
    have : (5 * (n : ℝ)) ^ 10 ≤ 5 ^ 10 * (1 / 5 ^ 10 * Real.exp (Real.log 2 * n)) := by
      rw [mul_pow]; gcongr
    calc _ ≤ _ := this
      _ = Real.exp (Real.log 2 * n) := by field_simp
  have e6 : ∀ᶠ n : ℕ in atTop,
      Real.exp (3 * n) * Real.exp (-((n : ℝ) / 3 - 3 / 2) ^ 2) ≤ 1 / 2 := by
    have := eventually_pow_mul_exp_neg_le 0 (c := 1) (δ := 1 / 2) one_pos (by norm_num)
    filter_upwards [this, e1] with n hn h200
    have hn' : (200 : ℝ) ≤ n := by exact_mod_cast h200
    have hq : 3 * (n : ℝ) - ((n : ℝ) / 3 - 3 / 2) ^ 2 ≤ -(1 * n) := by nlinarith
    calc Real.exp (3 * n) * Real.exp (-((n : ℝ) / 3 - 3 / 2) ^ 2)
        = Real.exp (3 * (n : ℝ) - ((n : ℝ) / 3 - 3 / 2) ^ 2) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(1 * n)) := by gcongr
      _ ≤ 1 / 2 := by simpa using hn
  have e7 : ∀ᶠ n : ℕ in atTop, 20 * (4 : ℝ) ^ n ≤ Real.exp (c / 2 * (n : ℝ) ^ 3) := by
    have := eventually_linear_le_cube (Real.log 4) (Real.log 20) (c := c / 2) (by positivity)
    filter_upwards [this] with n hn
    rw [four_pow_eq_exp]
    calc 20 * Real.exp (Real.log 4 * n) = Real.exp (Real.log 4 * n + Real.log 20) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]; ring
      _ ≤ _ := Real.exp_le_exp.2 hn
  filter_upwards [e1, e2, e3, e4, e5, e6, e7] with n a b c d e f g
  exact ⟨a, b, c, d, e, f, g⟩

end ElboimSly.Paper.Step
