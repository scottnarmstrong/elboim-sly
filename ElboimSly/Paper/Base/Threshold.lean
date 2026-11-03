/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# The threshold `n_{3.9}`

The threshold n_3.9 (ES22 §8, ES22 §8): for every integer `n ≥ 14980`,
`n^4 * 3.89^n < 3.9^n`.
-/

@[expose] public section

namespace ElboimSly.Paper

/-- The base case, decided by exact integer arithmetic. -/
theorem es8_threshold_base : 389 ^ 14980 * 14980 ^ 4 < 390 ^ 14980 := by
  decide +kernel

/-- The natural-number form of the threshold. -/
theorem es8_threshold_nat (n : ℕ) (hn : 14980 ≤ n) : 389 ^ n * n ^ 4 < 390 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => exact es8_threshold_base
  | succ n hn ih =>
    have h1 : 389 * (n + 1) ^ 4 ≤ 390 * n ^ 4 := by
      have h3 : 5835 * n ^ 3 ≤ n ^ 4 := by
        have := Nat.mul_le_mul_right (n ^ 3) (show 5835 ≤ n by omega)
        calc 5835 * n ^ 3 ≤ n * n ^ 3 := this
          _ = n ^ 4 := by ring
      have h2 : n ^ 3 ≥ n ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
      have h2' : n ^ 2 ≥ n := by nlinarith
      nlinarith [Nat.zero_le n]
    calc 389 ^ (n + 1) * (n + 1) ^ 4 = 389 ^ n * (389 * (n + 1) ^ 4) := by ring
      _ ≤ 389 ^ n * (390 * n ^ 4) := Nat.mul_le_mul_left _ h1
      _ = 390 * (389 ^ n * n ^ 4) := by ring
      _ < 390 * 390 ^ n := by
        exact Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ = 390 ^ (n + 1) := by ring

/-- The threshold n_3.9: for every integer `n ≥ 14980`, `n^4 * 3.89^n < 3.9^n`. -/
theorem es8_threshold (n : ℕ) (hn : 14980 ≤ n) :
    (n : ℝ) ^ 4 * (3.89 : ℝ) ^ n < (3.9 : ℝ) ^ n := by
  have h := es8_threshold_nat n hn
  have hR : ((389 ^ n * n ^ 4 : ℕ) : ℝ) < ((390 ^ n : ℕ) : ℝ) := by exact_mod_cast h
  have h100 : (0 : ℝ) < (100 : ℝ) ^ n := by positivity
  have e1 : (3.89 : ℝ) = 389 / 100 := by norm_num
  have e2 : (3.9 : ℝ) = 390 / 100 := by norm_num
  rw [e1, e2, div_pow, div_pow]
  push_cast at hR
  rw [← mul_div_assoc, mul_comm ((n : ℝ) ^ 4), div_lt_div_iff_of_pos_right h100]
  linarith

end ElboimSly.Paper
