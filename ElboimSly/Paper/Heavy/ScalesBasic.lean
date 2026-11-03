/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Thresholds

/-!
# Elementary estimates for the scales of ES22 §6

Supporting material for elementary facts about the scales: bounds on `δ`, `k`, and numeric inequalities for
`k ≥ 16`.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly

theorem heavy_indDelta_pos {d : ℕ} (hd : 1 ≤ d) : 0 < indDelta d := by
  unfold indDelta
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem four_indDelta_le {d : ℕ} (hd : 5 ≤ d) : 4 * indDelta d ≤ 1 / 18750 := by
  unfold indDelta
  have h5 : (5 : ℝ) ≤ d := by exact_mod_cast hd
  rw [show 4 * (1 / (3000 * (d : ℝ) ^ 2)) = 4 / (3000 * (d : ℝ) ^ 2) by ring]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem heavyLevel_le {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    (heavyLevel d n : ℝ) ≤ 4 * indDelta d * n :=
  Nat.floor_le (by have := heavy_indDelta_pos hd; positivity)

theorem lt_heavyLevel_add_one (d n : ℕ) : 4 * indDelta d * n < heavyLevel d n + 1 :=
  Nat.lt_floor_add_one _

/-- `k² < 2^k` for `k ≥ 5`. -/
theorem sq_lt_two_pow : ∀ k : ℕ, 5 ≤ k → k ^ 2 < 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [e]
    nlinarith

/-- `2 k^4 ≤ 4^k` for `k ≥ 16`. -/
theorem two_mul_pow_four_le : ∀ k : ℕ, 16 ≤ k → 2 * k ^ 4 ≤ 4 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e : 4 ^ (k + 1) = 4 * 4 ^ k := by ring
    rw [e]
    have h1 : (k + 1) ^ 4 ≤ 4 * k ^ 4 := by
      have : 16 * (k + 1) ≤ 17 * k := by omega
      have h2 : (16 * (k + 1)) ^ 4 ≤ (17 * k) ^ 4 := Nat.pow_le_pow_left this 4
      have h3 : 16 ^ 4 * (k + 1) ^ 4 ≤ 17 ^ 4 * k ^ 4 := by
        simpa [mul_pow] using h2
      nlinarith [Nat.zero_le (k ^ 4)]
    nlinarith

theorem logb_two_lt_half {k : ℕ} (hk : 16 ≤ k) : Real.logb 2 k < k / 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hk0]
  have h1 : k ^ 2 < 2 ^ k := sq_lt_two_pow k (by omega)
  have h2 : ((k : ℝ)) ^ 2 < 2 ^ k := by exact_mod_cast h1
  have hy : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = 2 ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show ((k : ℝ) / 2 * ((2 : ℕ) : ℝ)) = (k : ℝ) by push_cast; ring]
    exact Real.rpow_natCast 2 k
  rw [← hy] at h2
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2

theorem four_le_logb_two {k : ℕ} (hk : 16 ≤ k) : 4 ≤ Real.logb 2 k := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by omega : 0 < k))]
  norm_num
  exact_mod_cast hk

end ElboimSly.Paper
