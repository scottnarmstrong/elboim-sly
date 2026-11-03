/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.ThrA

/-!
# The thresholds are finite, part B: (T6)

The thresholds are finite.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

theorem ev_poly_le_two_pow_level (hd : 1 ≤ d) (q C : ℝ) : ∀ᶠ n : ℕ in atTop,
    C * (n : ℝ) ^ q ≤ (2 : ℝ) ^ (heavyLevel d n) := by
  have hδ := heavy_indDelta_pos hd
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [ev_rpow_le_exp q (Real.log 2 * (3 * indDelta d)) (by positivity) C,
    ev_three_delta_le_level hd] with n h1 h2
  have h3 : (2 : ℝ) ^ (3 * indDelta d * n) ≤ (2 : ℝ) ^ (heavyLevel d n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  rw [Real.rpow_natCast] at h3
  refine h1.trans (le_trans (le_of_eq ?_) h3)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1; ring

theorem ev_T6 (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ 41 + 3 * n ^ 3 < 2 ^ (heavyLevel d n - 1) ∧ 20 * (n : ℝ) ^ 3 ≤ 2 ^ heavyLevel d n ∧
    5 * (2 : ℝ) ^ (2 * indDelta d * (n + 1)) ≤ 2 ^ (4 * indDelta d * n) ∧
    (2 : ℝ) ^ (2 * indDelta d * (n + 1)) + (n : ℝ) ^ 41 ≤ (1.9 : ℝ) ^ (4 * indDelta d * n - 1) := by
  have hδ := heavy_indDelta_pos hd
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < Real.log 1.9 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 < 2 * Real.log 1.9 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by rw [Real.rpow_two]; norm_num)
  have e19 : ∀ x : ℝ, (1.9 : ℝ) ^ x = Real.exp (x * Real.log 1.9) := fun x => by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1.9) x, mul_comm]
  have e2 : ∀ x : ℝ, (2 : ℝ) ^ x = Real.exp (x * Real.log 2) := fun x => by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) x, mul_comm]
  have hk1 := (tendsto_heavyLevel hd).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [ev_poly_le_two_pow_level hd 41 16, ev_poly_le_two_pow_level hd 3 20,
    ev_lin_ge (by positivity : 0 < 2 * indDelta d) (2 * indDelta d + 3),
    ev_lin_ge (mul_pos (by linarith : 0 < 4 * Real.log 1.9 - 2 * Real.log 2) hδ)
      (2 * indDelta d * Real.log 2 + Real.log 1.9 + Real.log 2),
    ev_rpow_le_exp 41 (4 * indDelta d * Real.log 1.9) (by positivity) (2 * Real.exp (Real.log 1.9)),
    eventually_ge_atTop 1, hk1] with n h1 h2 h3 h4 h5 hn1 hk
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn41 : (n : ℝ) ^ (41 : ℝ) = (n : ℝ) ^ 41 := by rw [← Real.rpow_natCast]; norm_num
  have hn3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by rw [← Real.rpow_natCast]; norm_num
  rw [hn41] at h1 h5
  rw [hn3] at h2
  have h31 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 41 := pow_le_pow_right₀ hn1' (by norm_num)
  have hk' : 1 ≤ heavyLevel d n := by exact_mod_cast hk
  refine ⟨?_, h2, ?_, ?_⟩
  · have hp : (2 : ℝ) ^ (heavyLevel d n) = 2 * 2 ^ (heavyLevel d n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : (0 : ℝ) < 2 ^ (heavyLevel d n - 1) := by positivity
    nlinarith [pow_pos (by linarith : (0 : ℝ) < n) 41]
  · have e : (2 : ℝ) ^ (4 * indDelta d * n) =
        (2 : ℝ) ^ (2 * indDelta d * (n + 1)) * (2 : ℝ) ^ (2 * indDelta d * n - 2 * indDelta d) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    rw [e]
    have : (5 : ℝ) ≤ (2 : ℝ) ^ (2 * indDelta d * n - 2 * indDelta d) := by
      have h8 : (2 : ℝ) ^ (3 : ℝ) ≤ (2 : ℝ) ^ (2 * indDelta d * n - 2 * indDelta d) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have : (2 : ℝ) ^ (3 : ℝ) = 8 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      linarith
    have hp : 0 < (2 : ℝ) ^ (2 * indDelta d * (n + 1)) := by positivity
    nlinarith
  · have hexp : 2 * indDelta d * (n + 1) * Real.log 2 + Real.log 2 ≤
        (4 * indDelta d * n - 1) * Real.log 1.9 := by nlinarith [h4]
    have hA : 2 * (2 : ℝ) ^ (2 * indDelta d * (n + 1)) ≤ (1.9 : ℝ) ^ (4 * indDelta d * n - 1) := by
      rw [e2, e19]
      calc 2 * Real.exp (2 * indDelta d * (n + 1) * Real.log 2)
          = Real.exp (2 * indDelta d * (n + 1) * Real.log 2 + Real.log 2) := by
            rw [Real.exp_add, Real.exp_log (by norm_num)]; ring
        _ ≤ _ := Real.exp_le_exp.2 hexp
    have hB : 2 * (n : ℝ) ^ 41 ≤ (1.9 : ℝ) ^ (4 * indDelta d * n - 1) := by
      rw [e19]
      have : Real.exp ((4 * indDelta d * n - 1) * Real.log 1.9) =
          Real.exp (4 * indDelta d * Real.log 1.9 * n) * Real.exp (-Real.log 1.9) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      have hh : Real.exp (Real.log 1.9) * Real.exp (-Real.log 1.9) = 1 := by
        rw [← Real.exp_add]; simp
      have hpos := Real.exp_pos (-Real.log 1.9)
      calc 2 * (n : ℝ) ^ 41 = (2 * Real.exp (Real.log 1.9) * (n : ℝ) ^ 41) *
            Real.exp (-Real.log 1.9) := by
            have := hh; nlinarith
        _ ≤ _ := by gcongr
    linarith

end ElboimSly.Paper.Heavy
