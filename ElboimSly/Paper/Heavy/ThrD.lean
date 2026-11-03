/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.ThrC
public import ElboimSly.Paper.Heavy.Cor610

/-!
# The thresholds are finite, part D: (T9), (T10)

The thresholds are finite.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

theorem ev_T9 (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop,
    2 + heavyL d n * (3.9 : ℝ) ^ heavyLevel d n ≤
      4 ^ heavyLevel d n / (8 * indDelta d * n * (heavyLevel d n : ℝ) ^ 4) := by
  have hδ := heavy_indDelta_pos hd
  have hδ1 : indDelta d ≤ 1 / 3000 := by
    unfold indDelta
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hγ : 3 ≤ escGamma d := le_max_left _ _
  have hl : 0 < Real.log (4 / 3.9) := Real.log_pos (by norm_num)
  set M : ℝ := 8 * indDelta d * (2 + 3 ^ (d + 2)) with hM
  have hk := (tendsto_heavyLevel hd).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [ev_rpow_le_exp (escGamma d + 14) (3 * indDelta d * Real.log (4 / 3.9))
    (by positivity) M, ev_three_delta_le_level hd, hk, eventually_ge_atTop 1] with n h1 h2 hk1 hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set k := heavyLevel d n with hkdef
  have hle := heavyLevel_le hd n
  have hkn : (k : ℝ) ≤ n := by
    have : 4 * indDelta d * n ≤ n := by nlinarith
    linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have h39 : (1 : ℝ) ≤ 3.9 ^ k := one_le_pow₀ (by norm_num)
  have hpos : 0 < 8 * indDelta d * n * (k : ℝ) ^ 4 := by positivity
  rw [le_div_iff₀ hpos]
  -- 4^k = 3.9^k * (4/3.9)^k and (4/3.9)^k ≥ exp(3 δ n log(4/3.9))
  have h4k : (4 : ℝ) ^ k = 3.9 ^ k * (4 / 3.9) ^ k := by rw [← mul_pow]; norm_num
  have hr : Real.exp (3 * indDelta d * Real.log (4 / 3.9) * n) ≤ (4 / 3.9 : ℝ) ^ k := by
    have h3 : (4 / 3.9 : ℝ) ^ (3 * indDelta d * n) ≤ (4 / 3.9 : ℝ) ^ (k : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    rw [Real.rpow_natCast] at h3
    refine le_trans (le_of_eq ?_) h3
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4 / 3.9)]
    congr 1; ring
  have hnγ : (n : ℝ) ^ (escGamma d + 9) * (n : ℝ) ^ (5 : ℝ) = (n : ℝ) ^ (escGamma d + 14) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have hn5 : (n : ℝ) ^ (5 : ℝ) = (n : ℝ) ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hg9 : 1 ≤ (n : ℝ) ^ (escGamma d + 9) := Real.one_le_rpow hn1' (by linarith)
  have hk4 : (k : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ hk0.le hkn 4
  have hL : heavyL d n = 3 ^ (d + 2) * (n : ℝ) ^ (escGamma d + 9) := rfl
  have h3d : (1 : ℝ) ≤ 3 ^ (d + 2) := one_le_pow₀ (by norm_num)
  have hn5' : (n : ℝ) ≤ (n : ℝ) ^ 5 := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hn1' (by norm_num)
  -- the main chain
  have hmain : M * (n : ℝ) ^ (escGamma d + 14) * 3.9 ^ k ≤ 4 ^ k := by
    calc M * (n : ℝ) ^ (escGamma d + 14) * 3.9 ^ k ≤ Real.exp (3 * indDelta d *
          Real.log (4 / 3.9) * n) * 3.9 ^ k := by
          gcongr
      _ ≤ (4 / 3.9) ^ k * 3.9 ^ k := by gcongr
      _ = _ := by rw [h4k]; ring
  calc (2 + heavyL d n * 3.9 ^ k) * (8 * indDelta d * n * (k : ℝ) ^ 4)
      ≤ ((2 + 3 ^ (d + 2)) * (n : ℝ) ^ (escGamma d + 9) * 3.9 ^ k) *
          (8 * indDelta d * n * (n : ℝ) ^ 4) := by
        rw [hL]
        have e1 : 2 + 3 ^ (d + 2) * (n : ℝ) ^ (escGamma d + 9) * 3.9 ^ k ≤
            (2 + 3 ^ (d + 2)) * (n : ℝ) ^ (escGamma d + 9) * 3.9 ^ k := by
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 3 ^ (d + 2))
            (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (escGamma d + 9))]
        exact mul_le_mul e1 (by gcongr) (by positivity) (by positivity)
    _ = M * ((n : ℝ) ^ (escGamma d + 9) * (n : ℝ) ^ (5 : ℝ)) * 3.9 ^ k := by
        rw [hn5, hM]; ring
    _ = _ := by rw [hnγ]
    _ ≤ _ := hmain

theorem ev_T10 (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop,
    (2 * n * (3 * 4 ^ (4 * indDelta d * n + 1) + 4 +
        n * (4 : ℝ) ^ (3 * heavyEps d * (n + 1) / 10)) ≤ (4 : ℝ) ^ (heavyEps d * n / 2) ∧
    2 * n * ((n : ℝ) ^ 3 + 2) ≤ (4 : ℝ) ^ (heavyEps d * n / 2)) := by
  have hδ := heavy_indDelta_pos hd
  have hε := heavyEps_pos hd
  have hdd := indDelta_mul_d (d := d) hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hδε : 4 * indDelta d ≤ 2 / 5 * heavyEps d := by nlinarith
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have e4 : ∀ x : ℝ, (4 : ℝ) ^ x = Real.exp (x * Real.log 4) := fun x => by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4) x, mul_comm]
  filter_upwards [ev_rpow_le_exp 1 (Real.log 4 * (heavyEps d / 2 - 4 * indDelta d))
      (by nlinarith) 72,
    ev_rpow_le_exp 1 (Real.log 4 * (heavyEps d / 2)) (by positivity) 24,
    ev_rpow_le_exp 2 (Real.log 4 * (heavyEps d / 5)) (by positivity) (6 * 4 ^ (3 * heavyEps d / 10)),
    ev_rpow_le_exp 4 (Real.log 4 * (heavyEps d / 2)) (by positivity) 6, eventually_ge_atTop 1]
    with n h1 h2 h3 h4 hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  simp only [Real.rpow_one] at h1 h2
  have hn2 : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hn4 : (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hn2] at h3
  rw [hn4] at h4
  have hX : (4 : ℝ) ^ (heavyEps d * n / 2) = (4 : ℝ) ^ (4 * indDelta d * n) *
      Real.exp (Real.log 4 * (heavyEps d / 2 - 4 * indDelta d) * n) := by
    rw [e4, e4, ← Real.exp_add]; congr 1; ring
  have hY : (4 : ℝ) ^ (heavyEps d * n / 2) = (4 : ℝ) ^ (3 * heavyEps d * n / 10) *
      Real.exp (Real.log 4 * (heavyEps d / 5) * n) := by
    rw [e4, e4, ← Real.exp_add]; congr 1; ring
  have hZ : (4 : ℝ) ^ (3 * heavyEps d * (n + 1) / 10) =
      (4 : ℝ) ^ (3 * heavyEps d / 10) * (4 : ℝ) ^ (3 * heavyEps d * n / 10) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have hW : (4 : ℝ) ^ (4 * indDelta d * n + 1) = 4 * (4 : ℝ) ^ (4 * indDelta d * n) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  have hX0 : 0 < (4 : ℝ) ^ (4 * indDelta d * n) := by positivity
  have hY0 : 0 < (4 : ℝ) ^ (3 * heavyEps d * n / 10) := by positivity
  have hH0 : 0 < (4 : ℝ) ^ (heavyEps d * n / 2) := by positivity
  have h2' : 24 * (n : ℝ) ≤ (4 : ℝ) ^ (heavyEps d * n / 2) := by
    rw [e4]; convert h2 using 2; ring_nf
  have h1' : 72 * (n : ℝ) * (4 : ℝ) ^ (4 * indDelta d * n) ≤ (4 : ℝ) ^ (heavyEps d * n / 2) := by
    rw [hX]
    have : 72 * (n : ℝ) ≤ Real.exp (Real.log 4 * (heavyEps d / 2 - 4 * indDelta d) * n) := by
      exact h1
    nlinarith
  have h3' : 6 * (n : ℝ) ^ 2 * (4 : ℝ) ^ (3 * heavyEps d / 10) *
      (4 : ℝ) ^ (3 * heavyEps d * n / 10) ≤ (4 : ℝ) ^ (heavyEps d * n / 2) := by
    rw [hY]
    have : 6 * (n : ℝ) ^ 2 * (4 : ℝ) ^ (3 * heavyEps d / 10) ≤
        Real.exp (Real.log 4 * (heavyEps d / 5) * n) := by
      convert h3 using 1; ring_nf
    nlinarith
  constructor
  · rw [hW, hZ]
    nlinarith
  · have h4' : 6 * (n : ℝ) ^ 4 ≤ (4 : ℝ) ^ (heavyEps d * n / 2) := by
      rw [e4]; convert h4 using 2; ring_nf
    have : 2 * (n : ℝ) * ((n : ℝ) ^ 3 + 2) ≤ 6 * (n : ℝ) ^ 4 := by
      have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1'
      nlinarith [pow_pos (by linarith : (0 : ℝ) < n) 3]
    linarith

end ElboimSly.Paper.Heavy
