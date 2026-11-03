/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.ThrTools

/-!
# The thresholds are finite, part A: (T1)-(T5)

The thresholds are finite.  Each condition holds eventually in `n`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

theorem ev_T1 (hd : 1 ≤ d) (n₀ : ℕ) : ∀ᶠ n : ℕ in atTop,
    (n₀ : ℝ) ≤ heavyKappa d n ∧ 16 ≤ heavyLevel d n := by
  have hδ := heavy_indDelta_pos hd
  have h2 := (tendsto_heavyLevel hd).eventually (eventually_ge_atTop (16 : ℝ))
  filter_upwards [ev_kappa_ge hd, ev_lin_ge (by positivity : 0 < 3 / 2 * indDelta d) n₀, h2]
    with n h1 h2 h3
  exact ⟨by linarith, by exact_mod_cast h3⟩

theorem ev_T2 (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop,
    2 + 20 * Real.logb 2 n ≤ 2 * indDelta d * n ∧ 1 + 2 * indDelta d ≤ 2 * indDelta d * n ∧
      1 < indDelta d * n := by
  have hδ := heavy_indDelta_pos hd
  have hlog := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (ev_logb_le_mul (c := indDelta d / 20) (by positivity))
  filter_upwards [hlog, ev_lin_ge hδ 2, ev_lin_ge (by positivity : 0 < 2 * indDelta d)
    (1 + 2 * indDelta d)] with n h1 h2 h3
  refine ⟨by linarith, h3, by linarith⟩

theorem ev_T3 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 3 * (4 ^ (n + 1) + 1) ≤ 5 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1 : ℝ) < 5 / 4)
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 5))] with n hn
  have hp : (0 : ℝ) < (5 / 4) ^ n := by positivity
  rw [div_lt_iff₀ hp] at hn
  have h5 : (5 : ℝ) ^ n = (5 / 4) ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
  have h4 : (4 : ℝ) ^ (n + 1) + 1 ≤ 5 * 4 ^ n := by
    have : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    rw [pow_succ]; linarith
  calc (n : ℝ) ^ 3 * (4 ^ (n + 1) + 1) ≤ (n : ℝ) ^ 3 * (5 * 4 ^ n) := by gcongr
    _ = (5 * (n : ℝ) ^ 3) * 4 ^ n := by ring
    _ ≤ (5 / 4) ^ n * 4 ^ n := by gcongr; linarith
    _ = _ := h5.symm

theorem ev_T4 : ∀ᶠ n : ℕ in atTop, 4 ≤ n := eventually_ge_atTop 4

theorem ev_T5 (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop,
    144 * 4 ^ d * (n : ℝ) ^ (escGamma d + 8 + 20 * d) < (2 : ℝ) ^ (indDelta d * n) := by
  have hδ := heavy_indDelta_pos hd
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [ev_rpow_le_exp (escGamma d + 8 + 20 * d) (Real.log 2 * indDelta d)
    (by positivity) (288 * 4 ^ d)] with n h
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have e : Real.log 2 * (indDelta d * n) = Real.log 2 * indDelta d * n := by ring
  rw [e]
  have := Real.exp_pos (Real.log 2 * indDelta d * n)
  nlinarith

end ElboimSly.Paper.Heavy
