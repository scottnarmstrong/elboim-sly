/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Asymptotics for the thresholds of ES22 Claim 5.7

ES22 Claim 5.7 (choice of `β₅₇`).

Pure real-variable estimates, for `x = ln β`, `L₇ = x²` and `t₇ = L₇^{100/41}` (`1/θ_H`):
polylogarithmic bounds and the decay of the error terms.
-/

@[expose] public section

open Filter Topology Real

namespace ElboimSly.Paper.Escape

/-- The counting inequality `3^d C (r+1)² (ln (r+1))^{2d+2} ≤ r^{8/3}/2` for large `r`. -/
theorem polylog_bound (d : ℕ) : ∃ R : ℝ, 2 ≤ R ∧ ∀ r : ℝ, R ≤ r →
    3 ^ d * (6 * 33 ^ d * (r + 1) ^ 2 * Real.log (r + 1) ^ (2 * d + 2)) ≤
      r ^ (8 / 3 : ℝ) / 2 := by
  set K : ℝ := 3 ^ d * 6 * 33 ^ d with hK
  have hK0 : 0 < K := by positivity
  have h := (isLittleO_log_rpow_rpow_atTop (2 * (d : ℝ) + 2)
    (by norm_num : (0 : ℝ) < 1 / 3)).def (c := 1 / (16 * K)) (by positivity)
  obtain ⟨Y, hY⟩ := eventually_atTop.1 h
  refine ⟨max Y 2, le_max_right _ _, fun r hr => ?_⟩
  have hrY : Y ≤ r := le_trans (le_max_left _ _) hr
  have hr2 : 2 ≤ r := le_trans (le_max_right _ _) hr
  have hr1 : 1 ≤ r + 1 := by linarith
  have hy := hY (r + 1) (by linarith)
  have hlog0 : 0 ≤ Real.log (r + 1) := Real.log_nonneg hr1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hy
  have hcast : Real.log (r + 1) ^ (2 * d + 2) = Real.log (r + 1) ^ (2 * (d : ℝ) + 2) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  have e1 : 3 ^ d * (6 * 33 ^ d * (r + 1) ^ 2 * Real.log (r + 1) ^ (2 * d + 2)) =
      K * ((r + 1) ^ 2 * Real.log (r + 1) ^ (2 * d + 2)) := by rw [hK]; ring
  have e2 : (r + 1) ^ 2 * (r + 1) ^ (1 / 3 : ℝ) = (r + 1) ^ (7 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; norm_num
  have e3 : (r + 1) ^ (7 / 3 : ℝ) ≤ 8 * r ^ (8 / 3 : ℝ) := by
    have h1 : (r + 1) ^ (7 / 3 : ℝ) ≤ (2 * r) ^ (7 / 3 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
    have h2 : (2 : ℝ) ^ (7 / 3 : ℝ) ≤ 8 := by
      have : (2 : ℝ) ^ (7 / 3 : ℝ) ≤ 2 ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      calc (2 : ℝ) ^ (7 / 3 : ℝ) ≤ 2 ^ (3 : ℝ) := this
        _ = 8 := by norm_num
    have h3 : r ^ (7 / 3 : ℝ) ≤ r ^ (8 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h4 : 0 ≤ r ^ (7 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
    nlinarith
  rw [e1, hcast]
  calc K * ((r + 1) ^ 2 * Real.log (r + 1) ^ (2 * (d : ℝ) + 2))
      ≤ K * ((r + 1) ^ 2 * (1 / (16 * K) * (r + 1) ^ (1 / 3 : ℝ))) := by
        gcongr
    _ = (1 / 16) * ((r + 1) ^ 2 * (r + 1) ^ (1 / 3 : ℝ)) := by field_simp
    _ ≤ (1 / 16) * (8 * r ^ (8 / 3 : ℝ)) := by rw [e2]; gcongr
    _ = r ^ (8 / 3 : ℝ) / 2 := by ring

theorem asymT_pow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    ((x ^ 2) ^ (100 / 41 : ℝ)) ^ a = x ^ (200 / 41 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_mul hx]
  congr 1; push_cast; ring

theorem asym_two_le_rpow {x : ℝ} (hx : 8 ≤ x) : 2 ≤ x ^ (18 / 41 : ℝ) := by
  have h8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  calc (2 : ℝ) = 8 ^ (1 / 3 : ℝ) := h8.symm
    _ ≤ 8 ^ (18 / 41 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ x ^ (18 / 41 : ℝ) := Real.rpow_le_rpow (by norm_num) hx (by norm_num)

theorem asym_step_c {x : ℝ} (hx : 8 ≤ x) :
    x ^ 2 + 1 ≤ ((x ^ 2) ^ (100 / 41 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  rw [asymT_pow hx0]
  have h1 := asym_two_le_rpow hx
  have : x ^ (200 / 41 * (1 / 2) : ℝ) = x ^ 2 * x ^ (18 / 41 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; norm_num
  rw [this]; nlinarith [sq_nonneg x]

theorem asym_step_e : ∀ᶠ x : ℝ in atTop,
    (x ^ 2) ^ (100 / 41 : ℝ) + 4 * (x ^ 2 + 1) ^ 2 * Real.log (x ^ 2 + 1) ^ 2 < Real.exp x := by
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8
  have h1 : ∀ᶠ x : ℝ in atTop, x ^ 8 * Real.exp (-x) < 1 / 65 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  have hE : 0 < Real.exp x := Real.exp_pos x
  have hm : x ^ 8 * 65 < Real.exp x := by
    have : x ^ 8 * Real.exp (-x) * Real.exp x = x ^ 8 := by
      rw [mul_assoc, ← Real.exp_add]; simp
    nlinarith
  have hT : (x ^ 2) ^ (100 / 41 : ℝ) ≤ x ^ 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, ← Real.rpow_natCast x 8]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; norm_num)
  have hl : Real.log (x ^ 2 + 1) ^ 2 ≤ (x ^ 2 + 1) ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < x ^ 2 + 1 by positivity)
    have h0 : 0 ≤ Real.log (x ^ 2 + 1) := Real.log_nonneg (by nlinarith)
    nlinarith
  have hp : 4 * (x ^ 2 + 1) ^ 2 * Real.log (x ^ 2 + 1) ^ 2 ≤ 64 * x ^ 8 := by
    calc 4 * (x ^ 2 + 1) ^ 2 * Real.log (x ^ 2 + 1) ^ 2 ≤ 4 * (x ^ 2 + 1) ^ 2 * (x ^ 2 + 1) ^ 2 := by
          gcongr
      _ ≤ 4 * (2 * x ^ 2) ^ 2 * (2 * x ^ 2) ^ 2 := by
          have : x ^ 2 + 1 ≤ 2 * x ^ 2 := by nlinarith
          gcongr
      _ = 64 * x ^ 8 := by ring
  linarith

theorem asym_step_f {k : ℕ} (hk : 1 ≤ k) (C₁ C₂ c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ C₁ → 0 ≤ C₂ →
      C₁ * (x ^ 2 + 1) ^ k * ((x ^ 2) ^ (100 / 41 : ℝ)) ^ (-(k : ℝ) / 2) ≤ c ∧
      C₂ * (x ^ 2) ^ (-(1 : ℝ) / 30) ≤ c := by
  have t1 : Tendsto (fun x : ℝ => C₁ * 2 ^ k * x ^ (-(18 * k / 41 : ℝ))) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := 18 * k / 41) (by positivity)
    simpa using this.const_mul (C₁ * 2 ^ k)
  have t2 : Tendsto (fun x : ℝ => C₂ * x ^ (-(1 / 15 : ℝ))) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := 1 / 15) (by positivity)
    simpa using this.const_mul C₂
  filter_upwards [t1.eventually (gt_mem_nhds hc), t2.eventually (gt_mem_nhds hc),
    eventually_ge_atTop (1 : ℝ)] with x h1 h2 hx1
  intro hC1 hC2
  have hx0 : 0 ≤ x := by linarith
  constructor
  · have e : ((x ^ 2) ^ (100 / 41 : ℝ)) ^ (-(k : ℝ) / 2) = x ^ (-(100 * k / 41 : ℝ)) := by
      rw [asymT_pow hx0]; congr 1; ring
    have hb : (x ^ 2 + 1) ^ k ≤ 2 ^ k * x ^ (2 * k : ℝ) := by
      calc (x ^ 2 + 1) ^ k ≤ (2 * x ^ 2) ^ k := by
            gcongr; nlinarith
        _ = 2 ^ k * x ^ (2 * k : ℝ) := by
            rw [mul_pow, ← pow_mul, ← Real.rpow_natCast x (2 * k)]; push_cast; ring_nf
    have hp : 2 ^ k * x ^ (2 * k : ℝ) * x ^ (-(100 * k / 41 : ℝ)) = 2 ^ k * x ^ (-(18 * k / 41 : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add (by linarith)]; congr 2; ring
    rw [e]
    calc C₁ * (x ^ 2 + 1) ^ k * x ^ (-(100 * k / 41 : ℝ))
        ≤ C₁ * (2 ^ k * x ^ (2 * k : ℝ)) * x ^ (-(100 * k / 41 : ℝ)) := by gcongr
      _ = C₁ * 2 ^ k * x ^ (-(18 * k / 41 : ℝ)) := by rw [mul_assoc C₁ (2 ^ k * _), hp]; ring
      _ ≤ c := h1.le
  · have : (x ^ 2) ^ (-(1 : ℝ) / 30) = x ^ (-(1 / 15 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; congr 1; push_cast; ring
    rw [this]; exact h2.le

end ElboimSly.Paper.Escape
