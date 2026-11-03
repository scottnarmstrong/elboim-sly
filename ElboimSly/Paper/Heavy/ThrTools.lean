/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Thresholds
public import ElboimSly.Paper.Heavy.ScalesBasic

/-!
# Asymptotic tools for the thresholds are finite

* `ev_rpow_le_exp`: `C n^q ≤ e^{a n}` eventually.
* `ev_logb_le`: `log₂ x ≤ x / 8` eventually.
* `tendsto_heavyLevel`, `ev_three_delta_le_level`: the level `k` grows linearly in `n`.
* `ev_half_level_le_kappa`: `κ ≥ k / 2` eventually.
-/

@[expose] public section

open Filter Topology Asymptotics
open scoped Real

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

/-- Polynomial growth is eventually dominated by any positive exponential rate. -/
theorem ev_rpow_le_exp (q a : ℝ) (ha : 0 < a) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ q ≤ Real.exp (a * n) := by
  have h := (isLittleO_rpow_exp_pos_mul_atTop q ha).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := h.bound (c := 1 / (|C| + 1)) (by positivity)
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  simp only [Function.comp, Real.norm_eq_abs] at hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ q := by positivity
  rw [abs_of_nonneg hn0, abs_of_nonneg (Real.exp_pos _).le] at hn
  have h1 : (|C| + 1) * (n : ℝ) ^ q ≤ Real.exp (a * n) := by
    have := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ |C| + 1)
    have e : (|C| + 1) * (1 / (|C| + 1) * Real.exp (a * n)) = Real.exp (a * n) := by
      field_simp
    linarith
  calc C * (n : ℝ) ^ q ≤ |C| * (n : ℝ) ^ q := by gcongr; exact le_abs_self C
    _ ≤ (|C| + 1) * (n : ℝ) ^ q := by nlinarith
    _ ≤ _ := h1

/-- Eventually `log₂ x ≤ c x`. -/
theorem ev_logb_le_mul {c : ℝ} (hc : 0 < c) : ∀ᶠ x : ℝ in atTop, Real.logb 2 x ≤ c * x := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.isLittleO_log_id_atTop.bound (c := Real.log 2 * c) (by positivity)
  filter_upwards [hb, eventually_gt_atTop 0] with x hx hx0
  simp only [id, Real.norm_eq_abs] at hx
  rw [Real.logb, div_le_iff₀ hl2]
  have := (le_abs_self (Real.log x)).trans hx
  rw [abs_of_pos hx0] at this
  linarith

theorem ev_lin_ge {a : ℝ} (ha : 0 < a) (b : ℝ) : ∀ᶠ n : ℕ in atTop, b ≤ a * n := by
  filter_upwards [eventually_ge_atTop (⌈b / a⌉₊)] with n hn
  have h2 : b / a ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rwa [div_le_iff₀ ha, mul_comm] at h2

/-- Eventually `log₂ x ≤ x / 8`. -/
theorem ev_logb_le : ∀ᶠ x : ℝ in atTop, Real.logb 2 x ≤ x / 8 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.isLittleO_log_id_atTop.bound (c := Real.log 2 / 8) (by positivity)
  filter_upwards [hb, eventually_gt_atTop 0] with x hx hx0
  simp only [id, Real.norm_eq_abs] at hx
  rw [Real.logb, div_le_iff₀ hl2]
  have := (le_abs_self (Real.log x)).trans hx
  rw [abs_of_pos hx0] at this
  linarith

variable {d : ℕ}

theorem ev_three_delta_le_level (hd : 1 ≤ d) :
    ∀ᶠ n : ℕ in atTop, 3 * indDelta d * n ≤ (heavyLevel d n : ℝ) := by
  have hδ := heavy_indDelta_pos hd
  filter_upwards [eventually_ge_atTop (⌈1 / indDelta d⌉₊)] with n hn
  have h1 := lt_heavyLevel_add_one d n
  have h2 : 1 / indDelta d ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h3 : 1 ≤ indDelta d * n := by
    rw [div_le_iff₀ hδ] at h2; linarith
  linarith

theorem tendsto_heavyLevel (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ => (heavyLevel d n : ℝ)) atTop atTop := by
  have hδ := heavy_indDelta_pos hd
  refine tendsto_atTop_mono' _ (ev_three_delta_le_level hd) ?_
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)

/-- Eventually `κ ≥ k / 2`. -/
theorem ev_half_level_le_kappa (hd : 1 ≤ d) :
    ∀ᶠ n : ℕ in atTop, (heavyLevel d n : ℝ) / 2 ≤ heavyKappa d n := by
  have h1 := (tendsto_heavyLevel hd).eventually ev_logb_le
  have h2 := (tendsto_heavyLevel hd).eventually (eventually_ge_atTop 4)
  filter_upwards [h1, h2] with n hn1 hn2
  unfold heavyKappa
  linarith

theorem ev_kappa_ge (hd : 1 ≤ d) :
    ∀ᶠ n : ℕ in atTop, 3 / 2 * indDelta d * n ≤ heavyKappa d n := by
  filter_upwards [ev_half_level_le_kappa hd, ev_three_delta_le_level hd] with n h1 h2
  linarith

end ElboimSly.Paper.Heavy
