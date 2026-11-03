/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Large-`n` numerics for Lemmas 7.3 and 7.4

Elementary "for `n` large" facts, as `Filter.Eventually` statements along `atTop` on `ℕ`:
polynomial-times-exponential decay, and the comparisons of an exponential in `n` with `exp(c n³)`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Step

/-- `n^m e^{-c n} → 0`. -/
theorem eventually_pow_mul_exp_neg_le (m : ℕ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ m * Real.exp (-(c * n)) ≤ δ := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m
  have h2 : Tendsto (fun x : ℝ => (c * x) ^ m * Real.exp (-(c * x))) atTop (𝓝 0) :=
    h1.comp (tendsto_id.const_mul_atTop hc)
  have h3 : Tendsto (fun n : ℕ => ((c * (n : ℝ)) ^ m * Real.exp (-(c * n)))) atTop (𝓝 0) :=
    h2.comp tendsto_natCast_atTop_atTop
  have h4 := h3.const_mul (c ^ m)⁻¹
  rw [mul_zero] at h4
  have := h4.eventually (Iic_mem_nhds hδ)
  filter_upwards [this] with n hn
  have hcm : (c ^ m)⁻¹ * ((c * (n : ℝ)) ^ m * Real.exp (-(c * n))) =
      (n : ℝ) ^ m * Real.exp (-(c * n)) := by
    rw [mul_pow]; field_simp
  rw [← hcm]; exact hn

/-- `a n + b ≤ c n³` for `n` large (`c > 0`). -/
theorem eventually_linear_le_cube (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, a * n + b ≤ c * (n : ℝ) ^ 3 := by
  have hM : ∀ᶠ n : ℕ in atTop, max 1 ((|a| + |b| + 1) / c) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hM] with n hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : (|a| + |b| + 1) / c ≤ n := le_trans (le_max_right _ _) hn
  have h3 : |a| + |b| + 1 ≤ c * n := by
    rw [div_le_iff₀ hc] at hn2; linarith
  have : a * n + b ≤ (|a| + |b|) * n := by
    nlinarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have h4 : (|a| + |b| + 1) * n ≤ c * n * n := by nlinarith
  have h5 : c * (n : ℝ) ^ 2 ≤ c * (n : ℝ) ^ 3 := by
    have : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
    exact mul_le_mul_of_nonneg_left this hc.le
  nlinarith [abs_nonneg a, abs_nonneg b]

/-- `a n + b ≤ c n²` for `n` large (`c > 0`). -/
theorem eventually_linear_le_sq (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, a * n + b ≤ c * (n : ℝ) ^ 2 := by
  have hM : ∀ᶠ n : ℕ in atTop, max 1 ((|a| + |b| + 1) / c) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hM] with n hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : (|a| + |b| + 1) / c ≤ n := le_trans (le_max_right _ _) hn
  have h3 : |a| + |b| + 1 ≤ c * n := by
    rw [div_le_iff₀ hc] at hn2; linarith
  have : a * n + b ≤ (|a| + |b|) * n := by
    nlinarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have h4 : (|a| + |b| + 1) * n ≤ c * n * n := by nlinarith
  nlinarith [abs_nonneg a, abs_nonneg b]

end ElboimSly.Paper.Step
