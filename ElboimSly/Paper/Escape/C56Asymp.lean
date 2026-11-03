/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# ES22 Claim 5.6: the asymptotic conditions on `β`

ES22 Claim 5.6, "Choose `β_{56}` such that...".  Elementary eventual inequalities.
-/

@[expose] public section

open Filter Topology Real

namespace ElboimSly.Paper.Escape

/-- `exp(-b y^a) ≤ c y^{-p}` for large `y`. -/
theorem ev_exp_rpow {a b c p : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, Real.exp (-b * y ^ a) ≤ c * y ^ (-p) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / a) b hb
  have h2 : Tendsto (fun y : ℝ => y ^ a) atTop atTop := tendsto_rpow_atTop ha
  have h3 := (h1.comp h2).eventually (gt_mem_nhds hc)
  filter_upwards [h3, eventually_gt_atTop 0] with y hy hy0
  simp only [Function.comp] at hy
  have e : (y ^ a) ^ (p / a) = y ^ p := by
    rw [← Real.rpow_mul hy0.le]; congr 1; field_simp
  rw [e] at hy
  have hp : 0 < y ^ p := Real.rpow_pos_of_pos hy0 _
  rw [Real.rpow_neg hy0.le]
  have : y ^ p * Real.exp (-b * y ^ a) ≤ c := hy.le
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

/-- `exp(-(A log y + B)²) ≤ c y^{-p}` for large `y`. -/
theorem ev_exp_log_sq {A B c p : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, Real.exp (-(A * Real.log y + B) ^ 2) ≤ c * y ^ (-p) := by
  set m := p / A with hm
  set n := -p * B / A - Real.log c with hn
  have hlog : Tendsto (fun y : ℝ => A * Real.log y + B) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hA |>.comp Real.tendsto_log_atTop)
  filter_upwards [hlog.eventually_ge_atTop (|m| + |n| + 1), eventually_gt_atTop 0] with y hu hy0
  set u := A * Real.log y + B with hudef
  have hu1 : 1 ≤ u := by
    have := abs_nonneg m; have := abs_nonneg n; linarith
  have hkey : p * Real.log y - Real.log c ≤ u ^ 2 := by
    have e : p * Real.log y - Real.log c = m * u + n := by
      rw [hudef, hm, hn]; field_simp; ring
    rw [e]
    have h1 : m * u ≤ |m| * u := mul_le_mul_of_nonneg_right (le_abs_self m) (by linarith)
    have h2 : n ≤ |n| := le_abs_self n
    have h3 : |n| ≤ |n| * u := by nlinarith [abs_nonneg n]
    nlinarith [abs_nonneg m, abs_nonneg n]
  rw [Real.rpow_neg hy0.le]
  have hy' : y ^ p = Real.exp (p * Real.log y) := by
    rw [Real.rpow_def_of_pos hy0]; ring_nf
  rw [hy', ← Real.exp_neg]
  have : Real.exp (-u ^ 2) ≤ Real.exp (Real.log c + -(p * Real.log y)) :=
    Real.exp_le_exp.2 (by linarith)
  rw [Real.exp_add, Real.exp_log hc] at this
  exact this

/-- `D exp(-y^{0.4}/20) ≤ a / y^N / 4` for large `y`. -/
theorem evA {a D : ℝ} (ha : 0 < a) (N : ℕ) (hD : 0 ≤ D) :
    ∀ᶠ y : ℝ in atTop, D * Real.exp (-(1 / 24) * y ^ (0.4 : ℝ)) ≤ a / y ^ N / 4 := by
  have h := ev_exp_rpow (a := (0.4 : ℝ)) (b := 1 / 24) (c := a / (4 * (D + 1))) (p := (N : ℝ))
    (by norm_num) (by norm_num) (by positivity)
  filter_upwards [h, eventually_gt_atTop 0] with y hy hy0
  rw [Real.rpow_neg hy0.le, Real.rpow_natCast] at hy
  have hDp : 0 < D + 1 := by linarith
  calc D * Real.exp (-(1 / 24) * y ^ (0.4 : ℝ)) ≤ (D + 1) * (a / (4 * (D + 1)) * (y ^ N)⁻¹) := by
        have : 0 ≤ D := hD
        nlinarith [Real.exp_pos (-(1 / 24) * y ^ (0.4 : ℝ))]
    _ = a / y ^ N / 4 := by field_simp

/-- `exp(-(A log y + B)²) ≤ a / y^N / 4` for large `y`. -/
theorem evB {A B a : ℝ} (hA : 0 < A) (ha : 0 < a) (N : ℕ) :
    ∀ᶠ y : ℝ in atTop, Real.exp (-(A * Real.log y + B) ^ 2) ≤ a / y ^ N / 4 := by
  have h := ev_exp_log_sq (A := A) (B := B) (c := a / 4) (p := (N : ℝ)) hA (by positivity)
  filter_upwards [h, eventually_gt_atTop 0] with y hy hy0
  rw [Real.rpow_neg hy0.le, Real.rpow_natCast] at hy
  calc _ ≤ a / 4 * (y ^ N)⁻¹ := hy
    _ = a / y ^ N / 4 := by field_simp

end ElboimSly.Paper.Escape

end
