/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Asymptotics for the thresholds `n₁(d)` of the base coupling

ES22 (8.3): base coupling with precision n^10 ("Constants": (N1)-(N4) hold for all large `n`).
-/

@[expose] public section

open Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

/-- A polynomial of lower degree is eventually dominated by `α n^10`. -/
theorem eventually_poly_le {α : ℝ} (hα : 0 < α) (β γ : ℝ) :
    ∀ᶠ n : ℕ in atTop, γ + β * (n : ℝ) + (n : ℝ) ^ 4 ≤ α * (n : ℝ) ^ 10 := by
  have h6 : Tendsto (fun n : ℕ => (n : ℝ) ^ 6) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp tendsto_natCast_atTop_atTop
  filter_upwards [h6.eventually_ge_atTop ((3 + 3 * |β| + 3 * |γ|) / α),
    eventually_ge_atTop 1] with n h6n hn1
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn
  have h4' : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn (by norm_num)
  have hα6 : 3 + 3 * |β| + 3 * |γ| ≤ α * (n : ℝ) ^ 6 := by
    have := (div_le_iff₀ hα).1 h6n
    linarith
  have h10 : α * (n : ℝ) ^ 10 = α * (n : ℝ) ^ 6 * (n : ℝ) ^ 4 := by ring
  rw [h10]
  have hb : β * n ≤ |β| * (n : ℝ) ^ 4 := by
    calc β * n ≤ |β| * n := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |β| * (n : ℝ) ^ 4 := mul_le_mul_of_nonneg_left h4' (abs_nonneg _)
  have hg : γ ≤ |γ| * (n : ℝ) ^ 4 := by
    calc γ ≤ |γ| := le_abs_self _
      _ = |γ| * 1 := (mul_one _).symm
      _ ≤ |γ| * (n : ℝ) ^ 4 := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
  have := mul_le_mul_of_nonneg_right hα6 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 4)
  nlinarith [abs_nonneg β, abs_nonneg γ]

end StrongApprox
end ElboimSly
