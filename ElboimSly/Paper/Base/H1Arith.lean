/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.WindowCount
public import ElboimSly.Frozen.Defs.IndScale
public import ElboimSly.Frozen.Defs.ScaleIndex
public import Mathlib

/-!
# (H1) at the base: arithmetic

ES22 Lemma 8.1, Steps 1 and 4.

* `h1_budget`: `4d e^{-n⁴/8} + 2 e^{-n⁴} ≤ ½ e^{-n³}` for `n ≥ 16`, `2d ≤ n`.
* `h1_norm_le_l1`: the sup norm is bounded by `l1`.
* `scaleIndex_indScale`: `scaleIndex (4ⁿ t₀) = n` for `t₀ ∈ (1,4]`.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace ElboimSly.Paper

theorem h1_budget {d n : ℕ} (hn16 : 16 ≤ n) (hnd : 2 * d ≤ n) :
    4 * (d : ℝ) * Real.exp (-((n : ℝ) ^ 4 / 8)) + Real.exp (-(n : ℝ) ^ 4) +
      Real.exp (-(n : ℝ) ^ 4) ≤ 1 / 2 * Real.exp (-(n : ℝ) ^ 3) := by
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hnd' : (2 * d : ℝ) ≤ n := by exact_mod_cast hnd
  have h3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have h4 : (n : ℝ) ^ 4 = (n : ℝ) ^ 3 * n := by ring
  have e0 : Real.exp (-(n : ℝ) ^ 4) ≤ Real.exp (-((n : ℝ) ^ 4 / 8)) :=
    Real.exp_le_exp.2 (by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 4])
  have e1 : Real.exp (-((n : ℝ) ^ 4 / 8)) ≤ Real.exp (-(n : ℝ) ^ 3) * Real.exp (-(n : ℝ) ^ 3) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [h4]; nlinarith
  have e2 : (4 * (d : ℝ) + 2) * Real.exp (-(n : ℝ) ^ 3) ≤ 1 / 2 := by
    have hx := Real.add_one_le_exp ((n : ℝ) ^ 3)
    have hnn : (4 * (d : ℝ) + 2) ≤ Real.exp ((n : ℝ) ^ 3) / 2 := by
      have : (n : ℝ) ^ 3 ≥ 256 * n := by nlinarith [sq_nonneg (n : ℝ)]
      nlinarith
    calc (4 * (d : ℝ) + 2) * Real.exp (-(n : ℝ) ^ 3)
        ≤ (Real.exp ((n : ℝ) ^ 3) / 2) * Real.exp (-(n : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hnn (Real.exp_pos _).le
      _ = 1 / 2 := by
          rw [div_mul_eq_mul_div, ← Real.exp_add]; simp
  have hdn : (0 : ℝ) ≤ 4 * d + 2 := by positivity
  have hpos : 0 < Real.exp (-(n : ℝ) ^ 3) := Real.exp_pos _
  calc 4 * (d : ℝ) * Real.exp (-((n : ℝ) ^ 4 / 8)) + Real.exp (-(n : ℝ) ^ 4) +
        Real.exp (-(n : ℝ) ^ 4)
      ≤ (4 * (d : ℝ) + 2) * Real.exp (-((n : ℝ) ^ 4 / 8)) := by nlinarith
    _ ≤ (4 * (d : ℝ) + 2) * (Real.exp (-(n : ℝ) ^ 3) * Real.exp (-(n : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left e1 hdn
    _ = ((4 * (d : ℝ) + 2) * Real.exp (-(n : ℝ) ^ 3)) * Real.exp (-(n : ℝ) ^ 3) := by ring
    _ ≤ 1 / 2 * Real.exp (-(n : ℝ) ^ 3) := mul_le_mul_of_nonneg_right e2 hpos.le

theorem h1_norm_le_l1 {d : ℕ} (z : Fin d → ℤ) : ‖z‖ ≤ ElboimSly.SRW.l1 z := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
  rw [Int.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |(z j : ℝ)|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)

theorem scaleIndex_indScale {t0 : ℝ} (ht1 : 1 < t0) (ht4 : t0 ≤ 4) (n : ℕ) :
    ElboimSly.scaleIndex (ElboimSly.indScale t0 n) = n := by
  unfold ElboimSly.scaleIndex ElboimSly.indScale
  have hl : Real.logb 4 ((4 : ℝ) ^ n * t0) = n + Real.logb 4 t0 := by
    rw [Real.logb_mul (by positivity) (by linarith), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    simp
  have hp : 0 < Real.logb 4 t0 := Real.logb_pos (by norm_num) ht1
  have hq : Real.logb 4 t0 ≤ 1 := by
    have := Real.logb_le_logb_of_le (b := 4) (by norm_num) (by linarith) ht4
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have : ⌈Real.logb 4 ((4 : ℝ) ^ n * t0)⌉₊ = n + 1 := by
    rw [Nat.ceil_eq_iff (by omega), hl]
    push_cast
    constructor <;> linarith
  rw [this]; simp

end ElboimSly.Paper

end
