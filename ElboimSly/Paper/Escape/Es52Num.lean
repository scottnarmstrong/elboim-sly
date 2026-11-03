/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Aux
public import ElboimSly.Paper.Escape.Es53NumA
public import ElboimSly.Foundations.Brownian.EscapeLineProb
public import Mathlib

/-!
# ES22 Proposition 5.2: the final numerics

ES22 Proposition 5.2 proof, "Conclusion": for `n` large,
`4 ⌈β⌉ (1 - c/2)^I ≤ e^{-c₅₂ n³}` with `c₅₂ = c/8` (here `c = cline`), using `I ≥ n³/2`
(`escIstar_ge`) and `β < 4^{n+1}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Brownian

theorem cline_pos' (d : ℕ) : 0 < cline d := by
  unfold cline
  have h1 := ctube_pos d (3 * lineM1 d)
  have h2 := qstar_pos d
  positivity

/-- `(1 - c/2)^I ≤ e^{-c n³/4}` when `I ≥ n³/2`. -/
theorem pow_one_sub_le {cl : ℝ} (hcl : 0 < cl) {n I : ℕ} (hI : (n : ℝ) ^ 3 / 2 ≤ I) :
    (1 - ENNReal.ofReal (cl / 2)) ^ I ≤ ENNReal.ofReal (Real.exp (-(cl / 4 * (n : ℝ) ^ 3))) := by
  have hx : 0 ≤ cl / 2 := by positivity
  have h1 : 1 - ENNReal.ofReal (cl / 2) ≤ ENNReal.ofReal (Real.exp (-(cl / 2))) := by
    have := ENNReal.ofReal_sub 1 hx
    rw [ENNReal.ofReal_one] at this
    rw [← this]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (-(cl / 2))])
  calc (1 - ENNReal.ofReal (cl / 2)) ^ I ≤ ENNReal.ofReal (Real.exp (-(cl / 2))) ^ I :=
        pow_le_pow_left' h1 _
    _ = ENNReal.ofReal (Real.exp (-(cl / 2)) ^ I) := (ENNReal.ofReal_pow (Real.exp_pos _).le _).symm
    _ = ENNReal.ofReal (Real.exp (-(cl / 2) * I)) := by
        rw [← Real.exp_nat_mul]; congr 2; ring
    _ ≤ ENNReal.ofReal (Real.exp (-(cl / 4 * (n : ℝ) ^ 3))) := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        nlinarith

theorem num_main {cl : ℝ} (hcl : 0 < cl) {β : ℝ} (hβ0 : 0 < β) {n I : ℕ} (hn : 2000 ≤ n)
    (hN : 56 / cl ≤ n) (hβ : β ≤ 4 ^ (n + 1)) (hI : (n : ℝ) ^ 3 / 2 ≤ I) :
    2 * ((⌈β⌉₊ : ℝ≥0∞) * (2 * (1 - ENNReal.ofReal (cl / 2)) ^ I)) ≤
      ENNReal.ofReal (Real.exp (-(cl / 8 * (n : ℝ) ^ 3))) := by
  have hq := pow_one_sub_le hcl hI
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  have hceil : (⌈β⌉₊ : ℝ) ≤ β + 1 := (Nat.ceil_lt_add_one hβ0.le).le
  -- real inequality `4 ⌈β⌉ ≤ exp(cl n³ / 8)`
  have hreal : 4 * (⌈β⌉₊ : ℝ) ≤ Real.exp (cl / 8 * (n : ℝ) ^ 3) := by
    have h4 : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
    have h5 : 4 * (⌈β⌉₊ : ℝ) ≤ 2 ^ (2 * n + 5) := by
      have : (2 : ℝ) ^ (2 * n + 5) = 8 * 4 ^ (n + 1) := by
        rw [show 2 * n + 5 = 2 * (n + 1) + 3 by ring, pow_add, pow_mul]; norm_num; ring
      rw [this]; nlinarith
    have h6 : (2 : ℝ) ^ (2 * n + 5) = Real.exp (((2 * n + 5 : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h7 : (((2 * n + 5 : ℕ) : ℝ)) * Real.log 2 ≤ cl / 8 * (n : ℝ) ^ 3 := by
      have hc : 56 ≤ cl * n := by
        have := (div_le_iff₀ hcl).1 hN; linarith
      push_cast
      calc (2 * (n : ℝ) + 5) * Real.log 2 ≤ (2 * n + 5) * 1 := by gcongr
        _ ≤ 3 * n := by linarith
        _ ≤ cl / 8 * (n : ℝ) ^ 3 := by
          have h24 : 24 ≤ cl * (n : ℝ) ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right h24 (by linarith : (0 : ℝ) ≤ n)
          nlinarith
    calc 4 * (⌈β⌉₊ : ℝ) ≤ 2 ^ (2 * n + 5) := h5
      _ = Real.exp (((2 * n + 5 : ℕ) : ℝ) * Real.log 2) := h6
      _ ≤ _ := Real.exp_le_exp.2 h7
  calc 2 * ((⌈β⌉₊ : ℝ≥0∞) * (2 * (1 - ENNReal.ofReal (cl / 2)) ^ I))
      = ENNReal.ofReal (4 * (⌈β⌉₊ : ℝ)) * (1 - ENNReal.ofReal (cl / 2)) ^ I := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
        norm_num
        ring
    _ ≤ ENNReal.ofReal (4 * (⌈β⌉₊ : ℝ)) *
          ENNReal.ofReal (Real.exp (-(cl / 4 * (n : ℝ) ^ 3))) := by gcongr
    _ = ENNReal.ofReal (4 * (⌈β⌉₊ : ℝ) * Real.exp (-(cl / 4 * (n : ℝ) ^ 3))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(cl / 8 * (n : ℝ) ^ 3))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : Real.exp (-(cl / 8 * (n : ℝ) ^ 3)) =
            Real.exp (cl / 8 * (n : ℝ) ^ 3) * Real.exp (-(cl / 4 * (n : ℝ) ^ 3)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hreal (Real.exp_pos _).le

end ElboimSly.Paper.Escape
