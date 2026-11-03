/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56Geom
public import Mathlib

/-!
# Properties of the interpolating path `f_v` of Claim 5.6
-/

@[expose] public section

open Set
open scoped NNReal Real

namespace ElboimSly
namespace SRW

/-- Lipschitz bound for `λ(s) = √(2s/t)` on `[τ/2, ∞)` where `t = P² s₀²`. -/
theorem lam_lip {P s₀ s s' : ℝ} (hP : 0 < P) (hs₀ : 0 < s₀) (hs' : s₀ ^ 2 / 2 ≤ s')
    (hss : s' ≤ s) :
    √(2 * s / (P ^ 2 * s₀ ^ 2)) - √(2 * s' / (P ^ 2 * s₀ ^ 2)) ≤ (s - s') / (P * s₀ ^ 2) := by
  set t : ℝ := P ^ 2 * s₀ ^ 2 with ht
  have ht0 : 0 < t := by positivity
  have hs0' : 0 ≤ s' := by nlinarith [sq_nonneg s₀]
  have hs0 : 0 ≤ s := by linarith
  set a := √(2 * s / t) with ha
  set b := √(2 * s' / t) with hb
  have ha2 : a ^ 2 = 2 * s / t := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = 2 * s' / t := Real.sq_sqrt (by positivity)
  have hb1 : 1 / P ≤ b := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  have hab : b ≤ a := Real.sqrt_le_sqrt (by gcongr)
  have h1 : (a - b) * (a + b) = 2 * (s - s') / t := by
    rw [show (a - b) * (a + b) = a ^ 2 - b ^ 2 by ring, ha2, hb2]; ring
  have h2 : 2 / P ≤ a + b := by
    have : 1 / P ≤ a := hb1.trans hab
    have e : 2 / P = 1 / P + 1 / P := by ring
    linarith
  have hab0 : 0 ≤ a - b := by linarith
  have h3 : (a - b) * (2 / P) ≤ 2 * (s - s') / t := by
    calc (a - b) * (2 / P) ≤ (a - b) * (a + b) := by gcongr
      _ = _ := h1
  rw [le_div_iff₀ (by positivity)]
  have e : 2 * (s - s') / t * (P * s₀ ^ 2) = 2 * (s - s') / P := by
    rw [ht]; field_simp
  have h4 : (a - b) * (2 / P) * (P * s₀ ^ 2) ≤ 2 * (s - s') / t * (P * s₀ ^ 2) := by gcongr
  rw [e] at h4
  have e2 : (a - b) * (2 / P) * (P * s₀ ^ 2) = (a - b) * (2 * s₀ ^ 2) := by field_simp
  rw [e2] at h4
  have h5 := mul_le_mul_of_nonneg_left h4 hP.le
  have h6 : P * (2 * (s - s') / P) = 2 * (s - s') := by field_simp
  rw [h6] at h5
  nlinarith

theorem lam_ge {P s₀ s : ℝ} (hP : 0 < P) (hs₀ : 0 < s₀) (hs : s₀ ^ 2 / 2 ≤ s) :
    1 / P ≤ √(2 * s / (P ^ 2 * s₀ ^ 2)) := by
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem lam_le_one {P s₀ s : ℝ} (hP : 0 < P) (hs₀ : 0 < s₀) (hs : s ≤ P ^ 2 * s₀ ^ 2 / 2) :
    √(2 * s / (P ^ 2 * s₀ ^ 2)) ≤ 1 := by
  rw [Real.sqrt_le_one]
  rw [div_le_one (by positivity)]
  linarith

end SRW
end ElboimSly
