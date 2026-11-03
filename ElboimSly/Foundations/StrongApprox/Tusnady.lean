/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.TusnadyTail

/-!
# The Tusnády-type bound for $\mathrm{Bin}(m, \tfrac12)$

Tusn'ady-type bound for Bin(m,frac12) (Part I):
for all `m : ℕ` and `z : ℝ`,
`|saq m z - m/2 - (√m/2) z| ≤ C_T (1 + z²)` with `C_T = 2·10⁹` and `m₀ = 2·10⁹`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal Real ENNReal

namespace ElboimSly
namespace StrongApprox

/-- Step 5 of tusn'ady-type bound for Bin(m,frac12) for `z ∈ [0, X₀]`, with the scale `s`. -/
theorem tus_core {m : ℕ} (hm : 2000000000 ≤ m) {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ tV m / 4) :
    |(saq m z : ℝ) - m / 2 - sbS m * z| ≤ 2500 * (1 + z ^ 2) := by
  have hm' : (2000000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hs0 := sbS_pos m
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  have hsz : 0 ≤ sbS m * z := by positivity
  rw [abs_le]
  constructor
  · -- lower bound
    set w : ℝ := m / 2 + sbS m * z - 2500 * (1 + z ^ 2) with hw
    have h := tus_lower_tail hm hz0 hz (j := ⌊w⌋ + 1) (by
      push_cast; have := Int.floor_le w; linarith)
    have h2 := (le_saq_iff m z (⌊w⌋ + 1)).2 h
    have h3 : ((⌊w⌋ + 1 : ℤ) : ℝ) ≤ (saq m z : ℝ) := by exact_mod_cast h2
    have h4 := Int.lt_floor_add_one w
    push_cast at h3
    linarith
  · -- upper bound
    set w : ℝ := m / 2 + sbS m * z + 2500 * (1 + z ^ 2) with hw
    have hw0 : 0 ≤ w := by rw [hw]; positivity
    have h := tus_upper_tail hm hz0 hz (n := ⌈w⌉₊) (Nat.le_ceil w)
    have h1 : ¬ ((⌈w⌉₊ : ℤ) ≤ (saq m z : ℤ)) := by
      intro hle
      have := (le_saq_iff m z (⌈w⌉₊ : ℤ)).1 hle
      linarith
    have h2 : saq m z < ⌈w⌉₊ := by omega
    have h3 : saq m z + 1 ≤ ⌈w⌉₊ := h2
    have h4 := Nat.ceil_lt_add_one hw0
    have h5 : (saq m z : ℝ) + 1 ≤ ⌈w⌉₊ := by exact_mod_cast h3
    linarith

/-- Steps 5 for `z ∈ [-X₀, X₀]`. -/
theorem tus_core_symm {m : ℕ} (hm : 2000000000 ≤ m) {z : ℝ} (hz : |z| ≤ tV m / 4) :
    |(saq m z : ℝ) - m / 2 - sbS m * z| ≤ 2500 * (1 + z ^ 2) + 1 := by
  rcases le_total 0 z with h0 | h0
  · rw [abs_of_nonneg h0] at hz
    have := tus_core hm h0 hz
    linarith
  · rw [abs_of_nonpos h0] at hz
    have hz' : 0 ≤ -z := by linarith
    have := tus_core hm hz' hz
    have hneg := saq_neg m (-z)
    rw [neg_neg] at hneg
    have e : (-z) ^ 2 = z ^ 2 := by ring
    rw [e] at this
    rw [abs_le] at this ⊢
    rcases hneg with h | h
    · have : (saq m z : ℝ) = m - saq m (-z) - 1 := by exact_mod_cast h
      constructor <;> nlinarith [this]
    · have : (saq m z : ℝ) = m - saq m (-z) := by exact_mod_cast h
      constructor <;> nlinarith [this]

theorem sbS_sub_le {m : ℕ} (hm : 1 ≤ m) : sbS m - √(m : ℝ) / 2 ≤ 1 / (2 * √(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : 0 < √(m : ℝ) := Real.sqrt_pos.2 hm0
  have h1 : √((m : ℝ) + 1) * √((m : ℝ) + 1) = (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  have h2 : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm0.le
  have h3 : √(m : ℝ) ≤ √((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have h4 : √((m : ℝ) + 1) - √(m : ℝ) ≤ 1 / √(m : ℝ) := by
    rw [le_div_iff₀ hsq]
    nlinarith
  unfold sbS
  have : 1 / (2 * √(m : ℝ)) = (1 / √(m : ℝ)) / 2 := by field_simp
  rw [this]; linarith

/-- Tusn'ady-type bound for Bin(m,frac12), for `m ≥ m₀ = 2·10⁹` and `|z| ≤ X₀`. -/
theorem tus_mid {m : ℕ} (hm : 2000000000 ≤ m) {z : ℝ} (hz : |z| ≤ tV m / 4) :
    |(saq m z : ℝ) - m / 2 - √(m : ℝ) / 2 * z| ≤ 2500 * (1 + z ^ 2) + 2 := by
  have hm1 : 1 ≤ m := by omega
  have hm' : (2000000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : 0 < √(m : ℝ) := Real.sqrt_pos.2 (by linarith)
  have h1 := tus_core_symm hm hz
  have hsb := sbS_sub_le hm1
  have hsb0 : √(m : ℝ) / 2 ≤ sbS m := by
    unfold sbS
    have : √(m : ℝ) ≤ √((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    linarith
  have hzX : |z| * √(m : ℝ) ≤ 1 * √(m : ℝ) * (√(m : ℝ) / 19200) := by
    have : tV m / 4 = √(m : ℝ) / 19200 := by unfold tV; ring
    rw [this] at hz
    nlinarith [hz]
  have hprod : |z| * (sbS m - √(m : ℝ) / 2) ≤ 1 := by
    have h2 : |z| * (sbS m - √(m : ℝ) / 2) ≤ |z| * (1 / (2 * √(m : ℝ))) := by
      gcongr
    have h3 : |z| * (1 / (2 * √(m : ℝ))) = |z| * √(m : ℝ) / (2 * √(m : ℝ) * √(m : ℝ)) := by
      field_simp
    have h4 : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt (by linarith)
    have h5 : |z| ≤ √(m : ℝ) / 19200 := by
      have : tV m / 4 = √(m : ℝ) / 19200 := by unfold tV; ring
      rw [this] at hz; exact hz
    have h6 : |z| * (1 / (2 * √(m : ℝ))) ≤ (√(m : ℝ) / 19200) * (1 / (2 * √(m : ℝ))) := by
      gcongr
    have h7 : (√(m : ℝ) / 19200) * (1 / (2 * √(m : ℝ))) = 1 / 38400 := by field_simp; ring
    linarith
  have hdiff : |(sbS m * z) - √(m : ℝ) / 2 * z| ≤ 1 := by
    have : sbS m * z - √(m : ℝ) / 2 * z = (sbS m - √(m : ℝ) / 2) * z := by ring
    rw [this, abs_mul, abs_of_nonneg (sub_nonneg.2 hsb0), mul_comm]
    exact hprod
  have : (saq m z : ℝ) - m / 2 - √(m : ℝ) / 2 * z =
      ((saq m z : ℝ) - m / 2 - sbS m * z) + (sbS m * z - √(m : ℝ) / 2 * z) := by ring
  rw [this]
  calc _ ≤ |(saq m z : ℝ) - m / 2 - sbS m * z| + |sbS m * z - √(m : ℝ) / 2 * z| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Tusn'ady-type bound for Bin(m,frac12) (`C_T = 2·10⁹`, `m₀ = 2·10⁹`). For all `m : ℕ` and `z : ℝ`,
`|saq m z - m/2 - (√m/2) z| ≤ 2·10⁹ (1 + z²)`. -/
theorem tusnady (m : ℕ) (z : ℝ) :
    |(saq m z : ℝ) - m / 2 - √(m : ℝ) / 2 * z| ≤ 2000000000 * (1 + z ^ 2) := by
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  have hq0 : (0 : ℝ) ≤ saq m z := Nat.cast_nonneg _
  have hq1 : (saq m z : ℝ) ≤ m := by exact_mod_cast saq_le_m m z
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hsm : 0 ≤ √(m : ℝ) := Real.sqrt_nonneg _
  have hsm2 : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm0
  have h1 : |(saq m z : ℝ) - m / 2| ≤ m / 2 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |√(m : ℝ) / 2 * z| = √(m : ℝ) / 2 * |z| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have hsplit : (saq m z : ℝ) - m / 2 - √(m : ℝ) / 2 * z =
      ((saq m z : ℝ) - m / 2) - √(m : ℝ) / 2 * z := rfl
  have hcrude : |(saq m z : ℝ) - m / 2 - √(m : ℝ) / 2 * z| ≤ m / 2 + √(m : ℝ) / 2 * |z| := by
    calc _ ≤ |(saq m z : ℝ) - m / 2| + |√(m : ℝ) / 2 * z| := abs_sub _ _
      _ ≤ _ := by rw [h2]; linarith
  by_cases hm : m < 2000000000
  · -- small m
    have hm' : (m : ℝ) ≤ 2000000000 := by exact_mod_cast hm.le
    have hsq : √(m : ℝ) ≤ √(2000000000 : ℝ) := Real.sqrt_le_sqrt hm'
    have hsq2 : √(2000000000 : ℝ) * √(2000000000 : ℝ) = 2000000000 :=
      Real.mul_self_sqrt (by norm_num)
    have hsq0 := Real.sqrt_nonneg (2000000000 : ℝ)
    have h3 : √(m : ℝ) * |z| ≤ (2000000000 + z ^ 2) / 2 := by
      have : √(m : ℝ) * |z| ≤ √(2000000000 : ℝ) * |z| := by gcongr
      nlinarith [sq_abs z, sq_nonneg (√(2000000000 : ℝ) - |z|)]
    nlinarith
  · rw [not_lt] at hm
    by_cases hz : |z| ≤ tV m / 4
    · have := tus_mid hm hz
      nlinarith
    · rw [not_le] at hz
      have hX : tV m / 4 = √(m : ℝ) / 19200 := by unfold tV; ring
      rw [hX] at hz
      -- m < 19200² z²
      have h4 : √(m : ℝ) < 19200 * |z| := by linarith
      have h5 : (m : ℝ) < (19200 * |z|) ^ 2 := by
        have := mul_self_lt_mul_self hsm h4
        nlinarith
      have h6 : √(m : ℝ) * |z| ≤ 19200 * z ^ 2 := by
        have := mul_le_mul_of_nonneg_right h4.le (abs_nonneg z)
        nlinarith [sq_abs z]
      have h7 : (m : ℝ) / 2 + √(m : ℝ) / 2 * |z| ≤ 19200 ^ 2 * z ^ 2 := by
        nlinarith [sq_abs z]
      nlinarith

end StrongApprox
end ElboimSly
