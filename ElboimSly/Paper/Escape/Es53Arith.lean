/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Elementary estimates for the check of (2) and (3) in ES22 Lemma 5.3
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

theorem log_four_ge : (1 : ℝ) ≤ Real.log 4 := by
  have h := Real.log_two_gt_d9
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith

/-- (2): for `t ∈ [4^m, 4^{m+1})`, `2 √t / ln t < 2^{m+3}/m`. -/
theorem esArith_C2 {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (h1 : (4 : ℝ) ^ m ≤ t)
    (h2 : t < (4 : ℝ) ^ (m + 1)) : 2 * Real.sqrt t / Real.log t < 2 ^ (m + 3) / m := by
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) h1
  have hlog : (m : ℝ) ≤ Real.log t := by
    calc (m : ℝ) ≤ m * Real.log 4 := by nlinarith [log_four_ge]
      _ = Real.log ((4 : ℝ) ^ m) := by rw [Real.log_pow]
      _ ≤ Real.log t := Real.log_le_log (by positivity) h1
  have hlog0 : 0 < Real.log t := by linarith
  have hsq : Real.sqrt t < 2 ^ (m + 1) := by
    rw [Real.sqrt_lt' (by positivity)]
    calc t < (4 : ℝ) ^ (m + 1) := h2
      _ = ((2 : ℝ) ^ (m + 1)) ^ 2 := by rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have hpos : 0 < (2 : ℝ) ^ (m + 3) / m := by positivity
  rw [div_lt_iff₀ hlog0]
  calc 2 * Real.sqrt t < 2 * 2 ^ (m + 1) := by linarith
    _ = 2 ^ (m + 2) := by ring
    _ ≤ 2 ^ (m + 3) / m * m := by
        rw [div_mul_cancel₀ _ (by positivity)]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ 2 ^ (m + 3) / m * Real.log t := mul_le_mul_of_nonneg_left hlog hpos.le

/-- (3): the level `m' = max (m₁, ⌈log₄ t₁⌉)` satisfies `t₁ ≤ 4^{m'}` and `m' ≤ ln max(t, ln β)`. -/
theorem esArith_C3a {t₁ : ℝ} (ht₁ : 0 < t₁) (m₁ : ℕ) :
    t₁ ≤ (4 : ℝ) ^ (max m₁ ⌈Real.logb 4 t₁⌉₊) := by
  have h1 : t₁ ≤ (4 : ℝ) ^ (⌈Real.logb 4 t₁⌉₊ : ℝ) := by
    calc t₁ = (4 : ℝ) ^ (Real.logb 4 t₁) := (Real.rpow_logb (by norm_num) (by norm_num) ht₁).symm
      _ ≤ (4 : ℝ) ^ (⌈Real.logb 4 t₁⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  rw [Real.rpow_natCast] at h1
  exact h1.trans (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))

theorem esArith_C3b {t t₁ β : ℝ} (ht₁ : 0 < t₁) (ht₁t : t₁ ≤ t) {m₁ : ℕ} (hm8 : 8 ≤ m₁)
    (hm1a : (m₁ : ℝ) ≤ Real.log (Real.log β)) (hβ : Real.exp 2 ≤ Real.log β) :
    ((max m₁ ⌈Real.logb 4 t₁⌉₊ : ℕ) : ℝ) ≤ Real.log (max t (Real.log β)) := by
  have hlb : 0 < Real.log β := lt_of_lt_of_le (Real.exp_pos 2) hβ
  have hmono : Real.log (Real.log β) ≤ Real.log (max t (Real.log β)) :=
    Real.log_le_log hlb (le_max_right _ _)
  rcases le_total m₁ ⌈Real.logb 4 t₁⌉₊ with h | h
  · rw [max_eq_right h]
    -- `⌈log₄ t₁⌉ ≥ m₁ ≥ 8`
    set a := Real.logb 4 t₁ with ha
    have ha8 : 7 < a := by
      by_contra hh
      push Not at hh
      have : ⌈a⌉₊ ≤ 7 := Nat.ceil_le.2 (by exact_mod_cast hh)
      omega
    have hlt : Real.log t₁ = a * Real.log 4 := by
      rw [ha, Real.logb]; field_simp
    have hl4 : (1.38 : ℝ) ≤ Real.log 4 := by
      have := Real.log_two_gt_d9
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    have hceil : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
    have hlogt₁ : a + 1 ≤ Real.log t₁ := by rw [hlt]; nlinarith
    have hlt1t : Real.log t₁ ≤ Real.log t := by
      have : 0 < t := lt_of_lt_of_le ht₁ ht₁t
      exact Real.log_le_log ht₁ ht₁t
    have hlt2 : Real.log t ≤ Real.log (max t (Real.log β)) := by
      have : 0 < t := lt_of_lt_of_le ht₁ ht₁t
      exact Real.log_le_log this (le_max_left _ _)
    linarith
  · rw [max_eq_left h]
    exact hm1a.trans hmono

end ElboimSly.Paper.Escape
