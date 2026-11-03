/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Transfer
public import ElboimSly.Paper.Escape.Es53NumB
public import Mathlib

/-!
# The error terms of ES22 Lemma 5.3 are small
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian

theorem sum_inv_sq_le (a n : ℕ) (ha : 2 ≤ a) :
    ∑ m ∈ Finset.Icc a n, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) := by
  have ha1 : (0 : ℝ) < (a : ℝ) - 1 := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  by_cases hn : n < a
  · rw [Finset.Icc_eq_empty_of_lt hn, Finset.sum_empty]; exact (one_div_pos.2 ha1).le
  · push Not at hn
    have key : ∀ n, a ≤ n → ∑ m ∈ Finset.Icc a n, (1 : ℝ) / (m : ℝ) ^ 2 ≤
        1 / ((a : ℝ) - 1) - 1 / (n : ℝ) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        simp only [Finset.Icc_self, Finset.sum_singleton]
        have ha0 : (0 : ℝ) < a := by linarith
        rw [div_sub_div _ _ ha1.ne' ha0.ne']
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hn0 : (0 : ℝ) < n := by
          have : (2 : ℝ) ≤ a := by exact_mod_cast ha
          have : (a : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have h1 : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
          rw [div_sub_div _ _ hn0.ne' (by positivity)]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        push_cast
        linarith
    have := key n hn
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith

theorem errB_term (C : ℝ) (k m : ℕ) (hm : 1 ≤ m) :
    C * (2 ^ (m + 3) / (m : ℝ)) ^ k * ((4 : ℝ) ^ m) ^ (-(k : ℝ) / 2) = C * 8 ^ k / (m : ℝ) ^ k := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : ((4 : ℝ) ^ m) ^ (-(k : ℝ) / 2) = 1 / ((2 : ℝ) ^ m) ^ k := by
    have : (4 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ (2 : ℕ) := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, ← Real.rpow_natCast ((2 : ℝ) ^ m) 2, ← Real.rpow_mul (by positivity)]
    have : ((2 : ℕ) : ℝ) * (-(k : ℝ) / 2) = -(k : ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
  have h2 : (2 : ℝ) ^ (m + 3) = 8 * 2 ^ m := by rw [pow_add]; norm_num; ring
  rw [h1, h2, div_pow, mul_pow]
  have : ((2 : ℝ) ^ m) ^ k ≠ 0 := by positivity
  have : (m : ℝ) ^ k ≠ 0 := by positivity
  field_simp

theorem errB_le (C : ℝ) (hC : 0 ≤ C) (k m₁ n : ℕ) (hk : 2 ≤ k) (hm : 2 ≤ m₁) :
    errB C k m₁ n ≤ ENNReal.ofReal (C * 8 ^ k / ((m₁ : ℝ) - 1)) := by
  unfold errB
  have hterm : ∀ m ∈ Finset.Icc m₁ n, ENNReal.ofReal
      (C * (2 ^ (m + 3) / (m : ℝ)) ^ k * ((4 : ℝ) ^ m) ^ (-(k : ℝ) / 2)) ≤
      ENNReal.ofReal (C * 8 ^ k * (1 / (m : ℝ) ^ 2)) := by
    intro m hmm
    rw [Finset.mem_Icc] at hmm
    have hm1 : 1 ≤ m := by omega
    rw [errB_term C k m hm1]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ k := pow_le_pow_right₀ hm1' hk
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.mul_sum]
  have := sum_inv_sq_le m₁ n hm
  calc C * 8 ^ k * ∑ m ∈ Finset.Icc m₁ n, 1 / (m : ℝ) ^ 2 ≤ C * 8 ^ k * (1 / ((m₁ : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = C * 8 ^ k / ((m₁ : ℝ) - 1) := by rw [mul_one_div]

theorem errD_le (C c : ℝ) (hC : 0 ≤ C) (m₁ n : ℕ) (hc : Real.log 16 + 1 ≤ c * m₁) (hm : 1 ≤ m₁) :
    errD C c m₁ n ≤ ENNReal.ofReal (C * 2 * Real.exp (-(m₁ : ℝ))) := by
  unfold errD
  have hterm : ∀ m ∈ Finset.Icc m₁ n, ENNReal.ofReal (C * ((4 : ℝ) ^ m) ^ 2 *
      Real.exp (-(c * ((m : ℝ) ^ 2)))) ≤ ENNReal.ofReal (C * Real.exp (-1) ^ m) := by
    intro m hmm
    rw [Finset.mem_Icc] at hmm
    refine ENNReal.ofReal_le_ofReal ?_
    have hmr : (m₁ : ℝ) ≤ m := by exact_mod_cast hmm.1
    have hc0 : Real.log 16 + 1 ≤ c * m := by
      have hc1 : 0 ≤ c := by
        by_contra hneg
        push Not at hneg
        have : c * m₁ < 0 := mul_neg_of_neg_of_pos hneg (by exact_mod_cast hm)
        have h16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
        linarith
      nlinarith
    have h16 : ((4 : ℝ) ^ m) ^ 2 = Real.exp (m * Real.log 16) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num), ← pow_mul, mul_comm, pow_mul]; norm_num
    have hmpos : (0 : ℝ) < m := by
      have : (1 : ℝ) ≤ m₁ := by exact_mod_cast hm
      linarith
    rw [h16, mul_assoc, ← Real.exp_add]
    have : (m : ℝ) * Real.log 16 + -(c * (m : ℝ) ^ 2) ≤ -(1 : ℝ) * m := by nlinarith
    calc C * Real.exp (↑m * Real.log 16 + -(c * (m : ℝ) ^ 2)) ≤ C * Real.exp (-(1 : ℝ) * m) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) hC
      _ = C * Real.exp (-1) ^ m := by rw [← Real.exp_nat_mul]; ring_nf
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.mul_sum]
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by
      have := Real.add_one_le_exp (1 : ℝ); linarith)
  have hgeo : ∑ m ∈ Finset.Icc m₁ n, Real.exp (-1) ^ m ≤ Real.exp (-1) ^ m₁ / (1 - Real.exp (-1)) := by
    have hI : Finset.Icc m₁ n = Finset.Ico m₁ (n + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI]
    exact geom_sum_Ico_le_of_lt_one hr0 (by linarith)
  have : Real.exp (-1) ^ m₁ / (1 - Real.exp (-1)) ≤ 2 * Real.exp (-(m₁ : ℝ)) := by
    rw [div_le_iff₀ (by linarith)]
    have : Real.exp (-1) ^ m₁ = Real.exp (-(m₁ : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [this]
    nlinarith [Real.exp_pos (-(m₁ : ℝ))]
  calc C * ∑ m ∈ Finset.Icc m₁ n, Real.exp (-1) ^ m ≤ C * (2 * Real.exp (-(m₁ : ℝ))) :=
        mul_le_mul_of_nonneg_left (hgeo.trans this) hC
    _ = C * 2 * Real.exp (-(m₁ : ℝ)) := by ring

theorem errBp_le (C : ℝ) (hC : 0 ≤ C) (k j : ℕ) (hk : 2 ≤ k) (hj : 1 ≤ j) :
    C * ((2 : ℝ) ^ j) ^ k * ((j : ℝ) * 4 ^ j) ^ (-(k : ℝ) / 2) ≤ C / j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h4 : ((4 : ℝ) ^ j) ^ (-(k : ℝ) / 2) = 1 / ((2 : ℝ) ^ j) ^ k := by
    have : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ (2 : ℕ) := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, ← Real.rpow_natCast ((2 : ℝ) ^ j) 2, ← Real.rpow_mul (by positivity)]
    have : ((2 : ℕ) : ℝ) * (-(k : ℝ) / 2) = -(k : ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
  rw [Real.mul_rpow hj0.le (by positivity), h4]
  have hpos : ((2 : ℝ) ^ j) ^ k ≠ 0 := by positivity
  have h5 : C * ((2 : ℝ) ^ j) ^ k * ((j : ℝ) ^ (-(k : ℝ) / 2) * (1 / ((2 : ℝ) ^ j) ^ k)) =
      C * (j : ℝ) ^ (-(k : ℝ) / 2) := by field_simp
  rw [h5]
  have h6 : (j : ℝ) ^ (-(k : ℝ) / 2) ≤ (j : ℝ) ^ (-(1 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hj1 ?_
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [Real.rpow_neg_one] at h6
  calc C * (j : ℝ) ^ (-(k : ℝ) / 2) ≤ C * (j : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h6 hC
    _ = C / j := by rw [div_eq_mul_inv]

theorem errC_le (C : ℝ) (hC : 0 ≤ C) (n : ℕ) (hn : 3 ≤ n) :
    C * ((n : ℝ) ^ 17 / 7) ^ (-(1 : ℝ) / 30) ≤ C / (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ 15 ≤ (n : ℝ) ^ 17 / 7 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (n : ℝ) ^ 17 = (n : ℝ) ^ 15 * (n : ℝ) ^ 2 := by ring
    rw [this]
    have : (7 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [pow_pos hn0 15]
  have h2 : ((n : ℝ) ^ 17 / 7) ^ (-(1 : ℝ) / 30) ≤ ((n : ℝ) ^ 15) ^ (-(1 : ℝ) / 30) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  have h3 : ((n : ℝ) ^ 15) ^ (-(1 : ℝ) / 30) = ((n : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast (n : ℝ) 15, ← Real.rpow_mul hn0.le, ← Real.rpow_neg hn0.le]
    congr 1; push_cast; ring
  rw [h3] at h2
  calc C * ((n : ℝ) ^ 17 / 7) ^ (-(1 : ℝ) / 30) ≤ C * ((n : ℝ) ^ (1 / 2 : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left h2 hC
    _ = C / (n : ℝ) ^ (1 / 2 : ℝ) := (div_eq_mul_inv C _).symm

theorem eta_le (j : ℕ) (hj : 1 ≤ j) :
    Real.exp (-((avoidLevel ((j : ℝ) * 4 ^ j) : ℕ) : ℝ) ^ 2) ≤ 1 / j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hT : (4 : ℝ) ^ j ≤ (j : ℝ) * 4 ^ j := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) j]
  have hlog : (j : ℝ) ≤ Real.logb 4 ((j : ℝ) * 4 ^ j) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    exact hT
  have hceil : j ≤ ⌈Real.logb 4 ((j : ℝ) * 4 ^ j)⌉₊ := by
    have := hlog.trans (Nat.le_ceil (Real.logb 4 ((j : ℝ) * 4 ^ j)))
    exact_mod_cast this
  set a := avoidLevel ((j : ℝ) * 4 ^ j) with ha
  have haj : j - 1 ≤ a := by unfold avoidLevel at ha; omega
  have haj' : (j : ℝ) - 1 ≤ a := by
    have : ((j - 1 : ℕ) : ℝ) ≤ a := by exact_mod_cast haj
    rw [Nat.cast_sub hj] at this; simpa using this
  have ha2 : (a : ℝ) ≤ (a : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) a
  calc Real.exp (-((a : ℕ) : ℝ) ^ 2) ≤ Real.exp (-((j : ℝ) - 1)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = 1 / Real.exp ((j : ℝ) - 1) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / j := by
        apply one_div_le_one_div_of_le hj0
        have := Real.add_one_le_exp ((j : ℝ) - 1)
        linarith

end ElboimSly.Paper.Escape
