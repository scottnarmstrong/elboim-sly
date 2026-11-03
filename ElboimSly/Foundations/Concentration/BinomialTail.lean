/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.Binomial

/-!
# Chernoff bounds for the binomial law

Binomial tails (a)-(c).
-/

public section

namespace ElboimSly

open Finset

/-- `e⁻¹ ≤ 3/8`. -/
lemma exp_neg_one_le : Real.exp (-1) ≤ 3 / 8 := by
  have := Real.exp_one_gt_d9
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num at this ⊢
  linarith

/-- Binomial tails (a), first bound. -/
theorem concBinomLE_le_exp {K : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    concBinomLE K p m ≤ Real.exp (m - (1 - Real.exp (-1)) * K * p) := by
  have hx0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hx1 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  have h1 : concBinomLE K p m ≤
      ∑ i ∈ range (K + 1), Real.exp m * (concBinomWeight K p i * Real.exp (-1) ^ i) := by
    unfold concBinomLE
    refine Finset.sum_le_sum fun i _ => ?_
    have hw := concBinomWeight_nonneg (K := K) hp0 hp1 i
    have hexp : Real.exp m * Real.exp (-1) ^ i = Real.exp ((m : ℝ) - i) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    have : Real.exp m * (concBinomWeight K p i * Real.exp (-1) ^ i) =
        concBinomWeight K p i * Real.exp ((m : ℝ) - i) := by
      rw [← hexp]; ring
    rw [this]
    split_ifs with h
    · have : (1 : ℝ) ≤ Real.exp ((m : ℝ) - i) := by
        rw [Real.one_le_exp_iff]
        have : (i : ℝ) ≤ m := by exact_mod_cast h
        linarith
      nlinarith
    · exact mul_nonneg hw (Real.exp_pos _).le
  have h2 : ∑ i ∈ range (K + 1), Real.exp m * (concBinomWeight K p i * Real.exp (-1) ^ i) =
      Real.exp m * (1 - p + p * Real.exp (-1)) ^ K := by
    rw [← Finset.mul_sum, concBinomWeight_sum_mul_pow]
  have h3 : (1 - p + p * Real.exp (-1)) ^ K ≤ Real.exp (-((1 - Real.exp (-1)) * p)) ^ K := by
    refine pow_le_pow_left₀ ?_ ?_ K
    · nlinarith
    · have := Real.add_one_le_exp (-((1 - Real.exp (-1)) * p))
      linarith
  have h4 : Real.exp (-((1 - Real.exp (-1)) * p)) ^ K =
      Real.exp (-((1 - Real.exp (-1)) * K * p)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  calc concBinomLE K p m ≤ _ := h1
    _ = _ := h2
    _ ≤ Real.exp m * Real.exp (-((1 - Real.exp (-1)) * K * p)) :=
        mul_le_mul_of_nonneg_left (h3.trans h4.le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-- Binomial tails (a), second bound. -/
theorem concBinomLE_le_exp_div_eight {K : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (hm : 2 * (m : ℝ) ≤ K * p) : concBinomLE K p m ≤ Real.exp (-(K * p / 8)) := by
  refine (concBinomLE_le_exp hp0 hp1 m).trans (Real.exp_le_exp.2 ?_)
  have h := exp_neg_one_le
  have hKp : 0 ≤ (K : ℝ) * p := by positivity
  nlinarith

/-- Binomial tails (c), general form. -/
theorem concBinomLE_le_exp_cube {n K : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hKp : ((n : ℝ) ^ 3 - 1) / 2 ≤ K * p) {m : ℤ} (hm : m ≤ 5) :
    concBinomLE K p m ≤ Real.exp (-((n : ℝ) ^ 3 / 17)) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hcube : (27 : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
  rcases lt_or_ge m 0 with hneg | hnn
  · rw [concBinomLE_of_neg K p hneg]; exact (Real.exp_pos _).le
  · have h5 : concBinomLE K p m ≤ concBinomLE K p ((5 : ℕ) : ℤ) :=
      concBinomLE_mono hp0 hp1 (by simpa using hm)
    have h6 := concBinomLE_le_exp_div_eight (K := K) hp0 hp1 (m := 5) (by push_cast; linarith)
    refine h5.trans (h6.trans (Real.exp_le_exp.2 ?_))
    linarith

/-- Binomial tails (c), third example (ES22 §7). -/
theorem concBinomLE_le_exp_cube_sub_one_half {n : ℕ} (hn : 3 ≤ n) :
    concBinomLE (n ^ 3 - 1) (1 / 2) 2 ≤ Real.exp (-((n : ℝ) ^ 3 / 17)) := by
  have h1 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ (by omega)
  refine concBinomLE_le_exp_cube hn (by norm_num) (by norm_num) ?_ (by norm_num)
  rw [Nat.cast_sub h1]
  push_cast
  linarith

end ElboimSly
