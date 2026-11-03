/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Constants
public import ElboimSly.Paper.Base.ConstantsAsymp
public import Mathlib

/-!
# The threshold `n_K(d)`

Constants and thresholds of the base, "Existence of `n_K(d)`" (threshold (n6)): there is `N` such that
for all `n ≥ N`,
`C_𝒜(d) e^{-4ⁿ/12} + (2·4ⁿ)^d ε(n) ≤ e^{-n³}`.

Each of the five terms is handled by a separate lemma (`nK_F1`, `nK_F2`, `nK_F3`, `nK_F45`).
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper

theorem pow_eq_exp (b : ℝ) (hb : 0 < b) (n : ℕ) : b ^ n = Real.exp (Real.log b * n) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log hb]

theorem nK_F1 (A : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A * Real.exp (-(4 : ℝ) ^ n / 12) ≤ Real.exp (-(n : ℝ) ^ 3) / 2 := by
  set A' : ℝ := max A 1 with hA'
  have hA'1 : 1 ≤ A' := le_max_right _ _
  set L : ℝ := Real.log (2 * A') with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  obtain ⟨T1, hT1⟩ := exists_poly_le_exp 3 (Real.log 4) (12 * (1 + L))
    (Real.log_pos (by norm_num))
  refine ⟨max ⌈T1⌉₊ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnT1 : T1 ≤ n := (Nat.le_ceil T1).trans (by exact_mod_cast le_trans (le_max_left _ _) hn)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn3p : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnr
  have h1 := hT1 n hnT1
  have h4n : (4 : ℝ) ^ n = Real.exp (Real.log 4 * n) := pow_eq_exp 4 (by norm_num) n
  have h2 : (n : ℝ) ^ 3 + L ≤ (4 : ℝ) ^ n / 12 := by
    rw [h4n]
    have h3 : (n : ℝ) ^ 3 + L ≤ (1 + L) * (n : ℝ) ^ 3 := by
      nlinarith [mul_nonneg hL0 (sub_nonneg.2 hn3p)]
    linarith
  have h3 : A * Real.exp (-(4 : ℝ) ^ n / 12) ≤ A' * Real.exp (-(4 : ℝ) ^ n / 12) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have h4 : A' = Real.exp L / 2 := by
    rw [hL, Real.exp_log (by linarith)]; ring
  calc A * Real.exp (-(4 : ℝ) ^ n / 12) ≤ A' * Real.exp (-(4 : ℝ) ^ n / 12) := h3
    _ = Real.exp (L + -(4 : ℝ) ^ n / 12) / 2 := by rw [h4, Real.exp_add]; ring
    _ ≤ Real.exp (-(n : ℝ) ^ 3) / 2 := by
        gcongr
        linarith

theorem nK_F2 (c P Q : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 - c) ^ es8K n ≤ Real.exp (-((n : ℝ) ^ 3 + P * n + Q)) := by
  set M : ℝ := (1 + P + Q) / c + 1 with hM
  obtain ⟨T2, hT2⟩ := exists_poly_le_exp 8 (Real.log 1.9) (4 * M) (Real.log_pos (by norm_num))
  refine ⟨max ⌈T2⌉₊ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnT2 : T2 ≤ n := (Nat.le_ceil T2).trans (by exact_mod_cast le_trans (le_max_left _ _) hn)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn3p : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnr
  have hnn3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hnr (by norm_num)
  set w : ℝ := (n : ℝ) ^ 3 + P * n + Q with hw
  have hwle : w ≤ (1 + P + Q) * (n : ℝ) ^ 3 := by
    rw [hw]
    nlinarith [mul_nonneg hP (sub_nonneg.2 hnn3), mul_nonneg hQ (sub_nonneg.2 hn3p)]
  have hY : (0 : ℝ) < 4 * (n : ℝ) ^ 5 := by positivity
  have h19 : (1.9 : ℝ) ^ n = Real.exp (Real.log 1.9 * n) := pow_eq_exp 1.9 (by norm_num) n
  have h2 := hT2 n hnT2
  have hq : w / c + 1 ≤ M * (n : ℝ) ^ 3 := by
    have h1 : w / c ≤ (1 + P + Q) / c * (n : ℝ) ^ 3 := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hwle hc0.le
    rw [hM]
    nlinarith
  have hmain : (w / c + 1) * (4 * (n : ℝ) ^ 5) ≤ (1.9 : ℝ) ^ n := by
    rw [h19]
    refine le_trans ?_ h2
    calc (w / c + 1) * (4 * (n : ℝ) ^ 5) ≤ (M * (n : ℝ) ^ 3) * (4 * (n : ℝ) ^ 5) :=
          mul_le_mul_of_nonneg_right hq hY.le
      _ = 4 * M * (n : ℝ) ^ 8 := by ring
  have hr : w / c + 1 ≤ (1.9 : ℝ) ^ n / (4 * (n : ℝ) ^ 5) := (le_div_iff₀ hY).2 hmain
  have hk : (1.9 : ℝ) ^ n / (4 * (n : ℝ) ^ 5) - 1 ≤ (es8K n : ℝ) := by
    have := Nat.lt_floor_add_one ((1.9 : ℝ) ^ n / (4 * (n : ℝ) ^ 5))
    unfold es8K; linarith
  have hcw : w ≤ c * (es8K n : ℝ) := by
    have h1 : w / c ≤ (es8K n : ℝ) := by linarith
    have := (div_le_iff₀ hc0).1 h1
    linarith
  calc (1 - c) ^ es8K n ≤ (Real.exp (-c)) ^ es8K n := by
        refine pow_le_pow_left₀ (by linarith) ?_ _
        have := Real.add_one_le_exp (-c); linarith
    _ = Real.exp (-(c * es8K n)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-w) := Real.exp_le_exp.2 (by linarith)

theorem nK_F3 (S P Q : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 * (2 * 4 ^ (n + 1) / (n : ℝ) ^ 4 + 1) * Real.exp (S - (n : ℝ) ^ 5) ≤
        Real.exp (-((n : ℝ) ^ 3 + P * n + Q)) := by
  obtain ⟨N3, hN3⟩ := exists_nat_poly_le (Real.log 24 + S + Q) (Real.log 4 + P) 1
  refine ⟨max N3 1, fun n hn => ?_⟩
  have hn3 : N3 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h4n1 : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have h4n : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hnr
  have hfrac : 2 * (4 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4 ≤ 2 * 4 ^ (n + 1) := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hbound : 2 * (2 * (4 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4 + 1) ≤ 24 * 4 ^ n := by
    have : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
    nlinarith
  have hexp : 24 * (4 : ℝ) ^ n * Real.exp (S - (n : ℝ) ^ 5) ≤
      Real.exp (-((n : ℝ) ^ 3 + P * n + Q)) := by
    have h4 : (4 : ℝ) ^ n = Real.exp (Real.log 4 * n) := pow_eq_exp 4 (by norm_num) n
    have h24 : (24 : ℝ) = Real.exp (Real.log 24) := (Real.exp_log (by norm_num)).symm
    rw [h4, h24, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h5 := hN3 n hn3
    have hn45 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := pow_le_pow_right₀ hnr (by norm_num)
    linarith
  calc 2 * (2 * 4 ^ (n + 1) / (n : ℝ) ^ 4 + 1) * Real.exp (S - (n : ℝ) ^ 5)
      ≤ 24 * 4 ^ n * Real.exp (S - (n : ℝ) ^ 5) :=
        mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ ≤ _ := hexp

theorem nK_F45 (P Q : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) ^ 3 + P * n + Q ≤ (n : ℝ) ^ 4 / 2 := by
  obtain ⟨N5, hN5⟩ := exists_nat_poly_le (2 * Q) (2 * P) 2
  refine ⟨N5, fun n hn => ?_⟩
  have := hN5 n hn
  linarith

theorem exists_nK (d : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      es8CA d * Real.exp (-(4 : ℝ) ^ n / 12) + (2 * 4 ^ n) ^ d * es8Eps d n ≤
        Real.exp (-(n : ℝ) ^ 3) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hl2' : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  set P : ℝ := d * Real.log 4 with hP
  set Q : ℝ := d * Real.log 2 + Real.log 8 with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  obtain ⟨N1, h1⟩ := nK_F1 (es8CA d)
  obtain ⟨N2, h2⟩ := nK_F2 (es8C1 d) P Q (es8C1_pos d) (es8C1_lt_one d) hP0 hQ0
  obtain ⟨N3, h3⟩ := nK_F3 (4 * d * (Real.exp 1 - 1)) P Q
  obtain ⟨N5, h5⟩ := nK_F45 P Q
  refine ⟨max (max N1 N2) (max N3 N5), fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn5 : N5 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  set w : ℝ := (n : ℝ) ^ 3 + P * n + Q with hw
  have hpre : ((2 : ℝ) * 4 ^ n) ^ d = Real.exp (d * (Real.log 2 + n * Real.log 4)) := by
    calc ((2 : ℝ) * 4 ^ n) ^ d = (Real.exp (Real.log (2 * 4 ^ n))) ^ d := by
          rw [Real.exp_log (by positivity)]
      _ = Real.exp (d * Real.log (2 * 4 ^ n)) := (Real.exp_nat_mul _ _).symm
      _ = _ := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hew : Real.exp (-w) * ((2 : ℝ) * 4 ^ n) ^ d = Real.exp (-(n : ℝ) ^ 3) / 8 := by
    rw [hpre, ← Real.exp_add]
    have h8 : Real.exp (Real.log 8) = 8 := Real.exp_log (by norm_num)
    rw [eq_div_iff (by norm_num), ← h8, ← Real.exp_add]
    congr 1; rw [hw, hP, hQ]; ring
  have hF1 := h1 n hn1
  have hF2 := h2 n hn2
  have hF3 := h3 n hn3
  have hw5 := h5 n hn5
  have hF4 : Real.exp (-(n : ℝ) ^ 4) ≤ Real.exp (-w) := by
    refine Real.exp_le_exp.2 ?_
    have : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
    linarith
  have hF5 : ((2 : ℝ) ^ (n ^ 4))⁻¹ ≤ Real.exp (-w) := by
    have h2' : ((2 : ℝ) ^ (n ^ 4)) = Real.exp (Real.log 2 * ((n ^ 4 : ℕ) : ℝ)) :=
      pow_eq_exp 2 (by norm_num) _
    rw [h2', ← Real.exp_neg]
    refine Real.exp_le_exp.2 ?_
    push_cast
    have : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
    nlinarith
  have hε : es8Eps d n ≤ 4 * Real.exp (-w) := by
    unfold es8Eps
    linarith
  have hpos : (0 : ℝ) ≤ ((2 : ℝ) * 4 ^ n) ^ d := by positivity
  calc es8CA d * Real.exp (-(4 : ℝ) ^ n / 12) + (2 * 4 ^ n) ^ d * es8Eps d n ≤
        Real.exp (-(n : ℝ) ^ 3) / 2 + ((2 : ℝ) * 4 ^ n) ^ d * (4 * Real.exp (-w)) := by
        gcongr
    _ = Real.exp (-(n : ℝ) ^ 3) / 2 + 4 * (Real.exp (-w) * ((2 : ℝ) * 4 ^ n) ^ d) := by ring
    _ = Real.exp (-(n : ℝ) ^ 3) := by rw [hew]; ring

end ElboimSly.Paper
