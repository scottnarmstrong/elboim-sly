/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Levels
public import ElboimSly.Paper.Step.TravelNum
public import Mathlib

/-!
# Numerics of the block decomposition in Lemmas 7.3 and 7.4

ES22 Lemma 7.3; ES22 Lemma 7.4. For `A ≥ 1`, `k := ⌈A⌉` blocks of length `h := B / k`;
the second-moment bound `6dh + 2h^{2θ_H} + K² e^{-n(h)²} ≤ 7dh`; and the Freedman exponent.
-/

@[expose] public section

open Filter Topology Set

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- `k = ⌈A⌉` is between `A` and `2A`. -/
theorem blocks_k {A : ℝ} (hA : 1 ≤ A) :
    1 ≤ ⌈A⌉₊ ∧ A ≤ (⌈A⌉₊ : ℝ) ∧ (⌈A⌉₊ : ℝ) ≤ 2 * A := by
  refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne', Nat.le_ceil A, ?_⟩
  have := Nat.ceil_lt_add_one (by linarith : 0 ≤ A)
  linarith

/-- Block lengths `h = B / k` with `A ≤ k ≤ 2A`. -/
theorem blocks_h {A B : ℝ} {k : ℕ} (hA : 0 < A) (hB : 0 < B) (hk1 : A ≤ k) (hk2 : (k : ℝ) ≤ 2 * A) :
    B / (2 * A) ≤ B / k ∧ B / k ≤ B / A ∧ (k : ℝ) * (B / k) = B := by
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le hA hk1
  refine ⟨?_, ?_, by field_simp⟩
  · exact div_le_div_of_nonneg_left hB.le hkpos hk2
  · exact div_le_div_of_nonneg_left hB.le hA hk1

/-- `2 h^{2θ_H} ≤ h / 2` for `h ≥ 4096`. -/
theorem two_mul_rpow_theta_le {h : ℝ} (hh : 4096 ≤ h) : 2 * h ^ (2 * indThetaH) ≤ h / 2 := by
  have hh0 : 0 < h := by linarith
  have hθ : 2 * indThetaH = 41 / 50 := by unfold indThetaH; norm_num
  rw [hθ]
  set y : ℝ := h ^ ((9 : ℝ) / 50) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hh0 _
  have hy50 : y ^ 50 = h ^ 9 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hh0.le]; norm_num
  have hy4 : 4 ≤ y := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : y ^ 50 < 4 ^ 50 := pow_lt_pow_left₀ hcon hy0.le (by norm_num)
    have h2 : (4096 : ℝ) ^ 9 ≤ h ^ 9 := pow_le_pow_left₀ (by norm_num) hh 9
    rw [hy50] at h1
    norm_num at h1 h2
    linarith
  have hsplit : h ^ ((41 : ℝ) / 50) * y = h := by
    rw [hy, ← Real.rpow_add hh0]; norm_num
  have hpos : 0 < h ^ ((41 : ℝ) / 50) := Real.rpow_pos_of_pos hh0 _
  nlinarith

/-- A lower bound on the level of `h` from a lower bound on `log₄ h`. -/
theorem exp_neg_level_sq_le {h : ℝ} (hh : 1 < h) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m + 1 ≤ Real.logb 4 h) : Real.exp (-((stepLevel h : ℝ) ^ 2)) ≤ Real.exp (-m ^ 2) := by
  have h1 := stepLevel_ge_logb hh
  have h2 : m ≤ (stepLevel h : ℝ) := by linarith
  apply Real.exp_le_exp.2
  nlinarith

/-- The Freedman exponent of Lemma 7.3: with `u = t^{1/15} ≥ 64 n⁶`, `1 ≤ d ≤ n`, block length
`h ≤ u⁵`, `k h = u^{10}`, truncation level `K = n³ h` and `x = u⁶/4`:
`n³ ≤ x² / (2 (7 d k h + K x / 3))`. -/
theorem freedman_exponent_73 {u h n d : ℝ} (hn : 1 ≤ n) (hd : d ≤ n) (hd1 : 1 ≤ d)
    (hu : 64 * n ^ 6 ≤ u) (hh0 : 0 ≤ h) (hh : h ≤ u ^ 5) :
    n ^ 3 ≤ (u ^ 6 / 4) ^ 2 / (2 * (7 * d * u ^ 10 + n ^ 3 * h * (u ^ 6 / 4) / 3)) := by
  have hn6 : (1 : ℝ) ≤ n ^ 6 := one_le_pow₀ hn
  have hu64 : 64 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hn0 : 0 < n := by linarith
  have hden : 0 < 2 * (7 * d * u ^ 10 + n ^ 3 * h * (u ^ 6 / 4) / 3) := by positivity
  rw [le_div_iff₀ hden]
  have h10 : 0 < u ^ 10 := by positivity
  have e1 : d * n ^ 3 ≤ n ^ 6 := by
    calc d * n ^ 3 ≤ n * n ^ 3 := by gcongr
      _ = n ^ 4 := by ring
      _ ≤ n ^ 6 := pow_le_pow_right₀ hn (by norm_num)
  have e2 : n ^ 6 ≤ u / 64 := by linarith
  have e3 : n ^ 3 * h * (u ^ 6 / 4) / 3 ≤ n ^ 3 * u ^ 11 / 12 := by
    have : h * u ^ 6 ≤ u ^ 5 * u ^ 6 := by gcongr
    have h3 : 0 ≤ n ^ 3 := by positivity
    calc n ^ 3 * h * (u ^ 6 / 4) / 3 = n ^ 3 * (h * u ^ 6) / 12 := by ring
      _ ≤ n ^ 3 * (u ^ 5 * u ^ 6) / 12 := by gcongr
      _ = n ^ 3 * u ^ 11 / 12 := by ring
  have e4 : n ^ 3 * n ^ 3 = n ^ 6 := by ring
  have f1 : 14 * (d * n ^ 3) * u ^ 10 ≤ 14 * (u / 64) * u ^ 10 := by
    have : d * n ^ 3 ≤ u / 64 := e1.trans e2
    gcongr
  have f2 : n ^ 6 * u ^ 11 ≤ u / 64 * u ^ 11 := by gcongr
  have f3 : (u / 64) * u ^ 10 * 14 ≤ u ^ 12 / 32 := by
    have : u ^ 12 = u ^ 2 * u ^ 10 := by ring
    rw [this]
    have h2 : 64 * 14 ≤ u ^ 2 / 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 h10.le]
  have f4 : u / 64 * u ^ 11 / 6 ≤ u ^ 12 / 32 := by
    have : u ^ 12 = u * u ^ 11 := by ring
    rw [this]; nlinarith [pow_pos hu0 11]
  calc n ^ 3 * (2 * (7 * d * u ^ 10 + n ^ 3 * h * (u ^ 6 / 4) / 3))
      ≤ n ^ 3 * (2 * (7 * d * u ^ 10 + n ^ 3 * u ^ 11 / 12)) := by gcongr
    _ = 14 * (d * n ^ 3) * u ^ 10 + n ^ 6 * u ^ 11 / 6 := by ring
    _ ≤ 14 * (u / 64) * u ^ 10 + u / 64 * u ^ 11 / 6 := by gcongr
    _ ≤ u ^ 12 / 32 + u ^ 12 / 32 := by nlinarith [f3, f4]
    _ = (u ^ 6 / 4) ^ 2 := by ring

/-- The regime gives `4ⁿ < t_n ≤ 4^{n+1}`. -/
theorem indScale_bounds {n : ℕ} {t₀ : ℝ} (ht : t₀ ∈ Ioc (1 : ℝ) 4) :
    (4 : ℝ) ^ n < indScale t₀ n ∧ indScale t₀ n ≤ 4 ^ (n + 1) := by
  unfold indScale
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  refine ⟨?_, ?_⟩
  · nlinarith [ht.1]
  · rw [pow_succ]; nlinarith [ht.2]

end ElboimSly.Paper.Step
