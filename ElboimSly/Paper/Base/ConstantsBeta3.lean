/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ConstantsBeta2
public import Mathlib

/-!
# The threshold `β_0(d)`: condition (B4)

Constants and thresholds of the base, "Existence of `β_0(d)`".  The first term of (B4) is
`≤ 6 (2R+1)^{2d} e^{-c (x-1)^{1/10}/4}` and the second is
`C_{9.4} e^{-(x/2)^{ζ²/4}}`, with `x = e^{δ t}`, `R ≤ t² e^{t/2}`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper

theorem exists_B4a {d : ℕ} (hd : 1 ≤ d) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ t →
      2 * (2 * ((n : ℝ) ^ 2 * Real.exp (t / 2)) + 1) ^ d *
        ((2 * ((n : ℝ) ^ 2 * Real.exp (t / 2)) + 1) ^ ((2 * d : ℝ) / 5) + 2) *
        Real.exp (-es8Cocc d * (Real.exp (indDelta d * t) - 1) ^ ((1 : ℝ) / 10) / 4) ≤
      (1 / 4) * Real.exp (-t ^ 3) := by
  have hδ := indDelta_pos hd
  have hc : 0 < es8Cocc d := Brownian.cocc_pos d
  obtain ⟨T1, hT1⟩ := exists_B1 hd
  set K : ℝ := Real.log (24 * 9 ^ d) + 5 * d + 1 with hK
  obtain ⟨T2, hT2⟩ := exists_poly_le_exp 3 (indDelta d / 10) (8 * K / es8Cocc d) (by positivity)
  refine ⟨max 1 (max T1 T2), le_max_left _ _, fun t ht n hn1 hnt => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have htT1 : T1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htT2 : T2 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set x := Real.exp (indDelta d * t) with hx
  have hx4 : 4 ≤ x := hT1 t htT1
  set u : ℝ := 2 * ((n : ℝ) ^ 2 * Real.exp (t / 2)) + 1 with hu
  have hE1 : (1 : ℝ) ≤ Real.exp (t / 2) := Real.one_le_exp (by linarith)
  have hu1 : (1 : ℝ) ≤ u := by
    have : 0 ≤ (n : ℝ) ^ 2 * Real.exp (t / 2) := by positivity
    rw [hu]; linarith
  -- (a) the prefactor
  have hud : (1 : ℝ) ≤ u ^ d := one_le_pow₀ hu1
  have hrp : u ^ ((2 * d : ℝ) / 5) ≤ u ^ d := by
    calc u ^ ((2 * d : ℝ) / 5) ≤ u ^ ((d : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu1 (by
            have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
            linarith)
      _ = u ^ d := Real.rpow_natCast _ _
  have ha : 2 * u ^ d * (u ^ ((2 * d : ℝ) / 5) + 2) ≤ 6 * u ^ (2 * d) := by
    have : u ^ (2 * d) = u ^ d * u ^ d := by rw [two_mul, pow_add]
    rw [this]
    nlinarith
  -- (b) bound on u
  have hn2 : (n : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) hnt 2
  have ht2 : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ ht1
  have hprod : (1 : ℝ) ≤ t ^ 2 * Real.exp (t / 2) := by nlinarith
  have hub : u ≤ 3 * (t ^ 2 * Real.exp (t / 2)) := by
    rw [hu]
    have : (n : ℝ) ^ 2 * Real.exp (t / 2) ≤ t ^ 2 * Real.exp (t / 2) :=
      mul_le_mul_of_nonneg_right hn2 (Real.exp_pos _).le
    linarith
  have h9 : (3 : ℝ) ^ (2 * d) = 9 ^ d := by rw [pow_mul]; norm_num
  have hE2 : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE : Real.exp (t / 2) ^ (2 * d) = Real.exp t ^ d := by rw [pow_mul, hE2]
  have hu2d : u ^ (2 * d) ≤ 9 ^ d * (Real.exp t ^ d * (t ^ 2) ^ (2 * d)) := by
    calc u ^ (2 * d) ≤ (3 * (t ^ 2 * Real.exp (t / 2))) ^ (2 * d) :=
          pow_le_pow_left₀ (by linarith) hub _
      _ = 3 ^ (2 * d) * ((t ^ 2) ^ (2 * d) * Real.exp (t / 2) ^ (2 * d)) := by
          rw [mul_pow, mul_pow]
      _ = 9 ^ d * (Real.exp t ^ d * (t ^ 2) ^ (2 * d)) := by rw [h9, hE]; ring
  -- (c) the exponent
  set y : ℝ := Real.exp (indDelta d / 10 * t) with hy
  have hxy : y / 2 ≤ (x - 1) ^ ((1 : ℝ) / 10) := by
    have h1 : x / 2 ≤ x - 1 := by linarith
    have h2 : (x / 2) ^ ((1 : ℝ) / 10) ≤ (x - 1) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    refine le_trans ?_ h2
    have h3 : x / 2 = Real.exp (indDelta d * t - Real.log 2) := by
      rw [hx, Real.exp_sub, Real.exp_log (by norm_num)]
    rw [h3, rpow_exp_eq]
    have h4 : Real.exp ((indDelta d * t - Real.log 2) * (1 / 10)) =
        y * Real.exp (-(Real.log 2 / 10)) := by
      rw [hy, ← Real.exp_add]; congr 1; ring
    rw [h4]
    have h5 : (1 : ℝ) / 2 ≤ Real.exp (-(Real.log 2 / 10)) := by
      have : (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      rw [this]
      exact Real.exp_le_exp.2 (by linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)])
    have hy0 : 0 < y := Real.exp_pos _
    nlinarith
  have hexp : Real.exp (-es8Cocc d * (x - 1) ^ ((1 : ℝ) / 10) / 4) ≤
      Real.exp (-(es8Cocc d * y / 8)) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  -- (d) the polynomial factors
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have htE : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hpoly : (t ^ 2) ^ (2 * d) ≤ Real.exp t ^ (4 * d) := by
    rw [← pow_mul, show 2 * (2 * d) = 4 * d by ring]
    exact pow_le_pow_left₀ ht0 htE _
  have hcomb : Real.exp t ^ d * Real.exp t ^ (4 * d) = Real.exp (5 * d * t) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hlog0 : 0 ≤ Real.log (24 * 9 ^ d) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ 9 ^ d := one_le_pow₀ (by norm_num)
    linarith)
  have hT2t := hT2 t htT2
  have ht3 : (1 : ℝ) ≤ t ^ 3 := one_le_pow₀ ht1
  have ht3' : t ≤ t ^ 3 := by nlinarith
  have hyK : K * t ^ 3 ≤ es8Cocc d * y / 8 := by
    have : 8 * K / es8Cocc d * t ^ 3 ≤ y := hT2t
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at this
    linarith [mul_comm y (es8Cocc d)]
  have hkey : Real.log (24 * 9 ^ d) + 5 * d * t + t ^ 3 ≤ es8Cocc d * y / 8 := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : Real.log (24 * 9 ^ d) + 5 * d * t + t ^ 3 ≤ K * t ^ 3 := by
      have e : K * t ^ 3 = Real.log (24 * 9 ^ d) * t ^ 3 + 5 * d * t ^ 3 + t ^ 3 := by
        rw [hK]; ring
      have p1 : 0 ≤ Real.log (24 * 9 ^ d) * (t ^ 3 - 1) :=
        mul_nonneg hlog0 (sub_nonneg.2 ht3)
      have p2 : 0 ≤ (d : ℝ) * (t ^ 3 - t) := mul_nonneg hd0 (sub_nonneg.2 ht3')
      rw [e]
      linarith
    linarith
  have hfin : 6 * 9 ^ d * Real.exp (5 * d * t) * Real.exp (-(es8Cocc d * y / 8)) ≤
      (1 / 4) * Real.exp (-t ^ 3) := by
    have h24 : (24 : ℝ) * 9 ^ d = Real.exp (Real.log (24 * 9 ^ d)) :=
      (Real.exp_log (by positivity)).symm
    have : 6 * (9 : ℝ) ^ d * Real.exp (5 * d * t) * Real.exp (-(es8Cocc d * y / 8)) =
        (1 / 4) * Real.exp (Real.log (24 * 9 ^ d) + 5 * d * t - es8Cocc d * y / 8) := by
      rw [Real.exp_sub, Real.exp_add, ← h24]
      rw [Real.exp_neg]; field_simp; ring
    rw [this]
    gcongr
    linarith
  calc 2 * u ^ d * (u ^ ((2 * d : ℝ) / 5) + 2) * Real.exp (-es8Cocc d * (x - 1) ^ ((1 : ℝ) / 10) / 4)
      ≤ 6 * u ^ (2 * d) * Real.exp (-(es8Cocc d * y / 8)) := by
        gcongr
    _ ≤ 6 * (9 ^ d * (Real.exp t ^ d * (t ^ 2) ^ (2 * d))) * Real.exp (-(es8Cocc d * y / 8)) := by
        gcongr
    _ ≤ 6 * (9 ^ d * (Real.exp t ^ d * Real.exp t ^ (4 * d))) *
          Real.exp (-(es8Cocc d * y / 8)) := by
        gcongr
    _ = 6 * 9 ^ d * Real.exp (5 * d * t) * Real.exp (-(es8Cocc d * y / 8)) := by
        rw [← hcomb]; ring
    _ ≤ _ := hfin

end ElboimSly.Paper
