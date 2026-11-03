/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ConstantsBeta3
public import Mathlib

/-!
# The threshold `β_0(d)`: assembly

Constants and thresholds of the base, "Existence of `β_0(d)`".

* `exists_B4b`: the second term of (B4).
* `exists_beta0`: there is `β_0 ≥ 1` such that all of (B1)-(B4) hold for `β ≥ β_0`.
* `es8Beta0`: the chosen `β_0(d)`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper

theorem exists_B4b {d : ℕ} (hd : 1 ≤ d) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      es8C94 d * Real.exp (-(Real.exp (indDelta d * t) / 2) ^ (es8Zeta d ^ 2 / 4)) ≤
        (1 / 4) * Real.exp (-t ^ 3) := by
  have hδ := indDelta_pos hd
  have hζ := es8Zeta_pos hd
  have hζ1 := es8Zeta_le hd
  set κ : ℝ := es8Zeta d ^ 2 / 4 with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    rw [hκ]; nlinarith
  set Mc : ℝ := Real.log (4 * (|es8C94 d| + 1)) with hMc
  have hMc0 : 0 ≤ Mc := Real.log_nonneg (by nlinarith [abs_nonneg (es8C94 d)])
  obtain ⟨T, hT⟩ := exists_poly_le_exp 3 (κ * indDelta d) (2 * (Mc + 1)) (by positivity)
  refine ⟨max 1 T, le_max_left _ _, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have htT : T ≤ t := le_trans (le_max_right _ _) ht
  have ht3 : (1 : ℝ) ≤ t ^ 3 := one_le_pow₀ ht1
  set y : ℝ := (Real.exp (indDelta d * t) / 2) ^ κ with hy
  have hy1 : Real.exp (κ * indDelta d * t) / 2 ≤ y := by
    have h1 : Real.exp (indDelta d * t) / 2 = Real.exp (indDelta d * t - Real.log 2) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num)]
    rw [hy, h1, rpow_exp_eq]
    have h2 : Real.exp ((indDelta d * t - Real.log 2) * κ) =
        Real.exp (κ * indDelta d * t) * Real.exp (-(κ * Real.log 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    have h3 : (1 : ℝ) / 2 ≤ Real.exp (-(κ * Real.log 2)) := by
      have : (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      rw [this]
      exact Real.exp_le_exp.2 (by
        have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
        nlinarith)
    have h4 := Real.exp_pos (κ * indDelta d * t)
    nlinarith
  have hT3 := hT t htT
  have hyM : Mc + t ^ 3 ≤ y := by
    have : (Mc + 1) * t ^ 3 ≤ y := by
      have : 2 * (Mc + 1) * t ^ 3 ≤ Real.exp (κ * indDelta d * t) := hT3
      linarith
    nlinarith [mul_nonneg hMc0 (sub_nonneg.2 ht3)]
  have hc : es8C94 d ≤ |es8C94 d| + 1 := by linarith [le_abs_self (es8C94 d)]
  have hpos : 0 < 4 * (|es8C94 d| + 1) := by positivity
  calc es8C94 d * Real.exp (-y) ≤ (|es8C94 d| + 1) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ ≤ (|es8C94 d| + 1) * Real.exp (-(Mc + t ^ 3)) := by
        gcongr
    _ = (1 / 4) * Real.exp (-t ^ 3) := by
        rw [neg_add, Real.exp_add, Real.exp_neg Mc, hMc, Real.exp_log hpos]
        field_simp

theorem exists_beta0 {d : ℕ} (hd : 1 ≤ d) :
    ∃ β₀ : ℝ, 1 ≤ β₀ ∧ ∀ β : ℝ, β₀ ≤ β → es8BetaCond d β := by
  obtain ⟨T1, h1⟩ := exists_B1 hd
  obtain ⟨T2, hT21, h2⟩ := exists_B2 hd
  obtain ⟨T3, h3⟩ := exists_B3 hd
  obtain ⟨T4, hT41, h4⟩ := exists_B4a hd
  obtain ⟨T5, hT51, h5⟩ := exists_B4b hd
  set T : ℝ := max (max T1 T2) (max (max T3 T4) T5) with hT
  have hT1 : T1 ≤ T := by simp [hT]
  have hT2 : T2 ≤ T := by simp [hT]
  have hT3 : T3 ≤ T := by simp [hT]
  have hT4 : T4 ≤ T := by simp [hT]
  have hT5 : T5 ≤ T := by simp [hT]
  refine ⟨Real.exp T, Real.one_le_exp (by linarith), fun β hβ => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le (Real.exp_pos _) hβ
  set t : ℝ := Real.log β with ht
  have htT : T ≤ t := by
    rw [ht]; exact (Real.le_log_iff_exp_le hβ0).2 hβ
  have hβt : β = Real.exp t := (Real.exp_log hβ0).symm
  have hx : β ^ indDelta d = Real.exp (indDelta d * t) := by
    rw [Real.rpow_def_of_pos hβ0, mul_comm]
  have hsq : Real.sqrt β = Real.exp (t / 2) := by
    have e : Real.exp (t / 2) ^ 2 = β := by
      rw [← Real.exp_nat_mul, hβt]; congr 1; push_cast; ring
    rw [← e, Real.sqrt_sq (Real.exp_pos _).le]
  have hn : ∀ n : ℕ, (4 : ℝ) ^ n < β → (n : ℝ) ≤ t := fun n hn4 =>
    le_of_four_pow_lt (by rw [← hβt]; exact hn4)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hx]; exact h1 t (le_trans hT1 htT)
  · intro n hn1 hn4
    rw [hx]; exact h2 t (le_trans hT2 htT) n hn1 (hn n hn4)
  · rw [hx]; exact h3 t (le_trans hT3 htT)
  · intro n hn1 hn4
    rw [hsq, hx]
    have hnt := hn n hn4
    have e1 := h4 t (le_trans hT4 htT) n hn1 hnt
    have e2 := h5 t (le_trans hT5 htT)
    have e3 : Real.exp (-t ^ 3) ≤ Real.exp (-(n : ℝ) ^ 3) := by
      refine Real.exp_le_exp.2 ?_
      have : (n : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg n) hnt 3
      linarith
    linarith

open Classical in
/-- Constants and thresholds of the base: the threshold `β_0(d)`. -/
noncomputable def es8Beta0 (d : ℕ) : ℝ :=
  if h : 1 ≤ d then Classical.choose (exists_beta0 h) else 1

theorem es8Beta0_spec {d : ℕ} (hd : 1 ≤ d) :
    1 ≤ es8Beta0 d ∧ ∀ β : ℝ, es8Beta0 d ≤ β → es8BetaCond d β := by
  unfold es8Beta0
  rw [dite_eq_left hd]
  exact Classical.choose_spec (exists_beta0 hd)

/-- Constants and thresholds of the base: the threshold `n_K(d)`. -/
noncomputable def es8nK (d : ℕ) : ℕ := Classical.choose (exists_nK d)

theorem es8nK_spec (d : ℕ) : ∀ n : ℕ, es8nK d ≤ n →
    es8CA d * Real.exp (-(4 : ℝ) ^ n / 12) + (2 * 4 ^ n) ^ d * es8Eps d n ≤
      Real.exp (-(n : ℝ) ^ 3) :=
  Classical.choose_spec (exists_nK d)

/-- Constants and thresholds of the base: `n_0(d) = max {20, 2d, 77, n_1(d), n_𝒞(d), n_2(d), n_{3.9},
n_K(d)}`. -/
noncomputable def es8n0 (d : ℕ) : ℕ :=
  max 20 (max (2 * d) (max 77 (max (es8n1 d) (max (ElboimSly.SRW.lem82nC d) (max (ElboimSly.SRW.lem82n2 d)
    (max 14980 (es8nK d)))))))

end ElboimSly.Paper
