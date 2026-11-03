/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ConstantsN
public import Mathlib

/-!
# The threshold `β_0(d)`

Constants and thresholds of the base, "Existence of `β_0(d)`": the conditions (B1)-(B4) hold for every
`β ≥ β_0`.  With `t = log β` and `x = β^δ = e^{δ t}`, all four compare a positive power of `β`
with a power of `log β`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper

/-- Constants and thresholds of the base, thresholds on `β`: the conditions (B1)-(B4). -/
def es8BetaCond (d : ℕ) (β : ℝ) : Prop :=
  -- (B1)
  4 ≤ β ^ indDelta d ∧
  -- (B2)
  (∀ n : ℕ, 1 ≤ n → (4 : ℝ) ^ n < β →
    2 * (n : ℝ) ^ 10 ≤ (⌊β ^ indDelta d⌋₊ : ℝ) ∧
      (5 * (n : ℝ) ^ 10) ^ ((5 * d : ℝ) / 2) < (⌊β ^ indDelta d⌋₊ : ℝ)) ∧
  -- (B3)
  20 ≤ (β ^ indDelta d / 2) ^ (es8Zeta d ^ 3) ∧
  -- (B4)
  (∀ n : ℕ, 1 ≤ n → (4 : ℝ) ^ n < β →
    2 * (2 * ((n : ℝ) ^ 2 * Real.sqrt β) + 1) ^ d *
        ((2 * ((n : ℝ) ^ 2 * Real.sqrt β) + 1) ^ ((2 * d : ℝ) / 5) + 2) *
        Real.exp (-es8Cocc d * (β ^ indDelta d - 1) ^ ((1 : ℝ) / 10) / 4) +
      es8C94 d * Real.exp (-(β ^ indDelta d / 2) ^ (es8Zeta d ^ 2 / 4)) ≤
      (1 / 2) * Real.exp (-(n : ℝ) ^ 3))

theorem indDelta_pos {d : ℕ} (hd : 1 ≤ d) : 0 < indDelta d := by
  unfold indDelta
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

theorem one_lt_log_four : 1 < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem le_of_four_pow_lt {t : ℝ} {n : ℕ} (h : (4 : ℝ) ^ n < Real.exp t) : (n : ℝ) ≤ t := by
  have h4 : (4 : ℝ) ^ n = Real.exp (Real.log 4 * n) := pow_eq_exp 4 (by norm_num) n
  rw [h4] at h
  have := Real.exp_lt_exp.1 h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [one_lt_log_four]

theorem rpow_exp_eq (t a : ℝ) : Real.exp t ^ a = Real.exp (t * a) := by
  exact (Real.exp_mul t a).symm

theorem exists_B1 {d : ℕ} (hd : 1 ≤ d) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → 4 ≤ Real.exp (indDelta d * t) := by
  have hδ := indDelta_pos hd
  refine ⟨Real.log 4 / indDelta d, fun t ht => ?_⟩
  have : Real.log 4 ≤ indDelta d * t := by
    rwa [div_le_iff₀ hδ, mul_comm] at ht
  calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
    _ ≤ _ := Real.exp_le_exp.2 this

theorem exists_B3 {d : ℕ} (hd : 1 ≤ d) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → 20 ≤ (Real.exp (indDelta d * t) / 2) ^ (es8Zeta d ^ 3) := by
  have hδ := indDelta_pos hd
  have hζ := es8Zeta_pos hd
  have hζ3 : 0 < es8Zeta d ^ 3 := by positivity
  refine ⟨(Real.log 20 / es8Zeta d ^ 3 + Real.log 2) / indDelta d, fun t ht => ?_⟩
  have h1 : Real.log 20 / es8Zeta d ^ 3 + Real.log 2 ≤ indDelta d * t := by
    rwa [div_le_iff₀ hδ, mul_comm] at ht
  have h2 : (Real.exp (indDelta d * t) / 2) = Real.exp (indDelta d * t - Real.log 2) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  rw [h2, rpow_exp_eq]
  calc (20 : ℝ) = Real.exp (Real.log 20) := (Real.exp_log (by norm_num)).symm
    _ ≤ _ := Real.exp_le_exp.2 (by
        have : Real.log 20 / es8Zeta d ^ 3 ≤ indDelta d * t - Real.log 2 := by linarith
        rw [div_le_iff₀ hζ3] at this
        linarith)

end ElboimSly.Paper
