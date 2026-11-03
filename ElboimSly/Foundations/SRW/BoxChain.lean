/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.BoxSmall
public import ElboimSly.Foundations.SRW.WindowMain
public import Mathlib

/-!
# The chain of windows in confined point-to-point lower bound
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

theorem kernel1_chain (J : Set ℤ) (ρ : ℝ≥0) (g : ℕ → ℤ) :
    ∀ n : ℕ, ∏ k ∈ Finset.range (n + 1), kernel1 J ρ (g k) (g (k + 1)) ≤
      kernel1 J ((n + 1 : ℕ) * ρ) (g 0) (g (n + 1))
  | 0 => by simp
  | n + 1 => by
    have ih := kernel1_chain J ρ g n
    rw [Finset.prod_range_succ]
    have h2 := kernel1_add_ge J ((n + 1 : ℕ) * ρ) ρ (g 0) (g (n + 1 + 1)) (g (n + 1))
    have e : ((n + 1 + 1 : ℕ) : ℝ≥0) * ρ = (n + 1 : ℕ) * ρ + ρ := by
      push_cast; ring
    rw [e]
    refine le_trans ?_ h2
    exact mul_le_mul_of_nonneg_right ih (kernel1_nonneg _ _ _ _)

theorem exp_neg_four_ge : (1 / 55 : ℝ) ≤ Real.exp (-4) := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos 4) exp_four_le

theorem boxK_real : ((boxK : ℕ) : ℝ) = 26214400 := by norm_num [boxK]

/-- The rounded linear interpolation. -/
noncomputable def gInterp (a b : ℤ) (k : ℕ) : ℤ :=
  a + ⌊(k : ℝ) * ((b : ℝ) - a) / (boxK : ℝ)⌋

theorem gInterp_zero (a b : ℤ) : gInterp a b 0 = a := by simp [gInterp]

theorem gInterp_K (a b : ℤ) : gInterp a b boxK = b := by
  unfold gInterp
  have hK : (boxK : ℝ) ≠ 0 := by rw [boxK_real]; norm_num
  have : (boxK : ℝ) * ((b : ℝ) - a) / (boxK : ℝ) = ((b - a : ℤ) : ℝ) := by
    push_cast; field_simp
  rw [this, Int.floor_intCast]; ring

theorem gInterp_between (a b : ℤ) {k : ℕ} (hk : k ≤ boxK) :
    min a b ≤ gInterp a b k ∧ gInterp a b k ≤ max a b := by
  unfold gInterp
  have hK : (0 : ℝ) < boxK := by rw [boxK_real]; norm_num
  have hkK : (k : ℝ) ≤ boxK := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases le_total a b with h | h
  · have hd : (0 : ℝ) ≤ (b : ℝ) - a := by
      have : (a : ℝ) ≤ b := by exact_mod_cast h
      linarith
    have h1 : 0 ≤ (k : ℝ) * ((b : ℝ) - a) / boxK := by positivity
    have h2 : (k : ℝ) * ((b : ℝ) - a) / boxK ≤ ((b - a : ℤ) : ℝ) := by
      rw [div_le_iff₀ hK]; push_cast; nlinarith
    have f1 : 0 ≤ ⌊(k : ℝ) * ((b : ℝ) - a) / boxK⌋ := Int.floor_nonneg.2 h1
    have f2 : ⌊(k : ℝ) * ((b : ℝ) - a) / boxK⌋ ≤ b - a := by
      have := Int.floor_mono h2
      rwa [Int.floor_intCast] at this
    rw [min_eq_left h, max_eq_right h]
    constructor <;> omega
  · have hd : (b : ℝ) - a ≤ 0 := by
      have : (b : ℝ) ≤ a := by exact_mod_cast h
      linarith
    have h1 : (k : ℝ) * ((b : ℝ) - a) / boxK ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hK.le
      exact mul_nonpos_of_nonneg_of_nonpos hk0 hd
    have h2 : ((b - a : ℤ) : ℝ) ≤ (k : ℝ) * ((b : ℝ) - a) / boxK := by
      rw [le_div_iff₀ hK]; push_cast; nlinarith
    have f1 : ⌊(k : ℝ) * ((b : ℝ) - a) / boxK⌋ ≤ 0 := Int.floor_nonpos h1
    have f2 : b - a ≤ ⌊(k : ℝ) * ((b : ℝ) - a) / boxK⌋ := by
      have := Int.floor_mono h2
      rwa [Int.floor_intCast] at this
    rw [min_eq_right h, max_eq_left h]
    constructor <;> omega

theorem gInterp_step (a b : ℤ) (k : ℕ) :
    |((gInterp a b (k + 1) - gInterp a b k : ℤ) : ℝ)| ≤ |((b : ℝ) - a)| / boxK + 1 := by
  unfold gInterp
  have hK : (0 : ℝ) < boxK := by rw [boxK_real]; norm_num
  set x := (k : ℝ) * ((b : ℝ) - a) / boxK with hx
  set x' := ((k + 1 : ℕ) : ℝ) * ((b : ℝ) - a) / boxK with hx'
  have hdiff : x' - x = ((b : ℝ) - a) / boxK := by
    rw [hx, hx']; push_cast; ring
  have f1 := Int.floor_le x
  have f2 := Int.lt_floor_add_one x
  have f3 := Int.floor_le x'
  have f4 := Int.lt_floor_add_one x'
  have habs : |x' - x| = |(b : ℝ) - a| / boxK := by
    rw [hdiff, abs_div, abs_of_pos hK]
  rw [abs_le]
  have := le_abs_self (x' - x)
  have := neg_abs_le (x' - x)
  constructor <;> push_cast <;> linarith

end SRW
end ElboimSly
