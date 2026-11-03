/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.PointGeom
public import Mathlib

/-!
# Geometry of the starting point `p_i` relative to `B^-` and to the other points

ES22 Lemma 5.3 ("every point of `N(B^-, 2^{j-3}) ∪ ⋃_{ℓ≠i} B(p_ℓ, n^{17}/6)` is within
`ℓ∞`-distance `< 2^j` of `p_i`").
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

variable {k : ℕ} {n j : ℕ} {u : Fin (k + 2) → ℤ}

theorem escPoint_dist_blockMinus_le (hj : 2 ≤ j) (i : ℕ)
    (hi : (i : ℝ) * escLambda n ≤ 3 * ((2 : ℝ) ^ j / 16)) {y : Fin (k + 2) → ℤ}
    (hy : y ∈ escBlockMinus j u) :
    ‖escCast (escPoint n j u i) - escCast y‖ ≤ 3 * (2 : ℝ) ^ j / 4 := by
  have ha : (0 : ℝ) < (2 : ℝ) ^ j / 4 := by positivity
  have hh := cast_two_pow_pred (by omega : 1 ≤ j)
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro c
  simp only [Pi.sub_apply, escCast, Real.norm_eq_abs]
  rw [← Int.cast_sub]
  by_cases hc0 : c = 0
  · subst hc0
    have hp := escPoint_zero_coord (n := n) (u := u) hj i
    have h1 : (u 0 : ℝ) ≤ y 0 := by exact_mod_cast hy.1.1
    have h2 : (y 0 : ℝ) + 1 ≤ u 0 + (2 : ℝ) ^ j / 2 := by
      have : y 0 + 1 ≤ u 0 + 2 ^ (j - 1) := hy.1.2
      rw [← hh]; exact_mod_cast this
    rw [Int.cast_sub, hp, abs_le]
    constructor <;> linarith
  · have hyc := hy.2 c hc0
    have h1 : (u c : ℝ) ≤ y c := by exact_mod_cast hyc.1
    have h2 : (y c : ℝ) + 1 ≤ u c + (2 : ℝ) ^ j := by
      have : y c + 1 ≤ u c + 2 ^ j := hyc.2
      exact_mod_cast this
    by_cases hc1 : c = 1
    · subst hc1
      have hp := escPoint_one_coord (n := n) (u := u) hj i
      have hl : (0 : ℝ) ≤ (i : ℝ) * escLambda n := by positivity
      rw [Int.cast_sub, hp, abs_le]
      constructor <;> nlinarith
    · have hp := escPoint_other_coord (n := n) (u := u) hj i hc0 hc1
      rw [Int.cast_sub, hp, abs_le]
      constructor <;> nlinarith

/-- Points within `2^j/8` of `B^-` are within `< 2^j` of `p_i`. -/
theorem escPoint_norm_lt_of_infDist (hj : 2 ≤ j) (i : ℕ)
    (hi : (i : ℝ) * escLambda n ≤ 3 * ((2 : ℝ) ^ j / 16)) (z : Fin (k + 2) → ℤ)
    (h : Metric.infDist (fun c => ((z c : ℤ) : ℝ))
        ((fun x c => ((x c : ℤ) : ℝ)) '' escBlockMinus j u) ≤ (2 : ℝ) ^ j / 8) :
    ‖escCast z - escCast (escPoint n j u i)‖ < (2 : ℝ) ^ j := by
  have hne : ((fun x c => ((x c : ℤ) : ℝ)) '' escBlockMinus j u).Nonempty :=
    (escBlockMinus_nonempty (u := u) (by omega)).image _
  have key : ‖escCast z - escCast (escPoint n j u i)‖ - 3 * (2 : ℝ) ^ j / 4 ≤
      Metric.infDist (fun c => ((z c : ℤ) : ℝ))
        ((fun x c => ((x c : ℤ) : ℝ)) '' escBlockMinus j u) := by
    refine (Metric.le_infDist hne).2 ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [dist_eq_norm]
    have h1 := escPoint_dist_blockMinus_le (n := n) hj i hi hy
    have h2 : ‖escCast z - escCast (escPoint n j u i)‖ ≤
        ‖escCast z - escCast y‖ + ‖escCast (escPoint n j u i) - escCast y‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (escCast z) (escCast y) (escCast (escPoint n j u i))
      rw [norm_sub_rev (escCast y) (escCast (escPoint n j u i))] at this
      exact this
    show _ ≤ ‖(fun c => ((z c : ℤ) : ℝ)) - fun c => ((y c : ℤ) : ℝ)‖
    have e : ((fun c => ((z c : ℤ) : ℝ)) - fun c => ((y c : ℤ) : ℝ)) = escCast z - escCast y := rfl
    rw [e]
    linarith
  have ha : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  linarith

end ElboimSly.Paper.Escape
