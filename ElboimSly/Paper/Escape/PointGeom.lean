/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Stopping
public import ElboimSly.Paper.Escape.GeomBase
public import ElboimSly.Paper.Escape.Density
public import Mathlib

/-!
# Conditions (1), (4), (6) fail at the starting points `p_i`

The walks W_i and the stopping times tau_i; The points p_i.  Used to exclude the stopping conditions on the
interval `(0, ς_1)` before the first jump of the walk `W_i`, which the plan does not test.

* `escPoint_zero_coord`, `escPoint_one_coord`, `escPoint_other_coord`: real coordinates of `p_i`;
* `escPoint_ne_zero`: `p_i ≠ 0` for an admissible block;
* `escPoint_far_blockMinus`: every `y ∈ B^-` is at distance `> 2^j/8` from `p_i`;
* `escPoint_far_point`: `‖p_i - p_ℓ‖ > n^17/6` for `ℓ ≠ i`.
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

variable {k : ℕ} {n j : ℕ} {u : Fin (k + 2) → ℤ}

theorem escPoint_zero_coord (hj : 2 ≤ j) (i : ℕ) :
    ((escPoint n j u i 0 : ℤ) : ℝ) = u 0 + 3 * ((2 : ℝ) ^ j / 4) := by
  have h := cast_two_pow_div_four hj
  simp only [escPoint, ite_true, ite_eq_right (show (0 : Fin (k + 2)) ≠ 1 from by simp)]
  push_cast
  rw [h]; ring

theorem escPoint_one_coord (hj : 2 ≤ j) (i : ℕ) :
    ((escPoint n j u i 1 : ℤ) : ℝ) = u 1 + 2 * ((2 : ℝ) ^ j / 4) + i * escLambda n := by
  have h := cast_two_pow_div_four hj
  simp only [escPoint, ite_true, ite_eq_right (show (1 : Fin (k + 2)) ≠ 0 from by simp)]
  push_cast
  rw [h]; ring

theorem escPoint_other_coord (hj : 2 ≤ j) (i : ℕ) {c : Fin (k + 2)} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ((escPoint n j u i c : ℤ) : ℝ) = u c + 2 * ((2 : ℝ) ^ j / 4) := by
  have h := cast_two_pow_div_four hj
  simp only [escPoint, ite_eq_right hc0, ite_eq_right hc1]
  push_cast
  rw [h]; ring

/-- The point `p_i` lies in the block, if `i λ_n < 2^{j-1}`. -/
theorem escPoint_mem_block (hj : 2 ≤ j) (i : ℕ) (hi : (i : ℝ) * escLambda n < (2 : ℝ) ^ j / 2) :
    escPoint n j u i ∈ escBlock j u := by
  intro c
  have ha : (0 : ℝ) < (2 : ℝ) ^ j / 4 := by positivity
  have hl : (0 : ℝ) ≤ (i : ℝ) * escLambda n := by positivity
  by_cases hc0 : c = 0
  · subst hc0
    have := escPoint_zero_coord (n := n) (u := u) hj i
    constructor
    · have : (u 0 : ℝ) ≤ escPoint n j u i 0 := by rw [this]; linarith
      exact_mod_cast this
    · have : (escPoint n j u i 0 : ℝ) < u 0 + (2 : ℝ) ^ j := by rw [this]; linarith
      exact_mod_cast this
  · by_cases hc1 : c = 1
    · subst hc1
      have := escPoint_one_coord (n := n) (u := u) hj i
      constructor
      · have : (u 1 : ℝ) ≤ escPoint n j u i 1 := by rw [this]; linarith
        exact_mod_cast this
      · have : (escPoint n j u i 1 : ℝ) < u 1 + (2 : ℝ) ^ j := by rw [this]; linarith
        exact_mod_cast this
    · have := escPoint_other_coord (n := n) (u := u) hj i hc0 hc1
      constructor
      · have : (u c : ℝ) ≤ escPoint n j u i c := by rw [this]; linarith
        exact_mod_cast this
      · have : (escPoint n j u i c : ℝ) < u c + (2 : ℝ) ^ j := by rw [this]; linarith
        exact_mod_cast this

/-- `p_i ≠ 0` for an admissible block with `i λ_n < 2^{j-1}`. -/
theorem escPoint_ne_zero (hj : 2 ≤ j) (hadm : EscAdmissible j u) (i : ℕ)
    (hi : (i : ℝ) * escLambda n < (2 : ℝ) ^ j / 2) : escPoint n j u i ≠ 0 := by
  intro h0
  rcases hadm with hnot | hu
  · exact hnot (h0 ▸ escPoint_mem_block hj i hi)
  · have := escPoint_zero_coord (n := n) (u := u) hj i
    rw [h0] at this
    subst hu
    simp at this

/-- Every vertex of `B^-` is at distance `≥ 2^j/4 + 1` from `p_i`. -/
theorem escPoint_far_blockMinus (hj : 2 ≤ j) (i : ℕ) {y : Fin (k + 2) → ℤ}
    (hy : y ∈ escBlockMinus j u) :
    (2 : ℝ) ^ j / 4 + 1 ≤ ‖escCast (escPoint n j u i) - escCast y‖ := by
  have hp0 := escPoint_zero_coord (n := n) (u := u) hj i
  have hh := cast_two_pow_pred (by omega : 1 ≤ j)
  have h2 : y 0 + 1 ≤ u 0 + 2 ^ (j - 1) := hy.1.2
  have h2' : (y 0 : ℝ) + 1 ≤ u 0 + (2 : ℝ) ^ j / 2 := by rw [← hh]; exact_mod_cast h2
  have : (2 : ℝ) ^ j / 4 + 1 ≤ ((escPoint n j u i 0 : ℤ) : ℝ) - y 0 := by rw [hp0]; linarith
  have h3 := norm_le_pi_norm (escCast (escPoint n j u i) - escCast y) 0
  simp only [escCast, Pi.sub_apply, Real.norm_eq_abs] at h3
  have h4 : ((escPoint n j u i 0 : ℤ) : ℝ) - y 0 ≤ |((escPoint n j u i 0 : ℤ) : ℝ) - y 0| :=
    le_abs_self _
  exact le_trans (by linarith) h3

theorem escBlockMinus_nonempty (_hj : 1 ≤ j) : (escBlockMinus j u).Nonempty := by
  refine ⟨u, ⟨le_rfl, ?_⟩, fun c _ => ⟨le_rfl, ?_⟩⟩
  · have : (0 : ℤ) < 2 ^ (j - 1) := by positivity
    omega
  · have : (0 : ℤ) < 2 ^ j := by positivity
    omega

end ElboimSly.Paper.Escape
