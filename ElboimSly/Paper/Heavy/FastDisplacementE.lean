/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.FastDisplacement
public import ElboimSly.Paper.Heavy.Thresholds

/-!
# The `5^n` bound before `τ_fast`

Pathwise consequences of tfast and heavyJ (e).  Before `τ_fast(w; n³)` and up to the scale
`t_n = 4^n t₀ ≤ 4^{n+1}`, the path stays in the ball of radius `5^n`.  Only the single threshold
(T3) is used, and it is passed as a hypothesis `hT3` (it is the field `HeavyT.t3`).
-/

@[expose] public section

namespace ElboimSly.Paper

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

/-- Pathwise consequences of tfast and heavyJ (e), with (T3) as the explicit hypothesis. -/
theorem norm_lt_five_pow_of_lt_pathTfast (hw : IsCyclicPath w) {n : ℕ} {t : ℝ}
    (hT3 : (n : ℝ) ^ 3 * (4 ^ (n + 1) + 1) ≤ 5 ^ n) (hn : 0 < n) (ht0 : 0 ≤ t)
    (ht : t ≤ 4 ^ (n + 1))
    (h : ENNReal.ofReal t < pathTfast w ((n : ℝ) ^ 3)) : ‖w t‖ < 5 ^ n := by
  have hw0 : w 0 = 0 := hw.zero
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  rcases ht0.eq_or_lt with h0 | h0
  · subst h0; rw [hw0]; simp
  have := norm_sub_lt_of_lt_pathTfast hw hn3 le_rfl h0 h
  rw [hw0, sub_zero] at this
  refine this.trans_le ((mul_le_mul_of_nonneg_left (?_ : (⌈t - 0⌉₊ : ℝ) ≤ 4 ^ (n + 1) + 1)
    hn3.le).trans hT3)
  rw [sub_zero]
  have := (Nat.ceil_lt_add_one ht0).le
  linarith

/-- (e) for `τ_fast(w) = pathTfastCube`. -/
theorem norm_lt_five_pow_of_lt_pathTfastCube (hw : IsCyclicPath w) {n : ℕ} {t : ℝ}
    (hT3 : (n : ℝ) ^ 3 * (4 ^ (n + 1) + 1) ≤ 5 ^ n) (hn : 0 < n) (ht0 : 0 ≤ t)
    (ht : t ≤ 4 ^ (n + 1)) (h : ENNReal.ofReal t < pathTfastCube w n) : ‖w t‖ < 5 ^ n :=
  norm_lt_five_pow_of_lt_pathTfast hw hT3 hn ht0 ht h

end ElboimSly.Paper
