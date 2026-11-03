/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.GeomAway
public import Mathlib

/-!
# Geometry of the curve: distances between two points of the curve

Old history is far (preparation).  Three cases: both points in the first half
(`‖f(s) - f(s')‖ = |λ(s) - λ(s')| ‖q - v‖`), both in the second half
(`= |μ(s) - μ(s')| ‖q - z‖`), or one in each (transversality).
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.Brownian

variable {k : ℕ}

theorem pair_first {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) {t s s' : ℝ}
    (hs : s ≤ t / 2) (hs' : s' ≤ t / 2) :
    |Real.sqrt (2 * s / t) - Real.sqrt (2 * s' / t)| * ((2 : ℝ) ^ j / 4) ≤
      ‖escCurve j u v z t s - escCurve j u v z t s'‖ := by
  have hc : escCurve j u v z t s - escCurve j u v z t s' =
      (Real.sqrt (2 * s / t) - Real.sqrt (2 * s' / t)) • (escCentre j u - escCast v) := by
    unfold escCurve; rw [es56F_of_le hs, es56F_of_le hs']
    simp only [sub_smul]; abel
  rw [hc, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left h.norm_qv_ge (abs_nonneg _)

theorem pair_second {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) {t s s' : ℝ}
    (ht : 0 < t) (hs : t / 2 ≤ s) (hs' : t / 2 ≤ s') :
    |Real.sqrt (2 * (t - s) / t) - Real.sqrt (2 * (t - s') / t)| * ((2 : ℝ) ^ j / 4 - 1) ≤
      ‖escCurve j u v z t s - escCurve j u v z t s'‖ := by
  have hc : escCurve j u v z t s - escCurve j u v z t s' =
      (Real.sqrt (2 * (t - s) / t) - Real.sqrt (2 * (t - s') / t)) •
        (escCentre j u - escCast z) := by
    unfold escCurve; rw [es56F_of_ge ht hs, es56F_of_ge ht hs']
    simp only [sub_smul]; abel
  rw [hc, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left h.norm_qz_ge (abs_nonneg _)

theorem pair_mixed {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) {t s s' : ℝ}
    (ht : 0 < t) (hs : t / 2 ≤ s) (hs' : s' ≤ t / 2) :
    max (1 - Real.sqrt (2 * (t - s) / t)) (1 - Real.sqrt (2 * s' / t)) *
        ((2 : ℝ) ^ j / 12 - 1) ≤
      ‖escCurve j u v z t s - escCurve j u v z t s'‖ := by
  have h1 : Real.sqrt (2 * (t - s) / t) ≤ 1 := by
    rw [Real.sqrt_le_one]; rw [div_le_one ht]; linarith
  have h2 : Real.sqrt (2 * s' / t) ≤ 1 := by
    rw [Real.sqrt_le_one]; rw [div_le_one ht]; linarith
  have hc : escCurve j u v z t s - escCurve j u v z t s' =
      (1 - Real.sqrt (2 * (t - s) / t)) • (escCast z - escCentre j u) -
        (1 - Real.sqrt (2 * s' / t)) • (escCast v - escCentre j u) := by
    unfold escCurve; rw [es56F_of_ge ht hs, es56F_of_le hs']
    simp only [smul_sub, sub_smul, one_smul]; abel
  rw [hc]
  exact EscGeom.transversality h (by linarith) (by linarith [Real.sqrt_nonneg (2 * (t - s) / t)])
    (by linarith) (by linarith [Real.sqrt_nonneg (2 * s' / t)])

end ElboimSly.Paper
