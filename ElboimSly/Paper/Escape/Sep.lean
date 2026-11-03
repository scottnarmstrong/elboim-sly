/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.GeomPair
public import ElboimSly.Paper.Escape.SepArith
public import ElboimSly.Paper.Escape.SepAux
public import Mathlib

/-!
# Old history is far (old history is far, geometric core)

Old history is far.  `sep_core` is the pathwise statement: a lattice point `y` within `R_i` of
`f(s)` (phase `i ≥ 2`) is at distance `≥ 2` from every point `w'` that is either within `β^0.3` of
`v` (the phase-`0` history) or within `R_{i'}` of `f(s')` with `s'` in phase `i' ≤ i - 2`, whenever
`s - s' ≥ β`.  The hypotheses `2^40 ≤ β < 4^j` and `2^m · β^{1/4} ≤ √t` stand for `β ≥ β_56` and the
definition of `m = ⌊log₄(t/√β)⌋`.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.Brownian

variable {k : ℕ}

/-- The first case of `sep_core`: the history is the phase-`0` piece near `v`. -/
theorem sep_core_zero {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) {β t : ℝ}
    (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j) (ht2 : t ≤ 4 ^ j) (ht : 0 < t) {m i : ℕ}
    (hi1 : 1 ≤ i) (him : i ≤ 2 * m) {s : ℝ} (hs1 : escPhaseA t m (i - 1) ≤ s)
    (hs2 : s ≤ es56B t m i) (hsβ : β ≤ s) {y w' : Fin (k + 2) → ℤ}
    (hy : ‖escCast y - escCurve j u v z t s‖ ≤ escR t m i)
    (hw : ‖escCast w' - escCast v‖ ≤ β ^ (0.3 : ℝ)) : 2 ≤ ‖escCast y - escCast w'‖ := by
  have ha := h.a_ge
  have hT := esc_sqrt_le_two_pow ht2
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hsb : Real.sqrt β < 2 ^ j := by
    refine (Real.sqrt_lt' (by positivity)).2 ?_
    calc β < 4 ^ j := hβj
      _ = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsb' : (2 : ℝ) ^ 20 ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    calc ((2 : ℝ) ^ 20) ^ 2 = 2 ^ 40 := by rw [← pow_mul]
      _ ≤ β := hβ
  norm_num at hsb'
  have hbp := esc_beta_pow_le hβ
  have htri := tri_norm (escCurve j u v z t s) (escCast y) (escCast v) (escCast w')
  have hvw : ‖escCast w' - escCast v‖ = ‖escCast v - escCast w'‖ := norm_sub_rev _ _
  rcases phase_cases ht hi1 him hs1 hs2 with ⟨n, -, -, hs, hl, -, hR⟩ | ⟨n, -, hs, hl, -, hR⟩
  · have hc : escCurve j u v z t s - escCast v =
        Real.sqrt (2 * s / t) • (escCentre j u - escCast v) := by
      unfold escCurve; rw [es56F_of_le hs]; abel
    have h1 : Real.sqrt (2 * s / t) * (2 ^ j / 4) ≤ ‖escCurve j u v z t s - escCast v‖ := by
      rw [hc, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left h.norm_qv_ge (Real.sqrt_nonneg _)
    have hlam : Real.sqrt β / 2 ^ j ≤ Real.sqrt (2 * s / t) := by
      apply Real.le_sqrt_of_sq_le
      have h4 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [div_pow, Real.sq_sqrt hβ0.le, div_le_div_iff₀ (by positivity) ht, h4]
      nlinarith [mul_le_mul hsβ ht2 ht.le (by linarith : (0 : ℝ) ≤ s)]
    have hP : (0 : ℝ) < 2 ^ n := by positivity
    have hRl : escR t m i ≤ 2 ^ j / 16 * Real.sqrt (2 * s / t) := by
      have h2 : escR t m i ≤ 2 ^ j / (16 * 2 ^ n) :=
        hR.trans (div_le_div_of_nonneg_right hT (by positivity))
      refine h2.trans ?_
      have h3 : (2 : ℝ) ^ j / (16 * 2 ^ n) = 2 ^ j / 16 * (1 / 2 ^ n) := by field_simp
      rw [h3]
      exact mul_le_mul_of_nonneg_left hl (by positivity)
    have h5 := ar_far_first (T := Real.sqrt t) hT (Real.sqrt_nonneg _) hlam (by positivity) hRl
      (Real.sqrt_nonneg β)
    linarith
  · have hμ1 : Real.sqrt (2 * (t - s) / t) ≤ 1 := by
      rw [Real.sqrt_le_one]; rw [div_le_one ht]; linarith
    have hc : escCurve j u v z t s - escCast v =
        (1 - Real.sqrt (2 * (t - s) / t)) • (escCast z - escCentre j u) -
          (1 : ℝ) • (escCast v - escCentre j u) := by
      unfold escCurve; rw [es56F_of_ge ht hs]
      simp only [smul_sub, sub_smul, one_smul]; abel
    have htr := EscGeom.transversality h (x := 1 - Real.sqrt (2 * (t - s) / t)) (y := 1)
      (by linarith) (by linarith [Real.sqrt_nonneg (2 * (t - s) / t)]) (by norm_num)
      (by norm_num)
    have hmax : max (1 - Real.sqrt (2 * (t - s) / t)) 1 = 1 := by
      apply max_eq_right; linarith [Real.sqrt_nonneg (2 * (t - s) / t)]
    rw [hmax, one_mul, ← hc] at htr
    have hn : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h3 : escR t m i ≤ 2 ^ j / 64 := by
      refine hR.trans ?_
      calc Real.sqrt t / (64 * 2 ^ n) ≤ 2 ^ j / (64 * 2 ^ n) :=
            div_le_div_of_nonneg_right hT (by positivity)
        _ ≤ 2 ^ j / 64 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num); nlinarith
    linarith

end ElboimSly.Paper
