/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.GeomCurve
public import Mathlib

/-!
# Geometry of the curve: (c) away from `w = z`

Geometry of the curve (c).  The hypothesis `2^20 ≤ β < 4^j` stands for "`4^j > β` and `β`
large" (`β ≥ β_56`); it gives `a = 2^j > √β ≥ 1024`.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.Brownian

variable {k : ℕ}

lemma EscGeom.norm_vz_ge {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) :
    (2 : ℝ) ^ j / 4 - 1 ≤ ‖escCast v - escCast z‖ := by
  have ha := h.a_ge
  rcases h.boundary_cases with h0 | ⟨c, hc, hcc⟩
  · refine le_trans ?_ (norm_le_pi_norm (escCast v - escCast z) 0)
    simp only [Pi.sub_apply, escCast, h.z0, Real.norm_eq_abs]
    have : (v 0 : ℝ) = u 0 := by exact_mod_cast h0
    rw [this, abs_of_nonpos (by linarith)]; linarith
  · refine le_trans ?_ (norm_le_pi_norm (escCast v - escCast z) c)
    simp only [Pi.sub_apply, escCast, Real.norm_eq_abs]
    have hz := h.zc hc
    rcases hcc with e | e
    · rw [e]; rw [abs_of_nonpos (by linarith [hz.1])]; linarith [hz.1]
    · rw [e]; push_cast; rw [abs_of_nonneg (by linarith [hz.2])]; linarith [hz.2]

/-- Geometry of the curve (c): away from `w`. -/
theorem curve_away_from_z {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) {β t : ℝ}
    (hβ : (2 : ℝ) ^ 20 ≤ β) (hβj : β < 4 ^ j) (ht2 : t ≤ 4 ^ j) (ht : 0 < t) {m i : ℕ}
    (hi1 : 1 ≤ i) (him : i ≤ 2 * m) {s : ℝ} (hs1 : escPhaseA t m (i - 1) ≤ s)
    (hs2 : s ≤ es56B t m i) (hst : s ≤ t - β) :
    Real.sqrt β / 20 ≤ ‖escCurve j u v z t s - escCast z‖ - escR t m i := by
  have ha := h.a_ge
  have hT := esc_sqrt_le_two_pow ht2
  have hβ0 : 0 < β := by have : (0 : ℝ) < 2 ^ 20 := by positivity
                         linarith
  -- a > √β ≥ 1024
  have hsb : Real.sqrt β < 2 ^ j := by
    refine (Real.sqrt_lt' (by positivity)).2 ?_
    calc β < 4 ^ j := hβj
      _ = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsb' : (1024 : ℝ) ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  rcases phase_cases ht hi1 him hs1 hs2 with ⟨n, hn1, -, hs, hl, -, hR⟩ | ⟨n, -, hs, hl, -, hR⟩
  · have hc : escCurve j u v z t s - escCast z =
        -((1 : ℝ) • (escCast z - escCentre j u) -
          (1 - Real.sqrt (2 * s / t)) • (escCast v - escCentre j u)) := by
      unfold escCurve; rw [es56F_of_le hs]
      simp only [smul_sub, sub_smul, one_smul]; abel
    have hlam : Real.sqrt (2 * s / t) ≤ 1 := by
      rw [Real.sqrt_le_one]; rw [div_le_one ht]; linarith
    have htr := EscGeom.transversality h (x := 1) (y := 1 - Real.sqrt (2 * s / t))
      (by norm_num) (by norm_num) (by linarith) (by linarith [Real.sqrt_nonneg (2 * s / t)])
    have hmax : max (1 : ℝ) (1 - Real.sqrt (2 * s / t)) = 1 := by
      apply max_eq_left; linarith [Real.sqrt_nonneg (2 * s / t)]
    rw [hmax, one_mul] at htr
    rw [hc, norm_neg]
    have hn : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn1
    have h3 : escR t m i ≤ 2 ^ j / (16 * 2 ^ n) :=
      hR.trans (div_le_div_of_nonneg_right hT (by positivity))
    have h4 : (2 : ℝ) ^ j / (16 * 2 ^ n) ≤ 2 ^ j / 32 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num); nlinarith
    simp only [one_smul] at htr ⊢
    linarith
  · have hc : escCurve j u v z t s - escCast z =
        Real.sqrt (2 * (t - s) / t) • (escCentre j u - escCast z) := by
      unfold escCurve; rw [es56F_of_ge ht hs]; abel
    set μ := Real.sqrt (2 * (t - s) / t) with hμ
    have hμ0 : 0 ≤ μ := Real.sqrt_nonneg _
    have hqz := h.norm_qz_ge
    have hP : (0 : ℝ) < 2 ^ n := by positivity
    have hnorm : μ * (2 ^ j / 4 - 1) ≤ ‖escCurve j u v z t s - escCast z‖ := by
      rw [hc, norm_smul, Real.norm_of_nonneg hμ0]
      exact mul_le_mul_of_nonneg_left hqz hμ0
    have hRle : escR t m i ≤ μ / 12 * (2 ^ j / 4 - 1) := by
      refine margin_arith (c0 := 77 / 1200) (c := 64) (P := 2 ^ n) hP (by norm_num) hR hT
        ?_ ?_ (by linarith)
      · have : (77 / 1200 : ℝ) / 2 ^ n = (77 / 100 / 2 ^ n) / 12 := by ring
        rw [this]; linarith
      · linarith
    have hμβ : Real.sqrt β / 2 ^ j ≤ μ := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, Real.sq_sqrt hβ0.le, div_le_div_iff₀ (by positivity) ht]
      have h4 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h4]
      have hts : 0 ≤ t - s := by linarith
      have hbs : β ≤ t - s := by linarith
      nlinarith [mul_le_mul hbs ht2 ht.le hts]
    have h5 : Real.sqrt β / 2 ^ j * (2 ^ j / 4 - 1) ≤ μ * (2 ^ j / 4 - 1) :=
      mul_le_mul_of_nonneg_right hμβ (by linarith)
    have h6 : Real.sqrt β / 2 ^ j * (2 ^ j / 4 - 1) = Real.sqrt β / 4 - Real.sqrt β / 2 ^ j := by
      field_simp
    have h7 : Real.sqrt β / 2 ^ j ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hsb.le
    nlinarith [hnorm, hRle]

end ElboimSly.Paper
