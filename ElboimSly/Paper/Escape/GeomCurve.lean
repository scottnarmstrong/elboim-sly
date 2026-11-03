/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.GeomBox
public import ElboimSly.Paper.Escape.GeomPhase
public import Mathlib

/-!
# Geometry of the curve: (b) inside `B^-` and `‖f(s) - v‖ ≥ 4R_i`

Geometry of the curve (b).
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.Brownian

variable {k : ℕ}

lemma margin_arith {R T a θ P c0 c : ℝ} (hP : 0 < P) (hc : 0 < c) (hR : R ≤ T / (c * P))
    (hT : T ≤ a) (hθ : c0 / P ≤ θ) (hcc : a ≤ c0 * c * (a / 4 - 1)) (ha : 4 ≤ a) :
    R ≤ θ * (a / 4 - 1) := by
  have h1 : T / (c * P) ≤ a / (c * P) := div_le_div_of_nonneg_right hT (by positivity)
  have h2 : a / (c * P) ≤ (c0 * c * (a / 4 - 1)) / (c * P) :=
    div_le_div_of_nonneg_right hcc (by positivity)
  have h3 : (c0 * c * (a / 4 - 1)) / (c * P) = c0 / P * (a / 4 - 1) := by
    field_simp
  have h4 : c0 / P * (a / 4 - 1) ≤ θ * (a / 4 - 1) :=
    mul_le_mul_of_nonneg_right hθ (by linarith)
  linarith

lemma esc_sqrt_le_two_pow {j : ℕ} {t : ℝ} (ht : t ≤ 4 ^ j) : Real.sqrt t ≤ 2 ^ j := by
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  calc t ≤ 4 ^ j := ht
    _ = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

lemma escRealBox_z {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) :
    EscRealBox j u (escCast z) := by
  have ha := h.a_ge
  refine ⟨⟨?_, ?_⟩, fun c hc => ⟨?_, ?_⟩⟩
  · simp only [escCast]; rw [h.z0]; linarith
  · simp only [escCast]; rw [h.z0]
  · simp only [escCast]; linarith [(h.zc hc).1]
  · simp only [escCast]; linarith [(h.zc hc).2]

/-- Geometry of the curve (b), first half: lattice points within `R_i` of `f(s)` lie in `B^-`. -/
theorem curve_inside {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) {t : ℝ}
    (ht2 : t ≤ 4 ^ j) (ht : 0 < t) {m i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ 2 * m) {s : ℝ}
    (hs1 : escPhaseA t m (i - 1) ≤ s) (hs2 : s ≤ es56B t m i) {y : Fin (k + 2) → ℤ}
    (hy : ‖escCast y - escCurve j u v z t s‖ ≤ escR t m i) : y ∈ escBlockMinus j u := by
  have ha := h.a_ge
  have hT := esc_sqrt_le_two_pow ht2
  rcases phase_cases ht hi1 him hs1 hs2 with ⟨n, -, -, hs, hl, -, hR⟩ | ⟨n, -, hs, hl, -, hR⟩
  · have hc : escCurve j u v z t s = escCast v +
        Real.sqrt (2 * s / t) • (escCentre j u - escCast v) := by
      unfold escCurve; rw [es56F_of_le hs]
    rw [hc] at hy
    refine mem_blockMinus_of_margin h.hj4 (escRealBox_cast h.hj4 h.hvm) (Real.sqrt_nonneg _) ?_
      ?_ hy
    · rw [Real.sqrt_le_one]; rw [div_le_one ht]; linarith
    · refine margin_arith (c0 := 1) (c := 16) (P := 2 ^ n) (by positivity) (by norm_num) hR hT hl
        ?_ (by linarith)
      linarith
  · have hc : escCurve j u v z t s = escCast z +
        Real.sqrt (2 * (t - s) / t) • (escCentre j u - escCast z) := by
      unfold escCurve; rw [es56F_of_ge ht hs]
    rw [hc] at hy
    refine mem_blockMinus_of_margin h.hj4 (escRealBox_z h) (Real.sqrt_nonneg _) ?_ ?_ hy
    · rw [Real.sqrt_le_one]; rw [div_le_one ht]; linarith
    · refine margin_arith (c0 := 77 / 100) (c := 64) (P := 2 ^ n) (by positivity) (by norm_num)
        hR hT hl ?_ (by linarith)
      linarith

/-- Geometry of the curve (b), second half: `‖f(s) - v‖ ≥ 4 R_i`. -/
theorem curve_far_from_v {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) {t : ℝ}
    (ht2 : t ≤ 4 ^ j) (ht : 0 < t) {m i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ 2 * m) {s : ℝ}
    (hs1 : escPhaseA t m (i - 1) ≤ s) (hs2 : s ≤ es56B t m i) :
    4 * escR t m i ≤ ‖escCurve j u v z t s - escCast v‖ := by
  have ha := h.a_ge
  have hT := esc_sqrt_le_two_pow ht2
  rcases phase_cases ht hi1 him hs1 hs2 with ⟨n, -, -, hs, hl, -, hR⟩ | ⟨n, -, hs, hl, -, hR⟩
  · have hc : escCurve j u v z t s - escCast v =
        Real.sqrt (2 * s / t) • (escCentre j u - escCast v) := by
      unfold escCurve; rw [es56F_of_le hs]; abel
    rw [hc, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := h.norm_qv_ge
    have hP : (0 : ℝ) < 2 ^ n := by positivity
    have h2 : 4 * escR t m i ≤ 2 ^ j / 4 / 2 ^ n := by
      have : escR t m i ≤ 2 ^ j / (16 * 2 ^ n) :=
        hR.trans (div_le_div_of_nonneg_right hT (by positivity))
      calc 4 * escR t m i ≤ 4 * (2 ^ j / (16 * 2 ^ n)) := by linarith
        _ = 2 ^ j / 4 / 2 ^ n := by field_simp; ring
    calc 4 * escR t m i ≤ 2 ^ j / 4 / 2 ^ n := h2
      _ = 1 / 2 ^ n * (2 ^ j / 4) := by ring
      _ ≤ Real.sqrt (2 * s / t) * (2 ^ j / 4) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
  · have hc : escCurve j u v z t s - escCast v =
        (1 - Real.sqrt (2 * (t - s) / t)) • (escCast z - escCentre j u) -
          (1 : ℝ) • (escCast v - escCentre j u) := by
      unfold escCurve; rw [es56F_of_ge ht hs]
      simp only [smul_sub, sub_smul, one_smul]; abel
    have hμ1 : Real.sqrt (2 * (t - s) / t) ≤ 1 := by
      rw [Real.sqrt_le_one]; rw [div_le_one ht]; linarith
    have := EscGeom.transversality h (x := 1 - Real.sqrt (2 * (t - s) / t)) (y := 1)
      (by linarith) (by linarith [Real.sqrt_nonneg (2 * (t - s) / t)]) (by norm_num)
      (by norm_num)
    have hmax : max (1 - Real.sqrt (2 * (t - s) / t)) 1 = 1 := by
      apply max_eq_right; linarith [Real.sqrt_nonneg (2 * (t - s) / t)]
    rw [hmax, one_mul] at this
    rw [hc]
    simp only [one_smul] at this ⊢
    refine le_trans ?_ this
    have h3 : escR t m i ≤ 2 ^ j / (64 * 2 ^ n) :=
      hR.trans (div_le_div_of_nonneg_right hT (by positivity))
    have hn : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h4 : (2 : ℝ) ^ j / (64 * 2 ^ n) ≤ 2 ^ j / 64 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num); nlinarith
    linarith

end ElboimSly.Paper
