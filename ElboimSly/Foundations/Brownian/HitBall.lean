/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.FarHit
import Mathlib

/-!
# Ever hitting a cube or a ball

ES22 Lemma 9.1, as an upper bound: ever hitting a cube or a ball (ES22 Lemma 9.1 as an upper bound, deviation F20).

This file contains the single-time estimate of the middle range of the proof
(`hit_term_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- For `R ≥ 4 r`: `g_{r,r²}(ρ) ≤ 4 d exp(-(R/r)²/32)` whenever `ρ ≥ R/2`. -/
lemma winG_le_of_ge_half {r R ρ : ℝ} (hr : 0 < r) (hR : 4 * r ≤ R) (hρ : R / 2 ≤ ρ) :
    winG d r (r ^ 2) ρ ≤ ENNReal.ofReal (4 * d * Real.exp (-(R / r) ^ 2 / 32)) := by
  have hlt : r < ρ := by linarith
  rw [winG_of_lt hlt]
  refine (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : (0 : ℝ) ≤ 4 * d := by positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0
  have h1 : R / 4 ≤ ρ - r := by linarith
  have h2 : (R / 4) ^ 2 ≤ (ρ - r) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have hr2 : 0 < r ^ 2 := by positivity
  rw [div_pow, neg_div, neg_div, neg_le_neg_iff, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith only [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ r ^ 2 * 32)]

/-- The density of `B(t)` at a point `z` with `‖z‖ ≥ ‖w‖/2` is at most
`(2π)^{-d/2} (d/(2 e b))^{d/2}` with `b = ‖w‖²/8`. -/
lemma bmDensity_le_far (hd : 0 < d) (t : ℝ≥0) (ht : t ≠ 0) {w z : Fin d → ℝ} (hw : 0 < ‖w‖)
    (hz : ‖w‖ / 2 ≤ ‖z‖) :
    bmDensity d t z ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) *
      ((d : ℝ) / (2 * Real.exp 1 * (‖w‖ ^ 2 / 8))) ^ ((d : ℝ) / 2) := by
  have ht0 : (0 : ℝ) < t := by positivity
  refine (bmDensity_le t z).trans ?_
  have h1 : Real.exp (-‖z‖ ^ 2 / (2 * t)) ≤ Real.exp (-(‖w‖ ^ 2 / 8) / t) := by
    refine Real.exp_le_exp.2 ?_
    have h2 : (‖w‖ / 2) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hz 2
    rw [div_le_div_iff₀ (by positivity) ht0]
    linarith only [mul_le_mul_of_nonneg_right h2 ht0.le]
  have h3 := rpow_mul_exp_neg_div_le hd (b := ‖w‖ ^ 2 / 8) (u := t) (by positivity) ht0
  rw [Real.mul_rpow (by positivity) ht0.le, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc (t : ℝ) ^ (-(d : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (2 * t))
      ≤ (t : ℝ) ^ (-(d : ℝ) / 2) * Real.exp (-(‖w‖ ^ 2 / 8) / t) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ _ := h3

/-- The single-time estimate of the middle range in the proof of ES22 Lemma 9.1, as an upper bound: ever hitting a cube or a ball. -/
theorem hit_term_le [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (hd : 0 < d) {t : ℝ≥0} (ht : t ≠ 0) (w : Fin d → ℝ)
    {r : ℝ} (hr : 0 < r) (hR : 4 * r ≤ ‖w‖) :
    ∫⁻ ω, winG d r (r ^ 2) ‖w + B t ω‖ ∂P ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) *
        ((d : ℝ) / (2 * Real.exp 1 * (‖w‖ ^ 2 / 8))) ^ ((d : ℝ) / 2) * (Cwin d * r ^ d)) +
      ENNReal.ofReal (4 * d * Real.exp (-(‖w‖ / r) ^ 2 / 32)) := by
  have hw : 0 < ‖w‖ := by linarith
  set M1 : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) *
        ((d : ℝ) / (2 * Real.exp 1 * (‖w‖ ^ 2 / 8))) ^ ((d : ℝ) / 2)) with hM1
  set M2 : ℝ≥0∞ := ENNReal.ofReal (4 * d * Real.exp (-(‖w‖ / r) ^ 2 / 32)) with hM2
  have hG : Measurable fun z : Fin d → ℝ => winG d r (r ^ 2) ‖w + z‖ :=
    (measurable_winG d r _).comp (measurable_const.add measurable_id).norm
  have hρm : Measurable fun z => ENNReal.ofReal (bmDensity d t z) :=
    ENNReal.measurable_ofReal.comp (measurable_bmDensity d t)
  have hlaw := (hB.hasLaw_eval_density ht).map_eq
  have hpt : ∀ z : Fin d → ℝ, ENNReal.ofReal (bmDensity d t z) * winG d r (r ^ 2) ‖w + z‖ ≤
      M1 * winG d r (r ^ 2) ‖w + z‖ + M2 * ENNReal.ofReal (bmDensity d t z) := by
    intro z
    by_cases hz : ‖w + z‖ < ‖w‖ / 2
    · have hzw : ‖w‖ / 2 ≤ ‖z‖ := by
        have := norm_sub_norm_le w (-z)
        rw [norm_neg, sub_neg_eq_add] at this
        linarith
      have := ENNReal.ofReal_le_ofReal (bmDensity_le_far hd t ht hw hzw)
      exact (mul_le_mul_left this _).trans le_self_add
    · have hz' : ‖w‖ / 2 ≤ ‖w + z‖ := not_lt.1 hz
      have := winG_le_of_ge_half (d := d) hr hR hz'
      calc _ ≤ ENNReal.ofReal (bmDensity d t z) * M2 := mul_le_mul_right this _
        _ = M2 * ENNReal.ofReal (bmDensity d t z) := mul_comm _ _
        _ ≤ _ := le_add_self
  have hint : ∫⁻ z, ENNReal.ofReal (bmDensity d t z) = 1 := by
    have h1 : (P.map (B t)) Set.univ = 1 := by
      rw [Measure.map_apply (hB.measurable t) MeasurableSet.univ]; simp
    rw [hlaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    exact h1
  calc ∫⁻ ω, winG d r (r ^ 2) ‖w + B t ω‖ ∂P
      = ∫⁻ z, ENNReal.ofReal (bmDensity d t z) * winG d r (r ^ 2) ‖w + z‖ := by
        rw [← lintegral_map hG (hB.measurable t), hlaw]
        exact lintegral_withDensity_eq_lintegral_mul (μ := volume)
          (f := fun z => ENNReal.ofReal (bmDensity d t z)) hρm hG
    _ ≤ ∫⁻ z, (M1 * winG d r (r ^ 2) ‖w + z‖ + M2 * ENNReal.ofReal (bmDensity d t z)) :=
        lintegral_mono hpt
    _ = M1 * (∫⁻ z : Fin d → ℝ, winG d r (r ^ 2) ‖z‖) + M2 * 1 := by
        rw [lintegral_add_left (hG.const_mul M1), lintegral_const_mul _ hG,
          lintegral_const_mul _ hρm, hint]
        rw [lintegral_add_left_eq_self (μ := (volume : Measure (Fin d → ℝ)))
          (fun z => winG d r (r ^ 2) ‖z‖) w]
    _ ≤ M1 * ENNReal.ofReal (Cwin d * r ^ d) + M2 * 1 := by
        exact add_le_add (mul_le_mul_right (lintegral_winG_le d hr) _) le_rfl
    _ = _ := by
        rw [mul_one, hM1, ← ENNReal.ofReal_mul (by positivity)]

/-- ES22 Lemma 9.1, as an upper bound: ever hitting a cube or a ball. The constant `C_a = (2π)^{-d/2} (4d/e)^{d/2} C_win`. -/
noncomputable def Ca (d : ℕ) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2) * (4 * d / Real.exp 1) ^ ((d : ℝ) / 2) * Cwin d

/-- ES22 Lemma 9.1, as an upper bound: ever hitting a cube or a ball. The constant `C_b = (16 d / e)^{d/2}`. -/
noncomputable def Cb (d : ℕ) : ℝ := (16 * d / Real.exp 1) ^ ((d : ℝ) / 2)

/-- ES22 Lemma 9.1, as an upper bound: ever hitting a cube or a ball. The constant
`C_hit = max {4^{d-2}, 2 C_a + 12 d C_b + 2 (2π)^{-d/2} C_win/(d-2)}`. -/
noncomputable def Chit (d : ℕ) : ℝ :=
  max (4 ^ (d - 2)) (2 * Ca d + 12 * d * Cb d +
    2 * ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d) / ((d : ℝ) - 2))

lemma rpow_sq_half {R : ℝ} (hR : 0 < R) (d : ℕ) : (R ^ 2) ^ ((d : ℝ) / 2) = R ^ d := by
  rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le, ← Real.rpow_natCast R d]
  congr 1; push_cast; ring

lemma Ca_nonneg (d : ℕ) : 0 ≤ Ca d := by
  have := Cwin_nonneg d; unfold Ca; positivity

lemma Cb_nonneg (d : ℕ) : 0 ≤ Cb d := by unfold Cb; positivity

/-- The arithmetic at the end of the proof of ES22 Lemma 9.1, as an upper bound: ever hitting a cube or a ball. -/
lemma hit_arith {d : ℕ} (hd : 3 ≤ d) {r R : ℝ} (hr : 0 < r) (hR : 4 * r < R) {K : ℕ}
    (hK1 : (R / r) ^ 2 ≤ K) (hK2 : (K : ℝ) ≤ 2 * (R / r) ^ 2) :
    4 * d * Real.exp (-(R / r) ^ 2 / 32) +
      K * ((2 * Real.pi) ^ (-(d : ℝ) / 2) *
          ((d : ℝ) / (2 * Real.exp 1 * (R ^ 2 / 8))) ^ ((d : ℝ) / 2) * (Cwin d * r ^ d) +
        4 * d * Real.exp (-(R / r) ^ 2 / 32)) +
      (2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d * r ^ d *
        (2 / ((d : ℝ) - 2) * (r ^ 2) ^ (-(d : ℝ) / 2) * (K : ℝ) ^ (1 - (d : ℝ) / 2)) ≤
    (2 * Ca d + 12 * d * Cb d + 2 * ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d) / ((d : ℝ) - 2)) *
      (r / R) ^ (d - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hR0 : 0 < R := by linarith
  have hx : 0 < R / r := by positivity
  have hx4 : 4 < R / r := by rw [lt_div_iff₀ hr]; linarith
  set x := R / r with hxdef
  set v := r / R with hvdef
  have hv0 : 0 < v := by positivity
  have hvx : v * x = 1 := by rw [hvdef, hxdef]; field_simp
  have hv1 : v ≤ 1 := by
    have : v * 4 ≤ v * x := mul_le_mul_of_nonneg_left hx4.le hv0.le
    linarith
  have hxv : x⁻¹ = v := by rw [hxdef, hvdef, inv_div]
  have hd2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  -- the exponential
  have hE : Real.exp (-x ^ 2 / 32) ≤ Cb (m + 2) * v ^ (m + 2) := by
    have h1 := pow_mul_exp_neg_sq_le (d := m + 2) (by omega) hx
    have h2 : x ^ (m + 2) * Real.exp (-x ^ 2 / 32) ≤ Cb (m + 2) := h1
    have h3 : v ^ (m + 2) = (x ^ (m + 2))⁻¹ := by rw [← hxv, inv_pow]
    rw [h3, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  -- the main term
  have hA : (2 * Real.pi) ^ (-((m + 2 : ℕ) : ℝ) / 2) *
        (((m + 2 : ℕ) : ℝ) / (2 * Real.exp 1 * (R ^ 2 / 8))) ^ (((m + 2 : ℕ) : ℝ) / 2) *
        (Cwin (m + 2) * r ^ (m + 2)) = Ca (m + 2) * v ^ (m + 2) := by
    have e1 : ((m + 2 : ℕ) : ℝ) / (2 * Real.exp 1 * (R ^ 2 / 8)) =
        (4 * ((m + 2 : ℕ) : ℝ) / Real.exp 1) * (R ^ 2)⁻¹ := by
      field_simp; ring
    rw [e1, Real.mul_rpow (x := 4 * ((m + 2 : ℕ) : ℝ) / Real.exp 1) (y := (R ^ 2)⁻¹)
      (by positivity) (by positivity), Real.inv_rpow (by positivity), rpow_sq_half hR0]
    unfold Ca
    rw [hvdef, div_pow]
    field_simp
  -- the tail
  have hKpos : 0 < (K : ℝ) := lt_of_lt_of_le (by positivity) hK1
  have hKr : (K : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) ≤ v ^ m := by
    have e : 1 - ((m + 2 : ℕ) : ℝ) / 2 = -(m : ℝ) / 2 := by push_cast; ring
    rw [e]
    calc (K : ℝ) ^ (-(m : ℝ) / 2) ≤ (x ^ 2) ^ (-(m : ℝ) / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hK1 (by linarith)
      _ = v ^ m := by rw [sq_rpow_neg_half hx, ← hxv, inv_pow]
  have hrd : (r ^ 2) ^ (-((m + 2 : ℕ) : ℝ) / 2) * r ^ (m + 2) = 1 := by
    rw [sq_rpow_neg_half hr]; field_simp
  have hVpos : 0 < v ^ m := by positivity
  have hv2 : v ^ (m + 2) = v ^ m * v ^ 2 := by ring
  have hxv2 : x ^ 2 * v ^ 2 = 1 := by rw [← mul_pow, mul_comm, hvx, one_pow]
  have hCb := Cb_nonneg (m + 2)
  have hCa := Ca_nonneg (m + 2)
  have hc1 : 0 ≤ (2 * Real.pi) ^ (-((m + 2 : ℕ) : ℝ) / 2) * Cwin (m + 2) := by
    have := Cwin_nonneg (m + 2); positivity
  have hmc : ((m + 2 : ℕ) : ℝ) - 2 = m := by push_cast; ring
  rw [Nat.add_sub_cancel, hA, hmc]
  have hT0 : 4 * ((m + 2 : ℕ) : ℝ) * Real.exp (-x ^ 2 / 32) ≤
      4 * ((m + 2 : ℕ) : ℝ) * Cb (m + 2) * (v ^ m * v ^ 2) := by
    rw [← hv2]
    calc _ ≤ 4 * ((m + 2 : ℕ) : ℝ) * (Cb (m + 2) * v ^ (m + 2)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by ring
  have hAT : Ca (m + 2) * v ^ (m + 2) + 4 * ((m + 2 : ℕ) : ℝ) * Real.exp (-x ^ 2 / 32) ≤
      (Ca (m + 2) + 4 * ((m + 2 : ℕ) : ℝ) * Cb (m + 2)) * (v ^ m * v ^ 2) := by
    rw [hv2]; linarith only [hT0]
  have hKA : (K : ℝ) * (Ca (m + 2) * v ^ (m + 2) + 4 * ((m + 2 : ℕ) : ℝ) *
      Real.exp (-x ^ 2 / 32)) ≤ 2 * (Ca (m + 2) + 4 * ((m + 2 : ℕ) : ℝ) * Cb (m + 2)) * v ^ m := by
    have hnn : 0 ≤ Ca (m + 2) * v ^ (m + 2) + 4 * ((m + 2 : ℕ) : ℝ) * Real.exp (-x ^ 2 / 32) := by
      have := Real.exp_pos (-x ^ 2 / 32); have := pow_pos hv0 (m + 2); positivity
    calc _ ≤ (2 * x ^ 2) * ((Ca (m + 2) + 4 * ((m + 2 : ℕ) : ℝ) * Cb (m + 2)) *
          (v ^ m * v ^ 2)) := mul_le_mul hK2 hAT hnn (by positivity)
      _ = 2 * (Ca (m + 2) + 4 * ((m + 2 : ℕ) : ℝ) * Cb (m + 2)) * v ^ m * (x ^ 2 * v ^ 2) := by ring
      _ = _ := by rw [hxv2, mul_one]
  have htail : (2 * Real.pi) ^ (-((m + 2 : ℕ) : ℝ) / 2) * Cwin (m + 2) * r ^ (m + 2) *
      (2 / (m : ℝ) * (r ^ 2) ^ (-((m + 2 : ℕ) : ℝ) / 2) * (K : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2)) ≤
      2 * ((2 * Real.pi) ^ (-((m + 2 : ℕ) : ℝ) / 2) * Cwin (m + 2)) / (m : ℝ) * v ^ m := by
    have e : (2 * Real.pi) ^ (-((m + 2 : ℕ) : ℝ) / 2) * Cwin (m + 2) * r ^ (m + 2) *
        (2 / (m : ℝ) * (r ^ 2) ^ (-((m + 2 : ℕ) : ℝ) / 2) * (K : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2)) =
        ((2 * Real.pi) ^ (-((m + 2 : ℕ) : ℝ) / 2) * Cwin (m + 2)) * (2 / (m : ℝ)) *
          (((r ^ 2) ^ (-((m + 2 : ℕ) : ℝ) / 2) * r ^ (m + 2)) *
            (K : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2)) := by ring
    rw [e, hrd, one_mul]
    calc _ ≤ ((2 * Real.pi) ^ (-((m + 2 : ℕ) : ℝ) / 2) * Cwin (m + 2)) * (2 / (m : ℝ)) * v ^ m :=
          mul_le_mul_of_nonneg_left hKr (by positivity)
      _ = _ := by ring
  have hv2le : v ^ 2 ≤ 1 := pow_le_one₀ hv0.le hv1
  have hT0' : 4 * ((m + 2 : ℕ) : ℝ) * Real.exp (-x ^ 2 / 32) ≤
      4 * ((m + 2 : ℕ) : ℝ) * Cb (m + 2) * v ^ m := by
    refine hT0.trans ?_
    have : 0 ≤ 4 * ((m + 2 : ℕ) : ℝ) * Cb (m + 2) * v ^ m := by positivity
    linarith only [mul_le_mul_of_nonneg_left hv2le this]
  linarith

/-- ES22 Lemma 9.1, as an upper bound: ever hitting a cube or a ball (a), for `σ = 1`: the probability that `w + B` ever enters the
cube of radius `r` around `0` is at most `C_hit (r/‖w‖)^{d-2}`. -/
theorem hit_ball_unit [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (hd : 3 ≤ d) {w : Fin d → ℝ} (hw : w ≠ 0) {r : ℝ}
    (hr : 0 < r) :
    P {ω | ∃ t : ℝ≥0, ‖w + B t ω‖ ≤ r} ≤ ENNReal.ofReal (Chit d * (r / ‖w‖) ^ (d - 2)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hRpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set R := ‖w‖ with hRdef
  by_cases hR4 : R ≤ 4 * r
  · refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 / 4 : ℝ) ≤ r / R := by rw [le_div_iff₀ hRpos]; linarith
    have h2 : (1 / 4 : ℝ) ^ (d - 2) ≤ (r / R) ^ (d - 2) := pow_le_pow_left₀ (by norm_num) h1 _
    have h3 : (4 : ℝ) ^ (d - 2) ≤ Chit d := le_max_left _ _
    calc (1 : ℝ) = 4 ^ (d - 2) * (1 / 4) ^ (d - 2) := by rw [← mul_pow]; norm_num
      _ ≤ Chit d * (r / R) ^ (d - 2) := mul_le_mul h3 h2 (by positivity) (le_trans (by positivity) h3)
  · have hR4 := not_le.1 hR4
    set h : ℝ≥0 := (r ^ 2).toNNReal with hhdef
    have hhR : (h : ℝ) = r ^ 2 := Real.coe_toNNReal _ (sq_nonneg r)
    have hh0 : h ≠ 0 := by
      intro h0; rw [h0] at hhR; have := pow_pos hr 2; simp at hhR; linarith
    let a : ℕ → ℝ≥0 := fun k => (k * r ^ 2).toNNReal
    have haR : ∀ k, (a k : ℝ) = k * r ^ 2 := fun k => Real.coe_toNNReal _ (by positivity)
    have hsub : {ω | ∃ t : ℝ≥0, ‖w + B t ω‖ ≤ r} ⊆
        ⋃ k : ℕ, {ω | ∃ u, a k ≤ u ∧ u ≤ a k + h ∧ ‖w + B u ω‖ ≤ r} := by
      rintro ω ⟨t, ht⟩
      have hr2 : 0 < r ^ 2 := by positivity
      have h1 : (⌊(t : ℝ) / r ^ 2⌋₊ : ℝ) ≤ (t : ℝ) / r ^ 2 := Nat.floor_le (by positivity)
      have h2 : (t : ℝ) / r ^ 2 < ⌊(t : ℝ) / r ^ 2⌋₊ + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hr2] at h1
      rw [div_lt_iff₀ hr2] at h2
      refine Set.mem_iUnion.2 ⟨⌊(t : ℝ) / r ^ 2⌋₊, t, ?_, ?_, ht⟩
      · rw [← NNReal.coe_le_coe, haR]; linarith
      · rw [← NNReal.coe_le_coe, NNReal.coe_add, haR, hhR]; linarith
    set f : ℕ → ℝ≥0∞ := fun k => ∫⁻ ω, winG d r (r ^ 2) ‖w + B (a k) ω‖ ∂P with hf
    have hfk : ∀ k : ℕ, P {ω | ∃ u, a k ≤ u ∧ u ≤ a k + h ∧ ‖w + B u ω‖ ≤ r} ≤ f k := by
      intro k
      have := window_shift_le hB (a k) hh0 w r
      rw [hhR] at this
      exact this
    -- the three ranges
    set K : ℕ := ⌈(R / r) ^ 2⌉₊ with hK
    have hx2 : 16 ≤ (R / r) ^ 2 := by
      have : 4 ≤ R / r := by rw [le_div_iff₀ hr]; linarith
      calc (16 : ℝ) = 4 ^ 2 := by norm_num
        _ ≤ (R / r) ^ 2 := pow_le_pow_left₀ (by norm_num) this 2
    have hK1 : (R / r) ^ 2 ≤ K := Nat.le_ceil _
    have hK2 : (K : ℝ) ≤ 2 * (R / r) ^ 2 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ (R / r) ^ 2 by positivity)
      linarith
    have hKge : 1 ≤ K := by
      have : (1 : ℝ) ≤ K := by linarith
      exact_mod_cast this
    set T0 : ℝ := 4 * d * Real.exp (-(R / r) ^ 2 / 32) with hT0
    set A : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) *
        ((d : ℝ) / (2 * Real.exp 1 * (R ^ 2 / 8))) ^ ((d : ℝ) / 2) * (Cwin d * r ^ d) with hA
    have hT0nn : 0 ≤ T0 := by rw [hT0]; positivity
    have hAnn : 0 ≤ A := by rw [hA]; have := Cwin_nonneg d; positivity
    have hf0 : f 0 ≤ ENNReal.ofReal T0 := by
      have h0 : a 0 = 0 := by simp [a]
      have : ∀ ω, ‖w + B (a 0) ω‖ = R := by
        intro ω; rw [h0, (hB.continuous_zero ω).2, add_zero]
      simp only [hf, this, lintegral_const, measure_univ, mul_one]
      exact winG_le_of_ge_half hr hR4.le (by linarith)
    have hfmid : ∀ k : ℕ, f (k + 1) ≤ ENNReal.ofReal (A + T0) := by
      intro k
      have ha0 : a (k + 1) ≠ 0 := by
        intro h0
        have h1 := haR (k + 1)
        rw [h0, NNReal.coe_zero] at h1
        have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * r ^ 2 := by positivity
        linarith
      have := hit_term_le hB (by omega) ha0 w hr hR4.le
      rw [← ENNReal.ofReal_add hAnn hT0nn] at this
      exact this
    have hftail : ∀ j : ℕ, f (j + (K + 1)) ≤ ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) *
        Cwin d * r ^ d * ((((K + 1 + j : ℕ) : ℝ) * r ^ 2) ^ (-(d : ℝ) / 2))) := by
      intro j
      have ha0 : a (j + (K + 1)) ≠ 0 := by
        intro h0
        have h1 := haR (j + (K + 1))
        rw [h0, NNReal.coe_zero] at h1
        have : (0 : ℝ) < ((j + (K + 1) : ℕ) : ℝ) * r ^ 2 := by positivity
        linarith
      have := lintegral_winG_brownian_le hB ha0 w hr
      refine this.trans (le_of_eq ?_)
      congr 1
      rw [haR, Real.mul_rpow (by positivity) (by positivity)]
      have e : ((j + (K + 1) : ℕ) : ℝ) = ((K + 1 + j : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      ring
    set tailR : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d * r ^ d *
        (2 / ((d : ℝ) - 2) * (r ^ 2) ^ (-(d : ℝ) / 2) * (K : ℝ) ^ (1 - (d : ℝ) / 2)) with htailR
    have hc1 : 0 ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d * r ^ d := by
      have := Cwin_nonneg d; positivity
    have htailnn : 0 ≤ tailR := by
      rw [htailR]
      have h2 : 0 ≤ 2 / ((d : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
      exact mul_nonneg hc1 (mul_nonneg (mul_nonneg h2 (by positivity)) (by positivity))
    have htail : ∑' j, f (j + (K + 1)) ≤ ENNReal.ofReal tailR := by
      refine (ENNReal.tsum_le_tsum hftail).trans ?_
      refine tsum_ofReal_le_of_partial (fun j => mul_nonneg hc1 (by positivity)) fun n => ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_Ioc_mul_rpow_le hd (h := r ^ 2) (by positivity) hKge n) hc1
    have hsum : ∑' k, f k = ∑ k ∈ Finset.range (K + 1), f k + ∑' j, f (j + (K + 1)) :=
      (Summable.sum_add_tsum_nat_add' (f := f) (k := K + 1) ENNReal.summable).symm
    have hfront : ∑ k ∈ Finset.range (K + 1), f k ≤
        ENNReal.ofReal T0 + (K : ℝ≥0∞) * ENNReal.ofReal (A + T0) := by
      rw [Finset.sum_range_succ', add_comm]
      refine add_le_add hf0 ?_
      calc ∑ k ∈ Finset.range K, f (k + 1) ≤ ∑ _k ∈ Finset.range K, ENNReal.ofReal (A + T0) :=
            Finset.sum_le_sum fun k _ => hfmid k
        _ = _ := by simp
    have hmain := hit_arith hd hr hR4 hK1 hK2
    have hcoef : 2 * Ca d + 12 * d * Cb d +
        2 * ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Cwin d) / ((d : ℝ) - 2) ≤ Chit d := le_max_right _ _
    calc P {ω | ∃ t : ℝ≥0, ‖w + B t ω‖ ≤ r}
        ≤ P (⋃ k : ℕ, {ω | ∃ u, a k ≤ u ∧ u ≤ a k + h ∧ ‖w + B u ω‖ ≤ r}) := measure_mono hsub
      _ ≤ ∑' k : ℕ, P {ω | ∃ u, a k ≤ u ∧ u ≤ a k + h ∧ ‖w + B u ω‖ ≤ r} := measure_iUnion_le _
      _ ≤ ∑' k, f k := ENNReal.tsum_le_tsum hfk
      _ ≤ (ENNReal.ofReal T0 + (K : ℝ≥0∞) * ENNReal.ofReal (A + T0)) + ENNReal.ofReal tailR := by
          rw [hsum]; exact add_le_add hfront htail
      _ = ENNReal.ofReal (T0 + K * (A + T0) + tailR) := by
          have hKnn : (0 : ℝ) ≤ K * (A + T0) := mul_nonneg (Nat.cast_nonneg K) (add_nonneg hAnn hT0nn)
          rw [ENNReal.ofReal_add (add_nonneg hT0nn hKnn) htailnn, ENNReal.ofReal_add hT0nn hKnn,
            ENNReal.ofReal_mul (Nat.cast_nonneg K), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (Chit d * (r / R) ^ (d - 2)) := by
          refine ENNReal.ofReal_le_ofReal (hmain.trans ?_)
          exact mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- ES22 Lemma 9.1, as an upper bound: ever hitting a cube or a ball (a) (ES22 Lemma 9.1 as an upper bound, deviation F20). For `d ≥ 3`,
every standard Brownian motion, `x ≠ y` and `r, σ > 0`:
`P(∃ t ≥ 0, ‖y + σ B(t) - x‖ ≤ r) ≤ C_hit (r/‖y - x‖)^{d-2}`. -/
theorem hit_ball_le [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (hd : 3 ≤ d) {x y : Fin d → ℝ} (hxy : x ≠ y)
    {r σ : ℝ} (hr : 0 < r) (hσ : 0 < σ) :
    P {ω | ∃ t : ℝ≥0, ‖y + σ • B t ω - x‖ ≤ r} ≤
      ENNReal.ofReal (Chit d * (r / ‖y - x‖) ^ (d - 2)) := by
  have hw : σ⁻¹ • (y - x) ≠ 0 := by
    intro h
    rw [smul_eq_zero] at h
    rcases h with h | h
    · exact (inv_pos.2 hσ).ne' h
    · exact hxy (sub_eq_zero.1 h).symm
  have hyx : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  have := hit_ball_unit hB hd hw (div_pos hr hσ)
  have e : r / σ / ‖σ⁻¹ • (y - x)‖ = r / ‖y - x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hσ)]
    field_simp
  rw [e] at this
  refine le_trans (measure_mono ?_) this
  intro ω hω
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ?_⟩
  have h1 := norm_add_smul_eq hσ (y - x) (B t ω)
  have e2 : y + σ • B t ω - x = (y - x) + σ • B t ω := by abel
  rw [e2, h1] at ht
  rw [le_div_iff₀ hσ]
  linarith

end ElboimSly.Brownian
