/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Incl
public import ElboimSly.Paper.Escape.C56Point
public import ElboimSly.Paper.Escape.C56Det3
public import Mathlib

/-!
# ES22 Claim 5.6, phase `2m+1`: geometry

ES22 Claim 5.6, "Phase `2m+1`".  On `G_{2m}`: `W_v(ζ_{2m})` is within `S/512 + S/2048`
of `w`, and `W_v(s')` is at distance `≥ √β/20` from `w` for `s' ≤ ζ_{2m}`, `s' ≤ t - β`.
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

/-- The common numerical facts. -/
theorem sqrt_facts {β t : ℝ} {j : ℕ} (hj : 1 ≤ j) (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j)
    (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) :
    (2 : ℝ) ^ 20 ≤ Real.sqrt β ∧ Real.sqrt β ≤ t ∧ Real.sqrt β < 2 ^ j := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hS : (2 : ℝ) ^ 20 ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    calc ((2 : ℝ) ^ 20) ^ 2 = 2 ^ 40 := by rw [← pow_mul]
      _ ≤ β := hβ
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
  have h4 : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by
    obtain ⟨i0, hi0⟩ : ∃ i0, j = i0 + 1 := ⟨j - 1, by omega⟩
    rw [hi0]; simp [pow_succ]; ring
  refine ⟨hS, by nlinarith, ?_⟩
  refine (Real.sqrt_lt' (by positivity)).2 ?_
  calc β < 4 ^ j := hβj
    _ = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- On `G_{2m}`, `‖W_v(ζ_{2m}) - w‖ ≤ S/512 + S/2048`. -/
theorem W_zeta_near_z {j : ℕ} {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {β t : ℝ}
    (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (_ht2 : t ≤ 4 ^ j)
    (hm3 : 3 ≤ escPhaseM β t) (W : ℝ → Fin (k + 2) → ℤ)
    (hG : EscG β j u v z t W (2 * escPhaseM β t)) :
    ‖escCast (W (escZeta β W t (escPhaseM β t) (2 * escPhaseM β t))) - escCast z‖ ≤
      Real.sqrt β / 512 + Real.sqrt β / 2048 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  obtain ⟨hS, hsβ, hSj⟩ := sqrt_facts (by have := hgeom.hj; omega) hβ hβj ht1
  set m := escPhaseM β t with hm
  have hzm := escZeta_mem β W ht0.le m (2 * m)
  have hAm := escPhaseA_two_m (t := t) (by omega : 1 ≤ m)
  set T := escZeta β W t m (2 * m) with hT
  have hTa : t - t / (2 * 4 ^ m) ≤ T := by rw [← hAm]; exact hzm.1
  have hpm4 : (0 : ℝ) < 4 ^ m := by positivity
  have hTh : t / 2 ≤ T := by
    have : t / (2 * 4 ^ m) ≤ t / 2 := by
      apply div_le_div_of_nonneg_left ht0.le (by norm_num)
      have : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
      linarith
    linarith
  have hend : ‖escCast (W T) - escCurve j u v z t T‖ ≤ 24 / 100 * escR t m (2 * m) :=
    (hG.2 (2 * m) (by omega) le_rfl).2.2
  have hc : escCurve j u v z t T = escCast z +
      Real.sqrt (2 * (t - T) / t) • (escCentre j u - escCast z) := by
    unfold escCurve; rw [es56F_of_ge ht0 hTh]
  have hμ : Real.sqrt (2 * (t - T) / t) ≤ 1 / 2 ^ m := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ ht0]
    have h22 : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [div_pow, h22]
    have : 2 * (t - T) ≤ t / 4 ^ m := by
      have e : t / (2 * 4 ^ m) * 2 = t / 4 ^ m := by field_simp
      linarith
    calc 2 * (t - T) ≤ t / 4 ^ m := this
      _ = 1 ^ 2 / 4 ^ m * t := by field_simp
  have hcz : ‖escCurve j u v z t T - escCast z‖ ≤ 1 / 2 ^ m * (2 ^ j / 4) := by
    rw [hc, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul hμ hgeom.norm_qz_le (norm_nonneg _) (by positivity)
  have hR : escR t m (2 * m) ≤ Real.sqrt β / 2048 := by
    refine (escR_le_rho ht0 m _).trans ?_
    rw [rho_of_gt (by omega : m < 2 * m)]
    have e : 2 * m - m + 3 = m + 3 := by omega
    rw [e, pow_add]
    have := sqrt_t_div_le hβ hsβ
    have h8 : (2 : ℝ) ^ 3 = 8 := by norm_num
    rw [h8, ← div_div]
    have : Real.sqrt t / 2 ^ m / 8 ≤ Real.sqrt β / 256 / 8 := by gcongr
    linarith
  -- `2^j ≤ 2 √t`, hence `2^j / (4 · 2^m) ≤ S/512`
  have h2j : (2 : ℝ) ^ j ≤ 2 * Real.sqrt t := by
    have h4 : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by
      have hj := hgeom.hj
      obtain ⟨i0, hi0⟩ : ∃ i0, j = i0 + 1 := ⟨j - 1, by omega⟩
      rw [hi0]; simp [pow_succ]; ring
    have e : ((2 : ℝ) ^ j / 2) ^ 2 = 4 ^ (j - 1) := by
      rw [div_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
      rw [show (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) from h4]; ring
    have : (2 : ℝ) ^ j / 2 ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by rw [e]; exact ht1)
    linarith
  have hsq' := sqrt_t_div_le hβ hsβ
  have hpm2 : (0 : ℝ) < 2 ^ m := by positivity
  have h3 : 1 / (2 : ℝ) ^ m * (2 ^ j / 4) ≤ Real.sqrt β / 512 := by
    have : (2 : ℝ) ^ j / 4 ≤ Real.sqrt t / 2 := by linarith
    calc 1 / (2 : ℝ) ^ m * (2 ^ j / 4) ≤ 1 / (2 : ℝ) ^ m * (Real.sqrt t / 2) := by gcongr
      _ = (Real.sqrt t / 2 ^ m) / 2 := by field_simp
      _ ≤ (Real.sqrt β / 256) / 2 := by gcongr
      _ = Real.sqrt β / 512 := by ring
  calc ‖escCast (W T) - escCast z‖
      = ‖(escCast (W T) - escCurve j u v z t T) + (escCurve j u v z t T - escCast z)‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ 24 / 100 * escR t m (2 * m) + 1 / 2 ^ m * (2 ^ j / 4) := add_le_add hend hcz
    _ ≤ _ := by
        have := escR_pos ht0 m (2 * m)
        linarith

/-- Before the end of the phases, `W_v` stays `√β/20` away from `w`. -/
theorem W_far_from_z {j : ℕ} {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {β t : ℝ}
    (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j)
    (W : ℝ → Fin (k + 2) → ℤ) {i : ℕ} (him : i ≤ 2 * escPhaseM β t)
    (hG : EscG β j u v z t W i) {s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t - β)
    (hsi : s ≤ escZeta β W t (escPhaseM β t) i) :
    Real.sqrt β / 20 ≤ ‖escCast (W s) - escCast z‖ := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  obtain ⟨hS, hsβ, hSj⟩ := sqrt_facts (by have := hgeom.hj; omega) hβ hβj ht1
  have hbeta3 := esc_beta_pow_le hβ
  set m := escPhaseM β t with hm
  have hvz := hgeom.norm_vz_ge
  rcases phase_decomp (fun n => escZeta β W t m n) hsi with h0 | ⟨i'', hi1, hile, hlt, hle⟩
  · have h1 := (hG.1.2.1 s hs0 h0).2
    have : ‖escCast v - escCast z‖ ≤ ‖escCast v - escCast (W s)‖ + ‖escCast (W s) - escCast z‖ := by
      calc ‖escCast v - escCast z‖ = ‖(escCast v - escCast (W s)) + (escCast (W s) - escCast z)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev] at h1
    linarith
  · have hBi := hG.2 i'' hi1 hile
    have hw : ‖escCast (W s) - escCurve j u v z t s‖ ≤ escR t m i'' := hBi.2.1 s hlt.le hle
    have hz1 : escPhaseA t m (i'' - 1) ≤ s :=
      le_trans (escZeta_mem β W ht0.le m (i'' - 1)).1 hlt.le
    have hz2 : s ≤ es56B t m i'' := le_trans hle (escZeta_mem β W ht0.le m i'').2
    have hβ20 : (2 : ℝ) ^ 20 ≤ β := le_trans (by norm_num) hβ
    have haw := curve_away_from_z hgeom hβ20 hβj ht2 ht0 hi1 (by omega) hz1 hz2 hst
    have : ‖escCurve j u v z t s - escCast z‖ ≤ ‖escCurve j u v z t s - escCast (W s)‖ +
        ‖escCast (W s) - escCast z‖ := by
      calc ‖escCurve j u v z t s - escCast z‖ =
          ‖(escCurve j u v z t s - escCast (W s)) + (escCast (W s) - escCast z)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev] at hw
    linarith

end ElboimSly.Paper.Escape

end
