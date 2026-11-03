/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56GProps
public import ElboimSly.Paper.Escape.C56Param
public import ElboimSly.Paper.Escape.SepAux
public import Mathlib

/-!
# ES22 Claim 5.6: `G_{2m+1} ⊆ E_{56}`

ES22 Claim 5.6, "On `G_{2m+1}`, `E_{56}` holds".
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

/-- The event `E_{56}` for a path `y = W_v`. -/
def Esc56Event (β : ℝ) (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ)
    (y : ℝ → Fin (k + 2) → ℤ) : Prop :=
  y t = z ∧ (∀ s, 0 ≤ s → s ≤ t → y s ∈ escBlockMinus j u) ∧
    (∀ s, β ≤ s → s ≤ t → y s ≠ v) ∧ (∀ s, 0 ≤ s → s ≤ t - β → y s ≠ z)

theorem sqrt_t_div_le {β t : ℝ} (hβ : (2 : ℝ) ^ 40 ≤ β) (ht : Real.sqrt β ≤ t) :
    Real.sqrt t / 2 ^ escPhaseM β t ≤ Real.sqrt β / 256 := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hS : (2 : ℝ) ^ 20 ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    calc ((2 : ℝ) ^ 20) ^ 2 = 2 ^ 40 := by rw [← pow_mul]
      _ ≤ β := hβ
  have h4 := lt_four_pow_m_succ hβ0 ht
  set m := escPhaseM β t
  have hpm : (0 : ℝ) < 2 ^ m := by positivity
  have h22 : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have ht0 : 0 ≤ t := (Real.sqrt_nonneg _).trans ht
  rw [div_le_iff₀ hpm]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  rw [pow_succ] at h4
  have h5 : 4 * Real.sqrt β ≤ Real.sqrt β ^ 2 / 65536 := by nlinarith
  have e : (Real.sqrt β / 256 * 2 ^ m) ^ 2 = Real.sqrt β ^ 2 / 65536 * 4 ^ m := by
    rw [mul_pow, div_pow, h22]; ring
  rw [e]
  have h6 : (0 : ℝ) < 4 ^ m := by positivity
  nlinarith

/-- Facts about the last phase: `a_{2m} = t - τ/2` etc. -/
theorem escPhaseA_two_m {t : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    escPhaseA t m (2 * m) = t - t / (2 * 4 ^ m) := by
  unfold escPhaseA
  rw [ite_eq_right (by omega)]
  have : 2 * m - m = m := by omega
  rw [this]

theorem es56B_two_m_le {t : ℝ} (ht : 0 ≤ t) {m : ℕ} : es56B t m (2 * m) ≤ t := es56B_le_t ht m _

theorem Esc56_of_G {j : ℕ} {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {β t : ℝ}
    (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j)
    (hm3 : 3 ≤ escPhaseM β t) (W : ℝ → Fin (k + 2) → ℤ)
    (hG : EscG β j u v z t W (2 * escPhaseM β t)) (hL : EscBlast β j u z t W) :
    Esc56Event β j u v z t W := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  set m := escPhaseM β t with hm
  have hS : (2 : ℝ) ^ 20 ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    calc ((2 : ℝ) ^ 20) ^ 2 = 2 ^ 40 := by rw [← pow_mul]
      _ ≤ β := hβ
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
  have hsβ : Real.sqrt β ≤ t := by
    have h4 : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by
      have hj := hgeom.hj
      obtain ⟨i0, hi0⟩ : ∃ i0, j = i0 + 1 := ⟨j - 1, by omega⟩
      rw [hi0]; simp [pow_succ]; ring
    nlinarith
  have hSj : Real.sqrt β < 2 ^ j := by
    refine (Real.sqrt_lt' (by positivity)).2 ?_
    calc β < 4 ^ j := hβj
      _ = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hbeta3 := esc_beta_pow_le hβ
  have hz0 := (escZeta_mem β W ht0.le m 0)
  have hzm := escZeta_mem β W ht0.le m (2 * m)
  have hAm := escPhaseA_two_m (t := t) (by omega : 1 ≤ m)
  set T := escZeta β W t m (2 * m) with hT
  have hTa : t - t / (2 * 4 ^ m) ≤ T := by rw [← hAm]; exact hzm.1
  have hTb : T ≤ t := hzm.2.trans (es56B_two_m_le ht0.le)
  have hpm4 : (0 : ℝ) < 4 ^ m := by positivity
  have h4m := four_pow_m_le hβ0 hsβ
  have hlt4 := lt_four_pow_m_succ hβ0 hsβ
  rw [pow_succ] at hlt4
  have hτ : t / 4 ^ m < 4 * Real.sqrt β := by
    rw [div_lt_iff₀ hpm4]; linarith
  have htb : t - β < T := by
    have : t / (2 * 4 ^ m) < β := by
      have e : t / (2 * 4 ^ m) = t / 4 ^ m / 2 := by field_simp
      rw [e]; nlinarith
    linarith
  -- the three parts for the phases
  have hphase : ∀ s, 0 ≤ s → s ≤ T → (s ≤ escZeta β W t m 0 ∨ ∃ i'', 1 ≤ i'' ∧ i'' ≤ 2 * m ∧
      escZeta β W t m (i'' - 1) < s ∧ s ≤ escZeta β W t m i'') := by
    intro s _ hs
    exact phase_decomp (fun n => escZeta β W t m n) hs
  refine ⟨hL.2, ?_, ?_, ?_⟩
  · -- block
    intro s hs0 hst
    by_cases hsT : s ≤ T
    · rcases hphase s hs0 hsT with h0 | ⟨i'', hi1, hile, hlt, hle⟩
      · exact (hG.1.2.1 s hs0 h0).1
      · have hBi := hG.2 i'' hi1 hile
        have hw : ‖escCast (W s) - escCurve j u v z t s‖ ≤ escR t m i'' := hBi.2.1 s hlt.le hle
        have hz1 : escPhaseA t m (i'' - 1) ≤ s :=
          le_trans (escZeta_mem β W ht0.le m (i'' - 1)).1 hlt.le
        have hz2 : s ≤ es56B t m i'' := le_trans hle (escZeta_mem β W ht0.le m i'').2
        exact curve_inside hgeom ht2 ht0 hi1 hile hz1 hz2 hw
    · exact (hL.1 s (le_of_lt (not_le.1 hsT)) hst).1
  · -- `≠ v`
    intro s hs hst hWv
    by_cases hsT : s ≤ T
    · exact EscG_ne_v hgeom hβ hβj ht1 ht2 W le_rfl hG hs hsT hWv
    · push Not at hsT
      have hs2 : ‖escCast (W s) - escCast (W T)‖ ≤ β ^ (0.3 : ℝ) := (hL.1 s hsT.le hst).2
      have hend : ‖escCast (W T) - escCurve j u v z t T‖ ≤ 24 / 100 * escR t m (2 * m) :=
        (hG.2 (2 * m) (by omega) le_rfl).2.2
      have hTh : t / 2 ≤ T := by
        have : t / (2 * 4 ^ m) ≤ t / 2 := by
          apply div_le_div_of_nonneg_left ht0.le (by norm_num)
          have : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
          linarith
        linarith
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
      have hm8 : 1 / (2 : ℝ) ^ m ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (2 : ℝ) ^ 3 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm3
        norm_num at this ⊢; linarith
      have hvz := hgeom.norm_vz_ge
      have hWv' : W s = v := hWv
      have hs2' : ‖escCast (W s) - escCast z‖ ≤ ‖escCast (W s) - escCast (W T)‖ +
          (‖escCast (W T) - escCurve j u v z t T‖ + ‖escCurve j u v z t T - escCast z‖) := by
        calc ‖escCast (W s) - escCast z‖
            = ‖(escCast (W s) - escCast (W T)) + ((escCast (W T) - escCurve j u v z t T) +
                (escCurve j u v z t T - escCast z))‖ := by congr 1; abel
          _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      rw [hWv'] at hs2' hs2
      have hj0 : (0 : ℝ) < 2 ^ j := by positivity
      have h5 : 1 / (2 : ℝ) ^ m * (2 ^ j / 4) ≤ 2 ^ j / 32 := by
        calc 1 / (2 : ℝ) ^ m * (2 ^ j / 4) ≤ 1 / 8 * (2 ^ j / 4) := by gcongr
          _ = 2 ^ j / 32 := by ring
      have hfin : (2 : ℝ) ^ 20 ≤ 2 ^ j := hS.trans hSj.le
      linarith [hs2, hend, hcz, hR, hs2', hvz, hSj, hbeta3, hS, h5]
  · -- `≠ z`
    intro s hs0 hst hWz
    have hsT : s ≤ T := by linarith
    have hvz := hgeom.norm_vz_ge
    rcases hphase s hs0 hsT with h0 | ⟨i'', hi1, hile, hlt, hle⟩
    · have := (hG.1.2.1 s hs0 h0).2
      rw [hWz, norm_sub_rev] at this
      nlinarith [Real.sqrt_nonneg β]
    · have hBi := hG.2 i'' hi1 hile
      have hw : ‖escCast (W s) - escCurve j u v z t s‖ ≤ escR t m i'' := hBi.2.1 s hlt.le hle
      have hz1 : escPhaseA t m (i'' - 1) ≤ s :=
        le_trans (escZeta_mem β W ht0.le m (i'' - 1)).1 hlt.le
      have hz2 : s ≤ es56B t m i'' := le_trans hle (escZeta_mem β W ht0.le m i'').2
      have hβ20 : (2 : ℝ) ^ 20 ≤ β := le_trans (by norm_num) hβ
      have haw := curve_away_from_z hgeom hβ20 hβj ht2 ht0 hi1 hile hz1 hz2 hst
      rw [hWz] at hw
      rw [norm_sub_rev] at hw
      have hS0 : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
      linarith

end ElboimSly.Paper.Escape

end
