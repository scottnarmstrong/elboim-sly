/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Det
public import ElboimSly.Paper.Escape.Gamma
public import Mathlib

/-!
# ES22 Claim 5.6: numerical facts about the phases

ES22 Claim 5.6, "Phase `i`".  `3 ≤ m`, the length `T_i ≥ 0.9 √β` of each phase, the radii
`R_{i-1} ≤ 2 R_i`, and `ρ_i/8 ≤ R_i ≤ ρ_i`.
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

theorem es56Rho_pos {t : ℝ} (ht : 0 < t) (m i : ℕ) : 0 < es56Rho t m i := by
  unfold es56Rho
  have := Real.sqrt_pos.2 ht
  split_ifs <;> positivity

theorem escR_pos {t : ℝ} (ht : 0 < t) (m i : ℕ) : 0 < escR t m i := by
  unfold escR escKappa
  have := es56Rho_pos ht m i
  split_ifs <;> positivity

theorem escR_le_rho {t : ℝ} (ht : 0 < t) (m i : ℕ) : escR t m i ≤ es56Rho t m i := by
  unfold escR
  have := es56Rho_pos ht m i
  have := escKappa_le_one m i
  nlinarith

theorem rho_le_eight_escR {t : ℝ} (ht : 0 < t) (m i : ℕ) : es56Rho t m i ≤ 8 * escR t m i := by
  unfold escR escKappa
  have := es56Rho_pos ht m i
  split_ifs <;> linarith

/-- `4^m √β ≤ t`. -/
theorem four_pow_m_le {β t : ℝ} (hβ : 0 < β) (ht : Real.sqrt β ≤ t) :
    (4 : ℝ) ^ escPhaseM β t * Real.sqrt β ≤ t := by
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hx : 1 ≤ t / Real.sqrt β := by rw [le_div_iff₀ hsb]; linarith
  have hlog : 0 ≤ Real.logb 4 (t / Real.sqrt β) := Real.logb_nonneg (by norm_num) hx
  have h1 : (escPhaseM β t : ℝ) ≤ Real.logb 4 (t / Real.sqrt β) := Nat.floor_le hlog
  have h2 : (4 : ℝ) ^ escPhaseM β t ≤ t / Real.sqrt β := by
    calc (4 : ℝ) ^ escPhaseM β t = (4 : ℝ) ^ (escPhaseM β t : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (4 : ℝ) ^ (Real.logb 4 (t / Real.sqrt β)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = t / Real.sqrt β := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  rwa [le_div_iff₀ hsb] at h2

/-- `t < 4^{m+1} √β`. -/
theorem lt_four_pow_m_succ {β t : ℝ} (hβ : 0 < β) (ht : Real.sqrt β ≤ t) :
    t < (4 : ℝ) ^ (escPhaseM β t + 1) * Real.sqrt β := by
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hx : 1 ≤ t / Real.sqrt β := by rw [le_div_iff₀ hsb]; linarith
  have h1 : Real.logb 4 (t / Real.sqrt β) < (escPhaseM β t : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : t / Real.sqrt β < (4 : ℝ) ^ (escPhaseM β t + 1) := by
    have := (Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith)).1
      (show Real.logb 4 (t / Real.sqrt β) < ((escPhaseM β t + 1 : ℕ) : ℝ) by push_cast; exact h1)
    rwa [Real.rpow_natCast] at this
  rwa [div_lt_iff₀ hsb] at h2

theorem three_le_m {β t : ℝ} {j : ℕ} (hβ : (2 : ℝ) ^ 16 ≤ β) (hβj : β < 4 ^ j) (hj : 1 ≤ j)
    (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) : 3 ≤ escPhaseM β t := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have hs256 : (256 : ℝ) ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    calc (256 : ℝ) ^ 2 = 2 ^ 16 := by norm_num
      _ ≤ β := hβ
  have h4 : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by
    obtain ⟨i0, rfl⟩ : ∃ i0, j = i0 + 1 := ⟨j - 1, by omega⟩
    simp [pow_succ]; ring
  have htβ : β / 4 ≤ t := by linarith
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
  have hts : 64 * Real.sqrt β ≤ t := by nlinarith
  have hx : (64 : ℝ) ≤ t / Real.sqrt β := by rw [le_div_iff₀ hsb]; linarith
  unfold escPhaseM
  apply Nat.le_floor
  rw [Nat.cast_ofNat]
  have : (3 : ℝ) = Real.logb 4 (4 ^ (3 : ℝ)) := by
    rw [Real.logb_rpow (by norm_num) (by norm_num)]
  rw [this]
  exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (by norm_num; linarith)

/-- Each phase lasts at least `0.9 √β`: `b_i - b_{i-1} ≥ 0.9 √β`, for `1 ≤ i ≤ 2m`. -/
theorem phase_length_ge {β t : ℝ} (hβ : 0 < β) (ht : Real.sqrt β ≤ t) {i : ℕ} (hi1 : 1 ≤ i)
    (him : i ≤ 2 * escPhaseM β t) :
    9 / 10 * Real.sqrt β ≤ es56B t (escPhaseM β t) i - es56B t (escPhaseM β t) (i - 1) := by
  have h4 := four_pow_m_le hβ ht
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  set m := escPhaseM β t with hm
  have hpm : (0 : ℝ) < 4 ^ m := by positivity
  have hτ : Real.sqrt β ≤ t / 4 ^ m := by rw [le_div_iff₀ hpm]; linarith
  have ht0 : 0 < t := lt_of_lt_of_le hsb ht
  unfold es56B
  by_cases hA : i ≤ m
  · rw [ite_eq_left hA, ite_eq_left (by omega : i - 1 ≤ m)]
    obtain ⟨kk, hk⟩ : ∃ kk, m - i = kk := ⟨_, rfl⟩
    have hk' : m - (i - 1) = kk + 1 := by omega
    rw [hk, hk', pow_succ]
    have hx : (0 : ℝ) < 4 ^ kk := by positivity
    have e : 3 / 5 * t / 4 ^ kk - 3 / 5 * t / (4 ^ kk * 4) = 9 / 20 * (t / 4 ^ kk) := by
      field_simp; ring
    rw [e]
    have hm4 : (4 : ℝ) ^ m = 4 ^ kk * 4 ^ i := by rw [← pow_add]; congr 1; omega
    have hi4 : (4 : ℝ) ≤ 4 ^ i := by
      calc (4 : ℝ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ i := pow_le_pow_right₀ (by norm_num) hi1
    have hge : t / 4 ^ kk = (t / 4 ^ m) * 4 ^ i := by rw [hm4]; field_simp
    nlinarith
  · push Not at hA
    by_cases hB : i = m + 1
    · subst hB
      rw [ite_eq_right (by omega), ite_eq_left (by omega : m + 1 - 1 ≤ m)]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, div_one, show m + 1 - m = 1 by omega,
        pow_one]
      have hm1 : 1 ≤ m := by omega
      have h44 : (4 : ℝ) ≤ 4 ^ m := by
        calc (4 : ℝ) = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hm1
      have : 4 * Real.sqrt β ≤ t := by nlinarith
      linarith
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      obtain ⟨kk, hk⟩ : ∃ kk, i - m = kk + 2 := ⟨i - m - 2, by omega⟩
      have hk' : i - 1 - m = kk + 1 := by omega
      rw [hk, hk', pow_succ, pow_succ]
      have hx : (0 : ℝ) < 4 ^ kk := by positivity
      have e : t - 3 / 10 * t / (4 ^ kk * 4 * 4) - (t - 3 / 10 * t / (4 ^ kk * 4)) =
          9 / 160 * (t / 4 ^ kk) := by field_simp; ring
      rw [e]
      have hkm : kk + 2 ≤ m := by omega
      have hm4 : (4 : ℝ) ^ m = 4 ^ kk * 4 ^ (m - kk) := by rw [← pow_add]; congr 1; omega
      have h16 : (16 : ℝ) ≤ 4 ^ (m - kk) := by
        calc (16 : ℝ) = 4 ^ 2 := by norm_num
          _ ≤ 4 ^ (m - kk) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hge : t / 4 ^ kk = (t / 4 ^ m) * 4 ^ (m - kk) := by rw [hm4]; field_simp
      nlinarith

theorem rho_of_le {t : ℝ} {m i : ℕ} (h : i ≤ m) :
    es56Rho t m i = Real.sqrt t / 2 ^ (m - i + 5) := by
  unfold es56Rho; rw [ite_eq_left h]

theorem rho_of_gt {t : ℝ} {m i : ℕ} (h : m < i) :
    es56Rho t m i = Real.sqrt t / 2 ^ (i - m + 3) := by
  unfold es56Rho; rw [ite_eq_right (not_le.2 h)]

/-- `R_{i-1} ≤ 2 R_i` for `2 ≤ i ≤ 2m`, `m ≥ 3`. -/
theorem escR_ratio {t : ℝ} (ht : 0 < t) {m i : ℕ} (hm3 : 3 ≤ m) (hi2 : 2 ≤ i)
    (him : i ≤ 2 * m) : escR t m (i - 1) ≤ 2 * escR t m i := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  unfold escR escKappa
  by_cases hA : i + 2 ≤ m
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      rho_of_le (by omega), rho_of_le (by omega)]
    have h1 : m - (i - 1) + 5 = (m - i + 5) + 1 := by omega
    rw [h1, pow_succ, ← div_div]
    have hX : 0 < Real.sqrt t / 2 ^ (m - i + 5) := by positivity
    linarith
  · by_cases hB : i + 1 = m
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hB, ite_eq_right (by omega),
        rho_of_le (by omega), rho_of_le (by omega)]
      have h1 : m - (i - 1) + 5 = (m - i + 5) + 1 := by omega
      rw [h1, pow_succ, ← div_div]
      have hX : 0 < Real.sqrt t / 2 ^ (m - i + 5) := by positivity
      linarith
    · by_cases hC : i = m
      · subst hC
        rw [ite_eq_right (by omega), ite_eq_left (by omega : i - 1 + 1 = i), ite_eq_left le_rfl,
          rho_of_le (by omega), rho_of_le le_rfl]
        have h1 : i - (i - 1) + 5 = 6 := by omega
        rw [h1, Nat.sub_self]
        norm_num
        linarith
      · by_cases hD : i = m + 1
        · subst hD
          rw [ite_eq_left (by omega : m ≤ m + 1 - 1), ite_eq_left (by omega : m ≤ m + 1),
            rho_of_le (by omega : m + 1 - 1 ≤ m), rho_of_gt (by omega : m < m + 1)]
          have h1 : m + 1 - 1 = m := by omega
          rw [h1, Nat.sub_self, Nat.add_sub_cancel_left]
          norm_num
          linarith
        · have hE : m + 2 ≤ i := by omega
          rw [ite_eq_left (by omega : m ≤ i - 1), ite_eq_left (by omega : m ≤ i),
            rho_of_gt (by omega : m < i - 1), rho_of_gt (by omega : m < i)]
          obtain ⟨n, hn⟩ : ∃ n, i - m + 3 = n + 1 := ⟨i - m + 2, by omega⟩
          have h2 : i - 1 - m + 3 = n := by omega
          rw [h2, hn, pow_succ, ← div_div]
          have hX : 0 < Real.sqrt t / 2 ^ n := by positivity
          linarith

theorem rho_zero_eq {t : ℝ} {m : ℕ} (hm3 : 3 ≤ m) : es56Rho t m 0 = escR t m 1 / 2 := by
  unfold escR escKappa
  rw [ite_eq_right (by omega), ite_eq_right (by omega), rho_of_le (by omega), rho_of_le (by omega)]
  have h1 : m - 0 + 5 = (m - 1 + 5) + 1 := by omega
  rw [h1, pow_succ]
  field_simp

/-- The hypotheses of the tube lemma for the curve `s ↦ f(T + s)` at radius `ρ = (29/30) R_i`. -/
theorem tube_params {j : ℕ} {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {t : ℝ}
    (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j) {m i : ℕ} (hm3 : 3 ≤ m) (hi1 : 1 ≤ i)
    (him : i ≤ 2 * m) {T : ℝ} (hT1 : escPhaseA t m (i - 1) ≤ T) (hT2 : T ≤ es56B t m (i - 1))
    {x : Fin (k + 2) → ℤ}
    (hx : ‖escCast x - escCurve j u v z t T‖ ≤
      if i = 1 then es56Rho t m 0 else (24 / 100) * escR t m (i - 1)) :
    let ρ := 29 / 30 * escR t m i
    0 < ρ ∧ ρ ^ 2 / escKstar ≤ es56B t m i - T ∧ es56B t m i - T ≤ escKstar * ρ ^ 2 ∧
      (∀ a ∈ Set.Icc (0 : ℝ) (es56B t m i - T), ∀ b ∈ Set.Icc (0 : ℝ) (es56B t m i - T),
        ‖escCurve j u v z t (T + a) - escCurve j u v z t (T + b)‖ ≤ escKstar / ρ * |a - b|) ∧
      ‖escCast x - escCurve j u v z t (T + 0)‖ ≤ 3 * ρ / 5 := by
  intro ρ
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hRpos := escR_pos ht0 m i
  have hRle := escR_le_rho ht0 m i
  have hρ8 := rho_le_eight_escR ht0 m i
  have hρpos := es56Rho_pos ht0 m i
  have hρdef : ρ = 29 / 30 * escR t m i := rfl
  have hρ : 0 < ρ := by positivity
  have hK : escKstar = 4 * 10 ^ 4 := rfl
  obtain ⟨hw1, hw2, -⟩ := phase_window ht0 hi1 hT1 hT2
  have hρle : ρ ≤ es56Rho t m i := by rw [hρdef]; linarith
  refine ⟨hρ, ?_, ?_, ?_, ?_⟩
  · have : ρ ^ 2 ≤ es56Rho t m i ^ 2 := pow_le_pow_left₀ hρ.le hρle 2
    rw [div_le_iff₀ (by rw [hK]; norm_num)]
    rw [hK]
    nlinarith [sq_nonneg (es56Rho t m i)]
  · have h1 : es56Rho t m i ^ 2 ≤ 64 * escR t m i ^ 2 := by nlinarith
    have h2 : escR t m i ^ 2 = (30 / 29) ^ 2 * ρ ^ 2 := by
      show escR t m i ^ 2 = (30 / 29) ^ 2 * (29 / 30 * escR t m i) ^ 2
      ring
    rw [hK]
    nlinarith [sq_nonneg ρ]
  · intro a ha b hb
    have hh2 : (0 : ℝ) ≤ 2 ^ j / 2 := by positivity
    have hh2t : ((2 : ℝ) ^ j / 2) ^ 2 ≤ t := by
      have : ((2 : ℝ) ^ j / 2) ^ 2 = 4 ^ (j - 1) := by
        have hj : 1 ≤ j := by have := hgeom.hj; omega
        obtain ⟨i0, rfl⟩ : ∃ i0, j = i0 + 1 := ⟨j - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have e : (2 : ℝ) ^ (i0 + 1) / 2 = 2 ^ i0 := by rw [pow_succ]; ring
        rw [e, ← pow_mul, mul_comm, pow_mul]
        norm_num
      linarith
    have hqv : ‖escCentre j u - escCast v‖ ≤ 2 ^ j / 2 := hgeom.norm_qv_le
    have hqw : ‖escCentre j u - escCast z‖ ≤ 2 ^ j / 2 := by
      have := hgeom.norm_qz_le
      have h2j : (0 : ℝ) ≤ 2 ^ j := by positivity
      linarith
    have hl := curve_lipschitz (t := t) (h2 := 2 ^ j / 2) (ρ := es56Rho t m i) ht0 hh2 hh2t
      hi1 hρpos le_rfl (v := escCast v) (w := escCast z) (q := escCentre j u) hqv hqw
      (s := T + a) (s' := T + b) ⟨by linarith [ha.1], by linarith [ha.2]⟩
      ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have hab : |T + a - (T + b)| = |a - b| := by congr 1; ring
    rw [hab] at hl
    unfold escCurve
    refine hl.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [hK, div_le_div_iff₀ hρpos hρ]
    nlinarith
  · by_cases h1 : i = 1
    · subst h1
      simp only [ite_true] at hx
      rw [rho_zero_eq hm3] at hx
      rw [add_zero]
      show _ ≤ 3 * (29 / 30 * escR t m 1) / 5
      linarith [escR_pos ht0 m 1]
    · simp only [ite_eq_right h1] at hx
      have hr := escR_ratio ht0 hm3 (by omega) him
      rw [add_zero]
      show _ ≤ 3 * (29 / 30 * escR t m i) / 5
      linarith

end ElboimSly.Paper.Escape

end
