/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.GeomBase
public import ElboimSly.Paper.Escape.GeomPhase
public import ElboimSly.Foundations.Brownian.ESClaim56
public import Mathlib

/-!
# Geometry of the curve: (d) Lipschitz and window arithmetic

Geometry of the curve (d).  For `1 ≤ i` and `a' ∈ [a_{i-1}, b_{i-1}]`:
`57.6 ρ_i² ≤ b_i - a' ≤ 486.4 ρ_i²` and `(a' + b_i)/2 ≤ a_i`; the curve is `1/ρ`-Lipschitz on
`[a_{i-1}, b_i]` for every `0 < ρ ≤ ρ_i`.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.Brownian

variable {k : ℕ}

lemma rho_sq_of_le {t : ℝ} (ht : 0 < t) {m i : ℕ} (hi : i ≤ m) :
    es56Rho t m i ^ 2 = t / 4 ^ (m - i) / 1024 := by
  unfold es56Rho; rw [ite_eq_left hi, div_pow, Real.sq_sqrt ht.le, pow_add]
  have : ((2 : ℝ) ^ (m - i)) ^ 2 = 4 ^ (m - i) := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [mul_pow, this]; field_simp; norm_num

lemma rho_sq_of_gt {t : ℝ} (ht : 0 < t) {m i : ℕ} (hi : m < i) :
    es56Rho t m i ^ 2 = t / 4 ^ (i - m) / 64 := by
  unfold es56Rho; rw [ite_eq_right (not_le.2 hi), div_pow, Real.sq_sqrt ht.le, pow_add]
  have : ((2 : ℝ) ^ (i - m)) ^ 2 = 4 ^ (i - m) := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [mul_pow, this]; field_simp; norm_num

/-- Geometry of the curve (d), the windows. -/
theorem phase_window {t : ℝ} (ht : 0 < t) {m i : ℕ} (hi1 : 1 ≤ i) {a' : ℝ}
    (h1 : escPhaseA t m (i - 1) ≤ a') (h2 : a' ≤ es56B t m (i - 1)) :
    576 / 10 * es56Rho t m i ^ 2 ≤ es56B t m i - a' ∧
      es56B t m i - a' ≤ 4864 / 10 * es56Rho t m i ^ 2 ∧ (a' + es56B t m i) / 2 ≤ escPhaseA t m i := by
  by_cases hA : i ≤ m
  · obtain ⟨k, hk⟩ : ∃ k, m - i = k := ⟨_, rfl⟩
    have hk' : m - (i - 1) = k + 1 := by omega
    have hx : (0 : ℝ) < 4 ^ k := by positivity
    rw [rho_sq_of_le ht hA, hk]
    unfold escPhaseA es56B at *
    rw [ite_eq_left (by omega)] at h1
    rw [ite_eq_left (by omega)] at h2
    rw [ite_eq_left hA, ite_eq_left hA, hk]
    rw [hk', pow_succ] at h1 h2
    have e1 : t / (2 * (4 ^ k * 4)) = t / 4 ^ k / 8 := by field_simp; ring
    have e2 : 3 / 5 * t / (4 ^ k * 4) = 3 * (t / 4 ^ k) / 20 := by field_simp; ring
    have e3 : 3 / 5 * t / 4 ^ k = 3 * (t / 4 ^ k) / 5 := by field_simp
    have e4 : t / (2 * 4 ^ k) = t / 4 ^ k / 2 := by field_simp
    rw [e1] at h1; rw [e2] at h2; rw [e3, e4]
    have : 0 < t / 4 ^ k := by positivity
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · push Not at hA
    by_cases hB : i = m + 1
    · subst hB
      have hx := rho_sq_of_gt ht (Nat.lt_succ_self m)
      rw [hx, show m.succ - m = 1 by omega]
      unfold escPhaseA es56B at *
      simp only [Nat.add_sub_cancel, le_refl, ite_true, Nat.sub_self, pow_zero] at h1 h2 ⊢
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [Nat.add_sub_cancel_left, pow_one]
      refine ⟨?_, ?_, ?_⟩ <;> norm_num <;> linarith
    · obtain ⟨k, hk⟩ : ∃ k, i - m = k + 2 := ⟨i - m - 2, by omega⟩
      have hk' : i - 1 - m = k + 1 := by omega
      have hx : (0 : ℝ) < 4 ^ k := by positivity
      rw [rho_sq_of_gt ht hA, hk]
      unfold escPhaseA es56B at *
      rw [ite_eq_right (by omega)] at h1 h2
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [hk', pow_succ] at h1 h2
      rw [hk, pow_succ, pow_succ]
      have e1 : t / (2 * (4 ^ k * 4)) = t / 4 ^ k / 8 := by field_simp; ring
      have e2 : 3 / 10 * t / (4 ^ k * 4) = 3 * (t / 4 ^ k) / 40 := by field_simp; ring
      have e3 : 3 / 10 * t / (4 ^ k * 4 * 4) = 3 * (t / 4 ^ k) / 160 := by field_simp; ring
      have e4 : t / (2 * (4 ^ k * 4 * 4)) = t / 4 ^ k / 32 := by field_simp; ring
      have e5 : t / (4 ^ k * 4 * 4) = t / 4 ^ k / 16 := by field_simp; norm_num
      rw [e1] at h1; rw [e2] at h2; rw [e3, e4, e5]
      have : 0 < t / 4 ^ k := by positivity
      refine ⟨?_, ?_, ?_⟩ <;> norm_num <;> linarith

/-- Geometry of the curve (d), Lipschitz: on `[a_{i-1}, b_i]` the curve is `1/ρ`-Lipschitz for every
`0 < ρ ≤ ρ_i`.  Here `h2 = 2^j / 2 ≥ ‖q - v‖, ‖q - w‖` and `h2² ≤ t`. -/
theorem curve_lipschitz {t h2 ρ : ℝ} (ht : 0 < t) (hh2 : 0 ≤ h2) (hh2t : h2 ^ 2 ≤ t) {m i : ℕ}
    (hi1 : 1 ≤ i) (hρ : 0 < ρ) (hρi : ρ ≤ es56Rho t m i) {v w q : Fin (k + 2) → ℝ}
    (hqv : ‖q - v‖ ≤ h2) (hqw : ‖q - w‖ ≤ h2) {s s' : ℝ}
    (hs : s ∈ Set.Icc (escPhaseA t m (i - 1)) (es56B t m i))
    (hs' : s' ∈ Set.Icc (escPhaseA t m (i - 1)) (es56B t m i)) :
    ‖es56F t v w q s - es56F t v w q s'‖ ≤ 1 / ρ * |s - s'| := by
  have hρ2 : ρ ^ 2 ≤ es56Rho t m i ^ 2 := pow_le_pow_left₀ hρ.le hρi 2
  refine es56_lip ht hρ hh2 hh2t ?_ ?_ hqv hqw hs hs'
  · intro ha
    by_cases hA : i ≤ m
    · rw [rho_sq_of_le ht hA] at hρ2
      obtain ⟨n, hn⟩ : ∃ n, m - i = n := ⟨_, rfl⟩
      have hm : m - (i - 1) = n + 1 := by omega
      unfold escPhaseA
      rw [ite_eq_left (by omega), hm, pow_succ (4 : ℝ) n]
      rw [hn] at hρ2
      have hx : (0 : ℝ) < 4 ^ n := by positivity
      have e : t / (2 * (4 ^ n * 4)) = t / 4 ^ n / 8 := by field_simp; ring
      have : 0 < t / 4 ^ n := by positivity
      rw [e]
      linarith
    · push Not at hA
      by_cases hB : i = m + 1
      · subst hB
        rw [rho_sq_of_gt ht hA] at hρ2
        unfold escPhaseA
        simp only [Nat.add_sub_cancel, le_refl, ite_true, Nat.sub_self, pow_zero]
        rw [show m + 1 - m = 1 by omega] at hρ2
        norm_num
        norm_num at hρ2
        linarith
      · exfalso
        unfold escPhaseA at ha
        rw [ite_eq_right (by omega)] at ha
        have : (1 : ℝ) ≤ 4 ^ (i - 1 - m) := one_le_pow₀ (by norm_num)
        have h4 : (4 : ℝ) ≤ 4 * 4 ^ (i - 1 - m) := by linarith
        have : t / (2 * 4 ^ (i - 1 - m)) ≤ t / 2 := by
          apply div_le_div_of_nonneg_left ht.le (by norm_num); linarith
        have hne : i - 1 - m ≠ 0 := by omega
        have h5 : (4 : ℝ) ≤ 4 ^ (i - 1 - m) := by
          calc (4 : ℝ) = 4 ^ 1 := by norm_num
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
        have : t / (2 * 4 ^ (i - 1 - m)) ≤ t / 8 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
        linarith
  · intro hb
    have hb' := hs.2
    unfold es56B at hb hb'
    by_cases hA : i ≤ m
    · rw [ite_eq_left hA] at hb
      rw [rho_sq_of_le ht hA] at hρ2
      have hx : (1 : ℝ) ≤ 4 ^ (m - i) := one_le_pow₀ (by norm_num)
      have : 3 / 5 * t / 4 ^ (m - i) ≤ 3 / 5 * t := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have : t / 4 ^ (m - i) / 1024 ≤ t / 1024 := by
        rw [div_le_div_iff_of_pos_right (by norm_num), div_le_iff₀ (by positivity)]; nlinarith
      have hub : es56B t m i = 3 / 5 * t / 4 ^ (m - i) := by unfold es56B; rw [ite_eq_left hA]
      linarith [hub]
    · push Not at hA
      rw [ite_eq_right (not_le.2 hA)] at hb
      rw [rho_sq_of_gt ht hA] at hρ2
      have hx : (0 : ℝ) < 4 ^ (i - m) := by positivity
      have e : t - (t - 3 / 10 * t / 4 ^ (i - m)) = 3 / 10 * (t / 4 ^ (i - m)) := by ring
      have : 0 < t / 4 ^ (i - m) := by positivity
      have hub : es56B t m i = t - 3 / 10 * t / 4 ^ (i - m) := by
        unfold es56B; rw [ite_eq_right (not_le.2 hA)]
      have e2 : 3 / 10 * t / 4 ^ (i - m) = 3 / 10 * (t / 4 ^ (i - m)) := by ring
      linarith

end ElboimSly.Paper
