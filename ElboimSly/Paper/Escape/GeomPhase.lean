/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Phases
public import Mathlib

/-!
# Geometry of the curve: the two regimes of a phase

Geometry of the curve (b), (c), preparatory step.  For `1 ≤ i ≤ 2m` and
`s ∈ [a_{i-1}, b_i]` either `s ≤ t/2`, `i ≤ m` and `λ(s) = √(2s/t) ≥ 2^{-n}` with
`R_i ≤ √t / (16 · 2^n)`, or `s ≥ t/2` and `μ(s) = √(2(t-s)/t) ≥ 0.77 · 2^{-n}` with
`R_i ≤ √t / (64 · 2^n)`.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.Brownian

lemma escKappa_le_one (m i : ℕ) : escKappa m i ≤ 1 := by
  unfold escKappa; split_ifs <;> norm_num

lemma escKappa_nonneg (m i : ℕ) : 0 ≤ escKappa m i := by
  unfold escKappa; split_ifs <;> norm_num

lemma sqrt_two_mul_ge {t s c : ℝ} (ht : 0 < t) (_hc : 0 ≤ c) (h : c ^ 2 * t ≤ 2 * s) :
    c ≤ Real.sqrt (2 * s / t) := by
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ ht]; exact h

lemma phase_cases {t : ℝ} (ht : 0 < t) {m i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ 2 * m) {s : ℝ}
    (hs1 : escPhaseA t m (i - 1) ≤ s) (hs2 : s ≤ es56B t m i) :
    (∃ n : ℕ, 1 ≤ n ∧ n + i = m + 1 ∧ s ≤ t / 2 ∧ 1 / 2 ^ n ≤ Real.sqrt (2 * s / t) ∧
        Real.sqrt (2 * s / t) ≤ (22 / 10) / 2 ^ n ∧ escR t m i ≤ Real.sqrt t / (16 * 2 ^ n)) ∨
    (∃ n : ℕ, n + m = i ∧ t / 2 ≤ s ∧ (77 / 100) / 2 ^ n ≤ Real.sqrt (2 * (t - s) / t) ∧
        Real.sqrt (2 * (t - s) / t) ≤ 2 / 2 ^ n ∧ escR t m i ≤ Real.sqrt t / (64 * 2 ^ n)) := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hκ1 := escKappa_le_one m i
  have hκ0 := escKappa_nonneg m i
  by_cases hi : i ≤ m
  · have hA : escPhaseA t m (i - 1) = t / (2 * 4 ^ (m - i + 1)) := by
      unfold escPhaseA; rw [ite_eq_left (by omega)]
      have : m - (i - 1) = m - i + 1 := by omega
      rw [this]
    rw [hA] at hs1
    have hρ : es56Rho t m i = Real.sqrt t / 2 ^ (m - i + 4 + 1) := by
      unfold es56Rho; rw [ite_eq_left hi]
    by_cases hs : s ≤ t / 2
    · left
      refine ⟨m - i + 1, by omega, by omega, hs, ?_, ?_, ?_⟩
      · apply sqrt_two_mul_ge ht (by positivity)
        have h4 : (4 : ℝ) ^ (m - i + 1) = (2 ^ (m - i + 1)) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have h5 : t / (2 * 4 ^ (m - i + 1)) * (2 * 4 ^ (m - i + 1)) = t := by
          field_simp
        have h6 : 0 < (4 : ℝ) ^ (m - i + 1) := by positivity
        have : t ≤ 2 * s * 4 ^ (m - i + 1) := by
          calc t = t / (2 * 4 ^ (m - i + 1)) * (2 * 4 ^ (m - i + 1)) := h5.symm
            _ ≤ s * (2 * 4 ^ (m - i + 1)) := by
              exact mul_le_mul_of_nonneg_right hs1 (by positivity)
            _ = 2 * s * 4 ^ (m - i + 1) := by ring
        rw [div_pow, one_pow, ← h4]
        rw [div_mul_eq_mul_div, div_le_iff₀ h6]
        nlinarith
      · have hb : es56B t m i = 3 / 5 * t / 4 ^ (m - i) := by unfold es56B; rw [ite_eq_left hi]
        have hs2' := hs2
        rw [hb] at hs2'
        have h6 : 0 < (4 : ℝ) ^ (m - i) := by positivity
        have h7 : s * 4 ^ (m - i) ≤ 3 / 5 * t := by rwa [le_div_iff₀ h6] at hs2'
        have h4 : (4 : ℝ) ^ (m - i + 1) = (2 ^ (m - i + 1)) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
        rw [div_pow, div_le_div_iff₀ ht (by positivity), ← h4, pow_succ]
        nlinarith
      · unfold escR
        rw [hρ]
        have : escKappa m i * (Real.sqrt t / 2 ^ (m - i + 4 + 1)) ≤ Real.sqrt t / 2 ^ (m - i + 4 + 1) :=
          mul_le_of_le_one_left (by positivity) hκ1
        refine this.trans (le_of_eq ?_)
        rw [pow_succ, pow_add]; field_simp; ring
    · right
      push Not at hs
      have hb : es56B t m i = 3 / 5 * t / 4 ^ (m - i) := by unfold es56B; rw [ite_eq_left hi]
      rw [hb] at hs2
      have him' : m - i = 0 := by
        by_contra hne
        have h4 : (4 : ℝ) ≤ 4 ^ (m - i) := by
          calc (4 : ℝ) = 4 ^ 1 := by norm_num
            _ ≤ 4 ^ (m - i) := pow_le_pow_right₀ (by norm_num) (by omega)
        have : 3 / 5 * t / 4 ^ (m - i) ≤ 3 / 5 * t / 4 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) h4
        linarith
      have hmi : i = m := by omega
      subst hmi
      rw [him'] at hs2
      simp at hs2
      refine ⟨0, by omega, hs.le, ?_, ?_, ?_⟩
      · apply sqrt_two_mul_ge ht (by positivity)
        simp; nlinarith
      · refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
        rw [div_le_iff₀ ht]; norm_num; nlinarith
      · unfold escR escKappa es56Rho
        rw [ite_eq_left le_rfl, ite_eq_left le_rfl]
        norm_num
        linarith
  · right
    push Not at hi
    set n := i - m with hn
    have hb : es56B t m i = t - 3 / 10 * t / 4 ^ n := by
      unfold es56B; rw [ite_eq_right (by omega)]
    rw [hb] at hs2
    have hA : t / 2 ≤ escPhaseA t m (i - 1) := by
      unfold escPhaseA
      split_ifs with h
      · have : m - (i - 1) = 0 := by omega
        rw [this]; simp
      · have : (1 : ℝ) ≤ 4 ^ (i - 1 - m) := one_le_pow₀ (by norm_num)
        have : t / (2 * 4 ^ (i - 1 - m)) ≤ t / 2 := by
          apply div_le_div_of_nonneg_left ht.le (by norm_num); nlinarith
        linarith
    have hA2 : t - escPhaseA t m (i - 1) ≤ 2 * t / 4 ^ n := by
      unfold escPhaseA
      split_ifs with h
      · have h0 : m - (i - 1) = 0 := by omega
        have h1 : n = 1 := by omega
        rw [h0, h1]; simp; linarith
      · have h1 : n = (i - 1 - m) + 1 := by omega
        rw [h1, pow_succ]
        apply le_of_eq
        field_simp
        ring
    refine ⟨n, by omega, by linarith, ?_, ?_, ?_⟩
    · apply sqrt_two_mul_ge ht (by positivity)
      have h4 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h6 : 0 < (4 : ℝ) ^ n := by positivity
      have h7 : 3 / 10 * t / 4 ^ n ≤ t - s := by linarith
      have h8 : 3 / 10 * t ≤ (t - s) * 4 ^ n := by
        rwa [div_le_iff₀ h6] at h7
      rw [div_pow, ← h4]
      rw [div_mul_eq_mul_div, div_le_iff₀ h6]
      nlinarith [h8]
    · refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      have h4 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h6 : 0 < (4 : ℝ) ^ n := by positivity
      have h7 : t - s ≤ 2 * t / 4 ^ n := by linarith [hA2]
      have h8 : (t - s) * 4 ^ n ≤ 2 * t := by rwa [le_div_iff₀ h6] at h7
      rw [div_pow, div_le_div_iff₀ ht (by positivity), ← h4]
      nlinarith
    · simp only [escR, escKappa, es56Rho, ite_eq_left (show m ≤ i by omega),
        ite_eq_right (show ¬ i ≤ m by omega)]
      have h8 : (2 : ℝ) ^ (i - m + 3) = 2 ^ n * 8 := by rw [pow_add, ← hn]; norm_num
      rw [h8]
      apply le_of_eq
      field_simp
      norm_num

end ElboimSly.Paper
