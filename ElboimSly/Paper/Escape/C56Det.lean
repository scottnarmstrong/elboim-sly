/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Stop
public import ElboimSly.Paper.Escape.C56Rel2
public import ElboimSly.Paper.Escape.GeomWindow
public import ElboimSly.Paper.Avoid.CoreHit
public import Mathlib

/-!
# ES22 Claim 5.6, phase `i`: the deterministic step

ES22 Claim 5.6, "Phase `i ∈ [1, 2m]`", from "On `G_{i-1} ∩ E^a ∩ E^b ∩ E^d`, `thit(T) ≥ b_i`"
to "`ℬ_i` holds".  Everything here is pathwise.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

theorem window_gap {t : ℝ} (ht : 0 < t) {m i : ℕ} (hi1 : 1 ≤ i) :
    1 / 10 * (es56B t m i - escPhaseA t m (i - 1)) < es56B t m i - escPhaseA t m i := by
  unfold escPhaseA es56B
  by_cases hA : i ≤ m
  · obtain ⟨kk, hk⟩ : ∃ kk, m - i = kk := ⟨_, rfl⟩
    have hk' : m - (i - 1) = kk + 1 := by omega
    rw [ite_eq_left hA, ite_eq_left hA, ite_eq_left (by omega), hk, hk', pow_succ]
    have hx : (0 : ℝ) < 4 ^ kk := by positivity
    have e1 : t / (2 * (4 ^ kk * 4)) = t / 4 ^ kk / 8 := by field_simp; ring
    have e2 : 3 / 5 * t / 4 ^ kk = 3 * (t / 4 ^ kk) / 5 := by field_simp
    have e3 : t / (2 * 4 ^ kk) = t / 4 ^ kk / 2 := by field_simp
    rw [e1, e2, e3]
    have : 0 < t / 4 ^ kk := by positivity
    linarith
  · push Not at hA
    by_cases hB : i = m + 1
    · subst hB
      simp
      linarith
    · obtain ⟨kk, hk⟩ : ∃ kk, i - m = kk + 2 := ⟨i - m - 2, by omega⟩
      have hk' : i - 1 - m = kk + 1 := by omega
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), hk, hk', pow_succ, pow_succ]
      have hx : (0 : ℝ) < 4 ^ kk := by positivity
      have : 0 < t / 4 ^ kk := by positivity
      have e1 : t / (2 * (4 ^ kk * 4)) = t / 4 ^ kk / 8 := by field_simp; ring
      have e2 : 3 / 10 * t / (4 ^ kk * 4 * 4) = 3 * (t / 4 ^ kk) / 160 := by field_simp; ring
      have e3 : t / (2 * (4 ^ kk * 4 * 4)) = t / 4 ^ kk / 32 := by field_simp; ring
      rw [e1, e2, e3]
      linarith

theorem es56B_le_t {t : ℝ} (ht : 0 ≤ t) (m i : ℕ) : es56B t m i ≤ t := by
  unfold es56B
  split_ifs
  · have : (1 : ℝ) ≤ 4 ^ (m - i) := one_le_pow₀ (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have : 0 ≤ 3 / 10 * t / 4 ^ (i - m) := by positivity
    linarith

theorem norm_escCast {d : ℕ} (x : Fin d → ℤ) : ‖(fun c => (x c : ℝ))‖ = ‖x‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    simpa [Int.norm_eq_abs] using norm_le_pi_norm x i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have := norm_le_pi_norm (fun i => ((x i : ℤ) : ℝ)) i
    simpa [Int.norm_eq_abs] using this

theorem c56_norm_escCast_sub (x y : Fin (k + 2) → ℤ) : ‖escCast x - escCast y‖ = ‖x - y‖ := by
  have : escCast x - escCast y = fun c => ((x - y) c : ℝ) := by
    ext c; simp [escCast]
  rw [this]
  exact norm_escCast (x - y)

end ElboimSly.Paper.Escape

end
