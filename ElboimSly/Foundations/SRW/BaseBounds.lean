/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Maximal
public import ElboimSly.Foundations.SRW.FarWindows
public import Mathlib

/-!
# (8.1), (H3) and (8.2) at the base

(8.1) and (H3) at the base; (8.2) at the base.  Here `t_n = 4^n t_0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

theorem sq_le_two_pow (n : ℕ) : n ^ 2 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with h | h
    · interval_cases k <;> norm_num
    · calc (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ (k + 2) := by omega
        _ = 2 ^ (k + 1 + 2) := by ring

/-- (8.1) and (H3) at the base, first claim. -/
theorem IsSRW.base_far [NeZero d] (hZ : IsSRW P Z) {n : ℕ} (hn : 1 ≤ n) {t0 : ℝ≥0}
    (h1 : 1 < t0) :
    P.real {ω | ∃ s, s ≤ 4 ^ n * t0 ∧ (n : ℝ) ^ 2 * √((4 ^ n * t0 : ℝ≥0) : ℝ) ≤ ‖Z ω s‖} ≤
      4 * d * Real.exp (-((n : ℝ) ^ 4 / 8)) := by
  have hT : (0 : ℝ≥0) < 4 ^ n * t0 := by positivity
  have hTr : (0 : ℝ) < ((4 ^ n * t0 : ℝ≥0) : ℝ) := hT
  have ht0 : (1 : ℝ) < t0 := by exact_mod_cast h1
  have hsq : (n : ℝ) ^ 2 ≤ 4 * √((4 ^ n * t0 : ℝ≥0) : ℝ) := by
    have hle : ((n : ℝ) ^ 2 / 4) ^ 2 ≤ ((4 ^ n * t0 : ℝ≥0) : ℝ) := by
      push_cast
      have h2 : (n : ℝ) ^ 2 ≤ 2 ^ (n + 2) := by exact_mod_cast sq_le_two_pow n
      have h4 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h3 : (n : ℝ) ^ 2 / 4 ≤ 2 ^ n := by rw [pow_add] at h2; nlinarith
      calc ((n : ℝ) ^ 2 / 4) ^ 2 ≤ (2 ^ n) ^ 2 := by gcongr
        _ = 4 ^ n := h4.symm
        _ ≤ 4 ^ n * t0 := le_mul_of_one_le_right (by positivity) ht0.le
    have := Real.le_sqrt_of_sq_le hle
    linarith
  have := hZ.maximal_gauss hT (lam := (n : ℝ) ^ 2) (by positivity) hsq
  refine this.trans (le_of_eq ?_)
  congr 3
  ring

/-- (8.1) and (H3) at the base: the tail bound `e^{-n^3}`. -/
theorem IsSRW.base_far_tail [NeZero d] (hZ : IsSRW P Z) {n : ℕ} (h16 : 16 ≤ n) {t0 : ℝ≥0}
    (h1 : 1 < t0) (hd : Real.log (4 * d) ≤ n) :
    P.real {ω | ∃ s, s ≤ 4 ^ n * t0 ∧ (n : ℝ) ^ 2 * √((4 ^ n * t0 : ℝ≥0) : ℝ) ≤ ‖Z ω s‖} ≤
      Real.exp (-((n : ℝ) ^ 3)) := by
  have hn : 1 ≤ n := by omega
  have hd0 : (0 : ℝ) < 4 * d := by
    have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  refine (hZ.base_far hn h1).trans ?_
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast h16
  have h3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    have a2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left a2 (by linarith : (0 : ℝ) ≤ n)]
  have : 4 * (d : ℝ) ≤ Real.exp ((n : ℝ) ^ 3) := by
    calc 4 * (d : ℝ) = Real.exp (Real.log (4 * d)) := (Real.exp_log hd0).symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  calc 4 * (d : ℝ) * Real.exp (-((n : ℝ) ^ 4 / 8))
      ≤ Real.exp ((n : ℝ) ^ 3) * Real.exp (-((n : ℝ) ^ 4 / 8)) := by gcongr
    _ ≤ Real.exp (-((n : ℝ) ^ 3)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have : 0 ≤ (n : ℝ) ^ 3 := by positivity
        nlinarith [mul_nonneg this (sub_nonneg.2 hn16)]

/-- (8.2) at the base. -/
theorem IsSRW.base_fast (hZ : IsSRW P Z) {n : ℕ} (hd : 1 ≤ d) (hn : 2 * d ≤ n) {t0 : ℝ≥0}
    (_h1 : 1 < t0) (h4 : t0 ≤ 4) :
    P.real {ω | ∃ s s', s ≤ s' ∧ s' ≤ 4 ^ n * t0 ∧ s' - s ≤ 1 ∧
        (n : ℝ) ^ 5 < l1 (Z ω s' - Z ω s)} ≤ Real.exp (-((n : ℝ) ^ 4)) := by
  have hsub : {ω | ∃ s s', s ≤ s' ∧ s' ≤ 4 ^ n * t0 ∧ s' - s ≤ 1 ∧
        (n : ℝ) ^ 5 < l1 (Z ω s' - Z ω s)} ⊆
      {ω | ∃ s s', s ≤ s' ∧ s' ≤ 4 ^ n * t0 ∧ s' - s ≤ 1 ∧
        (n : ℝ) ^ 5 ≤ l1 (Z ω s' - Z ω s)} := by
    rintro ω ⟨s, s', a, b, c, e⟩; exact ⟨s, s', a, b, c, e.le⟩
  have := hZ.isProbabilityMeasure
  have hw := hZ.unit_windows (4 ^ n * t0) 1 one_pos ((n : ℝ) ^ 5)
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (hw.trans ?_)
  have hn2 : (2 : ℝ) ≤ n := by
    have : 2 ≤ n := by omega
    exact_mod_cast this
  have hdn : (d : ℝ) ≤ n / 2 := by
    have : (2 * d : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hT : ((4 ^ n * t0 : ℝ≥0) : ℝ) ≤ 4 ^ (n + 1) := by
    push_cast
    have : (t0 : ℝ) ≤ 4 := by exact_mod_cast h4
    rw [pow_succ]; nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) n]
  have h4e : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.exp_one_gt_d9
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have h4n : (4 : ℝ) ^ (n + 1) ≤ Real.exp (2 * (n + 1)) := by
    calc (4 : ℝ) ^ (n + 1) ≤ (Real.exp 2) ^ (n + 1) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hTp : ((4 ^ n * t0 : ℝ≥0) : ℝ) + 1 ≤ Real.exp (2 * n + 3) := by
    have hp : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
    calc ((4 ^ n * t0 : ℝ≥0) : ℝ) + 1 ≤ 2 * 4 ^ (n + 1) := by linarith
      _ ≤ Real.exp 1 * Real.exp (2 * (n + 1)) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he := exp_one_sub_one_le
  simp only [NNReal.coe_one, div_one]
  have hexp : Real.exp (4 * d * (1 : ℝ) * (Real.exp 1 - 1) - (n : ℝ) ^ 5) ≤
      Real.exp (-((n : ℝ) ^ 4) - (2 * n + 3)) := by
    apply Real.exp_le_exp.2
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have a2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have a3 : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith
    have h5 : (n : ℝ) ^ 4 ≥ 8 * n := by nlinarith
    have h6 : (n : ℝ) ^ 5 ≥ 2 * (n : ℝ) ^ 4 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ n) 4]
    nlinarith
  calc (((4 ^ n * t0 : ℝ≥0) : ℝ) + 1) * Real.exp (4 * d * (1 : ℝ) * (Real.exp 1 - 1) - (n : ℝ) ^ 5)
      ≤ Real.exp (2 * n + 3) * Real.exp (-((n : ℝ) ^ 4) - (2 * n + 3)) := by
        gcongr
    _ = Real.exp (-((n : ℝ) ^ 4)) := by rw [← Real.exp_add]; congr 1; ring

end SRW
end ElboimSly
