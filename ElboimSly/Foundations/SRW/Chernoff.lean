/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Moments
public import Mathlib

/-!
# The Chernoff bound for a one-dimensional SRW

Chernoff bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

theorem cosh_sub_one_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : Real.cosh θ - 1 ≤ θ ^ 2 := by
  have h2 := Real.cosh_le_exp_half_sq θ
  set x := θ ^ 2 / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by rw [hx]; nlinarith
  have h3 : Real.exp x ≤ 1 + 2 * x := by
    have h4 := Real.add_one_le_exp (-x)
    have h5 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have h6 : 0 < Real.exp x := Real.exp_pos x
    have h7 : 0 < Real.exp (-x) := Real.exp_pos _
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem IsSRW.integrable_exp_eval1 {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (t : ℝ≥0) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * (Y ω t 0 : ℝ))) P := by
  have h := hY.integral_exp_inner t (fun _ => θ)
  simp only [Fin.sum_univ_one] at h
  by_contra hni
  rw [integral_undef hni] at h
  exact (Real.exp_pos _).ne h

theorem IsSRW.mgf_eval1 {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (t : ℝ≥0) (θ : ℝ) :
    mgf (fun ω => (Y ω t 0 : ℝ)) P θ = Real.exp (2 * t * (Real.cosh θ - 1)) := by
  have h := hY.integral_exp_inner t (fun _ => θ)
  simp only [Fin.sum_univ_one] at h
  exact h

theorem IsSRW.tail_le_exp {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (T : ℝ≥0) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (a : ℝ) :
    P.real {ω | a ≤ (Y ω T 0 : ℝ)} ≤ Real.exp (-θ * a + 2 * T * θ ^ 2) := by
  have := hY.isProbabilityMeasure
  have := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => (Y ω T 0 : ℝ)) a h0
    (hY.integrable_exp_eval1 T θ)
  rw [hY.mgf_eval1 T θ] at this
  refine this.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have := cosh_sub_one_le h0 h1
  have hT : (0 : ℝ) ≤ T := T.2
  nlinarith

/-- Chernoff bound: one-sided. -/
theorem IsSRW.chernoff {Y : Ω → PathSpace 1} (hY : IsSRW P Y) {T : ℝ≥0} (hT : 0 < T) {a : ℝ}
    (ha : 0 ≤ a) :
    P.real {ω | a ≤ (Y ω T 0 : ℝ)} ≤ Real.exp (-min (a ^ 2 / (8 * T)) (a / 2)) := by
  have hT' : (0 : ℝ) < T := hT
  rcases le_or_gt a (4 * T) with hle | hgt
  · have hθ1 : a / (4 * T) ≤ 1 := by rw [div_le_one (by positivity)]; exact hle
    refine (hY.tail_le_exp T (by positivity) hθ1 a).trans (Real.exp_le_exp.2 ?_)
    have hm : min (a ^ 2 / (8 * T)) (a / 2) = a ^ 2 / (8 * T) := by
      apply min_eq_left
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [hm]
    have : -(a / (4 * T)) * a + 2 * T * (a / (4 * T)) ^ 2 = -(a ^ 2 / (8 * T)) := by
      field_simp; ring
    linarith
  · refine (hY.tail_le_exp T zero_le_one le_rfl a).trans (Real.exp_le_exp.2 ?_)
    have hm : min (a ^ 2 / (8 * T)) (a / 2) = a / 2 := by
      apply min_eq_right
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [hm]
    nlinarith

/-- Chernoff bound: two-sided. -/
theorem IsSRW.chernoff_abs {Y : Ω → PathSpace 1} (hY : IsSRW P Y) {T : ℝ≥0} (hT : 0 < T)
    {a : ℝ} (ha : 0 ≤ a) :
    P.real {ω | a ≤ |(Y ω T 0 : ℝ)|} ≤ 2 * Real.exp (-min (a ^ 2 / (8 * T)) (a / 2)) := by
  have := hY.isProbabilityMeasure
  have hmY := hY.measurable_eval1 T
  have hneg : P {ω | a ≤ -(Y ω T 0 : ℝ)} = P {ω | a ≤ (Y ω T 0 : ℝ)} := by
    have := hY.measure_eval_neg T {k : ℤ | a ≤ (k : ℝ)}
    simpa using this
  have hsub : {ω | a ≤ |(Y ω T 0 : ℝ)|} ⊆
      {ω | a ≤ (Y ω T 0 : ℝ)} ∪ {ω | a ≤ -(Y ω T 0 : ℝ)} := by
    intro ω hω
    simp only [mem_ofPred_eq, le_abs'] at hω
    rcases hω with h | h
    · right; simp only [mem_ofPred_eq]; linarith
    · left; exact h
  have hm1 : MeasurableSet {ω | a ≤ (Y ω T 0 : ℝ)} :=
    (measurableSet_le measurable_const
      ((Measurable.of_discrete (f := fun n : ℤ => (n : ℝ))).comp hmY))
  have h1 := measureReal_mono hsub (measure_ne_top P _)
  have h2 := measureReal_union_le (μ := P) {ω | a ≤ (Y ω T 0 : ℝ)} {ω | a ≤ -(Y ω T 0 : ℝ)}
  have h3 : P.real {ω | a ≤ -(Y ω T 0 : ℝ)} = P.real {ω | a ≤ (Y ω T 0 : ℝ)} := by
    rw [Measure.real, Measure.real, hneg]
  have h4 := hY.chernoff hT ha
  linarith

end SRW
end ElboimSly
