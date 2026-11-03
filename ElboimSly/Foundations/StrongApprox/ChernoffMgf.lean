/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.ChernoffAux
public import Mathlib

/-!
# Moment generating function of a centred clock

Chernoff bound for the clocks, Step 2 (Part II).

If `τ ≥ 0`, `E τ = 1` and `E exp(τ/(36M²)) ≤ 8`, then `E exp(u(τ-1)) ≤ exp(11500 u² M⁴)` for
`|u| ≤ 1/(72M²)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ElboimSly.StrongApprox

lemma exp_two_gt : (7.389 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]; nlinarith

lemma sq_le_exp {v : ℝ} (hv : 0 ≤ v) : v ^ 2 ≤ 4 / Real.exp 2 * Real.exp v := by
  have h1 : Real.exp 1 * (v / 2) ≤ Real.exp (v / 2) := by
    have := Real.add_one_le_exp (v / 2 - 1)
    have e : Real.exp (v / 2) = Real.exp 1 * Real.exp (v / 2 - 1) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le
  have h2 : (Real.exp 1 * (v / 2)) ^ 2 ≤ Real.exp (v / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have e2 : Real.exp (v / 2) ^ 2 = Real.exp v := by
    rw [← Real.exp_nat_mul]; ring_nf
  have e3 : Real.exp 1 ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e2, mul_pow, e3] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos 2)]
  nlinarith

/-- The pointwise bound `ξ² e^{|uξ|} ≤ 2848 M⁴ e^{τ/(36M²)}`, `ξ = τ - 1`. -/
lemma pointwise_quad {M u τ : ℝ} (hM : 1 ≤ M) (hu : |u| ≤ 1 / (72 * M ^ 2)) (hτ : 0 ≤ τ) :
    (τ - 1) ^ 2 * Real.exp |u * (τ - 1)| ≤ 2848 * M ^ 4 * Real.exp (τ / (36 * M ^ 2)) := by
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hM4 : 1 ≤ M ^ 4 := one_le_pow₀ hM
  have hMpos : 0 < M ^ 2 := by positivity
  set v : ℝ := τ / (72 * M ^ 2) with hv
  have hv0 : 0 ≤ v := by positivity
  have h72 : |u| ≤ 1 / 72 := hu.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  -- `|uξ| ≤ v + 1/72`
  have hxi : |u * (τ - 1)| ≤ v + 1 / 72 := by
    rw [abs_mul]
    have : |τ - 1| ≤ τ + 1 := by
      rw [abs_le]; constructor <;> linarith
    calc |u| * |τ - 1| ≤ |u| * (τ + 1) := by gcongr
      _ = |u| * τ + |u| := by ring
      _ ≤ 1 / (72 * M ^ 2) * τ + 1 / 72 := by gcongr
      _ = v + 1 / 72 := by rw [hv]; field_simp
  have hE1 : Real.exp |u * (τ - 1)| ≤ Real.exp (v + 1 / 72) := Real.exp_le_exp.2 hxi
  -- `τ² ≤ 2807 M⁴ e^v`
  have hτ2 : τ ^ 2 ≤ 2807 * M ^ 4 * Real.exp v := by
    have hτv : τ = 72 * M ^ 2 * v := by rw [hv]; field_simp
    have h1 := sq_le_exp hv0
    have h2 : 4 / Real.exp 2 ≤ 4 / 7.389 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) exp_two_gt.le
    calc τ ^ 2 = (72 * M ^ 2) ^ 2 * v ^ 2 := by rw [hτv]; ring
      _ ≤ (72 * M ^ 2) ^ 2 * (4 / Real.exp 2 * Real.exp v) := by gcongr
      _ ≤ (72 * M ^ 2) ^ 2 * (4 / 7.389 * Real.exp v) := by gcongr
      _ = (72 ^ 2 * 4 / 7.389) * M ^ 4 * Real.exp v := by ring
      _ ≤ 2807 * M ^ 4 * Real.exp v := by
        gcongr
        norm_num
  have hxi2 : (τ - 1) ^ 2 ≤ τ ^ 2 + 1 := by nlinarith
  have hev : 1 ≤ M ^ 4 * Real.exp v := by
    have := Real.one_le_exp hv0
    nlinarith
  have hsum : τ ^ 2 + 1 ≤ 2808 * M ^ 4 * Real.exp v := by nlinarith
  have he72 : Real.exp (1 / 72) ≤ 72 / 71 := by
    have := Real.add_one_le_exp (-(1 / 72 : ℝ))
    have h2 : Real.exp (-(1 / 72 : ℝ)) = (Real.exp (1 / 72))⁻¹ := Real.exp_neg _
    rw [h2] at this
    have hp := Real.exp_pos (1 / 72 : ℝ)
    rw [← sub_nonneg] at this ⊢
    have : (71 / 72 : ℝ) ≤ (Real.exp (1 / 72))⁻¹ := by linarith
    rw [le_inv_comm₀ (by norm_num) hp] at this
    linarith
  have e2v : Real.exp (v + 1 / 72) = Real.exp v * Real.exp (1 / 72) := Real.exp_add _ _
  have eτ : Real.exp (τ / (36 * M ^ 2)) = Real.exp v * Real.exp v := by
    rw [← Real.exp_add]; congr 1; rw [hv]; field_simp; ring
  calc (τ - 1) ^ 2 * Real.exp |u * (τ - 1)|
      ≤ (2808 * M ^ 4 * Real.exp v) * (Real.exp v * Real.exp (1 / 72)) := by
        rw [← e2v]
        exact mul_le_mul (hxi2.trans hsum) hE1 (Real.exp_pos _).le (by positivity)
    _ ≤ (2808 * M ^ 4 * Real.exp v) * (Real.exp v * (72 / 71)) := by gcongr
    _ = (2808 * 72 / 71) * M ^ 4 * (Real.exp v * Real.exp v) := by ring
    _ ≤ 2848 * M ^ 4 * (Real.exp v * Real.exp v) := by gcongr; norm_num
    _ = 2848 * M ^ 4 * Real.exp (τ / (36 * M ^ 2)) := by rw [eτ]

section Integrated

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma integrable_exp_clock {M : ℝ} {τ : Ω → ℝ} (hm : Measurable τ)
    (hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (τ ω / (36 * M ^ 2))) ∂P ≤ 8) :
    Integrable (fun ω => Real.exp (τ ω / (36 * M ^ 2))) P := by
  refine ⟨(Real.measurable_exp.comp (hm.div_const _)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  exact lt_of_le_of_lt hexp (by norm_num)

omit [IsProbabilityMeasure P] in
lemma integral_exp_clock_le {M : ℝ} {τ : Ω → ℝ} (hm : Measurable τ)
    (hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (τ ω / (36 * M ^ 2))) ∂P ≤ 8) :
    ∫ ω, Real.exp (τ ω / (36 * M ^ 2)) ∂P ≤ 8 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
    (Real.measurable_exp.comp (hm.div_const _)).aestronglyMeasurable]
  have := ENNReal.toReal_mono (by norm_num : (8 : ℝ≥0∞) ≠ ⊤) hexp
  simpa using this

/-- Chernoff bound for the clocks, Step 2. -/
lemma mgf_clock_le {M : ℝ} (hM : 1 ≤ M) {τ : Ω → ℝ} (hm : Measurable τ) (hnn : ∀ ω, 0 ≤ τ ω)
    (hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (τ ω / (36 * M ^ 2))) ∂P ≤ 8)
    (hmean : ∫ ω, τ ω ∂P = 1) {u : ℝ} (hu : |u| ≤ 1 / (72 * M ^ 2)) :
    Integrable (fun ω => Real.exp (u * (τ ω - 1))) P ∧
      mgf (fun ω => τ ω - 1) P u ≤ Real.exp (11500 * u ^ 2 * M ^ 4) := by
  have hM2 : 0 < M ^ 2 := by positivity
  set E : Ω → ℝ := fun ω => Real.exp (τ ω / (36 * M ^ 2)) with hE
  have hEint : Integrable E P := integrable_exp_clock hm hexp
  have hEle : ∫ ω, E ω ∂P ≤ 8 := integral_exp_clock_le hm hexp
  have hτint : Integrable τ P := by
    refine Integrable.mono' (hEint.const_mul (36 * M ^ 2)) hm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]
    have := Real.add_one_le_exp (τ ω / (36 * M ^ 2))
    have h2 : τ ω / (36 * M ^ 2) ≤ E ω := by simp only [hE]; linarith
    rw [div_le_iff₀ (by positivity)] at h2
    simp only [hE] at *
    nlinarith
  set R : Ω → ℝ := fun ω => 1 + u * (τ ω - 1) + u ^ 2 / 2 * (2848 * M ^ 4 * E ω) with hR
  have hRint : Integrable R P := by
    refine ((integrable_const _).add ((hτint.sub (integrable_const _)).const_mul u)).add
      (hEint.const_mul (2848 * M ^ 4) |>.const_mul (u ^ 2 / 2))
  have hpt : ∀ ω, Real.exp (u * (τ ω - 1)) ≤ R ω := by
    intro ω
    have h1 := exp_le_quad (u * (τ ω - 1))
    have h2 := pointwise_quad hM hu (hnn ω)
    have h3 : (u * (τ ω - 1)) ^ 2 / 2 * Real.exp |u * (τ ω - 1)| ≤
        u ^ 2 / 2 * (2848 * M ^ 4 * E ω) := by
      have : (u * (τ ω - 1)) ^ 2 / 2 * Real.exp |u * (τ ω - 1)| =
          u ^ 2 / 2 * ((τ ω - 1) ^ 2 * Real.exp |u * (τ ω - 1)|) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    simp only [hR]
    linarith
  have hmeasexp : Measurable fun ω => Real.exp (u * (τ ω - 1)) :=
    Real.measurable_exp.comp ((hm.sub_const 1).const_mul u)
  have hint : Integrable (fun ω => Real.exp (u * (τ ω - 1))) P := by
    refine Integrable.mono' hRint hmeasexp.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  have hint_le : ∫ ω, Real.exp (u * (τ ω - 1)) ∂P ≤ ∫ ω, R ω ∂P :=
    integral_mono hint hRint hpt
  have i3 : Integrable (fun ω => u * (τ ω - 1)) P :=
    (hτint.sub (integrable_const _)).const_mul u
  have i1 : Integrable (fun ω => 1 + u * (τ ω - 1)) P := (integrable_const _).add i3
  have i2 : Integrable (fun ω => u ^ 2 / 2 * (2848 * M ^ 4 * E ω)) P :=
    (hEint.const_mul (2848 * M ^ 4)).const_mul (u ^ 2 / 2)
  have i4 : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const _
  have hRval : ∫ ω, R ω ∂P = 1 + u * (1 - 1) + u ^ 2 / 2 * (2848 * M ^ 4 * ∫ ω, E ω ∂P) := by
    simp only [hR]
    rw [integral_add i1 i2, integral_add i4 i3, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_sub hτint (integrable_const _), hmean]
    simp
  have hbound : ∫ ω, R ω ∂P ≤ 1 + 11500 * u ^ 2 * M ^ 4 := by
    rw [hRval]
    have : u ^ 2 / 2 * (2848 * M ^ 4 * ∫ ω, E ω ∂P) ≤ u ^ 2 / 2 * (2848 * M ^ 4 * 8) := by
      gcongr
    nlinarith [sq_nonneg u, pow_nonneg (by positivity : (0 : ℝ) ≤ M) 4,
      mul_nonneg (sq_nonneg u) (pow_nonneg (by positivity : (0 : ℝ) ≤ M) 4)]
  calc mgf (fun ω => τ ω - 1) P u = ∫ ω, Real.exp (u * (τ ω - 1)) ∂P := rfl
    _ ≤ 1 + 11500 * u ^ 2 * M ^ 4 := hint_le.trans hbound
    _ ≤ Real.exp (11500 * u ^ 2 * M ^ 4) := by
      have := Real.add_one_le_exp (11500 * u ^ 2 * M ^ 4); linarith

end Integrated

end ElboimSly.StrongApprox
