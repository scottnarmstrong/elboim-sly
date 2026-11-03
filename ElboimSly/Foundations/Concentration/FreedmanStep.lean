/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.Exp

/-!
# One step of the exponential supermartingale

One step of the exponential supermartingale.
-/

public section

namespace ElboimSly

open MeasureTheory

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Pointwise bound `e^{λ D} ≤ 1 + λ D + ψ D²` when `λ D ≤ λ b`. -/
lemma exp_le_one_add_of_le {b l d : ℝ} (hb : 0 < b) (hl : 0 < l) (hd : d ≤ b) :
    Real.exp (l * d) ≤ 1 + l * d + concPhi (l * b) / b ^ 2 * d ^ 2 := by
  have h := concPhi_le_mul_concPhi (u := l * d) (w := l * b) (by positivity)
    (mul_le_mul_of_nonneg_left hd hl.le)
  have h2 : (l * d) ^ 2 * concPhi (l * b) / (l * b) ^ 2 = concPhi (l * b) / b ^ 2 * d ^ 2 := by
    field_simp
  simp only [concPhi] at h
  simp only [concPhi] at h2 ⊢
  linarith

/-- One step of the exponential supermartingale. -/
theorem concFreedman_step [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ m0)
    {b l : ℝ} (hb : 0 < b) (hl : 0 < l) {D v G : Ω → ℝ} (hD : Measurable D)
    (hDb : ∀ᵐ ω ∂μ, |D ω| ≤ b) (hD0 : μ[D | 𝒢] =ᵐ[μ] 0)
    (hv : StronglyMeasurable[𝒢] v) (hv0 : ∀ ω, 0 ≤ v ω)
    (hDv : μ[D ^ 2 | 𝒢] ≤ᵐ[μ] v)
    (hG : StronglyMeasurable[𝒢] G) (hG0 : ∀ ω, 0 ≤ G ω) {c : ℝ} (hGc : ∀ᵐ ω ∂μ, G ω ≤ c) :
    ∫ ω, G ω * Real.exp (l * D ω - concPhi (l * b) / b ^ 2 * v ω) ∂μ ≤ ∫ ω, G ω ∂μ := by
  set ψ : ℝ := concPhi (l * b) / b ^ 2 with hψ
  have hψpos : 0 < ψ := by
    have := sq_div_two_le_concPhi (w := l * b) (by positivity)
    have : 0 < concPhi (l * b) := lt_of_lt_of_le (by positivity) this
    positivity
  have hc0 : 0 ≤ c := by
    obtain ⟨ω, hω⟩ := (hGc.exists : ∃ ω, G ω ≤ c)
    exact (hG0 ω).trans hω
  -- the weight `H`
  set H : Ω → ℝ := fun ω => G ω * Real.exp (-(ψ * v ω)) with hH
  have hHm : StronglyMeasurable[𝒢] H :=
    hG.mul (Real.continuous_exp.comp_stronglyMeasurable (hv.const_mul ψ).neg)
  have hH0 : ∀ ω, 0 ≤ H ω := fun ω => mul_nonneg (hG0 ω) (Real.exp_pos _).le
  have hexp1 : ∀ ω, Real.exp (-(ψ * v ω)) ≤ 1 := fun ω => by
    rw [Real.exp_le_one_iff]; have := hv0 ω; nlinarith
  have hHG : ∀ ω, H ω ≤ G ω := fun ω => by
    have := hexp1 ω
    have := hG0 ω
    simp only [hH]; nlinarith
  have hHc : ∀ᵐ ω ∂μ, ‖H ω‖ ≤ c := hGc.mono fun ω h => by
    rw [Real.norm_of_nonneg (hH0 ω)]; exact (hHG ω).trans h
  have hHm0 : Measurable H := hHm.measurable.mono h𝒢 le_rfl
  have hDm : AEStronglyMeasurable D μ := hD.aestronglyMeasurable
  -- integrability
  have hHint : Integrable H μ :=
    Integrable.of_bound (hHm.mono h𝒢).aestronglyMeasurable c hHc
  have hGint : Integrable G μ :=
    Integrable.of_bound (hG.mono h𝒢).aestronglyMeasurable c
      (hGc.mono fun ω h => by rw [Real.norm_of_nonneg (hG0 ω)]; exact h)
  have hHDint : Integrable (fun ω => H ω * D ω) μ := by
    refine Integrable.of_bound ((hHm.mono h𝒢).aestronglyMeasurable.mul hDm) (c * b) ?_
    filter_upwards [hHc, hDb] with ω h1 h2
    rw [norm_mul, Real.norm_eq_abs (D ω)]
    exact mul_le_mul h1 h2 (abs_nonneg _) hc0
  have hD2int : Integrable (D ^ 2) μ := by
    refine Integrable.of_bound (hDm.pow 2) (b ^ 2) ?_
    filter_upwards [hDb] with ω h
    simp only [Pi.pow_apply, norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hHD2int : Integrable (fun ω => H ω * D ω ^ 2) μ := by
    refine Integrable.of_bound ((hHm.mono h𝒢).aestronglyMeasurable.mul hD2int.1) (c * b ^ 2) ?_
    filter_upwards [hHc, hDb] with ω h1 h2
    rw [norm_mul]
    simp only [norm_pow, Real.norm_eq_abs]
    exact mul_le_mul h1 (pow_le_pow_left₀ (abs_nonneg _) h2 2) (by positivity) hc0
  -- `H v` is bounded
  have hHv : ∀ᵐ ω ∂μ, H ω * v ω ≤ c / ψ := hGc.mono fun ω h => by
    have h1 : ψ * v ω * Real.exp (-(ψ * v ω)) ≤ 1 :=
      (mul_exp_neg_le_exp_neg_one _).trans (Real.exp_le_one_iff.2 (by norm_num))
    have h2 : H ω * v ω * ψ = G ω * (ψ * v ω * Real.exp (-(ψ * v ω))) := by
      simp only [hH]; ring
    rw [le_div_iff₀ hψpos, h2]
    calc G ω * (ψ * v ω * Real.exp (-(ψ * v ω))) ≤ G ω * 1 :=
          mul_le_mul_of_nonneg_left h1 (hG0 ω)
      _ ≤ c := by simpa using h
  have hHvint : Integrable (fun ω => H ω * v ω) μ := by
    refine Integrable.of_bound ((hHm.mono h𝒢).aestronglyMeasurable.mul
      (hv.mono h𝒢).aestronglyMeasurable) (c / ψ) ?_
    filter_upwards [hHv] with ω h
    rw [Real.norm_of_nonneg (mul_nonneg (hH0 ω) (hv0 ω))]; exact h
  -- pull-out
  have hpull1 : ∫ ω, H ω * D ω ∂μ = 0 := by
    have h := condExp_stronglyMeasurable_mul_of_bound h𝒢 hHm
      (Integrable.of_bound hDm b (hDb.mono fun ω h => by simpa using h)) c hHc
    calc ∫ ω, H ω * D ω ∂μ = ∫ ω, (μ[H * D | 𝒢]) ω ∂μ := (integral_condExp h𝒢).symm
      _ = ∫ ω, H ω * (μ[D | 𝒢]) ω ∂μ := integral_congr_ae h
      _ = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hD0] with ω h
        simp [h]
  have hpull2 : ∫ ω, H ω * D ω ^ 2 ∂μ ≤ ∫ ω, H ω * v ω ∂μ := by
    have h := condExp_stronglyMeasurable_mul_of_bound h𝒢 hHm hD2int c hHc
    calc ∫ ω, H ω * D ω ^ 2 ∂μ = ∫ ω, (μ[H * D ^ 2 | 𝒢]) ω ∂μ :=
          (integral_condExp h𝒢).symm
      _ = ∫ ω, H ω * (μ[D ^ 2 | 𝒢]) ω ∂μ := integral_congr_ae h
      _ ≤ ∫ ω, H ω * v ω ∂μ := by
        refine integral_mono_ae ?_ hHvint ?_
        · exact (integrable_condExp.congr h : _)
        · filter_upwards [hDv] with ω h
          exact mul_le_mul_of_nonneg_left h (hH0 ω)
  -- main estimate
  have hrewrite : ∀ ω, G ω * Real.exp (l * D ω - ψ * v ω) = H ω * Real.exp (l * D ω) := fun ω => by
    simp only [hH]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [hrewrite]
  have hbound : ∀ᵐ ω ∂μ, H ω * Real.exp (l * D ω) ≤
      H ω + l * (H ω * D ω) + ψ * (H ω * D ω ^ 2) := by
    filter_upwards [hDb] with ω h
    have := exp_le_one_add_of_le hb hl (le_trans (le_abs_self _) h)
    have h2 := mul_le_mul_of_nonneg_left this (hH0 ω)
    nlinarith
  have hA : Integrable (fun ω => H ω + l * (H ω * D ω)) μ := hHint.add (hHDint.const_mul l)
  have hint_rhs : Integrable (fun ω => H ω + l * (H ω * D ω) + ψ * (H ω * D ω ^ 2)) μ :=
    hA.add (hHD2int.const_mul ψ)
  have hexpint : Integrable (fun ω => H ω * Real.exp (l * D ω)) μ := by
    refine Integrable.of_bound ((hHm.mono h𝒢).aestronglyMeasurable.mul
      (Real.continuous_exp.comp_aestronglyMeasurable (hDm.const_mul l))) (c * Real.exp (l * b)) ?_
    filter_upwards [hHc, hDb] with ω h1 h2
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul h1 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
      (le_trans (le_abs_self _) h2) hl.le)) (Real.exp_pos _).le hc0
  calc ∫ ω, H ω * Real.exp (l * D ω) ∂μ
      ≤ ∫ ω, (H ω + l * (H ω * D ω) + ψ * (H ω * D ω ^ 2)) ∂μ :=
        integral_mono_ae hexpint hint_rhs hbound
    _ = ∫ ω, H ω ∂μ + l * ∫ ω, H ω * D ω ∂μ + ψ * ∫ ω, H ω * D ω ^ 2 ∂μ := by
        rw [integral_add hA (hHD2int.const_mul ψ),
          integral_add hHint (hHDint.const_mul l), integral_const_mul, integral_const_mul]
    _ ≤ ∫ ω, H ω ∂μ + ψ * ∫ ω, H ω * v ω ∂μ := by
        rw [hpull1]; nlinarith
    _ = ∫ ω, (H ω + ψ * (H ω * v ω)) ∂μ := by
        rw [integral_add hHint (hHvint.const_mul ψ), integral_const_mul]
    _ ≤ ∫ ω, G ω ∂μ := by
        refine integral_mono_ae (hHint.add (hHvint.const_mul ψ)) hGint (Filter.Eventually.of_forall fun ω => ?_)
        have h1 := one_add_mul_exp_neg_le_one (ψ * v ω)
        have : H ω + ψ * (H ω * v ω) = G ω * ((1 + ψ * v ω) * Real.exp (-(ψ * v ω))) := by
          simp only [hH]; ring
        show H ω + ψ * (H ω * v ω) ≤ G ω
        rw [this]
        calc G ω * ((1 + ψ * v ω) * Real.exp (-(ψ * v ω))) ≤ G ω * 1 :=
              mul_le_mul_of_nonneg_left h1 (hG0 ω)
          _ = G ω := mul_one _

end ElboimSly
