/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Freeze
public import Mathlib

/-!
# Freezing lower bound for an almost-measurable independent variable

Independence tools (e), used in ES22 Lemma 5.5 and ES22 Claim 5.7.

If `Y` is independent of a sub-`σ`-algebra `H` in the rectangle form
`P(A ∩ {Y ∈ Γ}) = P(A) P(Y ∈ Γ)` (`A ∈ H`), `U` is `H`-measurable, `A ∈ H`, and every slice
`{y | (U ω, y) ∈ S}` has `Y`-law at least `q` for `ω ∈ A`, then
`P(A ∩ {(U, Y) ∈ S}) ≥ q P(A)`.  Only almost-measurability of `Y` is needed (the walks of the
plan coupling are measurable only up to a null set).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

variable {Ω : Type*} {ζ Θ : Type*} [MeasurableSpace ζ] [MeasurableSpace Θ]

theorem freezeLowerAe (H : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (hH : H ≤ mΩ) {U : Ω → ζ} (hU : Measurable[H] U) {Y : Ω → Θ}
    (hY : AEMeasurable Y Pr)
    (hind : ∀ A, MeasurableSet[H] A → ∀ Γ : Set Θ, MeasurableSet Γ →
      Pr (A ∩ Y ⁻¹' Γ) = Pr A * Pr (Y ⁻¹' Γ))
    {A : Set Ω} (hA : MeasurableSet[H] A) {S : Set (ζ × Θ)} (hS : MeasurableSet S) {q : ℝ≥0∞}
    (hq : ∀ ω ∈ A, q ≤ (Pr.map Y) {y | (U ω, y) ∈ S}) :
    q * Pr A ≤ Pr (A ∩ {ω | (U ω, Y ω) ∈ S}) := by
  set Y₀ := hY.mk Y with hY₀
  have hY₀m : Measurable Y₀ := hY.measurable_mk
  have hae : Y =ᵐ[Pr] Y₀ := hY.ae_eq_mk
  have hmap : Pr.map Y = Pr.map Y₀ := Measure.map_congr hae
  have hAm : MeasurableSet A := hH _ hA
  have hset : ∀ Γ : Set Θ, MeasurableSet Γ → Y ⁻¹' Γ =ᵐ[Pr] Y₀ ⁻¹' Γ := fun Γ _ => by
    filter_upwards [hae] with ω hω
    simp only [mem_preimage, hω]
  have hind₀ : Indep H (MeasurableSpace.comap Y₀ inferInstance) Pr := by
    rw [Indep_iff]
    rintro t₁ t₂ ht₁ ⟨Γ, hΓ, rfl⟩
    have e1 : Pr (t₁ ∩ Y₀ ⁻¹' Γ) = Pr (t₁ ∩ Y ⁻¹' Γ) :=
      measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl (hset Γ hΓ).symm)
    rw [e1, hind t₁ ht₁ Γ hΓ, measure_congr (hset Γ hΓ)]
  have hIA : Measurable[H] (A.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have hZH : Measurable[H] (fun ω => (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) :=
    hU.prodMk hIA
  have hZ : Measurable (fun ω => (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) :=
    hZH.mono hH le_rfl
  have hindep : IndepFun (fun ω => (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) Y₀ Pr := by
    have hle : MeasurableSpace.comap (fun ω => (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω))
        inferInstance ≤ H := hZH.comap_le
    exact indep_of_indep_of_le_left hind₀ hle
  set φ : ζ × ℝ≥0∞ → Θ → ℝ≥0∞ := fun z y => z.2 * S.indicator (fun _ => (1 : ℝ≥0∞)) (z.1, y)
    with hφ
  have hφm : Measurable (Function.uncurry φ) := by
    refine (measurable_snd.comp measurable_fst).mul ?_
    exact measurable_const.indicator (hS.preimage (by fun_prop))
  have hfreeze := ElboimSly.Brownian.lintegral_freeze (P := Pr) hZ hY₀m hindep hφm
  have hlow : ∀ ω, A.indicator (fun _ => q) ω ≤
      ∫⁻ y, φ (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω) y ∂(Pr.map Y₀) := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω]
      have hsec : MeasurableSet {y | (U ω, y) ∈ S} := measurable_prodMk_left hS
      have : ∫⁻ y, φ (U ω, (1 : ℝ≥0∞)) y ∂(Pr.map Y₀) = (Pr.map Y₀) {y | (U ω, y) ∈ S} := by
        simp only [hφ, one_mul]
        rw [← lintegral_indicator_one hsec]
        rfl
      rw [this, ← hmap]
      exact hq ω hω
    · simp [indicator_of_notMem hω]
  have hup : ∀ ω, φ (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω) (Y₀ ω) =
      (A ∩ {ω | (U ω, Y₀ ω) ∈ S}).indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ A
    · by_cases hg : (U ω, Y₀ ω) ∈ S
      · have hmem : ω ∈ A ∩ {ω | (U ω, Y₀ ω) ∈ S} := ⟨hω, hg⟩
        simp only [hφ, indicator_of_mem hω, indicator_of_mem hg, indicator_of_mem hmem, one_mul]
        rfl
      · have hmem : ω ∉ A ∩ {ω | (U ω, Y₀ ω) ∈ S} := fun h => hg h.2
        simp [hφ, indicator_of_mem hω, indicator_of_notMem hg, indicator_of_notMem hmem]
    · have hmem : ω ∉ A ∩ {ω | (U ω, Y₀ ω) ∈ S} := fun h => hω h.1
      simp [hφ, indicator_of_notMem hω, indicator_of_notMem hmem]
  have hmain : q * Pr A ≤ Pr (A ∩ {ω | (U ω, Y₀ ω) ∈ S}) :=
    calc q * Pr A = ∫⁻ ω, A.indicator (fun _ => q) ω ∂Pr := (lintegral_indicator_const hAm _).symm
      _ ≤ ∫⁻ ω, ∫⁻ y, φ (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω) y ∂(Pr.map Y₀) ∂Pr :=
          lintegral_mono hlow
      _ = ∫⁻ ω, φ (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω) (Y₀ ω) ∂Pr := hfreeze.symm
      _ = ∫⁻ ω, (A ∩ {ω | (U ω, Y₀ ω) ∈ S}).indicator 1 ω ∂Pr := lintegral_congr hup
      _ ≤ _ := lintegral_indicator_one_le _
  have hcongr : A ∩ {ω | (U ω, Y ω) ∈ S} =ᵐ[Pr] A ∩ {ω | (U ω, Y₀ ω) ∈ S} := by
    filter_upwards [hae] with ω hω
    simp only [mem_inter_iff, mem_ofPred_eq, hω]
  rw [measure_congr hcongr]
  exact hmain

end ElboimSly.Paper.Escape
