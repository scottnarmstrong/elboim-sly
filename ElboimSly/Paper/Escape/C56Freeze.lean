/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Freeze
public import Mathlib

/-!
# Freezing lower bound

Independence tools (e), used in ES22 Claim 5.6.  If `X` is independent of `H`, `U` is
`H`-measurable and `A ∈ H`, and every slice `{y | (U ω, y) ∈ Γ}` has `X`-law at least `q` for
`ω ∈ A`, then `P(A ∩ {(U, X) ∈ Γ}) ≥ q P(A)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

variable {Ω : Type*} {𝒰 𝒳 : Type*} [MeasurableSpace 𝒰]
  [MeasurableSpace 𝒳]

theorem freeze_ge (H : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (hH : H ≤ mΩ) {U : Ω → 𝒰} (hU : Measurable[H] U) {X : Ω → 𝒳} (hX : Measurable X)
    (hind : Indep H (MeasurableSpace.comap X inferInstance) Pr) {A : Set Ω}
    (hA : MeasurableSet[H] A) {Γ : Set (𝒰 × 𝒳)} (hΓ : MeasurableSet Γ) {q : ℝ≥0∞}
    (hq : ∀ ω ∈ A, q ≤ (Pr.map X) {y | (U ω, y) ∈ Γ}) :
    q * Pr A ≤ Pr (A ∩ {ω | (U ω, X ω) ∈ Γ}) := by
  have hAm : MeasurableSet A := hH _ hA
  have hIA : Measurable[H] (A.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have hZH : Measurable[H] (fun ω => (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) :=
    hU.prodMk hIA
  have hZ : Measurable (fun ω => (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) :=
    hZH.mono hH le_rfl
  have hindep : IndepFun (fun ω => (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) X Pr := by
    have hle : MeasurableSpace.comap (fun ω => (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω))
        inferInstance ≤ H := hZH.comap_le
    exact indep_of_indep_of_le_left hind hle
  set φ : 𝒰 × ℝ≥0∞ → 𝒳 → ℝ≥0∞ := fun z y => z.2 * Γ.indicator (fun _ => (1 : ℝ≥0∞)) (z.1, y)
    with hφ
  have hφm : Measurable (Function.uncurry φ) := by
    refine (measurable_snd.comp measurable_fst).mul ?_
    exact measurable_const.indicator (hΓ.preimage (by fun_prop))
  have hfreeze := ElboimSly.Brownian.lintegral_freeze (P := Pr) hZ hX hindep hφm
  have hlow : ∀ ω, A.indicator (fun _ => q) ω ≤
      ∫⁻ y, φ (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω) y ∂(Pr.map X) := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω]
      have hsec : MeasurableSet {y | (U ω, y) ∈ Γ} := measurable_prodMk_left hΓ
      have : ∫⁻ y, φ (U ω, (1 : ℝ≥0∞)) y ∂(Pr.map X) = (Pr.map X) {y | (U ω, y) ∈ Γ} := by
        simp only [hφ, one_mul]
        rw [← lintegral_indicator_one hsec]
        rfl
      rw [this]
      exact hq ω hω
    · simp [indicator_of_notMem hω]
  have hup : ∀ ω, φ (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω) (X ω) =
      (A ∩ {ω | (U ω, X ω) ∈ Γ}).indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ A
    · by_cases hg : (U ω, X ω) ∈ Γ
      · have hmem : ω ∈ A ∩ {ω | (U ω, X ω) ∈ Γ} := ⟨hω, hg⟩
        simp only [hφ, indicator_of_mem hω, indicator_of_mem hg, indicator_of_mem hmem, one_mul]
        rfl
      · have hmem : ω ∉ A ∩ {ω | (U ω, X ω) ∈ Γ} := fun h => hg h.2
        simp [hφ, indicator_of_mem hω, indicator_of_notMem hg, indicator_of_notMem hmem]
    · have hmem : ω ∉ A ∩ {ω | (U ω, X ω) ∈ Γ} := fun h => hω h.1
      simp [hφ, indicator_of_notMem hω, indicator_of_notMem hmem]
  calc q * Pr A = ∫⁻ ω, A.indicator (fun _ => q) ω ∂Pr := (lintegral_indicator_const hAm _).symm
    _ ≤ ∫⁻ ω, ∫⁻ y, φ (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω) y ∂(Pr.map X) ∂Pr :=
        lintegral_mono hlow
    _ = ∫⁻ ω, φ (U ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω) (X ω) ∂Pr := hfreeze.symm
    _ = ∫⁻ ω, (A ∩ {ω | (U ω, X ω) ∈ Γ}).indicator 1 ω ∂Pr := lintegral_congr hup
    _ ≤ _ := lintegral_indicator_one_le _

end ElboimSly.Paper.Escape

end
