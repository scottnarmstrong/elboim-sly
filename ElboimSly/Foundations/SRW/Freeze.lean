/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.StrongMarkovMain
public import Mathlib

/-!
# Freezing measurable data at a stopping time

Freezing ℱ'_T-measurable data; Freezing data with values in a measurable space.

For `Γ` measurable in the product `E × PathSpace d` (a measurable version of an `ℰ`-regular set;
all paths in this development are regular, so no regularity bookkeeping is needed),
`φ z = Law(Z)(Γ_z)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω} {T : Ω → WithTop ℝ≥0}

/-- Freezing data with values in a measurable space (a): the section function `φ(z) = Law(Z)(Γ_z)` is measurable. -/
theorem measurable_section_law {E : Type*} [MeasurableSpace E] (L : Measure (PathSpace d))
    [SFinite L] {Γ : Set (E × PathSpace d)} (hΓ : MeasurableSet Γ) :
    Measurable fun z : E => L (Prod.mk z ⁻¹' Γ) :=
  measurable_measure_prodMk_left hΓ

/-- Freezing data with values in a measurable space (b): freezing `ℱ_T`-measurable data with values in a
measurable space. -/
theorem IsSRW.freeze_param (hZ : IsSRW P Z) (hF : IsAdmissible P Z F)
    (hT : IsStoppingTime hF.filtration T) {E : Type*} [MeasurableSpace E] {ξ : Ω → E}
    (hξ : Measurable[hT.measurableSpace] ξ) {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {Γ : Set (E × PathSpace d)} (hΓ : MeasurableSet Γ) :
    P (A ∩ {ω | T ω < ⊤} ∩ {ω | (ξ ω, thetaAt T Z ω) ∈ Γ}) =
      ∫⁻ ω in A ∩ {ω | T ω < ⊤}, P.map Z (Prod.mk (ξ ω) ⁻¹' Γ) ∂P := by
  have := hZ.isProbabilityMeasure
  have hth : Measurable (thetaAt T Z) :=
    measurable_thetaAt hT (fun s => (measurable_pi_apply s).comp hZ.1) hZ.2.1
  have hAm : MeasurableSet A := hT.measurableSpace_le A hA
  have hξm : Measurable ξ := hξ.mono hT.measurableSpace_le le_rfl
  have hTtop : MeasurableSet {ω | T ω < ⊤} := by
    have : {ω | T ω < ⊤} = {ω | T ω = ⊤}ᶜ := by
      ext ω; simp [lt_top_iff_ne_top]
    rw [this]; exact hT.measurableSet_top.compl
  set B : Set Ω := A ∩ {ω | T ω < ⊤} with hBdef
  have hBm : MeasurableSet B := hAm.inter hTtop
  have hpair : Measurable fun ω => (ξ ω, thetaAt T Z ω) := hξm.prodMk hth
  have hZmap : IsProbabilityMeasure (P.map Z) := by
    have := hZ.isProbabilityMeasure
    exact (Measure.isProbabilityMeasure_map_iff hZ.1.aemeasurable).2 inferInstance
  have hkey : (P.restrict B).map (fun ω => (ξ ω, thetaAt T Z ω)) =
      ((P.restrict B).map ξ).prod (P.map Z) := by
    symm
    refine Measure.prod_eq fun s t hs ht => ?_
    rw [Measure.map_apply hξm hs, Measure.restrict_apply (hξm hs),
      Measure.map_apply hpair (hs.prod ht), Measure.restrict_apply (hpair (hs.prod ht))]
    have hA' : MeasurableSet[hT.measurableSpace] (A ∩ ξ ⁻¹' s) := hA.inter (hξ hs)
    have := hZ.strong_markov hF hT hA' ht
    have e1 : (ξ ⁻¹' s ∩ B) = (A ∩ ξ ⁻¹' s) ∩ {ω | T ω < ⊤} := by
      ext ω; simp only [hBdef, mem_inter_iff, mem_preimage, mem_ofPred_eq]; tauto
    have e2 : ((fun ω => (ξ ω, thetaAt T Z ω)) ⁻¹' s ×ˢ t ∩ B) =
        (A ∩ ξ ⁻¹' s) ∩ {ω | T ω < ⊤} ∩ {ω | thetaAt T Z ω ∈ t} := by
      ext ω; simp only [hBdef, mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq]; tauto
    rw [e1, e2]
    exact this
  have hΓm := hΓ
  have := congrArg (fun μ => μ Γ) hkey
  simp only [Measure.map_apply hpair hΓ, Measure.restrict_apply (hpair hΓ)] at this
  rw [Measure.prod_apply hΓ, lintegral_map (measurable_section_law _ hΓ) hξm] at this
  have e3 : ((fun ω => (ξ ω, thetaAt T Z ω)) ⁻¹' Γ ∩ B) =
      B ∩ {ω | (ξ ω, thetaAt T Z ω) ∈ Γ} := by
    ext ω; simp [inter_comm]
  rw [e3] at this
  exact this

/-- Freezing data with values in a measurable space (c). -/
theorem IsSRW.freeze_param_le (hZ : IsSRW P Z) (hF : IsAdmissible P Z F)
    (hT : IsStoppingTime hF.filtration T) {E : Type*} [MeasurableSpace E] {ξ : Ω → E}
    (hξ : Measurable[hT.measurableSpace] ξ) {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {Γ : Set (E × PathSpace d)} (hΓ : MeasurableSet Γ) {C : Set E} (hC : MeasurableSet C)
    {p : ℝ≥0∞} (hp : ∀ z ∈ C, P.map Z (Prod.mk z ⁻¹' Γ) ≤ p) :
    P (A ∩ {ω | T ω < ⊤} ∩ {ω | ξ ω ∈ C} ∩ {ω | (ξ ω, thetaAt T Z ω) ∈ Γ}) ≤
      p * P (A ∩ {ω | T ω < ⊤} ∩ {ω | ξ ω ∈ C}) := by
  have hA' : MeasurableSet[hT.measurableSpace] (A ∩ ξ ⁻¹' C) := hA.inter (hξ hC)
  have h := hZ.freeze_param hF hT hξ hA' hΓ
  have e : A ∩ ξ ⁻¹' C ∩ {ω | T ω < ⊤} = A ∩ {ω | T ω < ⊤} ∩ {ω | ξ ω ∈ C} := by
    ext ω; simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]; tauto
  rw [e] at h
  rw [h]
  have hAm : MeasurableSet (A ∩ ξ ⁻¹' C) := hT.measurableSpace_le _ hA'
  calc ∫⁻ ω in A ∩ {ω | T ω < ⊤} ∩ {ω | ξ ω ∈ C}, P.map Z (Prod.mk (ξ ω) ⁻¹' Γ) ∂P
      ≤ ∫⁻ _ω in A ∩ {ω | T ω < ⊤} ∩ {ω | ξ ω ∈ C}, p ∂P := by
        refine setLIntegral_mono' ?_ fun ω hω => hp _ hω.2
        have hTtop : MeasurableSet {ω | T ω < ⊤} := by
          have : {ω | T ω < ⊤} = {ω | T ω = ⊤}ᶜ := by
            ext ω; simp [lt_top_iff_ne_top]
          rw [this]; exact hT.measurableSet_top.compl
        exact (hT.measurableSpace_le _ hA).inter hTtop |>.inter
          ((hξ.mono hT.measurableSpace_le le_rfl) hC)
    _ = p * P (A ∩ {ω | T ω < ⊤} ∩ {ω | ξ ω ∈ C}) := by
        rw [setLIntegral_const, mul_comm]

end SRW
end ElboimSly
