/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenCoupleDef
public import ElboimSly.Foundations.Cyclic.CycRegenShiftLaw
public import Mathlib

/-!
# ES22 Lemma 2.1 (b): the law of the environment after the stopping time

ES22 Lemma 2.1 (b), proof, "Freezing". Under the hypotheses of
Several walks explored one after another for `𝒫_reg` and an `(ℱ^{𝒫_reg}_s)`-stopping time `T`, the environment
`M = regM N N' T` is measurable, has the law of `N`, and the regenerated walk of `M` is fresh:
`P(A ∩ {T<∞} ∩ {W' ∈ Γ}) = P(A ∩ {T<∞}) P(W ∈ Γ)` for `A ∈ ℱ_T` (`regen_couple_core`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (ℕ × RingSpace d β)}
  (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity ℕ d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
theorem regen_couple_core (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt (regPlan d β) 𝒢₀ hN.measurable h𝒢 Pr) T) :
    Measurable (regM N N' T) ∧ Pr.map (regM N N' T) = Pr.map N ∧
    (∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A → ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)},
      MeasurableSet Γ →
      Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | regW (regM N N' T ω) ∈ Γ}) =
        Pr (A ∩ {ω | T ω ≠ ⊤}) * Pr {ω | regW (N ω) ∈ Γ}) := by
  classical
  obtain ⟨hE, hRec, hregset, -, -, hb, -, -, -⟩ :=
    cyc_multi_exploration_a (regPlan d β) 𝒢₀ hN hN' hI1 hI2 hK_regPlan' h𝒢 hT
  have hPr := hN.isProbabilityMeasure
  set E : Set Ω := {ω | T ω ≠ ⊤} with hEdef
  have hEm : MeasurableSet E := hT.measurableSpace_le _ hE
  have hZm : Measurable[hT.measurableSpace] (regZ N T) :=
    (measurable_recZ ((regPlan d β).junk)).comp hRec
  have hle : hT.measurableSpace.prod (inferInstance : MeasurableSpace (ℕ × RingSpace d β)) ≤
      mΩ.prod inferInstance :=
    sup_le_sup (MeasurableSpace.comap_mono hT.measurableSpace_le) le_rfl
  have hY : Measurable (regYtil N N' T) :=
    measurable_tildeTauG (cycIntensity ℕ d β) hN.measurable hN'.measurable (hle _ hregset)
  have hYae : ∀ᵐ ω ∂Pr, regYtil N N' T ω =
      tildeMeasure N N' (cycRegionStop (regPlan d β) (cycNgood N) T) ω := by
    filter_upwards [hN.tau_comp_ae_eq, hN'.tau_comp_ae_eq] with ω h1 h2
    unfold regYtil tildeMeasure
    beta_reduce
    rw [h1, h2]
  have hstep : ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {B : Set (Measure (ℕ × RingSpace d β))}, MeasurableSet B →
      Pr (E ∩ A ∩ regYtil N N' T ⁻¹' B) = Pr (E ∩ A) * (Pr.map N) B := by
    intro A hA B hB
    have h1 := hb hA hB
    have h2 : Pr (E ∩ A ∩ regYtil N N' T ⁻¹' B) =
        Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | tildeMeasure N N'
          (cycRegionStop (regPlan d β) (cycNgood N) T) ω ∈ B}) := by
      rw [show E ∩ A = A ∩ {ω | T ω ≠ ⊤} from inter_comm _ _]
      refine measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl ?_)
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hYae] with ω hω
      simp only [mem_preimage, hω]
    rw [h2, h1, inter_comm A]
  have hfr : ∀ {G : Ω × Measure (ℕ × RingSpace d β) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] G →
      ∫⁻ ω in E, G (ω, regYtil N N' T ω) ∂Pr = ∫⁻ ω in E, ∫⁻ ν, G (ω, ν) ∂(Pr.map N) ∂Pr :=
    fun hG => lintegral_freeze_restrict hT.measurableSpace hT.measurableSpace_le hE hY
      (Pr.map N) hstep hG
  have hMm : Measurable (regM N N' T) :=
    Measurable.ite hEm (measurable_cycShift.comp
      ((hZm.mono hT.measurableSpace_le le_rfl).prodMk hY)) hN'.measurable
  have hlawS : ∀ (z : ShiftPar d) {F : Set (Measure (ℕ × RingSpace d β))}, MeasurableSet F →
      (Pr.map N) {ν | cycShift z ν ∈ F} = (Pr.map N) F := by
    intro z F hF
    have hm : Measurable (cycShift z : Measure (ℕ × RingSpace d β) → Measure (ℕ × RingSpace d β)) :=
      measurable_cycShift_at z
    calc (Pr.map N) (cycShift z ⁻¹' F) = Pr (N ⁻¹' (cycShift z ⁻¹' F)) :=
          Measure.map_apply hN.measurable (hm hF)
      _ = Pr.map (fun ω => cycShift z (N ω)) F :=
          (Measure.map_apply (hm.comp hN.measurable) hF).symm
      _ = (Pr.map N) F := by rw [law_cycShift hN z]
  have hfst : @Measurable _ _ (hT.measurableSpace.prod inferInstance) hT.measurableSpace
      (Prod.fst : Ω × Measure (ℕ × RingSpace d β) → Ω) := @measurable_fst _ _ hT.measurableSpace _
  have hsnd : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
      (Prod.snd : Ω × Measure (ℕ × RingSpace d β) → Measure (ℕ × RingSpace d β)) :=
    @measurable_snd _ _ hT.measurableSpace _
  have hshift : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
      (fun p : Ω × Measure (ℕ × RingSpace d β) => cycShift (regZ N T p.1) p.2) :=
    measurable_cycShift.comp ((hZm.comp hfst).prodMk hsnd)
  have hfirst : ∀ {F : Set (Measure (ℕ × RingSpace d β))}, MeasurableSet F →
      Pr (E ∩ regM N N' T ⁻¹' F) = Pr E * (Pr.map N) F := by
    intro F hF
    set G : Ω × Measure (ℕ × RingSpace d β) → ℝ≥0∞ :=
      fun p => F.indicator 1 (cycShift (regZ N T p.1) p.2) with hG
    have hGm : Measurable[hT.measurableSpace.prod inferInstance] G :=
      (measurable_one.indicator hF).comp hshift
    have hS' : MeasurableSet {ω | cycShift (regZ N T ω) (regYtil N N' T ω) ∈ F} :=
      (measurable_cycShift.comp ((hZm.mono hT.measurableSpace_le le_rfl).prodMk hY)) hF
    have e0 : E ∩ regM N N' T ⁻¹' F =
        {ω | cycShift (regZ N T ω) (regYtil N N' T ω) ∈ F} ∩ E := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, hEdef, regM]
      constructor
      · rintro ⟨h1, h2⟩; rw [ite_eq_left h1] at h2; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; rw [ite_eq_left h1]; exact ⟨h1, h2⟩
    have e1 : Pr (E ∩ regM N N' T ⁻¹' F) = ∫⁻ ω in E, G (ω, regYtil N N' T ω) ∂Pr := by
      rw [e0, ← Measure.restrict_apply' hEm, ← lintegral_indicator_one hS']
      refine lintegral_congr fun ω => ?_
      simp only [hG, Set.indicator_apply, mem_ofPred_eq]
      rfl
    have e3 : ∀ ω, ∫⁻ ν, G (ω, ν) ∂(Pr.map N) = (Pr.map N) F := by
      intro ω
      have hm : Measurable (cycShift (regZ N T ω) :
          Measure (ℕ × RingSpace d β) → Measure (ℕ × RingSpace d β)) := measurable_cycShift_at _
      have : (fun ν => G (ω, ν)) = ((cycShift (regZ N T ω)) ⁻¹' F).indicator 1 := by
        funext ν; simp only [hG, Set.indicator_apply, mem_preimage]; rfl
      rw [this, lintegral_indicator_one (hm hF)]
      exact hlawS _ hF
    rw [e1, hfr hGm]
    simp_rw [e3]
    rw [setLIntegral_const]
    ring
  have hsecond : ∀ {F : Set (Measure (ℕ × RingSpace d β))}, MeasurableSet F →
      Pr (Eᶜ ∩ regM N N' T ⁻¹' F) = Pr Eᶜ * (Pr.map N) F := by
    intro F hF
    obtain ⟨t, ht, hte⟩ := exists_ae_top_set_multi 𝒢₀ (regPlan d β) h𝒢 hN.measurable hT
    have e0 : Eᶜ ∩ regM N N' T ⁻¹' F = {ω | T ω = ⊤} ∩ N' ⁻¹' F := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, mem_preimage, hEdef, mem_ofPred_eq, regM]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : ¬ T ω ≠ ⊤ := h1
        rw [ite_eq_right h1'] at h2
        exact ⟨not_not.1 h1', h2⟩
      · rintro ⟨h1, h2⟩
        have h1' : ¬ T ω ≠ ⊤ := not_not.2 h1
        rw [ite_eq_right h1']
        exact ⟨h1', h2⟩
    have hEc : Eᶜ = {ω | T ω = ⊤} := by
      ext ω; simp [hEdef]
    have hind := (Indep_iff _ _ Pr).1 hI2 (N' ⁻¹' F) t ⟨F, hF, rfl⟩ ht
    have hlawN' : Pr (N' ⁻¹' F) = (Pr.map N) F := by
      rw [← hN.map_eq_map hN', Measure.map_apply hN'.measurable hF]
    rw [e0, hEc]
    rw [measure_congr (Filter.EventuallyEqSet.inter hte Filter.EventuallyEq.rfl), inter_comm, hind,
      hlawN', measure_congr hte, mul_comm]
  have hall : ∀ {F : Set (Measure (ℕ × RingSpace d β))}, MeasurableSet F →
      Pr (regM N N' T ⁻¹' F) = (Pr.map N) F := by
    intro F hF
    have h1 := measure_inter_add_sdiff (μ := Pr) (regM N N' T ⁻¹' F) hEm
    have h2 : regM N N' T ⁻¹' F \ E = Eᶜ ∩ regM N N' T ⁻¹' F := by
      ext ω; simp [and_comm]
    rw [inter_comm, hfirst hF, h2, hsecond hF, ← add_mul, prob_add_prob_compl hEm, one_mul] at h1
    exact h1.symm
  have hlawM : Pr.map (regM N N' T) = Pr.map N := by
    ext F hF
    rw [Measure.map_apply hMm hF]
    exact hall hF
  refine ⟨hMm, hlawM, ?_⟩
  intro A hA Γ hΓ
  set G : Ω × Measure (ℕ × RingSpace d β) → ℝ≥0∞ := fun p =>
    {q : Ω × Measure (ℕ × RingSpace d β) |
      q.1 ∈ A ∧ regW (cycShift (regZ N T q.1) q.2) ∈ Γ}.indicator 1 p with hG
  have hGm : Measurable[hT.measurableSpace.prod inferInstance] G := by
    have h1 : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
        (fun p : Ω × Measure (ℕ × RingSpace d β) => regW (cycShift (regZ N T p.1) p.2)) :=
      measurable_regW.comp hshift
    have hS : @MeasurableSet _ (hT.measurableSpace.prod inferInstance)
        {q : Ω × Measure (ℕ × RingSpace d β) |
          q.1 ∈ A ∧ regW (cycShift (regZ N T q.1) q.2) ∈ Γ} :=
      (hfst hA).inter (h1 hΓ)
    exact Measurable.indicator measurable_const hS
  have hS' : MeasurableSet {ω | ω ∈ A ∧ regW (cycShift (regZ N T ω) (regYtil N N' T ω)) ∈ Γ} :=
    (hT.measurableSpace_le _ hA).inter
      ((measurable_regW.comp (measurable_cycShift.comp
        ((hZm.mono hT.measurableSpace_le le_rfl).prodMk hY))) hΓ)
  have e0 : A ∩ {ω | T ω ≠ ⊤} ∩ {ω | regW (regM N N' T ω) ∈ Γ} =
      {ω | ω ∈ A ∧ regW (cycShift (regZ N T ω) (regYtil N N' T ω)) ∈ Γ} ∩ E := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, hEdef, regM]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩; rw [ite_eq_left h1] at h2; exact ⟨⟨h0, h2⟩, h1⟩
    · rintro ⟨⟨h0, h2⟩, h1⟩; rw [ite_eq_left h1]; exact ⟨⟨h0, h1⟩, h2⟩
  have e1 : Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | regW (regM N N' T ω) ∈ Γ}) =
      ∫⁻ ω in E, G (ω, regYtil N N' T ω) ∂Pr := by
    rw [e0, ← Measure.restrict_apply' hEm, ← lintegral_indicator_one hS']
    refine lintegral_congr fun ω => ?_
    simp only [hG, Set.indicator_apply, mem_ofPred_eq]
    rfl
  have e3 : ∀ ω, ∫⁻ ν, G (ω, ν) ∂(Pr.map N) =
      A.indicator (fun _ => Pr {ω | regW (N ω) ∈ Γ}) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · have hm : Measurable (cycShift (regZ N T ω) :
          Measure (ℕ × RingSpace d β) → Measure (ℕ × RingSpace d β)) := measurable_cycShift_at _
      have : (fun ν => G (ω, ν)) =
          ((cycShift (regZ N T ω)) ⁻¹' (regW ⁻¹' Γ)).indicator 1 := by
        funext ν; simp only [hG, Set.indicator_apply, mem_preimage, mem_ofPred_eq, hω, true_and]
        rfl
      rw [this, lintegral_indicator_one (hm (measurable_regW hΓ)), Set.indicator_of_mem hω]
      have := hlawS (regZ N T ω) (measurable_regW hΓ)
      rw [show {ν | cycShift (regZ N T ω) ν ∈ regW ⁻¹' Γ} =
        cycShift (regZ N T ω) ⁻¹' (regW ⁻¹' Γ) from rfl] at this
      rw [this, Measure.map_apply hN.measurable (measurable_regW hΓ)]
      rfl
    · have : (fun ν => G (ω, ν)) = fun _ => 0 := by
        funext ν; simp [hG, Set.indicator_apply, hω]
      rw [this, Set.indicator_of_notMem hω]
      simp
  rw [e1, hfr hGm]
  simp_rw [e3]
  rw [lintegral_indicator_const (hT.measurableSpace_le _ hA), Measure.restrict_apply' hEm,
    mul_comm]

end ElboimSly.Cyclic

end
