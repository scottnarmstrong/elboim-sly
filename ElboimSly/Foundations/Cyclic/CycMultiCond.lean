/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiRecStop
public import ElboimSly.Foundations.Cyclic.CycMultiStopT
public import ElboimSly.Foundations.Cyclic.CycMultiRun
public import ElboimSly.Foundations.PPP.Indep
public import Mathlib

/-!
# Several walks explored one after another (a), Step 4: the conditional form

Several walks explored one after another (a), Step 4. For every `ℱ_T ⊗ 𝔊`-measurable
`F : Ω × 𝓜(𝒮) → [0, ∞]`,
`E F(·, N|_{𝒮∖R_T}) = E ∫ F(·, ν|_{𝒮∖R_T}) Π_μ(dν)`,
on `{T < ∞}` (`multi_cond_restrict`) and, if `P(T < ∞) = 1`, over all of `Ω`
(`multi_cond_of_ae_fin`). The proof freezes the `ℱ_T`-variable (`lintegral_freeze`) in the
independence `ℱ_T ⫫ Ñ_T` of Step 5 (`multi_stopped`), using `N|_{𝒮∖R_T} = Ñ_T|_{𝒮∖R_T}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS I d β)}

omit mΩ in
theorem measurableSet_cycRegionStop (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    MeasurableSet (cycRegionStop P N T ω) := by
  unfold cycRegionStop
  cases T ω using WithTop.recTopCoe with
  | top => exact MeasurableSet.empty
  | coe a => exact measurableSet_cycRegionAt P P.junk a ω N

omit [Fact (0 < β)] in
/-- `Trunc_s ∘ R` is `ℱ_s`-measurable for the joint exploration filtration. -/
theorem measurable_trunc_multiFilt (h𝒢 : 𝒢₀ ≤ mΩ) (Pr : Measure Ω)
    (hR : Measurable fun ω => P.envFinal (N ω)) (s : ℝ≥0) :
    Measurable[multiFilt 𝒢₀ P.junk Pr h𝒢 (fun ω => P.envFinal (N ω)) hR s]
      fun ω => CycRec.trunc s (P.envFinal (N ω)) := by
  have : Nonempty (CycEntry I d) := ⟨P.junk⟩
  rw [measurable_iff_comap_le]
  show _ ≤ cycFiltration Pr 𝒢₀ (fun ω => P.envFinal (N ω)) s
  rw [cycFiltration_eq 𝒢₀ P.junk]
  exact le_sup_of_le_left le_sup_right

/-- `Ñ_T`, built from the `τ`-truncated copies, is measurable. -/
theorem measurable_tildeTau {f : Filtration ℝ≥0 mΩ} {T : Ω → WithTop ℝ≥0}
    (hR : ∀ s, Measurable[f s] fun ω => CycRec.trunc s (P.envFinal (N ω)))
    (hT : IsStoppingTime f T) (hN : Measurable N) (hN' : Measurable N') :
    Measurable (tildeMeasure (fun ω => tau (cycIntensity I d β) (N ω))
      (fun ω => tau (cycIntensity I d β) (N' ω)) (cycRegionStop P N T)) := by
  have hle : hT.measurableSpace.prod (inferInstance : MeasurableSpace (CycS I d β)) ≤
      mΩ.prod inferInstance :=
    sup_le_sup (MeasurableSpace.comap_mono hT.measurableSpace_le) le_rfl
  have hZ : MeasurableSet {p : Ω × CycS I d β | p.2 ∈ cycRegionStop P N T p.1} :=
    hle _ (measurableSet_regionStop hR hT)
  have h1 := measurable_tau_restrict_section (cycIntensity I d β) hZ.compl
  have h2 := measurable_tau_restrict_section (cycIntensity I d β) hZ
  exact measurable_add_measure.comp
    ((h1.comp (measurable_id.prodMk hN)).prodMk (h2.comp (measurable_id.prodMk hN')))

theorem restrict_tilde_compl {S : Type*} [MeasurableSpace S] (μ μ' : Measure S) {Z : Set S}
    (hZ : MeasurableSet Z) : (μ.restrict Zᶜ + μ'.restrict Z).restrict Zᶜ = μ.restrict Zᶜ := by
  rw [Measure.restrict_add, Measure.restrict_restrict hZ.compl, Measure.restrict_restrict hZ.compl,
    inter_self, compl_inter_self, Measure.restrict_empty, add_zero]

theorem tilde_mem_lfSet {S : Type*} [MeasurableSpace S] (μ : Measure S) [SigmaFinite μ] {ν ν' : Measure S}
    (h : ν ∈ lfSet μ) (h' : ν' ∈ lfSet μ) (Z : Set S) :
    ν.restrict Zᶜ + ν'.restrict Z ∈ lfSet μ := fun k => by
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt (Measure.le_iff'.1 Measure.restrict_le_self _) (h k),
    lt_of_le_of_lt (Measure.le_iff'.1 Measure.restrict_le_self _) (h' k)⟩

section main

variable (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
/-- Several walks explored one after another (a), Step 4 (on `{T < ∞}`): for every
`ℱ_T ⊗ 𝔊`-measurable `F`,
`E[1_{T<∞} F(·, N|_{𝒮∖R_T})] = E[1_{T<∞} ∫ F(·, ν|_{𝒮∖R_T}) Π_μ(dν)]`. -/
theorem multi_cond_restrict (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ)
    (hR : Measurable fun ω => P.envFinal (N ω)) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (multiFilt 𝒢₀ P.junk Pr h𝒢 (fun ω => P.envFinal (N ω)) hR) T)
    {F : Ω × Measure (CycS I d β) → ℝ≥0∞}
    (hF : Measurable[hT.measurableSpace.prod inferInstance] F) :
    ∫⁻ ω in {ω | T ω ≠ ⊤}, F (ω, (N ω).restrict (cycRegionStop P N T ω)ᶜ) ∂Pr =
      ∫⁻ ω in {ω | T ω ≠ ⊤},
        ∫⁻ ν, F (ω, ν.restrict (cycRegionStop P N T ω)ᶜ) ∂(Pr.map N) ∂Pr := by
  have hPr := hN.isProbabilityMeasure
  set E : Set Ω := {ω | T ω ≠ ⊤} with hEdef
  have hEm : MeasurableSet E := hT.measurableSpace_le _ (measurableSet_ne_top hT)
  by_cases h0 : Pr E = 0
  · rw [Measure.restrict_eq_zero.2 h0]; simp
  have hRf := measurable_trunc_multiFilt P 𝒢₀ h𝒢 Pr hR
  set Rg := cycRegionStop P N T with hRg
  set Ytil := tildeMeasure (fun ω => tau (cycIntensity I d β) (N ω))
    (fun ω => tau (cycIntensity I d β) (N' ω)) Rg with hYdef
  have hY : Measurable Ytil := measurable_tildeTau P hRf hT hN.measurable hN'.measurable
  have hae : ∀ᵐ ω ∂Pr, Ytil ω = tildeMeasure N N' Rg ω := by
    filter_upwards [hN.tau_comp_ae_eq, hN'.tau_comp_ae_eq] with ω h1 h2
    simp only [hYdef, tildeMeasure]
    rw [h1, h2]
  have hstep : ∀ A, MeasurableSet[hT.measurableSpace] A → ∀ B : Set (Measure (CycS I d β)),
      MeasurableSet B → Pr (E ∩ (A ∩ Ytil ⁻¹' B)) = Pr (E ∩ A) * (Pr.map N) B := by
    intro A hA B hB
    have h1 := multi_stopped 𝒢₀ P hN hN' hI1 hI2 hK h𝒢 hR hT hA hB
    have e2 : Pr (A ∩ E ∩ Ytil ⁻¹' B) = Pr (A ∩ E ∩ {ω | tildeMeasure N N' Rg ω ∈ B}) := by
      refine measure_congr (EventuallyEqSet.inter Filter.EventuallyEq.rfl ?_)
      filter_upwards [hae] with ω hω
      apply propext
      simp only [mem_preimage, hω]
    have e3 : E ∩ (A ∩ Ytil ⁻¹' B) = A ∩ E ∩ Ytil ⁻¹' B := by
      ext ω; simp only [mem_inter_iff]; tauto
    rw [e3, e2, inter_comm E A]
    exact h1
  have hQ : IsProbabilityMeasure (cond Pr E) := cond_isProbabilityMeasure h0
  have hQapp : ∀ s : Set Ω, cond Pr E s = (Pr E)⁻¹ * Pr (E ∩ s) := fun s => cond_apply hEm Pr s
  have hPrE : Pr E ≠ ⊤ := measure_ne_top Pr E
  have hQ1 : ∀ B : Set (Measure (CycS I d β)), MeasurableSet B →
      cond Pr E (Ytil ⁻¹' B) = (Pr.map N) B := by
    intro B hB
    have := hstep univ MeasurableSet.univ B hB
    rw [univ_inter, inter_univ] at this
    rw [hQapp, this, ← mul_assoc, ENNReal.inv_mul_cancel h0 hPrE, one_mul]
  have hX : Measurable (GSpace.mk hT.measurableSpace) :=
    measurable_gspace_mk hT.measurableSpace hT.measurableSpace_le
  have hind : IndepFun (GSpace.mk hT.measurableSpace) Ytil (cond Pr E) := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro A B hA hB
    have hA' : MeasurableSet[hT.measurableSpace] (GSpace.mk hT.measurableSpace ⁻¹' A) := hA
    rw [hQapp, hstep _ hA' B hB, hQapp, hQ1 B hB, mul_assoc]

  have hmapY : (cond Pr E).map Ytil = Pr.map N := by
    ext B hB
    rw [Measure.map_apply hY hB, hQ1 B hB]
  have : IsProbabilityMeasure ((cond Pr E).map Ytil) :=
    ⟨by rw [hmapY, Measure.map_apply hN.measurable MeasurableSet.univ]; simp⟩
  set Zset : Set (GSpace hT.measurableSpace × CycS I d β) := {p | p.2 ∈ Rg p.1} with hZdef
  have hZ : MeasurableSet Zset := measurableSet_regionStop hRf hT
  have hGm : Measurable (fun p : GSpace hT.measurableSpace × Measure (CycS I d β) =>
      F (p.1, (tau (cycIntensity I d β) p.2).restrict (Prod.mk p.1 ⁻¹' Zsetᶜ))) :=
    hF.comp (measurable_fst.prodMk
      (measurable_tau_restrict_section (cycIntensity I d β) hZ.compl))
  have hfr := ElboimSly.lintegral_freeze (P := cond Pr E) hX hY hind hGm
  -- left-hand side
  have hlhs : ∀ᵐ ω ∂(cond Pr E), F (ω, (tau (cycIntensity I d β) (Ytil ω)).restrict
      (Prod.mk ω ⁻¹' Zsetᶜ)) = F (ω, (N ω).restrict (Rg ω)ᶜ) := by
    refine cond_absolutelyContinuous.ae_le ?_
    filter_upwards [hN.tau_comp_ae_eq] with ω h1
    have hmem : Ytil ω ∈ lfSet (cycIntensity I d β) :=
      tilde_mem_lfSet _ (tau_mem_lfSet _ _) (tau_mem_lfSet _ _) _
    have h2 := tau_of_mem (cycIntensity I d β) hmem
    show F (ω, (tau (cycIntensity I d β) (Ytil ω)).restrict (Rg ω)ᶜ) = _
    rw [h2]
    simp only [hYdef, tildeMeasure]
    rw [restrict_tilde_compl _ _ (measurableSet_cycRegionStop P (N := N) T ω), h1]
  -- right-hand side
  have hinner : ∀ ω, ∫⁻ y, F (ω, (tau (cycIntensity I d β) y).restrict (Rg ω)ᶜ) ∂(Pr.map N) =
      ∫⁻ y, F (ω, y.restrict (Rg ω)ᶜ) ∂(Pr.map N) := by
    intro ω
    refine lintegral_congr_ae ?_
    filter_upwards [(ae_map_iff hN.measurable.aemeasurable
      (measurableSet_lfSet (cycIntensity I d β))).2 hN.ae_mem_lfSet] with y hy
    rw [tau_of_mem _ hy]
  have hmeas_outer : Measurable fun x : GSpace hT.measurableSpace =>
      ∫⁻ y, F (x, (tau (cycIntensity I d β) y).restrict (Prod.mk x ⁻¹' Zsetᶜ)) ∂(Pr.map N) := by
    have : Measurable fun x : GSpace hT.measurableSpace =>
        ∫⁻ y, (fun p : GSpace hT.measurableSpace × Measure (CycS I d β) =>
          F (p.1, (tau (cycIntensity I d β) p.2).restrict (Prod.mk p.1 ⁻¹' Zsetᶜ))) (x, y)
          ∂(Pr.map N) := by
      have : SFinite (Pr.map N) := inferInstance
      exact measurable_lintegral_freeze (Pr.map N) hGm
    exact this
  rw [hmapY, lintegral_map hmeas_outer hX] at hfr
  have hQint : ∀ g : Ω → ℝ≥0∞, ∫⁻ ω, g ω ∂(cond Pr E) = (Pr E)⁻¹ * ∫⁻ ω in E, g ω ∂Pr := by
    intro g
    show ∫⁻ ω, g ω ∂((Pr E)⁻¹ • Pr.restrict E) = _
    rw [lintegral_smul_measure]
    rfl
  have hLq : ∫⁻ ω, F (ω, (N ω).restrict (Rg ω)ᶜ) ∂(cond Pr E) =
      ∫⁻ ω, ∫⁻ y, F (ω, y.restrict (Rg ω)ᶜ) ∂(Pr.map N) ∂(cond Pr E) := by
    rw [← lintegral_congr_ae hlhs]
    refine hfr.trans (lintegral_congr fun ω => ?_)
    exact hinner ω
  rw [hQint, hQint] at hLq
  have hc0 : (Pr E)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hPrE
  have hct : (Pr E)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  exact (ENNReal.mul_right_inj hc0 hct).1 hLq

include hN hN' hI1 hI2 in
/-- Several walks explored one after another (a), Step 4, for `P(T < ∞) = 1`. -/
theorem multi_cond_of_ae_fin (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ)
    (hR : Measurable fun ω => P.envFinal (N ω)) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (multiFilt 𝒢₀ P.junk Pr h𝒢 (fun ω => P.envFinal (N ω)) hR) T)
    (hfin : Pr {ω | T ω ≠ ⊤} = 1)
    {F : Ω × Measure (CycS I d β) → ℝ≥0∞}
    (hF : Measurable[hT.measurableSpace.prod inferInstance] F) :
    ∫⁻ ω, F (ω, (N ω).restrict (cycRegionStop P N T ω)ᶜ) ∂Pr =
      ∫⁻ ω, ∫⁻ ν, F (ω, ν.restrict (cycRegionStop P N T ω)ᶜ) ∂(Pr.map N) ∂Pr := by
  have hPr := hN.isProbabilityMeasure
  have hm : MeasurableSet {ω | T ω ≠ ⊤} := hT.measurableSpace_le _ (measurableSet_ne_top hT)
  have hc : Pr {ω | T ω ≠ ⊤}ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hm, hfin]; simp
  have hr : Pr.restrict {ω | T ω ≠ ⊤} = Pr := by
    rw [Measure.restrict_eq_self_of_ae_mem]
    exact (measure_eq_zero_iff_ae_notMem.1 hc).mono fun ω h => by simpa using h
  have := multi_cond_restrict P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hR hT hF
  rwa [hr] at this

end main

end ElboimSly.Cyclic

end
