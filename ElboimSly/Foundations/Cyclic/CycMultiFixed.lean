/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiRun
public import ElboimSly.Foundations.Cyclic.CycMultiGen
public import Mathlib

/-!
# Several walks explored one after another (a), Step 1: fixed times

Several walks explored one after another (a), Step 1. For a fixed `s ∈ [0, ∞)` the measure
`Ñ_s = N|_{S ∖ R_s} + N'|_{R_s}` is independent of `ℱ^𝒫_s` and has the law of `N`
(`multi_fixed_time`). Run the environment scheme with global horizon `s` and auxiliary variable
`U = id : (Ω, 𝒜) → (Ω, 𝒢₀)`; by sequential first-point exploration (g) `Ñ_κ` is independent of `𝒢_κ`
(`CycSchemeEnv`/`cyc_env_scheme_c`), `R_s = 𝒵_κ` a.s., and `𝒢₀`, `σ(Rec(s'))` are a.s. contained
in `𝒢_κ`; the `π`-`λ` lemma `indep_of_generators` extends this to `ℱ_s`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}

section tilde

variable {U : Type*} [MeasurableSpace U] {sc : ℝ≥0∞} (run : ExplRun (cycScheme P sc U) Pr)

theorem ntilKappa_eq (ω : Ω) :
    run.NtilKappa (CycSchemeEnv.kappa run) ω =
      tildeMeasure run.N run.N' (CycSchemeEnv.Zkappa run) ω := by
  induction hκ : CycSchemeEnv.kappa run ω using ENat.recTopCoe with
  | top =>
    simp only [ExplRun.NtilKappa, CycSchemeEnv.Zkappa, tildeMeasure, hκ, ENat.recTopCoe_top]
    rfl
  | coe j =>
    simp only [ExplRun.NtilKappa, CycSchemeEnv.Zkappa, tildeMeasure, hκ, ENat.recTopCoe_natCast]
    rfl

theorem ae_ntilKappa_eq (hK : 0 < P.K) {s : ℝ≥0} (hsc : sc = s) {N N' : Ω → Measure (CycS I d β)}
    (hN : ∀ᵐ ω ∂Pr, run.N ω = N ω) (hN' : ∀ᵐ ω ∂Pr, run.N' ω = N' ω) :
    ∀ᵐ ω ∂Pr, run.NtilKappa (CycSchemeEnv.kappa run) ω =
      tildeMeasure N N' (cycRegionAt P N s) ω := by
  filter_upwards [CycSchemeEnv.ae_Zkappa_eq run hK, hN, hN'] with ω hZ h1 h2
  rw [ntilKappa_eq]
  unfold tildeMeasure cycRegionAt
  rw [hZ]
  unfold CycSchemeEnv.cycRecAt
  rw [h1, h2]
  subst hsc
  simp

end tilde

section main

variable {N N' : Ω → Measure (CycS I d β)}
  (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
/-- Several walks explored one after another (a), Step 1 (fixed times): `Ñ_s` is independent of
`ℱ^𝒫_s` with the law of `N`. -/
theorem multi_fixed_time (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ)
    (hR : Measurable fun ω => P.envFinal (N ω)) (s : ℝ≥0)
    {A : Set Ω} (hA : MeasurableSet[cycFiltration Pr 𝒢₀ (fun ω => P.envFinal (N ω)) s] A)
    {F : Set (Measure (CycS I d β))} (hF : MeasurableSet F) :
    Pr (A ∩ {ω | tildeMeasure N N' (cycRegionAt P N s) ω ∈ F}) = Pr A * (Pr.map N) F := by
  have := hN.isProbabilityMeasure
  have : Nonempty (CycEntry I d) := ⟨P.junk⟩
  set run := multiRun 𝒢₀ P (s : ℝ≥0∞) h𝒢 hN hN' hI1 hI2 with hrun
  obtain ⟨hκ, -, hY⟩ := CycSchemeEnv.cyc_env_scheme_c run hK
  obtain ⟨Y', hY'm, hY'e⟩ := hY s le_rfl
  have hNae : ∀ᵐ ω ∂Pr, run.N ω = N ω := hN.tau_comp_ae_eq
  have hN'ae : ∀ᵐ ω ∂Pr, run.N' ω = N' ω := hN'.tau_comp_ae_eq
  have hNt := ae_ntilKappa_eq P run hK rfl hNae hN'ae
  have hmap : Pr.map run.N = Pr.map N := Measure.map_congr hNae
  have hNtm : Measurable (run.NtilKappa (CycSchemeEnv.kappa run)) := run.measurable_NtilKappa hκ
  have hYm : Measurable fun ω => CycRec.trunc s (P.envFinal (N ω)) :=
    measurable_trunc.comp (hR.prodMk measurable_const)
  rw [cycFiltration_eq 𝒢₀ P.junk Pr] at hA
  have hmain : Pr (A ∩ run.NtilKappa (CycSchemeEnv.kappa run) ⁻¹' F) = Pr A * (Pr.map N) F := by
    refine indep_of_generators 𝒢₀ Pr h𝒢 _ hYm _ (Pr.map N) ?_ hNtm hA hF
    intro A' hA' B hB F' hF'
    obtain ⟨B0, hB0, rfl⟩ := hB
    have hG : run.InGkappa (CycSchemeEnv.kappa run)
        ((run.u ⁻¹' (show Set (GSpace 𝒢₀) from A')) ∩ Y' ⁻¹' B0) :=
      inGkappa_inter run (inGkappa_u run hκ (show MeasurableSet (show Set (GSpace 𝒢₀) from A') from hA'))
        (hY'm B0 hB0)
    have hind : Pr (((run.u ⁻¹' (show Set (GSpace 𝒢₀) from A')) ∩ Y' ⁻¹' B0) ∩ run.NtilKappa (CycSchemeEnv.kappa run) ⁻¹' F') = Pr ((run.u ⁻¹' (show Set (GSpace 𝒢₀) from A')) ∩ Y' ⁻¹' B0) * (Pr.map run.N) F' := run.stopping_indep hκ hG hF'
    have hGae : (A' ∩ (fun ω => CycRec.trunc s (P.envFinal (N ω))) ⁻¹' B0) =ᵐ[Pr]
        ((run.u ⁻¹' (show Set (GSpace 𝒢₀) from A')) ∩ Y' ⁻¹' B0) := by
      filter_upwards [hNae, hY'e] with ω h1 h2
      apply propext
      simp only [mem_inter_iff, mem_preimage]
      rw [h2, h1]
      rfl
    rw [measure_congr (hGae.inter Filter.EventuallyEq.rfl), hind, hmap, measure_congr hGae]
  rw [← hmain]
  refine measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl ?_)
  filter_upwards [hNt] with ω hω
  apply propext
  simp only [mem_preimage]
  rw [hω]

end main

end ElboimSly.Cyclic

end
