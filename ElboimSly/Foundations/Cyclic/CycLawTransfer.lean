/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenLawMeas
public import ElboimSly.Foundations.Cyclic.CycDrivenLawPair
public import ElboimSly.Foundations.Cyclic.CycMultiDriven
public import Mathlib

/-!
# Equality in law of functionals of the environment and driven final records

Several walks explored one after another (b), used in driven and environment walks agree in law, the constructions of the regenerated walk and
ES22 Lemma 2.1 (e).

`law_transfer`: let `Φ` be a measurable function of the record. If `Φ(ρ^𝒫(ν)) = A(ν)` for good
`ν` and `Φ(ρ^𝒫(X)) = B(Ñ)` for almost every driver `Ñ` (in law), with `A`, `B` measurable, then
`Law(B(Ñ)) = Law(A(N))`, for every Poisson point process `N` (almost surely good) and `Ñ`, with no
independent copies required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

theorem map_prod_snd_comp' {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (W : Measure α)
    [IsProbabilityMeasure W] {G : α → γ} (hG : Measurable G) :
    (W.prod W).map (G ∘ Prod.snd) = W.map G := by
  have := Measure.map_map hG measurable_snd (μ := W.prod W)
  rw [Measure.map_snd_prod, measure_univ, one_smul] at this
  exact this.symm

variable {I : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] {J : Type} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]

theorem law_transfer {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) (P : CycPlan I d β)
    (hj : ∀ k, Measurable (jx k)) (hK : 0 < P.K)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {Pe : Measure Ω} {Pd : Measure Ω'}
    {N : Ω → Measure (CycS I d β)} {Nd : Ω' → Measure (DrvS d J)}
    (hN : IsPoissonPointProcess N (cycIntensity I d β) Pe)
    (hNd : IsPoissonPointProcess Nd (drvIntensity d J) Pd)
    (hgood : ∀ᵐ ω ∂Pe, CycGood (N ω)) {γ : Type*} [MeasurableSpace γ]
    {Φ : CycRec I d → γ} (hΦ : Measurable Φ)
    {A : Measure (CycS I d β) → γ} (_hA : Measurable A)
    {B : Measure (DrvS d J) → γ} (hB : Measurable B)
    (hAe : ∀ ν : Measure (CycS I d β), CycGood ν → Φ (P.envFinal ν) = A ν)
    (hBd : ∀ᵐ Ñ ∂(Pd.map Nd), Φ (P.drivenFinal jx (fun j => srwPath Ñ j)) = B Ñ) :
    Pd.map (fun ω => B (Nd ω)) = Pe.map (fun ω => A (N ω)) := by
  have := hN.isProbabilityMeasure
  have := hNd.isProbabilityMeasure
  obtain ⟨hs2e, hs1e, hie⟩ := hN.indep_pair
  obtain ⟨hs2d, hs1d, hid⟩ := hNd.indep_pair
  obtain ⟨⟨g, hg, hgae⟩, hlaw⟩ := cyc_multi_driven (jx := jx) j0 P hj hK hs2e hs1e hie hs2d hs1d hid
  set We := Pe.map N with hWe
  set Wd := Pd.map Nd with hWd
  have : IsProbabilityMeasure We := by rw [hWe]; infer_instance
  have : IsProbabilityMeasure Wd := by rw [hWd]; infer_instance
  have hgoodE : ∀ᵐ ν ∂We, CycGood ν := by
    rw [hWe, ae_map_iff hN.measurable.aemeasurable measurableSet_cycGood]
    exact hgood
  have hgoodP : ∀ᵐ p ∂(We.prod We), CycGood p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := We) (ν := We)).ae hgoodE
  have hBdP : ∀ᵐ p ∂(Wd.prod Wd),
      Φ (P.drivenFinal jx (fun j => srwPath p.2 j)) = B p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := Wd) (ν := Wd)).ae hBd
  have hMenv := P.measurable_envFinalOr (CycRec.empty)
  have hlaw' : (Wd.prod Wd).map g = (We.prod We).map (P.envFinalOr CycRec.empty ∘ Prod.snd) := by
    rw [Measure.map_congr hgae, hlaw]
    refine Measure.map_congr ?_
    filter_upwards [hgoodP] with p hp
    exact (P.envFinalOr_of_good _ hp).symm
  have h1 := congrArg (fun m => m.map Φ) hlaw'
  rw [Measure.map_map hΦ hg, Measure.map_map hΦ (hMenv.comp measurable_snd)] at h1
  have hL : (Wd.prod Wd).map (Φ ∘ g) = Pd.map (fun ω => B (Nd ω)) := by
    have e1 : (Wd.prod Wd).map (Φ ∘ g) = (Wd.prod Wd).map (B ∘ Prod.snd) := by
      refine Measure.map_congr ?_
      filter_upwards [hgae, hBdP] with p hp1 hp2
      simp only [Function.comp_apply]
      rw [hp1]
      exact hp2
    rw [e1, map_prod_snd_comp' Wd hB, hWd, Measure.map_map hB hNd.measurable]
    rfl
  have hR : (We.prod We).map (Φ ∘ (P.envFinalOr CycRec.empty ∘ Prod.snd)) =
      Pe.map (fun ω => A (N ω)) := by
    rw [← Function.comp_assoc, map_prod_snd_comp' We (hΦ.comp hMenv), hWe,
      Measure.map_map (hΦ.comp hMenv) hN.measurable]
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    simp only [Function.comp_apply]
    rw [P.envFinalOr_of_good _ hω, hAe _ hω]
  rw [← hL, ← hR, h1]

end ElboimSly.Cyclic

end
