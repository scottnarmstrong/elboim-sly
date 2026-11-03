/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenLawBridge
public import ElboimSly.Foundations.Cyclic.CycDrivenLawPair
public import ElboimSly.Foundations.Cyclic.CycMultiDriven
public import Mathlib

/-!
# Driven and environment walks agree in law

Driven and environment walks agree in law. ES22 §2 ("it is clear that the walk `W` defined in the above
way has the same law as the cyclic random walk", finding F05).

* `cyc_driven_law`: `Law((W^X(s ∧ t_reg^X))_s, t_reg^X) = Law((W(s ∧ t_reg))_s, t_reg)`, where `X`
  is the canonical SRW of a Poisson point process `N₀` on `𝒟 × ℝ` and `W` the cyclic walk of a
  Poisson point process `ν` on `S_β`.
* `cyc_driven_law_general`: the general statement, for every exploration plan and every driving
  assignment, is `cyc_multi_driven` (several walks explored one after another (b)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem map_prod_snd_comp {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (W : Measure α)
    [IsProbabilityMeasure W] {G : α → γ} (hG : Measurable G) :
    (W.prod W).map (G ∘ Prod.snd) = W.map G := by
  have := Measure.map_map hG measurable_snd (μ := W.prod W)
  rw [Measure.map_snd_prod, measure_univ, one_smul] at this
  exact this.symm

/-- **driven and environment walks agree in law**: the pair `((W^X(s ∧ t_reg^X))_{s ≥ 0}, t_reg^X)` of the driven walk
of the canonical SRW has the law of the pair `((W(s ∧ t_reg))_{s ≥ 0}, t_reg)` of the cyclic
walk. -/
theorem cyc_driven_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Pe : Measure Ω} {Pd : Measure Ω'} {ν : Ω → Measure (RingSpace d β)}
    {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe)
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd) :
    Pd.map (fun ω => drivenPair β.toNNReal (canonical d N₀ ω)) =
      Pe.map (fun ω => cycPair (ν ω)) := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have hNe := isPPP_envUnit hν
  have hNd := isPPP_drvUnit hN₀
  have := hNe.isProbabilityMeasure
  have := hNd.isProbabilityMeasure
  set P := regionPlan d β with hP
  obtain ⟨hs2e, hs1e, hie⟩ := hNe.indep_pair
  obtain ⟨hs2d, hs1d, hid⟩ := hNd.indep_pair
  have hK : 0 < P.K := by
    show (0 : ℕ∞) < 1
    norm_num
  obtain ⟨⟨g, hg, hgae⟩, hlaw⟩ := cyc_multi_driven (jx := fun _ _ => ()) () P
    (fun _ => measurable_const) hK hs2e hs1e hie hs2d hs1d hid
  set We := Pe.map (fun ω => (ν ω).map (Prod.mk ())) with hWe
  set Wd := Pd.map (fun ω => drvUnit (N₀ ω)) with hWd
  have : IsProbabilityMeasure We := by rw [hWe]; infer_instance
  have : IsProbabilityMeasure Wd := by rw [hWd]; infer_instance
  -- goodness
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := Interchange.ae_good hν
  have hgoodE : ∀ᵐ N ∂We, CycGood N := by
    rw [hWe, ae_map_iff hNe.measurable.aemeasurable measurableSet_cycGood]
    filter_upwards [hgood] with ω hω using cycGood_map_unit hω
  have hgoodP : ∀ᵐ p ∂(We.prod We), CycGood p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := We) (ν := We)).ae hgoodE
  -- coincidence-freeness
  have hWdppp : IsPoissonPointProcess (fun Ñ : Measure ((Dir d × Unit) × ℝ) => Ñ)
      (drvIntensity d Unit) Wd := hNd.isPPPLaw_map
  have hcf : ∀ᵐ Ñ ∂Wd, (srwPath Ñ ()).1.fn ∈ CycCF β.toNNReal := by
    have := ae_canonical_mem_cycCF (subProcess_ppp (ι := Unit) hWdppp ()) β.toNNReal hb
    filter_upwards [this] with Ñ hÑ
    exact hÑ
  have hcfP : ∀ᵐ p ∂(Wd.prod Wd), (srwPath p.2 ()).1.fn ∈ CycCF β.toNNReal :=
    (Measure.quasiMeasurePreserving_snd (μ := Wd) (ν := Wd)).ae hcf
  -- the measurable maps
  have hF := measurable_firstPiece (I := Unit) (d := d) P.junk
  have hMenv := P.measurable_envFinalOr (CycRec.empty)
  have hGd : Measurable fun Ñ : Measure ((Dir d × Unit) × ℝ) =>
      drivenPair β.toNNReal (srwPath Ñ ()).1.fn := measurable_drivenPair hb ()
  -- the two sides of `hlaw`, composed with the first world-line
  have hlaw' : (Wd.prod Wd).map g = (We.prod We).map (P.envFinalOr CycRec.empty ∘ Prod.snd) := by
    rw [Measure.map_congr hgae, hlaw]
    refine Measure.map_congr ?_
    filter_upwards [hgoodP] with p hp
    exact (P.envFinalOr_of_good _ hp).symm
  have h1 := congrArg (fun m => m.map (firstPiece P.junk)) hlaw'
  rw [Measure.map_map hF hg, Measure.map_map hF (hMenv.comp measurable_snd)] at h1
  have hL : (Wd.prod Wd).map (firstPiece P.junk ∘ g) =
      Pd.map (fun ω => drivenPair β.toNNReal (canonical d N₀ ω)) := by
    have e1 : (Wd.prod Wd).map (firstPiece P.junk ∘ g) =
        (Wd.prod Wd).map ((fun Ñ => drivenPair β.toNNReal (srwPath Ñ ()).1.fn) ∘ Prod.snd) := by
      refine Measure.map_congr ?_
      filter_upwards [hgae, hcfP] with p hp1 hp2
      simp only [Function.comp_apply]
      rw [hp1]
      exact firstPiece_drivenFinal hp2
    rw [e1, map_prod_snd_comp Wd hGd, hWd, Measure.map_map hGd hNd.measurable]
    congr 1
    funext ω
    have : (srwPath (drvUnit (N₀ ω)) ()).1.fn = canonical d N₀ ω :=
      funext (srwPath_drvUnit_fn (N₀ ω))
    simp only [Function.comp_apply, this]
  -- the environment side
  have hR : (We.prod We).map (firstPiece P.junk ∘ (P.envFinalOr CycRec.empty ∘ Prod.snd)) =
      Pe.map (fun ω => cycPair (ν ω)) := by
    rw [← Function.comp_assoc, map_prod_snd_comp We (hF.comp hMenv), hWe,
      Measure.map_map (hF.comp hMenv) hNe.measurable]
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    simp only [Function.comp_apply]
    rw [P.envFinalOr_of_good _ (cycGood_map_unit hω)]
    have h2 := firstPiece_envFinal (d := d) (β := β) (N := (ν ω).map (Prod.mk ()))
      (by rw [cycSlice_map_unit]; exact hω)
    rw [h2, cycSlice_map_unit]
    rfl
  rw [← hL, ← hR, h1]

end ElboimSly.Cyclic

end
