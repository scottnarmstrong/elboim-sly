/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvFinal
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvMain
public import ElboimSly.Foundations.PPP.Exploration.ExplRunOf
public import Mathlib

/-!
# Several walks explored one after another (b): the driven counterpart

Several walks explored one after another (b). The environment final record `ρ^𝒫(N)` and the driven
final record `ρ^𝒫(𝐗)` have the same law on `CycRec`, and `ρ^𝒫(𝐗)` is almost surely equal to a
measurable map.

* `ae_recPhi_eq_envFinal`: `ρ^𝒫(N) = Φ(H_∞)` a.s. (the environment scheme (b), `s_∘ = ∞`);
* `ae_recPhi_drv_eq_drivenFinal`: `ρ^𝒫(𝐗) = Φ(Ψ_∞(H'_∞))` a.s. (the driving scheme (c));
* `cyc_multi_driven`: the law identity, from the driving scheme (d) (`drvScheme_law_Hinf`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

namespace CycSchemeEnv

variable {P : CycPlan I d β} {U : Type*} [MeasurableSpace U] {Ω : Type*} [MeasurableSpace Ω]
  {Pr : Measure Ω}

/-- The environment scheme (b) with `s_∘ = ∞`: almost surely `ρ^𝒫(N) = Φ(H_∞)`. -/
theorem ae_recPhi_eq_envFinal (run : ExplRun (cycScheme P ⊤ U) Pr) (hK : 0 < P.K) :
    ∀ᵐ ω ∂Pr, recPhi P ⊤ U P.junk (run.Hinf ω) = P.envFinal (run.N ω) := by
  filter_upwards [goodEv_ae run] with ω hω
  rw [recPhi_eq_recLim run P.junk hK hω,
    (trajOf run ω hω).recLim_eq_cycRecAt P.junk hω.1 hK rfl]
  simp [cycRecAt]

end CycSchemeEnv

section main

variable {J : Type} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) (P : CycPlan I d β) (hj : ∀ k, Measurable (jx k))
  {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {Pe : Measure Ω} {Pd : Measure Ω'}

include j0 hj in
/-- Several walks explored one after another (b): the driven final record `ρ^𝒫(𝐗)` (the walks `X_j`
built from a Poisson point process `Nd` on `J × Dir × ℝ`) is almost surely a measurable map, and has
the law of the environment final record `ρ^𝒫(N)` on `CycRec`. The runs of the explorations need an
independent copy of each process (`N'`, `Nd'`), as in the source setting of the theorem. -/
theorem cyc_multi_driven (hK : 0 < P.K)
    {N N' : Ω → Measure (CycS I d β)}
    (hN : IsPoissonPointProcess N (cycIntensity I d β) Pe)
    (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pe) (hind : IndepFun N' N Pe)
    {Nd Nd' : Ω' → Measure (DrvS d J)}
    (hNd : IsPoissonPointProcess Nd (drvIntensity d J) Pd)
    (hNd' : IsPoissonPointProcess Nd' (drvIntensity d J) Pd) (hindd : IndepFun Nd' Nd Pd) :
    (∃ g : Ω' → CycRec I d, Measurable g ∧
      g =ᵐ[Pd] fun ω => P.drivenFinal jx (fun j => srwPath (Nd ω) j)) ∧
    Pd.map (fun ω => P.drivenFinal jx (fun j => srwPath (Nd ω) j)) =
      Pe.map (fun ω => P.envFinal (N ω)) := by
  have := hN.isProbabilityMeasure
  have := hNd.isProbabilityMeasure
  let run : ExplRun (cycScheme P ⊤ Unit) Pe :=
    ExplRun.ofPPP (cycScheme P ⊤ Unit) (u := fun _ => ()) measurable_const hN
      (indepFun_const_left () N) hN'
      (hind.comp measurable_id (measurable_prodMk_left (x := ())))
  let run' : ExplRun (drvScheme j0 P ⊤ Unit hj) Pd :=
    ExplRun.ofPPP (drvScheme j0 P ⊤ Unit hj) (u := fun _ => ()) measurable_const hNd
      (indepFun_const_left () Nd) hNd'
      (hindd.comp measurable_id (measurable_prodMk_left (x := ())))
  have hEnv := CycSchemeEnv.ae_recPhi_eq_envFinal run hK
  have hNae : ∀ᵐ ω ∂Pe, run.N ω = N ω := hN.tau_comp_ae_eq
  have hDrv := CycSchemeGen.ae_recPhi_drvPsiInf j0 P ⊤ hj run' hK rfl
  have hNdae : ∀ᵐ ω ∂Pd, run'.N ω = Nd ω := hNd.tau_comp_ae_eq
  have hEnv' : (fun ω => CycSchemeEnv.recPhi P ⊤ Unit P.junk (run.Hinf ω)) =ᵐ[Pe]
      fun ω => P.envFinal (N ω) := by
    filter_upwards [hEnv, hNae] with ω h1 h2
    rw [h1]; exact congrArg _ h2
  have hDrv' : (fun ω => CycSchemeEnv.recPhi P ⊤ Unit P.junk
      (drvPsiInf (jx := jx) (β := β) j0 P ⊤ (run'.Hinf ω))) =ᵐ[Pd]
      fun ω => P.drivenFinal jx (fun j => srwPath (Nd ω) j) := by
    filter_upwards [hDrv, hNdae] with ω h1 h2
    rw [h1, h2]
  have hmΦ := CycSchemeEnv.measurable_recPhi (P := P) (sc := ⊤) (U := Unit) P.junk
  have hmΨ := measurable_drvPsiInf (U := Unit) (β := β) (jx := jx) j0 P ⊤ hj
  refine ⟨⟨_, hmΦ.comp (hmΨ.comp run'.measurable_Hinf), hDrv'⟩, ?_⟩
  have hu : Pd.map run'.u = Pe.map run.u := by
    show Pd.map (fun _ => ()) = Pe.map (fun _ => ())
    rw [Measure.map_const, Measure.map_const, measure_univ, measure_univ]
  have hlaw := drvScheme_law_Hinf j0 P ⊤ hj run run' hu
  have e1 : Pd.map (fun ω => CycSchemeEnv.recPhi P ⊤ Unit P.junk
      (drvPsiInf (jx := jx) (β := β) j0 P ⊤ (run'.Hinf ω))) =
      (Pd.map (fun ω => drvPsiInf (jx := jx) (β := β) j0 P ⊤ (run'.Hinf ω))).map
        (CycSchemeEnv.recPhi P ⊤ Unit P.junk) :=
    (Measure.map_map hmΦ (hmΨ.comp run'.measurable_Hinf)).symm
  have e2 : Pe.map (fun ω => CycSchemeEnv.recPhi P ⊤ Unit P.junk (run.Hinf ω)) =
      (Pe.map run.Hinf).map (CycSchemeEnv.recPhi P ⊤ Unit P.junk) :=
    (Measure.map_map hmΦ run.measurable_Hinf).symm
  rw [← Measure.map_congr hDrv', ← Measure.map_congr hEnv', e1, e2, hlaw]

end main

end ElboimSly.Cyclic

end
