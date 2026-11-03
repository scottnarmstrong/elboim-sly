/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlanCouplingDef
public import ElboimSly.Foundations.Cyclic.CycHitCov
public import Mathlib

/-!
# The recentred environment path has the law of the cyclic walk

Plan-level coupling after a stopping time, proof of (b): "First, for every fixed datum
`δ' = (ι', u', q', σ')`, `Law(P^N_{δ'} - u') = Law(W)`."
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

theorem law_envWalk {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {Pr : Measure Ω}
    {Pr' : Measure Ω'} {N : Ω → Measure (CycS I d β)} {M : Ω' → Measure (RingSpace d β)}
    (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
    (hM : IsPoissonPointProcess M (ringIntensity d β) Pr') (δ : CycData I d) :
    Pr.map (fun ω (s : ℝ≥0) => envWalk (N ω) δ s - δ.start) =
      Pr'.map (fun ω' => walkMap (M ω')) := by
  have h₁ := isPoissonPointProcess_envMeasure hN δ
  set N₂ : Ω → Measure (RingSpace d β) :=
    fun ω => hitShift (δ.start, δ.sgn * δ.phase) (envMeasure (N ω) δ) with hN₂def
  have hN₂m : Measurable N₂ :=
    measurable_hitShift.comp (measurable_const.prodMk h₁.measurable)
  have hN₂ : IsPoissonPointProcess N₂ (ringIntensity d β) Pr :=
    h₁.of_map_eq hN₂m (law_hitShift h₁ _)
  have hae : (fun ω (s : ℝ≥0) => envWalk (N ω) δ s - δ.start) =ᵐ[Pr] fun ω => walkMap (N₂ ω) := by
    filter_upwards [CycSchemeEnv.ae_cycGood' hN, h₁.ae_mem_lfSet] with ω hg hlf
    funext s
    have hg' : Good (cycSlice δ.copy (N ω)) := hg δ.copy
    have hgm : Good (envMeasure (N ω) δ) := good_envMeasure hg'
    have e1 : envWalk (N ω) δ s = ElboimSly.cycWalk (envMeasure (N ω) δ) δ.start
        (δ.sgn * δ.phase) (s : ℝ) := by
      unfold envWalk
      rw [ite_eq_left hg, envFn_eq_fwdTraj hg', cycWalk_of_nonneg hgm _ _ (NNReal.coe_nonneg s)]
    have e2 : N₂ ω = (envMeasure (N ω) δ).map (hitPhi δ.start (δ.sgn * δ.phase)) := by
      simp only [hN₂def, hitShift]
      rw [tau_of_mem _ hlf]
    have hgx : Good (N₂ ω) := by
      rw [e2]; exact good_map_hitPhi hgm _ _
    classical
    show _ = ElboimSly.cycWalk (if Good (N₂ ω) then N₂ ω else 0) 0 0 (s : ℝ)
    rw [ite_eq_left hgx, e2, cycWalk_map_hitPhi hgm _ _ (NNReal.coe_nonneg s), e1]
  have hWm : Measurable fun ω (s : ℝ≥0) => envWalk (N ω) δ s - δ.start := by
    refine measurable_pi_iff.2 fun s => ?_
    have := (measurable_pi_apply s).comp
      (measurable_envWalk.comp (hN.measurable.prodMk (measurable_const (a := δ))))
    exact this.sub_const _
  rw [Measure.map_congr hae]
  have e1 : Pr.map (fun ω => walkMap (N₂ ω)) = (Pr.map N₂).map walkMap :=
    (Measure.map_map measurable_walkMap hN₂m).symm
  have e2 : Pr'.map (fun ω' => walkMap (M ω')) = (Pr'.map M).map walkMap :=
    (Measure.map_map measurable_walkMap hM.measurable).symm
  rw [e1, e2, hN₂.map_eq_map hM]

end ElboimSly.Cyclic

end
