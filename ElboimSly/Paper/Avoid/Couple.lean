/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.CoupleAux
public import Mathlib

/-!
# ES22 §4: Lemma 2.1 for the regenerated walk, the form used in §4–§5

ES22 Lemma 2.1 (supplement to ES22 §4, ES22 §5; from ES22 Lemma 2.1).

In the setting `Es4Setting`, for an a.s. finite `(avoidFilt)`-stopping time `T` there is a
`PPP(# ⊗ μ_β)` `M` (the environment after `T`), whose regenerated walk (made everywhere good by
`cycNgood`) is `W̃ = avoidPath (cycNgood M)`, such that:

* (a) `W̃` is a measurable process with right-continuous paths, independent of `ℱ_T`, with the
  law of `W`;
* (b) a.s., for `t = T`: `W(t + s) - W(t) = W̃(s)` for `t + s ≤ thit(t)`; if `α(t) < t`, the first
  regeneration time of `W̃` (`cycTreg` of the first copy of `M`) exceeds `thit(t) - t`;
  and `thit(t) = ∞` if `α(t) = t`;
* (c) a.s., `thit(t)` is the infimum of the times `s > t` such that some `s' ∈ s + βℤ` with
  `α(t) < s' < t` has `‖W(t) + W̃(s - t) - W(s')‖ ≤ 1`.

Deviation from the written proof: the environment `M` is exposed, because "the first regeneration time
of `W̃`" is `cycTreg` of its first copy.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ}
  {Ω : Type} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ d β)}

/-- **ES22 Lemma 2.1** (Lemma 2.1 of ES22 for the regenerated walk, form used in §4–§5). -/
theorem es4_couple (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (avoidFilt 𝒢₀ S.space) T) (hfin : ∀ᵐ ω ∂Pr, T ω ≠ ⊤) :
    ∃ M : Ω → Measure (CycS ℕ d β), IsPoissonPointProcess M (cycIntensity ℕ d β) Pr ∧
      (Measurable (avoidPath (cycNgood M)) ∧ (∀ ω, IsRCPath (avoidPath (cycNgood M) ω)) ∧
        Indep hT.measurableSpace
          (MeasurableSpace.comap (avoidPath (cycNgood M)) inferInstance) Pr ∧
        Pr.map (avoidPath (cycNgood M)) = Pr.map (avoidPath N)) ∧
      (∀ᵐ ω ∂Pr, ∀ t : ℝ≥0, T ω = t →
        (∀ s : ℝ≥0, ENNReal.ofReal ((t : ℝ) + s) ≤ avoidThit N ω (t : ℝ) →
          avoidWalk N ω ((t : ℝ) + s) - avoidWalk N ω (t : ℝ) = avoidPath (cycNgood M) ω s) ∧
        (regenStart (avoidEnv N ω) (t : ℝ) < t →
          ∀ s : ℝ≥0, ENNReal.ofReal ((t : ℝ) + s) ≤ avoidThit N ω (t : ℝ) →
            (s : ℝ≥0∞) < cycTreg (avoidEnv M ω 0)) ∧
        (regenStart (avoidEnv N ω) (t : ℝ) = t → avoidThit N ω (t : ℝ) = ⊤) ∧
        avoidThit N ω (t : ℝ) =
          ⨅ s ∈ {s : ℝ | (t : ℝ) < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
            regenStart (avoidEnv N ω) (t : ℝ) < s' ∧ s' < t ∧
            ‖avoidWalk N ω (t : ℝ) + avoidPath (cycNgood M) ω (s - t).toNNReal -
              avoidWalk N ω s'‖ ≤ 1}, ENNReal.ofReal s) := by
  have hPr := S.space.ppp.isProbabilityMeasure
  have hfin1 : Pr {ω | T ω ≠ ⊤} = 1 :=
    (prob_compl_eq_zero_iff (hT.measurableSpace_le _ (measurableSet_ne_top hT))).1 (ae_iff.1 hfin)
  obtain ⟨M, hM, -, -, -, hind, hae⟩ := cyc_hit_couple_regen 𝒢₀ S.space.ppp S.space.ppp'
    S.space.indep S.space.indep' S.space.le hT
  have hM1 := ae_avoidPath_cycNgood hM
  have hN1 := ae_avoidPath_cycNgood S.space.ppp
  have hfg : avoidPath (cycNgood M) =ᵐ[Pr] fun ω => regW (M ω) :=
    hM1.mono fun ω h => h.1
  have hind' := hind hfin1
  refine ⟨M, hM, ⟨measurable_avoidPath_cycNgood hM.measurable,
    fun ω => isRCPath_avoidPath (cycGood_cycNgood M ω),
    indep_comap_congr hfg hind'.1, ?_⟩, ?_⟩
  · rw [Measure.map_congr hfg, hind'.2]
    exact Measure.map_congr (hN1.mono fun ω h => h.2.symm)
  · filter_upwards [hae, hM1] with ω hω hMω t ht
    obtain ⟨hMg, h1, h2, h3, h4, h5⟩ := hω.2 t ht
    have hW : ∀ s : ℝ≥0, avoidPath (cycNgood M) ω s = regenWalk (slices (M ω)) (s : ℝ) := by
      intro s
      rw [hMω.1, regW_eq_regenWalk hMg]
    have hWN : ∀ x : ℝ, avoidWalk N ω x = regenWalk (slices (N ω)) x := fun x => by
      simp only [avoidWalk, avoidEnv_eq_cycSlice]
    have hTh : avoidThit N ω (t : ℝ) = cycThit (slices (N ω)) (t : ℝ) := by
      simp only [avoidThit, avoidEnv_eq_cycSlice]
    have hSt : regenStart (avoidEnv N ω) (t : ℝ) = regenStart (slices (N ω)) (t : ℝ) := by
      simp only [avoidEnv_eq_cycSlice]
    have hE0 : avoidEnv M ω 0 = slices (M ω) 0 := by simp only [avoidEnv_eq_cycSlice]
    simp only [hW, hWN, hTh, hSt, hE0]
    refine ⟨h1, h2, h3, ?_⟩
    rw [h5]
    refine iInf_congr fun s => iInf_congr_Prop ?_ fun _ => rfl
    refine and_congr_right fun hts => ?_
    rw [Real.coe_toNNReal _ (sub_nonneg.2 hts.le)]

end ElboimSly.Paper

end
