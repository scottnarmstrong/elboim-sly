/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.FastDisp
public import ElboimSly.Paper.Step.AvoidSetting
public import ElboimSly.Paper.Step.RegenMeas
public import ElboimSly.Paper.Step.StopHist2
public import ElboimSly.Paper.Step.StopHit
public import ElboimSly.Paper.Step.ZetaSRW
public import ElboimSly.Foundations.Cyclic.CycFast
public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import ElboimSly.Foundations.PPP.Existence
public import Mathlib

/-!
# ES22 Claim 2.3 for the driven regenerated walk

ES22 Claim 2.3; ES22 Lemma 7.1 Step 5.

`stepFast_prob`: for any SRW `Y` with driving paths and `W = W_reg^{θ_a Y}`,
`P(τ_fast(W; L) ≤ T) ≤ C T² e^{-cL}`. The event is a measurable event of the path (by the rational
form of `τ_fast`), so its probability is the one of the regenerated walk of a Poisson environment
(`stepReg_law`), where ES22 Claim 2.3 (`cyc_fast`) applies.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem isRegularPath_of_isRegPath {x : ℝ≥0 → Fin d → ℤ} (hx : IsRegPath x) : IsRegularPath x := by
  intro t
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hx.rc t)
  have htu : t < u := hu
  refine ⟨u - t, tsub_pos_of_lt htu, fun s hts hst => hsub ⟨hts, ?_⟩⟩
  rwa [add_tsub_cancel_of_le htu.le] at hst

theorem isSRW_theta {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
    (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0) :
    IsSRW P (fun ω => theta a (Y ω)) := by
  obtain ⟨hm, -, Ω', _, P', N', hN', hlaw⟩ := hY
  exact ⟨(measurable_theta a).comp hm,
    fun ω => isRegularPath_of_isRegPath (stepShift_mem (hYp ω) a).toIsRegPath, Ω', inferInstance,
    P', N', hN', by
      rw [IsSRW.map_theta ⟨hm, fun ω => isRegularPath_of_isRegPath (hYp ω).toIsRegPath, Ω',
        inferInstance, P', N', hN', hlaw⟩ a]
      exact hlaw⟩

theorem rc_stepExt {g : ℝ≥0 → Fin d → ℤ} (hg : ∀ s, ∀ᶠ u in 𝓝[≥] s, g u = g s) {r : ℝ}
    (_hr : 0 ≤ r) : ∀ᶠ u in 𝓝[≥] r, stepExt g u = stepExt g r := by
  obtain ⟨ε, hε, hc⟩ := exists_Ico_const_stepExt hg r
  exact Filter.mem_of_superset (Ico_mem_nhdsGE (lt_add_of_pos_right r hε)) hc

/-- The measurable rational witness set of `τ_fast ≤ T`. -/
def fastWitness (d : ℕ) (L T : ℝ) : Set (PathSpace d) :=
  ⋃ t ∈ rationalTimes T, ⋃ q : ℚ, ⋃ (_ : t - 1 ≤ (q : ℝ) ∧ (q : ℝ) < t),
    {x | L ≤ ‖stepExt x t - stepExt x (max (q : ℝ) 0)‖}

theorem measurableSet_fastWitness (L T : ℝ) : MeasurableSet (fastWitness d L T) := by
  refine MeasurableSet.biUnion (rationalTimes_countable T) fun t _ => ?_
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => ?_
  refine measurableSet_le measurable_const ?_
  have h1 : Measurable fun x : PathSpace d => stepExt x t := measurable_pi_apply _
  have h2 : Measurable fun x : PathSpace d => stepExt x (max (q : ℝ) 0) := measurable_pi_apply _
  exact (h1.sub h2).norm

/-- **ES22 Claim 2.3 for the driven regenerated walk.** -/
theorem stepFast_prob (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) [Fact (0 < β)], 1 ≤ β →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d},
        IsSRW P Y → (∀ ω, Y ω ∈ StepPath d) → ∀ (a : ℝ≥0) {L T : ℝ}, 1 ≤ L → 1 ≤ T →
          P.real {ω | pathTfast (stepWr β a Y ω) L ≤ ENNReal.ofReal T} ≤
            C * T ^ 2 * Real.exp (-(c * L)) := by
  obtain ⟨C, c, hC, hc, H⟩ := cyc_fast hd
  refine ⟨C, c, hC, hc, fun β _ hβ Ω _ P Y hY hYp a L T hL hT => ?_⟩
  have hPprob := hY.isProbabilityMeasure
  obtain ⟨Ω₀, mΩ₀, Pr₀, N₀, hPr₀, hN₀, -⟩ :=
    exists_isPoissonPointProcess ((Measure.count : Measure ℕ).prod (ringIntensity d β))
  have hY1 := isSRW_theta hY hYp a
  have hY1p : ∀ ω, theta a (Y ω) ∈ StepPath d := fun ω => stepShift_mem (hYp ω) a
  have hlaw := stepReg_law (β := β) hY1 hY1p hN₀
  have hfm := measurable_stepReg_comp (β := β) hY1 hY1p
  have hL0 : 0 < L := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hsub : {ω | pathTfast (stepWr β a Y ω) L ≤ ENNReal.ofReal T} ⊆
      (fun ω (t : ℝ≥0) => stepReg β (theta a (Y ω)) t) ⁻¹' fastWitness d L T := by
    intro ω hω
    have hreg : IsRegPath (stepReg β (stepShift a (Y ω))) :=
      isRegPath_stepReg (stepShift_mem (hYp ω) a).toIsRegPath
    have hrc : ∀ s : ℝ, 0 ≤ s → ∀ᶠ u in 𝓝[≥] s, stepWr β a Y ω u = stepWr β a Y ω s :=
      fun s hs => rc_stepExt hreg.rc hs
    have hz : stepWr β a Y ω 0 = 0 := by
      simp only [stepWr, Real.toNNReal_zero]
      exact stepReg_zero' (stepShift_mem (hYp ω) a)
    obtain ⟨t, ht, q, hq1, hq2, hLt⟩ := (pathTfast_le_iff_rational' hrc hz hL0 hT0).1 hω
    simp only [fastWitness, mem_iUnion, mem_preimage, mem_ofPred_eq]
    exact ⟨t, ht, q, ⟨hq1, hq2⟩, hLt⟩
  have h1 : P {ω | pathTfast (stepWr β a Y ω) L ≤ ENNReal.ofReal T} ≤
      Pr₀ {ω | cycTfast (fun k => cycSlice k (N₀ ω)) L ≤ ENNReal.ofReal T} := by
    refine (measure_mono hsub).trans ?_
    have e1 : P ((fun ω (t : ℝ≥0) => stepReg β (theta a (Y ω)) t) ⁻¹' fastWitness d L T) =
        (P.map (fun ω (t : ℝ≥0) => stepReg β (theta a (Y ω)) t)) (fastWitness d L T) :=
      (Measure.map_apply hfm (measurableSet_fastWitness L T)).symm
    rw [e1, hlaw, Measure.map_apply_of_aemeasurable (aemeasurable_regenWalk_path hN₀)
      (measurableSet_fastWitness L T)]
    refine measure_mono fun ω hω => ?_
    simp only [fastWitness, mem_iUnion, mem_preimage, mem_ofPred_eq] at hω
    obtain ⟨t, ht, q, ⟨hq1, hq2⟩, hLt⟩ := hω
    obtain ⟨ht0, htT⟩ := rationalTimes_pos ht
    have hq0 : (0 : ℝ) ≤ max (q : ℝ) 0 := le_max_right _ _
    simp only [stepExt, Real.coe_toNNReal _ ht0.le,
      Real.coe_toNNReal _ hq0] at hLt
    show cycTfast (fun k => cycSlice k (N₀ ω)) L ≤ ENNReal.ofReal T
    unfold cycTfast
    refine iInf₂_le_of_le t ⟨ht0, q, hq1, hq2.le, ?_⟩ (ENNReal.ofReal_le_ofReal htT)
    simpa only [copyEnv_eq_cycSlice] using hLt
  have h2 := H β hβ Ω₀ Pr₀ N₀ hN₀ hL hT
  calc P.real {ω | pathTfast (stepWr β a Y ω) L ≤ ENNReal.ofReal T}
      ≤ Pr₀.real {ω | cycTfast (fun k => cycSlice k (N₀ ω)) L ≤ ENNReal.ofReal T} :=
        ENNReal.toReal_mono (measure_ne_top _ _) h1
    _ ≤ _ := h2

end ElboimSly.Paper.Step
