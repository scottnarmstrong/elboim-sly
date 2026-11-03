/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78TauIndep
public import ElboimSly.Paper.Step.Lemma78TauMeas
public import ElboimSly.Paper.Step.AvoidStopping
public import ElboimSly.Paper.Avoid.CoreMain
public import Mathlib

/-!
# The `τ'` bound

One excursion succeeds with probability at least frac12, "History" (the use of ES22 Lemma 4.1 with `ℋ = ℱ⁺_{ζ_i}`,
`a = 0`, `T = ζ_i`, the history `w = W₂|_{[0,ζ_i]}` and `W̃ = W'_i`).

`step78_tau_bound`: for `G ∈ ℱ⁺_{ζ_i}` with `ζ_i < ∞` and `ζ_i ∈ 𝒯₂` on `G`,
`P(G ∩ {τ' < 4ⁿ}) ≤ C β^{-δ/30} P(G)`, where `τ' = hitTime β W₂ 0 ζ_i (W₂(ζ_i) + W'_i)` and `W'_i`
is the glued continuation of w_2 after zeta_i, given ℱ^+_zeta_i. The proof freezes the history against the
measurable right-continuous surrogate `planSurr` of `W'_i` (independent of `ℱ⁺_{ζ_i}` under
`P(· | ζ_i < ∞)`), and passes from the lower bound of `es4_1_core` to the upper bound by the
measurability of `{τ' < 4ⁿ}` (`measurableSet_hitTime_lt`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The law of the regenerated walk of the copies of `N''` is the law of `avoidPath N₀`. -/
theorem step78_map_regen_eq_avoid {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N'' : Ω → Measure (ℕ × RingSpace d β)}
    (hN'' : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {Pr₀ : Measure Ω₀} {N₀ : Ω₀ → Measure (CycS ℕ d β)}
    (hN₀ : IsPoissonPointProcess N₀ (cycIntensity ℕ d β) Pr₀) :
    Pr.map (fun ω (t : ℝ≥0) => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) =
      Pr₀.map (avoidPath N₀) := by
  have e1 : Pr.map (fun ω (t : ℝ≥0) => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) =
      Pr.map (fun ω => regW (N'' ω)) := by
    refine Measure.map_congr ?_
    filter_upwards [ae_cycGood hN''] with ω hω
    funext t
    exact regenWalk_eq_contGlue (ν := fun k => cycSlice k (N'' ω)) hω t
  have e2 : Pr₀.map (avoidPath N₀) = Pr₀.map (fun ω => regW (N₀ ω)) := by
    refine Measure.map_congr ?_
    filter_upwards [ae_cycGood hN₀] with ω hω
    funext t
    show ElboimSly.regenWalk (avoidEnv N₀ ω) (t : ℝ) = _
    rw [avoidEnv_eq_cycSlice]
    exact regenWalk_eq_contGlue (ν := fun k => cycSlice k (N₀ ω)) hω t
  have h1 : Pr.map N'' = Pr₀.map N₀ := hN₀.map_eq_map hN''
  have e3 : Pr.map (fun ω => regW (N'' ω)) = (Pr.map N'').map regW :=
    (Measure.map_map measurable_regW hN''.measurable).symm
  have e4 : Pr₀.map (fun ω => regW (N₀ ω)) = (Pr₀.map N₀).map regW :=
    (Measure.map_map measurable_regW hN₀.measurable).symm
  rw [e1, e2, e3, e4, h1]

/-- From the lower bound for `P(G ∩ B)` and `P(G ∩ B) + P(G ∩ Bᶜ) = P(G)` to the upper bound. -/
theorem ennreal_upper_of_lower {a b g : ℝ≥0∞} {c : ℝ} (hab : a + b = g) (hg : g ≠ ⊤)
    (hc : 0 ≤ c) (h : ENNReal.ofReal (1 - c) * g ≤ b) : a ≤ ENNReal.ofReal c * g := by
  rcases le_or_gt 1 c with h1 | h1
  · calc a ≤ g := hab ▸ le_self_add
      _ = 1 * g := (one_mul g).symm
      _ ≤ ENNReal.ofReal c * g := by
        gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1
  · have hfin : ENNReal.ofReal (1 - c) * g ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg
    have h2 : a + ENNReal.ofReal (1 - c) * g ≤ ENNReal.ofReal c * g + ENNReal.ofReal (1 - c) * g := by
      calc a + ENNReal.ofReal (1 - c) * g ≤ a + b := by gcongr
        _ = g := hab
        _ = (ENNReal.ofReal c + ENNReal.ofReal (1 - c)) * g := by
            rw [← ENNReal.ofReal_add hc (by linarith)]; simp
        _ = _ := add_mul _ _ _
    exact (ENNReal.add_le_add_iff_right hfin).1 h2


universe u

/-- **one excursion succeeds with probability at least frac12, the `τ'` bound.** In the regime `StepRegime`, for `β` large and
`G ∈ ℱ⁺_{ζ_i}` on which `ζ_i < ∞` is a relaxed time `ζ_i ∈ 𝒯₂`:
`P(G ∩ {τ' < 4ⁿ}) ≤ C β^{-δ/30} P(G)`, where `τ' = hitTime β W₂ 0 ζ_i (W₂(ζ_i) + W'_i)` and `W'_i`
is the glued continuation of w_2 after zeta_i, given ℱ^+_zeta_i. -/
theorem step78_tau_bound (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₁ : ℕ, ∃ β41 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ),
      β41 ≤ β → ∀ (hreg : StepRegime d n₁ β n t₀)
      (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0) {Ω : Type u} (𝒢₀ : MeasurableSpace Ω)
      [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
      {N N' : Ω → Measure (CycS Unit d β)} {N'' : Ω → Measure (ℕ × RingSpace d β)}
      (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr)
      (_hN' : IsPoissonPointProcess N' (cycIntensity Unit d β) Pr)
      (_hN'' : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr)
      (_hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
      (_hI2 : Indep (MeasurableSpace.comap N' inferInstance)
        (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
      (_hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
        (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
          cycNull Pr) Pr)
      (h𝒢 : 𝒢₀ ≤ mΩ) (ρ : ℝ) (i : ℕ) {G : Set Ω},
      MeasurableSet[(Step78Data.isStoppingTime_zp_zeta
        (step78_frame u q Tn 𝒢₀ hN h𝒢 (by omega) hreg.2.1 n ρ) i).2.measurableSpace] G →
      (∀ ω ∈ G, ∃ t : ℝ≥0, (step78SliceData (cycNgood N) u q Tn n ρ).zeta i ω = t ∧
        (t : ℝ) ∈ (step78SliceData (cycNgood N) u q Tn n ρ).relaxed ω) →
      Pr (G ∩ {ω | ∃ t : ℝ≥0, (step78SliceData (cycNgood N) u q Tn n ρ).zeta i ω = t ∧
          hitTime β ((step78SliceData (cycNgood N) u q Tn n ρ).path ω) 0 (t : ℝ)
            (fun s => (step78SliceData (cycNgood N) u q Tn n ρ).path ω (t : ℝ) +
              contGlue β.toNNReal (planFirst (step78Plan d β u q Tn) N N'
                (step78T Tn ((step78SliceData (cycNgood N) u q Tn n ρ).zeta i))
                (step78Delta N u q ((step78SliceData (cycNgood N) u q Tn n ρ).zeta i)) ω)
                (contSeq N'' ω) s.toNNReal) < ENNReal.ofReal ((4 : ℝ) ^ n)}) ≤
        ENNReal.ofReal (C * β ^ (-indDelta d / 30)) * Pr G := by
  obtain ⟨C, hC, H0⟩ := es4_1_core.{u} hd
  refine ⟨C, hC, fun n₁ => ?_⟩
  obtain ⟨β41, H1⟩ := H0 n₁
  refine ⟨max β41 (max ((10 : ℝ) ^ 14) ((4 : ℝ) ^ (n₁ + 2))), ?_⟩
  intro β _ n t₀ hβ hreg u q Tn Ω 𝒢₀ mΩ Pr N N' N'' hN hN' hN'' hI1 hI2 hI3 h𝒢 ρ i G hG hGrel
  have hβ41 : β41 ≤ β := (le_max_left _ _).trans hβ
  have hβ14 : (10 : ℝ) ^ 14 ≤ β := ((le_max_left _ _).trans (le_max_right _ _)).trans hβ
  have hβ4 : (4 : ℝ) ^ (n₁ + 2) ≤ β := ((le_max_right _ _).trans (le_max_right _ _)).trans hβ
  have hp := es4Params_of_stepRegime hd hreg hβ14 hβ4
  have := hN.isProbabilityMeasure
  have hF := step78_frame u q Tn 𝒢₀ hN h𝒢 (by omega) hreg.2.1 n ρ
  have hZ := (Step78Data.isStoppingTime_zp_zeta hF i).2
  set D := step78SliceData (cycNgood N) u q Tn n ρ with hD
  set Z := D.zeta i with hZdef
  set E : Set Ω := {ω | step78T Tn Z ω ≠ ⊤} with hE
  have hT := step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ
  have hEm : MeasurableSet E := hT.measurableSpace_le _ (measurableSet_ne_top hT)
  have hEfin : Pr E ≠ ⊤ := measure_ne_top _ _
  have hGm : MeasurableSet G := hZ.measurableSpace_le _ hG
  have hGE : G ⊆ E := by
    intro ω hω
    obtain ⟨t, ht, -⟩ := hGrel ω hω
    show step78T Tn Z ω ≠ ⊤
    rw [step78T, ht, ← WithTop.coe_add]
    exact WithTop.coe_ne_top
  by_cases hne : Pr E = 0
  · have : Pr G = 0 := measure_mono_null hGE hne
    exact (measure_mono inter_subset_left).trans (by simp [this])
  obtain ⟨hind, hlaw⟩ := step78_surr_indep_law u q Tn 𝒢₀ hN hN' hN'' hI1 hI2 hI3 h𝒢 hZ hne
  have : IsProbabilityMeasure (Pr[|E]) := cond_isProbabilityMeasure hne
  set Pr' := Pr[|E] with hPr'
  set W := planSurr (step78Plan d β u q Tn) N N' N'' (step78T Tn Z) (step78Delta N u q Z)
    with hW
  have hWm : Measurable W := measurable_planSurr (step78Plan d β u q Tn) 𝒢₀ hN hN' hI1 hI2
    (step78Plan_K_pos u q Tn) h𝒢 (step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ)
    (step78_measurable_delta u q Tn 𝒢₀ hN h𝒢 (step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ))
    hN''
  have hWrc : ∀ ω, IsRCPath (W ω) := isRCPath_planSurr (step78Plan d β u q Tn) _ _
  -- the environment of the core lemma
  obtain ⟨Ω₀, mΩ₀, Pr₀, N₀, hPr₀, hN₀, -⟩ := exists_isPoissonPointProcess (cycIntensity ℕ d β)
  have hlaw' : Pr'.map W = Pr₀.map (avoidPath N₀) := hlaw.trans (step78_map_regen_eq_avoid hN'' hN₀)
  -- history data
  have hTm := step78_measurable_stopReal u q Tn 𝒢₀ hN h𝒢 hZ
  have hhist := step78_measurable_hist u q Tn 𝒢₀ hN h𝒢 n ρ hZ
  have hrcH := step78_isRCPath_hist u q Tn (N := N) n ρ Z
  have hcore := H1 β n t₀ hβ41 hp Pr₀ N₀ hN₀ hZ.measurableSpace hZ.measurableSpace_le Pr'
    (fun _ => 0) (fun ω => ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ)) D.path W
    (fun ω => NNReal.coe_nonneg _) measurable_const hTm hhist hrcH hWm hWrc hind hlaw'
  obtain ⟨-, hcore2⟩ := hcore
  have hrel : ∀ ω ∈ G, IsRelaxedTimeWrt β (D.path ω) ((fun _ => (0 : ℝ)) ω)
      ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ) := by
    intro ω hω
    obtain ⟨t, ht, hrel⟩ := hGrel ω hω
    have hsr : ElboimSly.SRW.stopReal Z ω = t := by
      unfold ElboimSly.SRW.stopReal; rw [ht]; rfl
    rw [hsr]
    exact hrel.2
  have hAR := hcore2 (A := G) hG hrel
  -- the event `{τ' < 4ⁿ}` for the surrogate
  set Bc : Set Ω := {ω | hitTime β (D.path ω) 0 ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ)
    (fun r => D.path ω ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ) + W ω r.toNNReal) <
      ENNReal.ofReal ((4 : ℝ) ^ n)} with hBc
  have hBcm : MeasurableSet Bc :=
    measurableSet_hitTime_lt (β := β) hZ.measurableSpace hZ.measurableSpace_le hTm hhist
      (fun ω => NNReal.coe_nonneg _) (fun ω s => exists_Ico_const_stepExt (hF.hrc ω) s) hWm
      (fun ω t => hWrc ω t) _
  have hsplit : Pr' (G ∩ Bc) + Pr' (G ∩ {ω | ENNReal.ofReal ((4 : ℝ) ^ n) ≤
      hitTime β (D.path ω) ((fun _ => (0 : ℝ)) ω) ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ)
        (fun r => D.path ω ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ) + W ω r.toNNReal)}) =
      Pr' G := by
    rw [← measure_inter_add_sdiff G hBcm]
    congr 2
    ext ω
    simp only [mem_inter_iff, Set.mem_sdiff, hBc, mem_ofPred_eq, not_lt]
  have hc0 : 0 ≤ C * β ^ (-indDelta d / 30) := by
    have : 0 < β := Fact.out
    positivity
  have hup := ennreal_upper_of_lower hsplit (measure_ne_top _ _) hc0 hAR
  -- back to `Pr`
  have hsub : ∀ s : Set Ω, s ⊆ E → Pr s = Pr E * Pr' s := by
    intro s hs
    rw [hPr', cond_apply hEm, inter_eq_right.2 hs, ← mul_assoc, ENNReal.mul_inv_cancel hne hEfin,
      one_mul]
  have hGBc : G ∩ Bc ⊆ E := inter_subset_left.trans hGE
  have hae : ∀ᵐ ω ∂Pr, W ω = contGlue β.toNNReal (planFirst (step78Plan d β u q Tn) N N'
      (step78T Tn Z) (step78Delta N u q Z) ω) (contSeq N'' ω) :=
    planSurr_ae_eq (step78Plan d β u q Tn) 𝒢₀ hN hN' hI1 hI2 (N'' := N'') (T := step78T Tn Z)
      (step78Delta N u q Z)
  calc Pr (G ∩ {ω | ∃ t : ℝ≥0, Z ω = t ∧ hitTime β (D.path ω) 0 (t : ℝ)
          (fun s => D.path ω (t : ℝ) + contGlue β.toNNReal (planFirst (step78Plan d β u q Tn)
            N N' (step78T Tn Z) (step78Delta N u q Z) ω) (contSeq N'' ω) s.toNNReal) <
          ENNReal.ofReal ((4 : ℝ) ^ n)})
      ≤ Pr (G ∩ Bc) := by
        refine measure_mono_ae ?_
        filter_upwards [hae] with ω hω hmem
        obtain ⟨hωG, t, ht, hlt⟩ := hmem
        have hsr : ElboimSly.SRW.stopReal Z ω = t := by
          unfold ElboimSly.SRW.stopReal; rw [ht]; rfl
        refine ⟨hωG, ?_⟩
        show hitTime β (D.path ω) 0 ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ)
          (fun r => D.path ω ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ) + W ω r.toNNReal) <
            ENNReal.ofReal ((4 : ℝ) ^ n)
        rw [hsr, hω]
        exact hlt
    _ = Pr E * Pr' (G ∩ Bc) := hsub _ hGBc
    _ ≤ Pr E * (ENNReal.ofReal (C * β ^ (-indDelta d / 30)) * Pr' G) := by gcongr
    _ = ENNReal.ofReal (C * β ^ (-indDelta d / 30)) * (Pr E * Pr' G) := by ring
    _ = ENNReal.ofReal (C * β ^ (-indDelta d / 30)) * Pr G := by rw [hsub G hGE]

end ElboimSly.Paper.Step

end
