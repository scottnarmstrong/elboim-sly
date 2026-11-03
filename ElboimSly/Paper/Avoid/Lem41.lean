/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Couple
public import ElboimSly.Paper.Avoid.Lem41Meas
public import ElboimSly.Paper.Avoid.Lem41Hit
public import Mathlib

/-!
# ES22 §4: Lemma 4.1

ES22 Lemma 4.1 (§4; proof ES22 §4).

Under (S1)–(S2) with `β ≥ β₄₁`, for every a.s. finite `(avoidFilt)`-stopping time `T`,
`P(thit(T) ≥ T + 4ⁿ | ℱ_T) ≥ 1 - C₄₁ β^{-δ/30}` a.s. on `{T ∈ 𝒯}`. The conditional probability
is stated, as in ES22 Lemma 4.1, in integrated form: for every `A ∈ ℱ_T` which is a.s. contained in
`{T ∈ 𝒯}`, `(1 - C₄₁ β^{-δ/30}) P(A) ≤ P(A ∩ {thit(T) ≥ T + 4ⁿ})`.

The proof applies `es4_1_core` with `ℋ = ℱ_T`, `a = α(T)`, `w = W` and the coupled walk `W̃`
of `es4_couple`; the pathwise step is `ofReal_add_le_of_hitTime`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {d : ℕ}

/-- Joint measurability of the recorded history, from the measurability of the record. -/
theorem measurable_hist_rec {Ω : Type*} (H : MeasurableSpace Ω) (junk : CycEntry ℕ d)
    (ρ : Ω → CycRec ℕ d) (hρ : Measurable[H] ρ) (a Tr : Ω → ℝ) (ha : Measurable[H] a)
    (hT : Measurable[H] Tr) :
    Measurable[H.prod inferInstance] (fun p : Ω × ℝ =>
      recWalkAt junk (min (a p.1 + max p.2 0) (Tr p.1)).toNNReal (ρ p.1)) := by
  let : MeasurableSpace Ω := H
  exact (measurable_recWalkAt_var junk).comp ((hρ.comp measurable_fst).prodMk
    ((((ha.comp measurable_fst).add (measurable_snd.max measurable_const)).min
      (hT.comp measurable_fst)).real_toNNReal))

/-- **ES22 Lemma 4.1** (ES22 Lemma 4.1). -/
theorem es4_1 (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, ∃ β41 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ),
      β41 ≤ β → ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
        {N N' : Ω → Measure (CycS ℕ d β)} (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N')
        {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime (avoidFilt 𝒢₀ S.space) T),
        (∀ᵐ ω ∂Pr, T ω ≠ ⊤) →
        ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
          (∀ᵐ ω ∂Pr, ω ∈ A → ∃ t : ℝ≥0, T ω = t ∧ IsRelaxedTime (avoidEnv N ω) (t : ℝ)) →
          ENNReal.ofReal (1 - C * β ^ (-indDelta d / 30)) * Pr A ≤
            Pr (A ∩ {ω | ∀ t : ℝ≥0, T ω = t →
              ENNReal.ofReal ((t : ℝ) + (4 : ℝ) ^ n) ≤ avoidThit N ω (t : ℝ)}) := by
  obtain ⟨C, hC, H0⟩ := es4_1_core hd
  refine ⟨C, hC, fun n₀ => ?_⟩
  obtain ⟨β41, H1⟩ := H0 n₀
  refine ⟨β41, fun β _ n t₀ hβ Ω 𝒢₀ mΩ Pr N N' S T hT hfin A hA hArel => ?_⟩
  have hPr := S.space.ppp.isProbabilityMeasure
  obtain ⟨M, hM, ⟨hXm, hXrc, hind, hlaw⟩, hcpl⟩ := es4_couple S hT hfin
  have hNm : Measurable N := S.space.ppp.measurable
  have hNg1 : ∀ᵐ ω ∂Pr, cycNgood N ω = N ω := ae_cycNgood_eq S.space.ppp
  -- the data of the core lemma
  set junk := (regPlan d β).junk with hjunk
  set ρ : Ω → CycRec ℕ d := cycRecStop (regPlan d β) (cycNgood N) T with hρdef
  have hρ : Measurable[hT.measurableSpace] ρ :=
    measurable_cycRecStop (measurable_trunc_multiFilt (regPlan d β) 𝒢₀ S.space.le Pr
      (measurable_envFinal_cycNgood (regPlan d β) hNm)) hT
  set Tr : Ω → ℝ := fun ω => ((ElboimSly.SRW.stopReal T ω : ℝ≥0) : ℝ) with hTr
  have hTrm : Measurable[hT.measurableSpace] Tr :=
    (measurable_stopReal_stop hT).coe_nnreal_real
  set a : Ω → ℝ := fun ω => (recAlpha (ρ ω)).toReal with ha
  have ham : Measurable[hT.measurableSpace] a :=
    ENNReal.measurable_toReal.comp ((measurable_recAlpha junk).comp hρ)
  set w : Ω → ℝ → Fin d → ℤ := fun ω x => avoidWalk (cycNgood N) ω x with hw
  have hgood : ∀ ω, CycGood (cycNgood N ω) := cycGood_cycNgood N
  have haeq : ∀ ω, a ω = regenStart (avoidEnv (cycNgood N) ω) (Tr ω) := by
    intro ω
    simp only [ha, hρdef, cycRecStop, hTr]
    rw [recAlpha_trunc_regPlan (hgood ω)]
    simp only [regenStart, avoidEnv_eq_cycSlice]
  have ha0 : ∀ ω, 0 ≤ a ω := fun ω => ENNReal.toReal_nonneg
  have haT : ∀ ω, a ω ≤ Tr ω := by
    intro ω
    rw [haeq]
    exact regenStart_le _ (NNReal.coe_nonneg _)
  have hwrec : ∀ ω (x : ℝ), 0 ≤ x → x ≤ Tr ω →
      w ω x = recWalkAt junk x.toNNReal (ρ ω) := by
    intro ω x hx0 hxT
    have hle : x.toNNReal ≤ ElboimSly.SRW.stopReal T ω := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0]; exact hxT
    simp only [hρdef, cycRecStop]
    rw [recWalkAt_trunc_regPlan (hgood ω) _ junk hle, regW_eq_regenWalk (hgood ω),
      Real.coe_toNNReal _ hx0]
    simp only [hw, avoidWalk, avoidEnv_eq_cycSlice]
  have hmin : ∀ ω (s : ℝ), 0 ≤ min (a ω + max s 0) (Tr ω) ∧ min (a ω + max s 0) (Tr ω) ≤ Tr ω :=
    fun ω s => ⟨le_min (by linarith [ha0 ω, le_max_right s 0]) (le_trans (ha0 ω) (haT ω)),
      min_le_right _ _⟩
  have hhist : Measurable[hT.measurableSpace.prod inferInstance]
      (fun p : Ω × ℝ => w p.1 (min (a p.1 + max p.2 0) (Tr p.1))) := by
    have := measurable_hist_rec hT.measurableSpace junk ρ hρ a Tr ham hTrm
    have e : (fun p : Ω × ℝ => w p.1 (min (a p.1 + max p.2 0) (Tr p.1))) =
        fun p => recWalkAt junk (min (a p.1 + max p.2 0) (Tr p.1)).toNNReal (ρ p.1) :=
      funext fun p => hwrec p.1 _ (hmin p.1 p.2).1 (hmin p.1 p.2).2
    rw [e]
    exact this
  have hrc : ∀ ω, IsRCPath (fun s : ℝ≥0 => w ω (min (a ω + s) (Tr ω))) := by
    intro ω
    have e : (fun s : ℝ≥0 => w ω (min (a ω + s) (Tr ω))) =
        avoidPath (cycNgood N) ω ∘ fun s : ℝ≥0 => (min (a ω + s) (Tr ω)).toNNReal := by
      funext s
      have h0 : 0 ≤ min (a ω + (s : ℝ)) (Tr ω) :=
        le_min (by linarith [ha0 ω, s.2]) (le_trans (ha0 ω) (haT ω))
      simp only [Function.comp, avoidPath, Real.coe_toNNReal _ h0]
      rfl
    rw [e]
    refine isRCPath_comp_mono (isRCPath_avoidPath (hgood ω)) ?_ ?_
    · exact continuous_real_toNNReal.comp (by fun_prop)
    · intro s s' hss
      have h : (s : ℝ) ≤ s' := by exact_mod_cast hss
      exact Real.toNNReal_mono (min_le_min (by linarith) le_rfl)
  have hcore := H1 β n t₀ hβ S.params Pr N S.space.ppp hT.measurableSpace hT.measurableSpace_le
    Pr a Tr w (avoidPath (cycNgood M)) haT ham hTrm hhist hrc hXm hXrc hind hlaw
  obtain ⟨hRel, hcore2⟩ := hcore
  have hAR := hcore2 (A := A ∩ {ω | IsRelaxedTimeWrt β (w ω) (a ω) (Tr ω)}) (hA.inter hRel)
    (fun ω hω => hω.2)
  have hwN : ∀ ω, cycNgood N ω = N ω → w ω = avoidWalk N ω := by
    intro ω hN
    exact avoidWalk_congr hN
  have haN : ∀ ω, cycNgood N ω = N ω → a ω = regenStart (avoidEnv N ω) (Tr ω) := by
    intro ω hN
    rw [haeq, avoidEnv_congr hN]
  have hTrt : ∀ ω (t : ℝ≥0), T ω = t → Tr ω = t := by
    intro ω t htT
    simp only [hTr, ElboimSly.SRW.stopReal, htT]
    rfl
  have h1 : A ≤ᵐ[Pr] A ∩ {ω | IsRelaxedTimeWrt β (w ω) (a ω) (Tr ω)} := by
    filter_upwards [hNg1, hArel] with ω hN hAω hω
    obtain ⟨t, htT, hrel⟩ := hAω hω
    refine ⟨hω, ?_⟩
    show IsRelaxedTimeWrt β (w ω) (a ω) (Tr ω)
    rw [haN ω hN, hwN ω hN, hTrt ω t htT]
    exact hrel
  have h2 : (A ∩ {ω | IsRelaxedTimeWrt β (w ω) (a ω) (Tr ω)}) ∩ {ω | ENNReal.ofReal ((4 : ℝ) ^ n) ≤
      hitTime β (w ω) (a ω) (Tr ω) (fun r => w ω (Tr ω) + avoidPath (cycNgood M) ω r.toNNReal)}
        ≤ᵐ[Pr] A ∩ {ω | ∀ t : ℝ≥0, T ω = t →
          ENNReal.ofReal ((t : ℝ) + (4 : ℝ) ^ n) ≤ avoidThit N ω (t : ℝ)} := by
    filter_upwards [hNg1, hcpl] with ω hN hc hω
    obtain ⟨⟨hωA, -⟩, hE4⟩ := hω
    refine ⟨hωA, fun t htT => ?_⟩
    obtain ⟨-, -, -, h4⟩ := hc t htT
    have hE4' := hE4
    simp only [mem_ofPred_eq] at hE4'
    rw [haN ω hN, hwN ω hN, hTrt ω t htT] at hE4'
    exact ofReal_add_le_of_hitTime (w := avoidWalk N ω) (X := avoidPath (cycNgood M) ω)
      hE4' h4
  calc ENNReal.ofReal (1 - C * β ^ (-indDelta d / 30)) * Pr A
      ≤ ENNReal.ofReal (1 - C * β ^ (-indDelta d / 30)) *
        Pr (A ∩ {ω | IsRelaxedTimeWrt β (w ω) (a ω) (Tr ω)}) :=
        mul_le_mul_right (measure_mono_ae h1) _
    _ ≤ _ := hAR
    _ ≤ _ := measure_mono_ae h2

end ElboimSly.Paper

end
