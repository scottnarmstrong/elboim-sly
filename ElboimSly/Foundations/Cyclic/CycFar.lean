/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFarDriven
public import ElboimSly.Foundations.Cyclic.CycFarRc
public import ElboimSly.Foundations.Cyclic.CycSrwShortLaw
public import ElboimSly.Foundations.SRW.FarWindows
public import ElboimSly.Foundations.PPP.Existence
public import Mathlib

/-!
# ES22 Lemma 2.2

ES22 Lemma 2.2. For `L ≥ 1` and `t ≥ 0`, the regenerated walk `W` of regenerated cyclic walk
(construction (i), from the copies of a Poisson environment on `ℕ × S_β`) satisfies
`P(max_{s ≤ t} ‖W(s)‖ ≥ 10 d L t) ≤ e^{-L t}` (`cyc_far`).

Proof, as in the written proof: by the constructions of the regenerated walk (equality in law of constructions (i) and
(iii), `regen_law_env_cut`) the event has the same probability for `W^X_reg`, whose deviation is at
most `2 M((0,t])` (`norm_drivenRegenFrom_le`, from closing for the driven walk (a), (d)), with
`M((0,t]) ~ Poi(2dt)` (`winCount_tail`). The event "`∃ s ≤ t`" is replaced by the measurable
event over the countable set of times `checkTimes t` using the right-continuity of the
regenerated walk (`regenWalk_rc`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ}

/-- The countable set of check times `(ℚ ∩ [0, t]) ∪ {t}`. -/
def checkTimes (t : ℝ≥0) : Set ℝ≥0 := insert t {q | q ≤ t ∧ ∃ r : ℚ, q = Real.toNNReal r}

theorem countable_checkTimes (t : ℝ≥0) : (checkTimes t).Countable :=
  ((Set.countable_range (fun r : ℚ => Real.toNNReal r)).mono
    (fun q hq => by obtain ⟨r, hr⟩ := hq.2; exact ⟨r, hr.symm⟩)).insert t

/-- The measurable event "`‖f q‖ ≥ R` for some check time `q`". -/
def farSet (R : ℝ) (t : ℝ≥0) : Set (ℝ≥0 → Fin d → ℤ) :=
  ⋃ q ∈ checkTimes t, {f | R ≤ ‖f q‖}

theorem measurableSet_farSet (R : ℝ) (t : ℝ≥0) : MeasurableSet (farSet (d := d) R t) :=
  MeasurableSet.biUnion (countable_checkTimes t) fun q _ =>
    measurableSet_le measurable_const
      ((measurable_of_countable (fun x : Fin d → ℤ => ‖x‖)).comp (measurable_pi_apply q))

/-- A right-continuous path attaining a property at some time `s ≤ t` attains it at a check time. -/
theorem exists_check_of_rc {V : Type*} {f : ℝ≥0 → V} (hf : ∀ s, ∀ᶠ u in 𝓝[≥] s, f u = f s)
    {t s : ℝ≥0} (hst : s ≤ t) {P : V → Prop} (hP : P (f s)) : ∃ q ∈ checkTimes t, P (f q) := by
  rcases hst.lt_or_eq with hlt | rfl
  · obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hf s)
    have hlt' : (s : ℝ) < min (u' : ℝ) (t : ℝ) := lt_min (by exact_mod_cast hu') (by exact_mod_cast hlt)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt'
    have hr0 : (0 : ℝ) < r := lt_of_le_of_lt s.2 hr1
    have hq : (Real.toNNReal r : ℝ) = r := Real.coe_toNNReal r hr0.le
    refine ⟨Real.toNNReal r, Or.inr ⟨?_, r, rfl⟩, ?_⟩
    · rw [← NNReal.coe_le_coe, hq]; exact (hr2.trans_le (min_le_right _ _)).le
    · have hmem : Real.toNNReal r ∈ Ico s u' := by
        refine ⟨?_, ?_⟩
        · rw [← NNReal.coe_le_coe, hq]; exact hr1.le
        · rw [← NNReal.coe_lt_coe, hq]; exact hr2.trans_le (min_le_left _ _)
      rw [hsub hmem]; exact hP
  · exact ⟨s, Or.inl rfl, hP⟩

section Main

variable {β : ℝ} [Fact (0 < β)]

theorem far_numeric {d : ℕ} (hd : 1 ≤ d) {L t : ℝ} (hL : 1 ≤ L) (ht : 0 ≤ t) :
    2 * d * (Real.exp 1 - 1) * (t - 0) - 10 * d * L * t / 2 ≤ -(L * t) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 := exp_one_sub_one_le
  have h5 : 0 ≤ (5 * (d : ℝ) - 1) * (L - 1) :=
    mul_nonneg (by linarith) (sub_nonneg.2 hL)
  have hdt : 0 ≤ (d : ℝ) * t := by positivity
  have hkey : 4 * (d : ℝ) - 5 * d * L + L ≤ 0 := by nlinarith
  have h3 : 2 * (d : ℝ) * (Real.exp 1 - 1) * (t - 0) ≤ 2 * d * 2 * t := by
    rw [sub_zero]; nlinarith
  nlinarith [mul_nonneg ht (neg_nonneg.2 hkey)]

/-- **ES22 Lemma 2.2** (ES22 Lemma 2.2): for `d ≥ 1`, `L ≥ 1` and `t ≥ 0`, the regenerated walk `W`
built from the copies of a Poisson environment on `ℕ × S_β` satisfies
`P(max_{s ≤ t} ‖W(s)‖ ≥ 10 d L t) ≤ e^{-L t}`. -/
theorem cyc_far (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    {L t : ℝ} (hL : 1 ≤ L) (ht : 0 ≤ t) :
    Pe.real {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ 10 * d * L * t ≤
        ‖ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (s : ℝ)‖} ≤ Real.exp (-(L * t)) := by
  have := hN.isProbabilityMeasure
  obtain ⟨Ω', _, Pd, N₀, hPd, hN₀, -⟩ := exists_isPoissonPointProcess (clockIntensity (Dir d))
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have : Nonempty (CycEntry ℕ d) := ⟨(regPlan d β).junk⟩
  set R : ℝ := 10 * d * L * t with hR
  set t' : ℝ≥0 := t.toNNReal with ht'
  have ht'c : (t' : ℝ) = t := Real.coe_toNNReal t ht
  have hC := measurableSet_farSet (d := d) R t'
  -- measurability of the two processes
  have hWm : AEMeasurable (fun ω (u : ℝ≥0) =>
      ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((u : ℝ≥0) : ℝ)) Pe := by
    have hmeas : Measurable fun ω => regRecProc
        ((regPlan d β).envFinalOr CycRec.empty (N ω)) :=
      measurable_regRecProc.comp (((regPlan d β).measurable_envFinalOr CycRec.empty).comp
        hN.measurable)
    exact hmeas.aemeasurable.congr ((regen_env_ae hN).mono fun ω h => h.symm)
  have hVm : Measurable fun ω (u : ℝ≥0) =>
      drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) u := by
    have hV : (fun ω (u : ℝ≥0) => drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) u) =
        fun ω (u : ℝ≥0) => drivenRegenFrom β.toNNReal (drivePath (N₀ ω)).fn u := by
      funext ω u
      have h0 : canonical d N₀ ω 0 = 0 := by simp [canonical, walk_zero]
      exact drivenRegenWalkCut_eq_drivenRegenFrom hb h0 u
    rw [hV]
    exact measurable_pi_iff.2 fun u => measurable_drivenRegenFrom_at hb
      (X := fun ω => drivePath (N₀ ω)) (measurable_drivePath.comp hN₀.measurable) u
  have hlaw := regen_law_env_cut hN hN₀
  have e1 : Pe ((fun ω (u : ℝ≥0) => ElboimSly.regenWalk (fun k => cycSlice k (N ω))
        ((u : ℝ≥0) : ℝ)) ⁻¹' farSet R t') =
      Pd ((fun ω (u : ℝ≥0) => drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) u) ⁻¹'
        farSet R t') := by
    rw [← Measure.map_apply_of_aemeasurable hWm hC, ← Measure.map_apply hVm hC, hlaw]
  -- the environment event is contained in the preimage of the measurable event
  have hsub1 : {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ R ≤
        ‖ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (s : ℝ)‖} ≤ᵐ[Pe]
      ((fun ω (u : ℝ≥0) => ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((u : ℝ≥0) : ℝ)) ⁻¹'
        farSet R t') := by
    filter_upwards [ae_cycGood hN] with ω hω ⟨s, hs, hRs⟩
    have hst : s ≤ t' := (Real.le_toNNReal_iff_coe_le ht).2 hs
    obtain ⟨q, hq, hRq⟩ := exists_check_of_rc
      (f := fun u : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (u : ℝ))
      (regenWalk_rc hω) hst (P := fun v => R ≤ ‖v‖) hRs
    exact mem_iUnion₂.2 ⟨q, hq, hRq⟩
  -- the driven event is contained in a Poisson tail
  have hsub2 : ((fun ω (u : ℝ≥0) => drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) u) ⁻¹'
        farSet R t') ≤ᵐ[Pd] {ω | R / 2 ≤ (winCount N₀ 0 t ω : ℝ)} := by
    filter_upwards [ae_canonical_mem_cycCF hN₀ β.toNNReal hb] with ω hω hmem
    obtain ⟨q, hq, hRq⟩ := mem_iUnion₂.1 hmem
    have hqt : q ≤ t' := by
      rcases hq with rfl | ⟨h, -⟩
      · exact le_rfl
      · exact h
    have h0 : canonical d N₀ ω 0 = 0 := by simp [canonical, walk_zero]
    have hq' : drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) q =
        drivenRegenFrom β.toNNReal (canonical d N₀ ω) q :=
      drivenRegenWalkCut_eq_drivenRegenFrom hb h0 q
    have hRq' : R ≤ ‖drivenRegenFrom β.toNNReal (canonical d N₀ ω) q‖ := by
      rw [← hq']; exact hRq
    have hcan : canonical d N₀ ω = fun u : ℝ≥0 => walk d (N₀ ω) (u : ℝ) := rfl
    have := norm_drivenRegenFrom_le hb (ν := N₀ ω) (by rw [← hcan]; exact hω) hqt
    rw [ht'c] at this
    rw [hcan] at hRq'
    show R / 2 ≤ (winCount N₀ 0 t ω : ℝ)
    unfold winCount
    linarith
  have hfin := winCount_tail hN₀ (le_refl (0 : ℝ)) ht (R / 2)
  calc Pe.real _ ≤ Pe.real _ := measureReal_mono_ae' hsub1
    _ = Pd.real _ := by simp only [Measure.real, e1]
    _ ≤ Pd.real {ω | R / 2 ≤ (winCount N₀ 0 t ω : ℝ)} := measureReal_mono_ae' hsub2
    _ ≤ Real.exp (2 * d * (Real.exp 1 - 1) * (t - 0) - R / 2) := hfin
    _ ≤ Real.exp (-(L * t)) := Real.exp_le_exp.2 (far_numeric hd hL ht)

end Main

end ElboimSly.Cyclic

end
