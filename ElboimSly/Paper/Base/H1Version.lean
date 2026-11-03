/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Induction.RelaxedMeasWrt
public import ElboimSly.Paper.Induction.RelaxedMeasRegen2
public import ElboimSly.Paper.Base.IdentRegen
public import Mathlib

/-!
# (H1) at the base: the relaxed-path event as a regular set

ES22 Lemma 8.1, Step 0.  The probability transfer `regenPath_prob_eq_srw` needs the
event as a regular set.  We use the relaxed times of the stopped path, extended to real times by
`h1Walk`, and prove that the event has a measurable version (it is measurable on the measurable
space of regular paths, where `(γ, s) ↦ γ s` is jointly measurable via `SRW.ev`).

* `isRegSet_h1Set`: the event `|{s ≤ T relaxed for γ}| ≥ c` is a regular set.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW

variable {d : ℕ}

/-- A path stopped at `T`, extended to real times (constant on `(-∞,0]`). -/
def h1Walk (T : ℝ≥0) (γ : PathSpace d) : ℝ → Fin d → ℤ := fun s => γ (min s.toNNReal T)

/-- The relaxed times in `[0,T]` of the stopped path. -/
def h1RelTimes (β : ℝ) (T : ℝ≥0) (γ : PathSpace d) : Set ℝ :=
  {s | s ∈ Icc (0 : ℝ) (T : ℝ) ∧ IsRelaxedTimeWrt β (h1Walk T γ) 0 s}

/-- The event: the relaxed times of the stopped path have measure at least `c`. -/
def h1Set (β : ℝ) (T : ℝ≥0) (c : ℝ) : Set (PathSpace d) :=
  {γ | ENNReal.ofReal c ≤ volume (h1RelTimes β T γ)}

theorem h1Walk_rc {T : ℝ≥0} {γ : PathSpace d} (hγ : IsRegularPath γ) (s : ℝ) :
    ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), h1Walk T γ s' = h1Walk T γ s := by
  by_cases hs : s < 0
  · refine ⟨-s, by linarith, fun s' hs' => ?_⟩
    have h1 : s'.toNNReal = 0 := Real.toNNReal_of_nonpos (by linarith [hs'.2])
    have h2 : s.toNNReal = 0 := Real.toNNReal_of_nonpos hs.le
    simp [h1Walk, h1, h2]
  · push Not at hs
    obtain ⟨δ, hδ, h⟩ := hγ s.toNNReal
    refine ⟨δ, by exact_mod_cast hδ, fun s' hs' => ?_⟩
    have hs'0 : 0 ≤ s' := hs.trans hs'.1
    have e1 : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs
    have e2 : (s'.toNNReal : ℝ) = s' := Real.coe_toNNReal _ hs'0
    have hle : s.toNNReal ≤ s'.toNNReal := Real.toNNReal_le_toNNReal hs'.1
    have hlt : s'.toNNReal < s.toNNReal + δ := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_add, e1, e2]; linarith [hs'.2]
    unfold h1Walk
    rcases le_total s.toNNReal T with hT | hT
    · rw [min_eq_left hT]
      refine h _ (le_min hle hT) ?_
      exact lt_of_le_of_lt (min_le_left _ _) hlt
    · rw [min_eq_right hT, min_eq_right (hT.trans hle)]

theorem isRegSet_h1Set (β : ℝ) [Fact (0 < β)] (T : ℝ≥0) (c : ℝ) :
    IsRegSet (h1Set (d := d) β T c) := by
  let w : {γ : PathSpace d // IsRegularPath γ} → ℝ → Fin d → ℤ := fun γ s => h1Walk T γ.1 s
  have hw : Measurable fun p : {γ : PathSpace d // IsRegularPath γ} × ℝ => w p.1 p.2 := by
    have e : (fun p : {γ : PathSpace d // IsRegularPath γ} × ℝ => w p.1 p.2) =
        fun p => ev (min p.2.toNNReal T) p.1.1 := by
      funext p; simp only [w, h1Walk]; exact (ev_of_regular p.1.2 _).symm
    rw [e]
    exact measurable_ev.comp ((measurable_snd.real_toNNReal.min measurable_const).prodMk
      (measurable_subtype_coe.comp measurable_fst))
  have hM := measurableSet_isRelaxedTimeWrt (β := β) w (fun _ _ => 0) hw measurable_const
    (fun γ s => h1Walk_rc γ.2 s)
  set M' : Set ({γ : PathSpace d // IsRegularPath γ} × ℝ) :=
    {p | p.2 ∈ Icc (0 : ℝ) T ∧ IsRelaxedTimeWrt β (w p.1) 0 p.2} with hM'def
  have hM' : MeasurableSet M' := by
    have e : M' = {p : {γ : PathSpace d // IsRegularPath γ} × ℝ |
        IsRelaxedTimeWrt β (w p.1) ((fun _ _ => (0 : ℝ)) p.1 p.2) p.2} ∩
        (fun p => p.2) ⁻¹' Icc (0 : ℝ) T := by
      ext p; simp only [hM'def, mem_ofPred_eq, mem_inter_iff, mem_preimage]; tauto
    rw [e]
    exact hM.inter (measurable_snd measurableSet_Icc)
  have hmeas : Measurable fun γ : {γ : PathSpace d // IsRegularPath γ} =>
      volume (Prod.mk γ ⁻¹' M') := measurable_measure_prodMk_left hM'
  have hS : MeasurableSet {γ : {γ : PathSpace d // IsRegularPath γ} |
      ENNReal.ofReal c ≤ volume (Prod.mk γ ⁻¹' M')} := measurableSet_le measurable_const hmeas
  obtain ⟨Γ', hΓ', hpre⟩ := hS
  refine ⟨Γ', hΓ', fun γ hγ => ?_⟩
  have h1 : (⟨γ, hγ⟩ : {γ : PathSpace d // IsRegularPath γ}) ∈ Subtype.val ⁻¹' Γ' ↔ γ ∈ Γ' :=
    Iff.rfl
  rw [← h1, hpre]
  rfl

section Regen

variable {β : ℝ} [Fact (0 < β)]

theorem isRelaxedTimeWrt_congr_ofLe {w w' : ℝ → Fin d → ℤ} {a t : ℝ}
    (h : ∀ s, a ≤ s → s ≤ t → w s = w' s) (hat : a ≤ t) :
    IsRelaxedTimeWrt β w a t ↔ IsRelaxedTimeWrt β w' a t := by
  have hβ : 0 < β := Fact.out
  have hv : visitedSet w a t = visitedSet w' a t := Set.image_congr fun s hs => h s hs.1 hs.2
  have ht := h t hat le_rfl
  have hp : 0 ≤ β ^ (3 * indDelta d) := Real.rpow_nonneg hβ.le _
  unfold IsRelaxedTimeWrt IsHeavy
  simp only [hv, ht]
  refine and_congr Iff.rfl (forall_congr' fun s => ?_)
  by_cases hs : a ≤ s
  · simp only [hs, true_implies]
    refine imp_congr_right fun hs2 => ?_
    rw [h s hs (by linarith)]
  · simp [hs]

/-- The path of a regenerated walk. -/
noncomputable def pathOf (ν : ℕ → Measure (RingSpace d β)) : PathSpace d :=
  fun s => regenWalk ν (s : ℝ)

theorem regenStart_eq_zero (ν : ℕ → Measure (RingSpace d β)) {s : ℝ} (hs : s < β) :
    regenStart ν s = 0 := by
  have hβ : 0 < β := Fact.out
  have h : ENNReal.ofReal s < cycTreg (ν 0) :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hβ).2 hs) (le_cycTreg (ν 0))
  simp [regenStart, regenCount_eq_zero h, Roots.regenSigma_zero]

theorem h1RelTimes_pathOf_subset (ν : ℕ → Measure (RingSpace d β)) {T : ℝ≥0}
    (hT : (T : ℝ) ≤ β) :
    h1RelTimes β T (pathOf ν) ⊆ {s | s ∈ Icc (0 : ℝ) T ∧ IsRelaxedTime ν s} ∪ {β} := by
  rintro s ⟨hsI, hs⟩
  by_cases hsβ : s = β
  · exact Or.inr hsβ
  · left
    have hlt : s < β := lt_of_le_of_ne (hsI.2.trans hT) hsβ
    refine ⟨hsI, ?_⟩
    unfold IsRelaxedTime
    rw [regenStart_eq_zero ν hlt]
    refine (isRelaxedTimeWrt_congr_ofLe (fun u hu0 hus => ?_) hsI.1).1 hs
    have hu : u.toNNReal ≤ T := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0]; exact hus.trans hsI.2
    simp only [h1Walk, pathOf, min_eq_left hu, Real.coe_toNNReal _ hu0]

theorem h1Walk_stopPath (T : ℝ≥0) (γ : PathSpace d) : h1Walk T (stopPath T γ) = h1Walk T γ := by
  funext s
  simp [h1Walk, stopPath]

/-- **ES22 Lemma 8.1, Step 0.** The probability of the event "the relaxed times of an SRW path have
measure at least `c`" is at most the probability that the regenerated walk is a relaxed path with
threshold `c`. -/
theorem srw_h1Set_le_regen {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {T : ℝ≥0} (hT : (T : ℝ) ≤ β) (c : ℝ) {Z' : Ω' → PathSpace d} (hZ' : IsSRW P' Z') :
    P' {ω | Z' ω ∈ h1Set β T c} ≤
      P {ω | ENNReal.ofReal c ≤
        volume {s : ℝ | s ∈ Icc (0 : ℝ) T ∧ IsRelaxedTime (fun k => copyEnv (N ω) k) s}} := by
  rw [← regenPath_prob_eq_srw hN hT (isRegSet_h1Set β T c) (fun γ => by
    show ENNReal.ofReal c ≤ volume (h1RelTimes β T γ) ↔
      ENNReal.ofReal c ≤ volume (h1RelTimes β T (stopPath T γ))
    simp only [h1RelTimes, h1Walk_stopPath]) hZ']
  refine measure_mono fun ω hω => ?_
  have h1 : ENNReal.ofReal c ≤ volume (h1RelTimes β T (pathOf (fun k => copyEnv (N ω) k))) := hω
  refine h1.trans ?_
  refine (measure_mono (h1RelTimes_pathOf_subset _ hT)).trans ?_
  refine (measure_union_le _ _).trans ?_
  simp

end Regen

end ElboimSly.Paper

end
