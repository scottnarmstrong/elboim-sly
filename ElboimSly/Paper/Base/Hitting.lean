/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Progressive
public import ElboimSly.Paper.Base.StepPath
public import ElboimSly.Foundations.SRW.Stopping
public import ElboimSly.Foundations.SRW.HittingTime
public import Mathlib

/-!
# Hitting times of adapted step processes

Hitting times of adapted step processes (supplement).

Let `(ℱ_t)` be a filtration, `Y` a `ℤ^k`-valued adapted process whose paths are step paths, `K(ω)`
a random subset of `ℤ^k` with `{z ∈ K} ∈ ℱ₀`, `σ` a stopping time and `h ≥ 0`.  Then
`τ = inf {t ≥ σ + h : Y(t) ∈ K}` (`inf ∅ = ∞`, and `τ = ∞` if `σ = ∞`) is a stopping time,
`τ ≥ σ + h`, the infimum is attained, and `Y(τ)` is `ℱ_τ`-measurable on `{τ < ∞}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {k : ℕ}

open Classical in
/-- Hitting times of adapted step processes: `τ = inf {t ≥ σ + h : Y(t) ∈ K}`, with `inf ∅ = ∞` and
`τ = ∞` when `σ = ∞`. -/
noncomputable def hitAfter (Y : Ω → ℝ≥0 → Fin k → ℤ) (K : Ω → Set (Fin k → ℤ))
    (σ : Ω → WithTop ℝ≥0) (h : ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  if σ ω = ⊤ then ⊤
  else if ∃ s, stopReal σ ω + h ≤ s ∧ Y ω s ∈ K ω then
    ((sInf {s | stopReal σ ω + h ≤ s ∧ Y ω s ∈ K ω} : ℝ≥0) : WithTop ℝ≥0)
  else ⊤

theorem isRegularPath_of_isStepPath {γ : ℝ≥0 → Fin k → ℤ} (hγ : IsStepPath γ) :
    IsRegularPath (d := k) γ := by
  intro t
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hγ.rc t)
  refine ⟨u' - t, tsub_pos_of_lt hu', fun s hs1 hs2 => hsub ⟨hs1, ?_⟩⟩
  rwa [add_tsub_cancel_of_le (Set.mem_Ioi.1 hu').le] at hs2

section

variable {Y : Ω → ℝ≥0 → Fin k → ℤ} {K : Ω → Set (Fin k → ℤ)} {σ : Ω → WithTop ℝ≥0} {h : ℝ≥0}

theorem hitAfter_top (ω : Ω) (hσ : σ ω = ⊤) : hitAfter Y K σ h ω = ⊤ := by
  unfold hitAfter; rw [ite_eq_left hσ]

/-- The infimum is attained. -/
theorem hitAfter_attained (hY : ∀ ω, IsStepPath (Y ω)) {ω : Ω} {t : ℝ≥0}
    (ht : hitAfter Y K σ h ω = (t : WithTop ℝ≥0)) :
    σ ω ≠ ⊤ ∧ stopReal σ ω + h ≤ t ∧ Y ω t ∈ K ω := by
  unfold hitAfter at ht
  by_cases hσ : σ ω = ⊤
  · rw [ite_eq_left hσ] at ht; exact absurd ht.symm WithTop.coe_ne_top
  · rw [ite_eq_right hσ] at ht
    by_cases hex : ∃ s, stopReal σ ω + h ≤ s ∧ Y ω s ∈ K ω
    · rw [ite_eq_left hex] at ht
      have := hitTime_attained (isRegularPath_of_isStepPath (hY ω)) hex
      have e : sInf {s | stopReal σ ω + h ≤ s ∧ Y ω s ∈ K ω} = t := WithTop.coe_injective ht
      rw [e] at this
      exact ⟨hσ, this⟩
    · rw [ite_eq_right hex] at ht; exact absurd ht WithTop.top_ne_coe

/-- `τ ≥ σ + h` on `{σ < ∞}`. -/
theorem le_hitAfter (hY : ∀ ω, IsStepPath (Y ω)) (ω : Ω) (_hσ : σ ω ≠ ⊤) :
    ((stopReal σ ω + h : ℝ≥0) : WithTop ℝ≥0) ≤ hitAfter Y K σ h ω := by
  cases hτ : hitAfter Y K σ h ω using WithTop.recTopCoe with
  | top => exact le_top
  | coe t => exact WithTop.coe_le_coe.2 (hitAfter_attained hY hτ).2.1

variable (f : Filtration ℝ≥0 mΩ)

/-- The event that the sought time is at most `q`. -/
def hitCell (Y : Ω → ℝ≥0 → Fin k → ℤ) (K : Ω → Set (Fin k → ℤ))
    (σ : Ω → WithTop ℝ≥0) (h q : ℝ≥0) : Set Ω :=
  {ω | σ ω ≠ ⊤ ∧ stopReal σ ω + h ≤ q} ∩ {ω | Y ω q ∈ K ω}

theorem measurableSet_hitCell (hσ : IsStoppingTime f σ) (hY : ∀ t, Measurable[f t] fun ω => Y ω t)
    (hK : ∀ z, MeasurableSet[f 0] {ω | z ∈ K ω}) (q : ℝ≥0) :
    MeasurableSet[f q] (hitCell Y K σ h q) := by
  let : MeasurableSpace Ω := f q
  refine MeasurableSet.inter ?_ ?_
  · by_cases hq : h ≤ q
    · have : {ω | σ ω ≠ ⊤ ∧ stopReal σ ω + h ≤ q} =
          {ω | σ ω ≤ ((q - h : ℝ≥0) : WithTop ℝ≥0)} := by
        ext ω
        simp only [mem_ofPred_eq]
        cases hh : σ ω using WithTop.recTopCoe with
        | top =>
          exact ⟨fun h => absurd rfl h.1, fun h => absurd h (WithTop.not_top_le_coe _)⟩
        | coe s =>
          have : stopReal σ ω = s := by simp only [stopReal, hh]; rfl
          rw [this, WithTop.coe_le_coe]
          exact ⟨fun h => le_tsub_of_add_le_right h.2, fun h =>
            ⟨WithTop.coe_ne_top, ((le_tsub_iff_right hq).1 h)⟩⟩
      rw [this]; exact f.mono tsub_le_self _ (hσ (q - h))
    · have : {ω | σ ω ≠ ⊤ ∧ stopReal σ ω + h ≤ q} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hle
        exact hq ((le_add_self).trans hle)
      rw [this]; exact MeasurableSet.empty
  · have : {ω | Y ω q ∈ K ω} = ⋃ z : Fin k → ℤ, {ω | Y ω q = z} ∩ {ω | z ∈ K ω} := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iUnion fun z =>
      (hY q (measurableSet_singleton z)).inter ((f.mono bot_le) _ (hK z))

theorem hitAfter_le_of_mem_hitCell {q : ℝ≥0} {ω : Ω} (hω : ω ∈ hitCell Y K σ h q) :
    hitAfter Y K σ h ω ≤ (q : WithTop ℝ≥0) := by
  obtain ⟨⟨hσω, hle⟩, hq⟩ := hω
  have hex : ∃ s, stopReal σ ω + h ≤ s ∧ Y ω s ∈ K ω := ⟨q, hle, hq⟩
  unfold hitAfter
  rw [ite_eq_right hσω, ite_eq_left hex]
  exact WithTop.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) ⟨hle, hq⟩)

theorem hitAfter_isStoppingTime (hσ : IsStoppingTime f σ)
    (hY : ∀ t, Measurable[f t] fun ω => Y ω t) (hstep : ∀ ω, IsStepPath (Y ω))
    (hK : ∀ z, MeasurableSet[f 0] {ω | z ∈ K ω}) : IsStoppingTime f (hitAfter Y K σ h) := by
  intro t
  have key : {ω | hitAfter Y K σ h ω ≤ (t : WithTop ℝ≥0)} = hitCell Y K σ h t ∪
      ⋃ (j : ℕ) (m : ℕ) (_ : (j : ℝ≥0) / 2 ^ m < t), hitCell Y K σ h ((j : ℝ≥0) / 2 ^ m) := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_union, Set.mem_iUnion]
    constructor
    · intro hle
      cases hτ : hitAfter Y K σ h ω using WithTop.recTopCoe with
      | top => rw [hτ] at hle; exact absurd hle (WithTop.not_top_le_coe _)
      | coe t' =>
        rw [hτ] at hle
        have ht' : t' ≤ t := WithTop.coe_le_coe.1 hle
        obtain ⟨hσω, h1, h2⟩ := hitAfter_attained hstep hτ
        rcases ht'.lt_or_eq with hlt | heq
        · right
          obtain ⟨m0, hm0⟩ := exists_plateau (hstep ω).rc t'
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (tsub_pos_of_lt hlt)
            (show (1 / 2 : ℝ≥0) < 1 by norm_num)
          set m := max m0 n with hm
          have hdy : dyUp m t' < t := by
            have h3 := dyUp_lt m t'
            have h4 : ((1 / 2 : ℝ≥0)) ^ m ≤ (1 / 2) ^ n :=
              pow_le_pow_of_le_one bot_le (by norm_num) (le_max_right _ _)
            have h5 : t' + (1 / 2) ^ m < t :=
              (lt_tsub_iff_left.1 (lt_of_le_of_lt h4 hn))
            exact h3.trans h5
          refine ⟨⌈t' * 2 ^ m⌉₊, m, hdy, ⟨⟨hσω, h1.trans (le_dyUp m t')⟩, ?_⟩⟩
          have e : Y ω (dyUp m t') = Y ω t' := hm0 m (le_max_left _ _) _ (le_dyUp m t') le_rfl
          show Y ω (dyUp m t') ∈ K ω
          rw [e]; exact h2
        · left
          subst heq
          exact ⟨⟨hσω, h1⟩, h2⟩
    · rintro (hc | ⟨j, m, hq, hc⟩)
      · exact (hitAfter_le_of_mem_hitCell hc)
      · exact (hitAfter_le_of_mem_hitCell hc).trans (WithTop.coe_le_coe.2 hq.le)
  rw [key]
  refine (measurableSet_hitCell f hσ hY hK t).union (MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun hq => ?_)
  exact f.mono hq.le _ (measurableSet_hitCell f hσ hY hK _)

/-- `Y(τ)` is `ℱ_τ`-measurable on `{τ < ∞}`, for any stopping time `τ` and any adapted process
with step paths. -/
theorem measurableSet_stopped_eq {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime f τ)
    (hY : ∀ t, Measurable[f t] fun ω => Y ω t) (hstep : ∀ ω, IsStepPath (Y ω))
    (z : Fin k → ℤ) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤ ∧ Y ω (stopReal τ ω) = z} := by
  have hprog := isStronglyProgressive_of_rc f (fun t ω => Y ω t) hY
    (fun ω t => (hstep ω).rc t)
  have hm := measurable_stoppedValue hprog hτ
  have h1 : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    (hτ.measurable (measurableSet_singleton (⊤ : WithTop ℝ≥0))).compl
  have h2 : MeasurableSet[hτ.measurableSpace] (stoppedValue (fun t ω => Y ω t) τ ⁻¹' {z}) :=
    hm (measurableSet_singleton z)
  have : {ω | τ ω ≠ ⊤ ∧ Y ω (stopReal τ ω) = z} =
      {ω | τ ω ≠ ⊤} ∩ stoppedValue (fun t ω => Y ω t) τ ⁻¹' {z} := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      stoppedValue]
    refine and_congr_right fun hne => ?_
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
    simp only [stopReal, ← ha, WithTop.untopD_coe]
  rw [this]
  exact h1.inter h2

end

end ElboimSly.Paper
