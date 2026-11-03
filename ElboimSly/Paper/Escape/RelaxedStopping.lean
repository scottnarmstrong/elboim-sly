/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.RelaxedFirst
public import ElboimSly.Paper.Escape.Phases
public import ElboimSly.Paper.Step.RelaxedAdapted
public import ElboimSly.Foundations.Cyclic.CPathStop
public import Mathlib

/-!
# First relaxed times are stopping times

First relaxed times are relaxed and are stopping times (c).  For an adapted process `P` with paths in `CPath`, a
stopping time `prev` (the role of `ζ_{i-1}`) and constants `0 ≤ lo ≤ hi` (`a_i`, `b_i`) with
`prev ≤ lo`, the time `escZetaStep β (cpathReal (P ω)) lo hi (prev ω)` (`ζ_i`) is a stopping time.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {k : ℕ}

lemma cpathReal_rc (p : CPath (Fin (k + 2) → ℤ)) (r : ℝ) :
    ∃ ε > 0, ∀ s' ∈ Ico r (r + ε), cpathReal p s' = cpathReal p r := by
  by_cases hr : r < 0
  · refine ⟨-r, by linarith, fun s' hs' => ?_⟩
    have h1 : s'.toNNReal = 0 := Real.toNNReal_of_nonpos (by linarith [hs'.2])
    have h2 : r.toNNReal = 0 := Real.toNNReal_of_nonpos hr.le
    simp only [cpathReal, h1, h2]
  · push Not at hr
    obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (p.rc r.toNNReal)
    refine ⟨(u' : ℝ) - r, ?_, fun s' hs' => ?_⟩
    · have : (r.toNNReal : ℝ) < u' := by exact_mod_cast hu'
      rw [Real.coe_toNNReal _ hr] at this
      linarith
    · have hs'0 : 0 ≤ s' := hr.trans hs'.1
      have := hsub ⟨Real.toNNReal_le_toNNReal hs'.1, by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs'0]; linarith [hs'.2]⟩
      exact this

lemma cpathReal_hrc (p : CPath (Fin (k + 2) → ℤ)) {a : ℝ} (_ha : 0 ≤ a) :
    ∀ s, a ≤ s → ∀ᶠ u in 𝓝[≥] s, cpathReal p u = cpathReal p s := by
  intro s hs
  obtain ⟨ε, hε, h⟩ := cpathReal_rc p s
  exact mem_nhdsGE_iff_exists_Ico_subset.2 ⟨s + ε, lt_add_of_pos_right s hε, fun u hu => h u hu⟩

/-- Pointwise: for a deadline `s < hi`, `ζ ≤ s` iff some relaxed time lies in `[lo, s]`. -/
lemma escZetaStep_le_iff {β : ℝ} {y : ℝ → Fin (k + 2) → ℤ} {lo hi prev s : ℝ}
    (hrc : ∀ r, prev ≤ r → ∀ᶠ u in 𝓝[≥] r, y u = y r) (hs : s < hi) :
    escZetaStep β y lo hi prev ≤ s ↔
      ∃ s' ∈ relaxedSet β y prev, lo ≤ s' ∧ s' ≤ s := by
  unfold escZetaStep
  split_ifs with h
  · have hne : (relaxedSet β y prev ∩ Ici lo).Nonempty := by
      obtain ⟨s0, hs0, h1, -⟩ := h
      exact ⟨s0, hs0, h1⟩
    constructor
    · intro hle
      obtain ⟨hm, hlm⟩ := csInf_mem_relaxedSet hrc hne
      exact ⟨_, hm, hlm, hle⟩
    · rintro ⟨s', hs', hl, hss⟩
      exact (csInf_le (show BddBelow (relaxedSet β y prev ∩ Ici lo) from ⟨lo, fun x hx => hx.2⟩) ⟨hs', hl⟩).trans hss
  · constructor
    · intro hle; exact absurd hle (not_le.2 hs)
    · rintro ⟨s', hs', hl, hss⟩
      exact absurd ⟨s', hs', hl, lt_of_le_of_lt hss hs⟩ h

lemma escZetaStep_le_hi {β : ℝ} {y : ℝ → Fin (k + 2) → ℤ} {lo hi prev : ℝ} :
    escZetaStep β y lo hi prev ≤ hi := by
  unfold escZetaStep
  split_ifs with h
  · obtain ⟨s0, hs0, h1, h2⟩ := h
    exact ((csInf_le (show BddBelow (relaxedSet β y prev ∩ Ici lo) from ⟨lo, fun x hx => hx.2⟩) ⟨hs0, h1⟩).trans h2.le)
  · exact le_rfl

/-- Measurability of the event `∃ s' ∈ S ∩ [lo, s]` in `𝓕_s`. -/
theorem measurableSet_exists_relaxed {Ω : Type*} {mΩ : MeasurableSpace Ω} {β : ℝ} (hβ : 0 < β)
    (f : Filtration ℝ≥0 mΩ) (P : Ω → CPath (Fin (k + 2) → ℤ))
    (hP : ∀ s, Measurable[f s] fun ω => (P ω).fn s) (prev : Ω → ℝ≥0)
    (hprev : IsStoppingTime f fun ω => ((prev ω : ℝ≥0) : WithTop ℝ≥0)) {lo : ℝ} (hlo : 0 ≤ lo)
    (hpl : ∀ ω, (prev ω : ℝ) ≤ lo) (s : ℝ≥0) :
    MeasurableSet[f s]
      {ω | ∃ s' ∈ relaxedSet β (cpathReal (P ω)) (prev ω), lo ≤ s' ∧ s' ≤ s} := by
  have : Fact (0 < β) := ⟨hβ⟩
  -- the stopped paths
  have hP' : Measurable[f s] fun ω => (P ω).stop s := by
    have h := measurable_stoppedPath (f := f) P hP (isStoppingTime_const f s)
    rw [IsStoppingTime.measurableSpace_const] at h
    exact h
  have hprevN : Measurable[f s] fun ω => min (prev ω) s := by
    let : MeasurableSpace Ω := f s
    refine measurable_of_Iic fun x => ?_
    by_cases hx : s ≤ x
    · have : (fun ω => min (prev ω) s) ⁻¹' Iic x = univ := by
        ext ω; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (min_le_right _ _).trans hx
      rw [this]; exact MeasurableSet.univ
    · push Not at hx
      have : (fun ω => min (prev ω) s) ⁻¹' Iic x = {ω | (prev ω : WithTop ℝ≥0) ≤ x} := by
        ext ω
        simp only [mem_preimage, mem_Iic, mem_ofPred_eq, WithTop.coe_le_coe]
        constructor
        · intro h
          rcases min_le_iff.1 h with h | h
          · exact h
          · exact absurd h (not_le.2 hx)
        · intro h; exact (min_le_left _ _).trans h
      rw [this]; exact f.mono hx.le _ (hprev x)
  -- equal to the event for the stopped paths
  set P' : Ω → CPath (Fin (k + 2) → ℤ) := fun ω => (P ω).stop s with hP'def
  have hcongr : ∀ ω, ∀ s' : ℝ, 0 ≤ s' → s' ≤ s → (prev ω : ℝ) ≤ s' →
      (ElboimSly.IsRelaxedTimeWrt β (cpathReal (P ω)) (prev ω) s' ↔
        ElboimSly.IsRelaxedTimeWrt β (cpathReal (P' ω)) ((min (prev ω) s : ℝ≥0) : ℝ) s') := by
    intro ω s' hs'0 hs's hps
    have hmin : ((min (prev ω) s : ℝ≥0) : ℝ) = prev ω := by
      rw [min_eq_left]; exact_mod_cast hps.trans hs's
    rw [hmin]
    refine isRelaxedTimeWrt_congr_le hβ (fun r hr0 hrs => ?_) (NNReal.coe_nonneg _) hs'0
    simp only [cpathReal, hP'def, CPath.stop_fn]
    rw [min_eq_left]
    exact Real.toNNReal_le_iff_le_coe.2 (hrs.trans hs's)
  have hminle : ∀ ω, ((min (prev ω) s : ℝ≥0) : ℝ) ≤ prev ω := fun ω => by
    exact_mod_cast min_le_left (prev ω) s
  have hset : {ω | ∃ s' ∈ relaxedSet β (cpathReal (P ω)) (prev ω), lo ≤ s' ∧ s' ≤ s} =
      {ω | (lo ≤ s ∧ ElboimSly.IsRelaxedTimeWrt β (cpathReal (P' ω)) ((min (prev ω) s : ℝ≥0) : ℝ) lo) ∨
        ∃ k : ℕ, lo < ((P' ω).jt k).toReal ∧ (P' ω).jt k ≤ (s : ℝ≥0∞) ∧
          ElboimSly.IsRelaxedTimeWrt β (cpathReal (P' ω)) ((min (prev ω) s : ℝ≥0) : ℝ)
            ((P' ω).jt k).toReal} := by
    ext ω
    have hpl' : ((min (prev ω) s : ℝ≥0) : ℝ) ≤ lo := (hminle ω).trans (hpl ω)
    rw [mem_ofPred_eq, mem_ofPred_eq, ← exists_relaxed_iff_jumps (β := β) (P' ω) hpl' hlo s]
    constructor
    · rintro ⟨s', hs', hl, hss⟩
      have hps : (prev ω : ℝ) ≤ s' := hs'.1
      exact ⟨s', ⟨(hminle ω).trans hps, (hcongr ω s' (hlo.trans hl) hss hps).1 hs'.2⟩, hl, hss⟩
    · rintro ⟨s', hs', hl, hss⟩
      have hps : (prev ω : ℝ) ≤ s' := (hpl ω).trans hl
      exact ⟨s', ⟨hps, (hcongr ω s' (hlo.trans hl) hss hps).2 hs'.2⟩, hl, hss⟩
  rw [hset]
  -- measurability
  let : MeasurableSpace Ω := f s
  have hW : Measurable fun p : Ω × ℝ => cpathReal (P' p.1) p.2 :=
    measurable_fn_at (α := Ω × ℝ) (fun p => P' p.1) (hP'.comp measurable_fst) _
      measurable_snd.real_toNNReal
  have ha : Measurable fun ω => ((min (prev ω) s : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp hprevN
  have ha' : Measurable fun p : Ω × ℝ =>
      (fun (ω : Ω) (_ : ℝ) => ((min (prev ω) s : ℝ≥0) : ℝ)) p.1 p.2 :=
    ha.comp measurable_fst
  have hrc : ∀ ω r, ∃ ε > 0, ∀ s' ∈ Ico r (r + ε), cpathReal (P' ω) s' = cpathReal (P' ω) r :=
    fun ω r => cpathReal_rc (P' ω) r
  rw [ofPred_or]
  refine MeasurableSet.union ?_ ?_
  · by_cases hls : lo ≤ s
    · have := measurableSet_relaxed_section (Ω' := Ω) hβ (fun ω r => cpathReal (P' ω) r)
        (fun ω => ((min (prev ω) s : ℝ≥0) : ℝ)) lo hW ha hrc
      simp only [hls, true_and]; exact this
    · simp [hls]
  · rw [ofPred_exists]
    refine MeasurableSet.iUnion fun k => ?_
    have hτ : Measurable fun ω => ((P' ω).jt k).toReal :=
      ENNReal.measurable_toReal.comp ((CPath.measurable_jt k).comp hP')
    have hjt : Measurable fun ω => (P' ω).jt k := (CPath.measurable_jt k).comp hP'
    have hjoint := measurableSet_isRelaxedTimeWrt (β := β) (fun ω r => cpathReal (P' ω) r)
      (fun ω _ => ((min (prev ω) s : ℝ≥0) : ℝ)) hW ha' hrc
    have hpre : MeasurableSet {ω | ElboimSly.IsRelaxedTimeWrt β (cpathReal (P' ω))
        ((min (prev ω) s : ℝ≥0) : ℝ) ((P' ω).jt k).toReal} :=
      (measurable_id.prodMk hτ) hjoint
    have h1 : MeasurableSet {ω | lo < ((P' ω).jt k).toReal} := measurableSet_lt measurable_const hτ
    have h2 : MeasurableSet {ω | (P' ω).jt k ≤ (s : ℝ≥0∞)} := measurableSet_le hjt measurable_const
    exact (h1.inter (h2.inter hpre))

/-- First relaxed times are relaxed and are stopping times (c).  If `prev` is a stopping time with `prev ≤ lo`, then
`ζ = escZetaStep β (cpathReal (P ·)) lo hi prev` (the first relaxed time `≥ lo`, or `hi`) is a
stopping time. -/
theorem isStoppingTime_escZetaStep {Ω : Type*} {mΩ : MeasurableSpace Ω} {β : ℝ} (hβ : 0 < β)
    (f : Filtration ℝ≥0 mΩ) (P : Ω → CPath (Fin (k + 2) → ℤ))
    (hP : ∀ s, Measurable[f s] fun ω => (P ω).fn s) (prev : Ω → ℝ≥0)
    (hprev : IsStoppingTime f fun ω => ((prev ω : ℝ≥0) : WithTop ℝ≥0)) {lo hi : ℝ}
    (hlo : 0 ≤ lo) (_hlh : lo ≤ hi) (hpl : ∀ ω, (prev ω : ℝ) ≤ lo) :
    IsStoppingTime f fun ω =>
      (((escZetaStep β (cpathReal (P ω)) lo hi (prev ω)).toNNReal : ℝ≥0) : WithTop ℝ≥0) := by
  intro s
  have key : {ω | (((escZetaStep β (cpathReal (P ω)) lo hi (prev ω)).toNNReal : ℝ≥0) :
      WithTop ℝ≥0) ≤ s} = {ω | escZetaStep β (cpathReal (P ω)) lo hi (prev ω) ≤ s} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
  rw [key]
  by_cases hs : hi ≤ s
  · have : {ω | escZetaStep β (cpathReal (P ω)) lo hi (prev ω) ≤ s} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact escZetaStep_le_hi.trans hs
    rw [this]; exact MeasurableSet.univ
  · push Not at hs
    have : {ω | escZetaStep β (cpathReal (P ω)) lo hi (prev ω) ≤ s} =
        {ω | ∃ s' ∈ relaxedSet β (cpathReal (P ω)) (prev ω), lo ≤ s' ∧ s' ≤ s} := by
      ext ω
      exact escZetaStep_le_iff (cpathReal_hrc (P ω) (NNReal.coe_nonneg _)) hs
    rw [this]
    exact measurableSet_exists_relaxed hβ f P hP prev hprev hlo hpl s

end ElboimSly.Paper
