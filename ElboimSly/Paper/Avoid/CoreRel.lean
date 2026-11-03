/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.CoreGammaImp
public import ElboimSly.Paper.Induction.RelaxedMeasWrt
public import Mathlib

/-!
# ES22 §4, Lemma 4.1 (core form): measurability of the relaxedness event

ES22 Lemma 4.1 ("`Rel` lies in `ℋ`"), via measurability of relaxed times.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- Relaxedness along `w|[a, T]` depends only on `w` on `[a, T]`. -/
theorem isRelaxedTimeWrt_congr_on {β : ℝ} {w w' : ℝ → Fin d → ℤ} {a T : ℝ} (_hb : 0 ≤ β ^ indDelta d)
    (hb3 : 0 ≤ β ^ (3 * indDelta d)) (h : ∀ s, a ≤ s → s ≤ T → w s = w' s) (haT : a ≤ T) :
    IsRelaxedTimeWrt β w a T ↔ IsRelaxedTimeWrt β w' a T := by
  have hT : w T = w' T := h T haT le_rfl
  have hV : visitedSet w a T = visitedSet w' a T := by
    unfold visitedSet
    exact Set.image_congr fun s hs => h s hs.1 hs.2
  unfold IsRelaxedTimeWrt IsHeavy
  rw [hT, hV]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun s has hs => ?_⟩
    have := h2 s has hs
    rwa [h s has (by linarith)] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun s has hs => ?_⟩
    have := h2 s has hs
    rwa [← h s has (by linarith)] at this

/-- Real-time right-continuity of the shifted history path. -/
theorem rc_real_of_rc {h : ℝ≥0 → Fin d → ℤ} (hh : IsRCPath h) (c s : ℝ) :
    ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), h (s' - c).toNNReal = h (s - c).toNNReal := by
  by_cases hs : s < c
  · refine ⟨c - s, by linarith, fun s' hs' => ?_⟩
    rw [Real.toNNReal_of_nonpos (by linarith [hs'.2]), Real.toNNReal_of_nonpos (by linarith)]
  · push Not at hs
    set σ : ℝ≥0 := (s - c).toNNReal with hσ
    have hσR : (σ : ℝ) = s - c := Real.coe_toNNReal _ (by linarith)
    obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hh σ)
    refine ⟨(u' : ℝ) - σ, by
      have : (σ : ℝ) < u' := by exact_mod_cast hu'
      linarith, fun s' hs' => ?_⟩
    have hmem : (s' - c).toNNReal ∈ Ico σ u' := by
      refine ⟨Real.toNNReal_le_toNNReal (by linarith [hs'.1]), ?_⟩
      rw [Real.toNNReal_lt_iff_lt_coe (by linarith [hs'.1])]
      linarith [hs'.2]
    exact hsub hmem

/-- **`Rel ∈ ℋ`**: the event that `T` is relaxed along `w|[a, T]` is measurable when the history
is measurable (measurability of relaxed times). Here the ambient `σ`-algebra is `ℋ`. -/
theorem measurableSet_rel {β : ℝ} [Fact (0 < β)] {Ω' : Type*} [MeasurableSpace Ω'] (a T : Ω' → ℝ)
    (w : Ω' → ℝ → Fin d → ℤ) (haT : ∀ ω, a ω ≤ T ω) (ha : Measurable a) (hT : Measurable T)
    (hhist : Measurable fun p : Ω' × ℝ => w p.1 (min (a p.1 + max p.2 0) (T p.1)))
    (hrc : ∀ ω, IsRCPath (fun s : ℝ≥0 => w ω (min (a ω + s) (T ω)))) :
    MeasurableSet {ω | IsRelaxedTimeWrt β (w ω) (a ω) (T ω)} := by
  set w'' : Ω' → ℝ → Fin d → ℤ := fun ω s => w ω (min (a ω + max (s - a ω) 0) (T ω)) with hw''
  have hb : 0 < β ^ indDelta d := Real.rpow_pos_of_pos Fact.out _
  have hb3 : 0 < β ^ (3 * indDelta d) := Real.rpow_pos_of_pos Fact.out _
  have hmeas : Measurable fun p : Ω' × ℝ => w'' p.1 p.2 := by
    have : Measurable fun p : Ω' × ℝ => (p.1, p.2 - a p.1) :=
      measurable_fst.prodMk (measurable_snd.sub (ha.comp measurable_fst))
    exact hhist.comp this
  have hrc'' : ∀ ω s, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), w'' ω s' = w'' ω s := by
    intro ω s
    obtain ⟨ε, hε, hh⟩ := rc_real_of_rc (hrc ω) (a ω) s
    refine ⟨ε, hε, fun s' hs' => ?_⟩
    have := hh s' hs'
    simp only [hw'']
    have e : ∀ x : ℝ, max (x - a ω) 0 = (((x - a ω).toNNReal : ℝ≥0) : ℝ) := fun x => by
      rw [Real.coe_toNNReal']
    rw [e s', e s]
    exact this
  have hS := measurableSet_isRelaxedTimeWrt (β := β) w'' (fun ω _ => a ω) hmeas
    (ha.comp measurable_fst) hrc''
  have : {ω | IsRelaxedTimeWrt β (w ω) (a ω) (T ω)} =
      (fun ω => (ω, T ω)) ⁻¹' {p : Ω' × ℝ | IsRelaxedTimeWrt β (w'' p.1) (a p.1) p.2} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    refine isRelaxedTimeWrt_congr_on hb.le hb3.le (fun s has hsT => ?_) (haT ω)
    simp only [hw'']
    rw [max_eq_left (by linarith), show a ω + (s - a ω) = s by ring]
    exact congrArg (w ω) (min_eq_left hsT).symm
  rw [this]
  exact hS.preimage (measurable_id.prodMk hT)

end ElboimSly.Paper

end
