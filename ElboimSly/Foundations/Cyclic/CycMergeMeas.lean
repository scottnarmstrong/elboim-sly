/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycEvents
public import ElboimSly.Foundations.Cyclic.BwdTrajMeas
public import ElboimSly.Frozen.Defs.CycOmega
import Mathlib

/-!
# Measurability of the merging events

Measurability, Step 4 (merging and `Ω`), and Step 5 (joint measurability of `W`).

For a fixed shift `k`, the agreement `W₁(s) = W₂(s + c - kβ)` of two right-continuous piecewise
constant paths on a closed interval holds somewhere iff it holds at a rational point of
`[α, α')` or at the right endpoint `α'`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Rational reduction for a predicate that persists to the right. -/
theorem exists_Icc_iff_rational {P : ℝ → Prop} {α α' : ℝ} (hle : α ≤ α')
    (hP : ∀ s ∈ Ico α α', P s → ∃ ε > 0, ∀ u ∈ Ico s (s + ε), P u) :
    (∃ s ∈ Icc α α', P s) ↔ (∃ q : ℚ, (q : ℝ) ∈ Ico α α' ∧ P q) ∨ P α' := by
  constructor
  · rintro ⟨s, ⟨hs1, hs2⟩, hs⟩
    rcases hs2.lt_or_eq with hlt | rfl
    · left
      obtain ⟨ε, hε, hu⟩ := hP s ⟨hs1, hlt⟩ hs
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hlt (lt_add_of_pos_right s hε))
      exact ⟨q, ⟨hs1.trans hq1.le, hq2.trans_le (min_le_left _ _)⟩,
        hu q ⟨hq1.le, hq2.trans_le (min_le_right _ _)⟩⟩
    · exact Or.inr hs
  · rintro (⟨q, hq, hPq⟩ | h)
    · exact ⟨q, ⟨hq.1, hq.2.le⟩, hPq⟩
    · exact ⟨α', ⟨hle, le_rfl⟩, h⟩

theorem cycWalk_rightCont {ν : Measure (RingSpace d β)} (hν : Good ν) (x : Fin d → ℤ) (q : ℝ)
    {s : ℝ} (hs : 0 ≤ s) : ∀ᶠ u in 𝓝[≥] s, cycWalk ν x q u = cycWalk ν x q s := by
  have hpath := (fwdTraj_isPathOn hν x q (q + s + 1)).1 (q + s) ⟨by linarith, by linarith⟩
  have ht : Tendsto (fun u : ℝ => q + u) (𝓝[≥] s) (𝓝[≥] (q + s)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_const.add continuous_id).tendsto s |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (a := s) (s := Ici s)] with u hu
      exact (add_le_add_iff_left q).mpr hu
  filter_upwards [ht.eventually hpath, self_mem_nhdsWithin (a := s) (s := Ici s),
    (nhdsWithin_le_nhds (Iio_mem_nhds (show s < s + 1 by linarith)))] with u h1 h2 h3
  rw [cycWalk_of_nonneg hν x q (hs.trans h2), cycWalk_of_nonneg hν x q hs]
  exact h1 (by simp only [Set.mem_Iio] at h3; linarith)

theorem cycWalk_pair_persist {ν : Measure (RingSpace d β)} (hν : Good ν)
    (u₁ u₂ : Fin d → ℤ) (q₁ q₂ δ : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : 0 ≤ s + δ)
    (hP : cycWalk ν u₁ q₁ s = cycWalk ν u₂ q₂ (s + δ)) :
    ∃ ε > 0, ∀ u ∈ Ico s (s + ε), cycWalk ν u₁ q₁ u = cycWalk ν u₂ q₂ (u + δ) := by
  have e1 := cycWalk_rightCont hν u₁ q₁ hs0
  have e2 := cycWalk_rightCont hν u₂ q₂ hs1
  have ht : Tendsto (fun u : ℝ => u + δ) (𝓝[≥] s) (𝓝[≥] (s + δ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_id.add continuous_const).tendsto s |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (a := s) (s := Ici s)] with u hu
      exact (add_le_add_iff_right δ).mpr hu
  have hev : ∀ᶠ u in 𝓝[≥] s, cycWalk ν u₁ q₁ u = cycWalk ν u₂ q₂ (u + δ) := by
    filter_upwards [e1, ht.eventually e2] with u h1 h2
    rw [h1, h2, hP]
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
  exact ⟨u' - s, by simp only [Set.mem_Ioi] at hu'; linarith, fun u hu => hsub
    ⟨hu.1, by have := hu.2; linarith⟩⟩

theorem measurableSet_and_of {α : Type*} [MeasurableSpace α] (c : Prop) {A : Set α}
    (hA : c → MeasurableSet A) : MeasurableSet {x | c ∧ x ∈ A} := by
  by_cases hc : c
  · simpa [hc] using hA hc
  · simp [hc]

theorem cycMerges_iff_rational {ν : Measure (RingSpace d β)} (hν : Good ν)
    (u₁ u₂ : Fin d → ℤ) (q₁ q₂ t' : ℝ) :
    cycMerges ν u₁ u₂ q₁ q₂ t' ↔ ∃ k : ℤ,
      max 0 (-(q₁ - q₂ - k * β)) ≤ min t' (t' - (q₁ - q₂ - k * β)) ∧
      ((∃ r : ℚ, (r : ℝ) ∈ Ico (max 0 (-(q₁ - q₂ - k * β))) (min t' (t' - (q₁ - q₂ - k * β))) ∧
          cycWalk ν u₁ q₁ r = cycWalk ν u₂ q₂ (r + (q₁ - q₂ - k * β))) ∨
        cycWalk ν u₁ q₁ (min t' (t' - (q₁ - q₂ - k * β))) =
          cycWalk ν u₂ q₂ (min t' (t' - (q₁ - q₂ - k * β)) + (q₁ - q₂ - k * β))) := by
  have step : cycMerges ν u₁ u₂ q₁ q₂ t' ↔ ∃ k : ℤ, ∃ s ∈ Icc (max 0 (-(q₁ - q₂ - k * β)))
      (min t' (t' - (q₁ - q₂ - k * β))), cycWalk ν u₁ q₁ s =
        cycWalk ν u₂ q₂ (s + (q₁ - q₂ - k * β)) := by
    constructor
    · rintro ⟨s₁, s₂, ⟨h1, h1'⟩, ⟨h2, h2'⟩, ⟨k, hk⟩, hW⟩
      have e : s₂ = s₁ + (q₁ - q₂ - k * β) := by linarith
      refine ⟨k, s₁, ⟨max_le h1 (by linarith), le_min h1' (by linarith)⟩, ?_⟩
      rw [← e]; exact hW
    · rintro ⟨k, s, ⟨h1, h2⟩, hW⟩
      have a1 := le_max_left 0 (-(q₁ - q₂ - k * β))
      have a2 := le_max_right 0 (-(q₁ - q₂ - k * β))
      have b1 := min_le_left t' (t' - (q₁ - q₂ - k * β))
      have b2 := min_le_right t' (t' - (q₁ - q₂ - k * β))
      refine ⟨s, s + (q₁ - q₂ - k * β), ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
        ⟨k, by linarith⟩, hW⟩
  rw [step]
  refine exists_congr fun k => ?_
  set δ := q₁ - q₂ - k * β with hδ
  set α := max 0 (-δ)
  set α' := min t' (t' - δ)
  constructor
  · rintro ⟨s, hs, hW⟩
    have hle : α ≤ α' := hs.1.trans hs.2
    refine ⟨hle, (exists_Icc_iff_rational hle (P := fun s => cycWalk ν u₁ q₁ s =
      cycWalk ν u₂ q₂ (s + δ)) ?_).mp ⟨s, hs, hW⟩⟩
    intro s' hs' hP
    have a1 := le_max_left 0 (-δ)
    have a2 := le_max_right 0 (-δ)
    exact cycWalk_pair_persist hν u₁ u₂ q₁ q₂ δ (a1.trans hs'.1) (by linarith [hs'.1]) hP
  · rintro ⟨hle, h⟩
    exact (exists_Icc_iff_rational hle (P := fun s => cycWalk ν u₁ q₁ s =
      cycWalk ν u₂ q₂ (s + δ)) (fun s' hs' hP => by
        have a1 := le_max_left 0 (-δ)
        have a2 := le_max_right 0 (-δ)
        exact cycWalk_pair_persist hν u₁ u₂ q₁ q₂ δ (a1.trans hs'.1)
          (by linarith [hs'.1]) hP)).mpr h

/-- The merging event is measurable (on `Good`). -/
theorem measurableSet_cycMerges (u₁ u₂ : Fin d → ℤ) (q₁ q₂ t' : ℝ) :
    MeasurableSet {ν : Measure (RingSpace d β) | Good ν ∧ cycMerges ν u₁ u₂ q₁ q₂ t'} := by
  refine measurableSet_good_and ?_
  let eqs : ℝ → Set (GoodSet d β) := fun s => {ν | cycWalk ν.1 u₁ q₁ s = cycWalk ν.1 u₂ q₂ (s + (0:ℝ))}
  have key : ∀ (δ : ℝ) (s : ℝ), 0 ≤ s → 0 ≤ s + δ →
      MeasurableSet {ν : GoodSet d β | cycWalk ν.1 u₁ q₁ s = cycWalk ν.1 u₂ q₂ (s + δ)} :=
    fun δ s h1 h2 => measurableSet_eq_fun (measurable_cycWalk u₁ q₁ h1) (measurable_cycWalk u₂ q₂ h2)
  have : {ν : GoodSet d β | cycMerges ν.1 u₁ u₂ q₁ q₂ t'} = ⋃ k : ℤ,
      ({_ν : GoodSet d β | max 0 (-(q₁ - q₂ - k * β)) ≤ min t' (t' - (q₁ - q₂ - k * β))} ∩
        ((⋃ r : ℚ, {ν : GoodSet d β | (r : ℝ) ∈ Ico (max 0 (-(q₁ - q₂ - k * β)))
            (min t' (t' - (q₁ - q₂ - k * β))) ∧ cycWalk ν.1 u₁ q₁ r =
              cycWalk ν.1 u₂ q₂ (r + (q₁ - q₂ - k * β))}) ∪
          {ν : GoodSet d β | max 0 (-(q₁ - q₂ - k * β)) ≤ min t' (t' - (q₁ - q₂ - k * β)) ∧
            cycWalk ν.1 u₁ q₁ (min t' (t' - (q₁ - q₂ - k * β))) =
            cycWalk ν.1 u₂ q₂ (min t' (t' - (q₁ - q₂ - k * β)) + (q₁ - q₂ - k * β))})) := by
    ext ν
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_union]
    rw [cycMerges_iff_rational ν.2]
    constructor
    · rintro ⟨k, hle, h⟩
      exact ⟨k, hle, h.imp id (fun h' => ⟨hle, h'⟩)⟩
    · rintro ⟨k, hle, h⟩
      exact ⟨k, hle, h.imp id (fun h' => h'.2)⟩
  rw [this]
  refine MeasurableSet.iUnion fun k => (MeasurableSet.const _).inter ?_
  set δ := q₁ - q₂ - k * β
  refine MeasurableSet.union (MeasurableSet.iUnion fun r => ?_) ?_
  · have hh := measurableSet_and_of (α := GoodSet d β)
      ((r : ℝ) ∈ Ico (max 0 (-δ)) (min t' (t' - δ)))
      (A := {ν : GoodSet d β | cycWalk ν.1 u₁ q₁ r = cycWalk ν.1 u₂ q₂ (r + δ)}) (fun h =>
        key δ r ((le_max_left _ _).trans h.1) (by have := h.1; have := le_max_right 0 (-δ); linarith))
    exact hh
  · refine measurableSet_and_of (α := GoodSet d β) (max 0 (-δ) ≤ min t' (t' - δ)) (fun hle => ?_)
    exact key δ _ ((le_max_left _ _).trans hle) (by have := le_max_right 0 (-δ); linarith)

/-- The event `Ω(u₁, u₂, q₁, q₂; t')` is measurable (on `Good`). -/
theorem measurableSet_cycOmega (u₁ u₂ : Fin d → ℤ) (q₁ q₂ t' : ℝ) :
    MeasurableSet {ν : Measure (RingSpace d β) | Good ν ∧ cycOmega ν u₁ u₂ q₁ q₂ t'} := by
  have : {ν : Measure (RingSpace d β) | Good ν ∧ cycOmega ν u₁ u₂ q₁ q₂ t'} =
      {ν | Good ν} \ ({ν | Good ν ∧ cycMerges ν u₁ u₂ q₁ q₂ t'} ∪
        {ν | Good ν ∧ cycClosesBy ν u₁ q₁ t'} ∪ {ν | Good ν ∧ cycClosesBy ν u₂ q₂ t'}) := by
    ext ν
    simp only [cycOmega, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union]
    tauto
  rw [this]
  exact measurableSet_good.diff (((measurableSet_cycMerges u₁ u₂ q₁ q₂ t').union
    (measurableSet_cycClosesBy u₁ q₁ t')).union (measurableSet_cycClosesBy u₂ q₂ t'))

end ElboimSly.Cyclic

end
