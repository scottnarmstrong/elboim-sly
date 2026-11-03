/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadMeasRelaxed
public import ElboimSly.Paper.Heavy.BadFinite

/-!
# Measurability of badness: auxiliary facts

Properties of discovered bad blocks (c), (d).

* `IsCyclicPath.exists_plateau`: a cyclic path is constant on a right neighbourhood of each
  `s ≥ 0`.
* `exists_Icc_iff_rat`: for a right-open property `P` on `[a, b]`, `∃ u ∈ [a, b], P u` iff `P b` or
  `P q` for a rational `q ∈ (a, b)`.  This is the "elementary fact" of the proof of (d).
* `AdaptedCyclic.measurableSet_segClosed`: closing of a segment is `ℱ_t`-measurable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

theorem IsCyclicPath.exists_plateau {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w) {s : ℝ}
    (hs : 0 ≤ s) : ∃ η > 0, ∀ s' ∈ Ico s (s + η), w s' = w s := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw.rc s hs)
  exact ⟨u - s, sub_pos.2 (mem_Ioi.1 hu), fun s' hs' => hsub ⟨hs'.1, by linarith [hs'.2]⟩⟩

theorem exists_Icc_iff_rat {P : ℝ → Prop} {a b : ℝ} (hab : a ≤ b)
    (hP : ∀ u ∈ Icc a b, ∃ η > 0, ∀ u' ∈ Ico u (u + η), P u' ↔ P u) :
    (∃ u ∈ Icc a b, P u) ↔ P b ∨ ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b ∧ P q := by
  constructor
  · rintro ⟨u, hu, hPu⟩
    rcases hu.2.eq_or_lt with rfl | hlt
    · exact Or.inl hPu
    · obtain ⟨η, hη, hη'⟩ := hP u hu
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u < min b (u + η) from
        lt_min hlt (by linarith))
      refine Or.inr ⟨q, hu.1.trans_lt hq1, hq2.trans_le (min_le_left _ _), ?_⟩
      exact (hη' q ⟨hq1.le, hq2.trans_le (min_le_right _ _)⟩).2 hPu
  · rintro (h | ⟨q, hq1, hq2, hq⟩)
    · exact ⟨b, ⟨hab, le_rfl⟩, h⟩
    · exact ⟨q, ⟨hq1.le, hq2.le⟩, hq⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m} {W : Ω → ℝ → Fin d → ℤ}

theorem AdaptedCyclic.measurableSet_eq (h : AdaptedCyclic f W) {s₁ s₂ : ℝ} (h1 : 0 ≤ s₁)
    (h2 : 0 ≤ s₂) {t : ℝ≥0} (h1t : s₁ ≤ t) (h2t : s₂ ≤ t) :
    MeasurableSet[f t] {ω | W ω s₁ = W ω s₂} := by
  have := (h.measurableSet_ne h1 h2 h1t h2t).compl
  convert this using 1
  ext ω; simp

/-- Closing of the segment at `x` is `ℱ_t`-measurable when `x + t'_k ≤ t`. -/
theorem AdaptedCyclic.measurableSet_segClosed (h : AdaptedCyclic f W) {β tk x : ℝ}
    (_hβ : 0 < β) {t : ℝ≥0} (_htk : 0 ≤ tk) (hx : 0 ≤ x) (hxt : x + tk ≤ t) :
    MeasurableSet[f t] {ω | SegClosed β tk (W ω) x} := by
  have hset : {ω | SegClosed β tk (W ω) x} =
      ⋃ ℓ : ℤ, ⋃ _ : 0 < (ℓ : ℝ) * β ∧ (ℓ : ℝ) * β ≤ tk, {ω | W ω (x + ℓ * β) = W ω x} := by
    ext ω
    simp only [SegClosed, mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨u, hu0, hu1, ⟨ℓ, rfl⟩, hw⟩
      exact ⟨ℓ, ⟨hu0, hu1⟩, hw⟩
    · rintro ⟨ℓ, ⟨hu0, hu1⟩, hw⟩
      exact ⟨ℓ * β, hu0, hu1, ⟨ℓ, rfl⟩, hw⟩
  rw [hset]
  refine MeasurableSet.iUnion fun ℓ => MeasurableSet.iUnion fun hℓ => ?_
  exact h.measurableSet_eq (by linarith [hℓ.1]) hx (by linarith [hℓ.2]) (by linarith)

end ElboimSly.Paper
