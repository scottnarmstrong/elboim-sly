/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasJump2

/-!
# `τ_fast` is a stopping time

Measurability (c).

`pathTfast_le_iff_rational`: `τ_fast(w; L) ≤ T` iff there are `t ∈ rationalTimes T` and a rational
`q ∈ [t - 1, t)` with `L ≤ ‖w t - w (max q 0)‖`.  (Shift `(s, t)` to the right by the same small
amount and then move `s` to a rational: both evaluations are right-locally constant.)
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

theorem pathTfast_le_iff_rational (hw : IsCyclicPath w) {L : ℝ} (hL : 0 < L) {T : ℝ}
    (hT : 0 ≤ T) :
    pathTfast w L ≤ ENNReal.ofReal T ↔
      ∃ t ∈ rationalTimes T, ∃ q : ℚ, t - 1 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧
        L ≤ ‖w t - w (max (q : ℝ) 0)‖ := by
  constructor
  · intro h
    have hnot : ¬ ENNReal.ofReal T < pathTfast w L := not_lt.2 h
    rw [ofReal_lt_pathTfast_iff hw hL] at hnot
    push Not at hnot
    obtain ⟨t, ht0, htT, s, hs1, hs2, hL'⟩ := hnot
    have hst : s < t := by
      rcases hs2.eq_or_lt with rfl | h
      · rw [max_eq_left ht0.le, sub_self, norm_zero] at hL'; linarith
      · exact h
    obtain ⟨ηt, hηt, hsubt⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw.rc t ht0.le)
    obtain ⟨ηs, hηs, hsubs⟩ := mem_nhdsGE_iff_exists_Ico_subset.1
      (hw.rc (max s 0) (le_max_right _ _))
    have hηt' : t < ηt := mem_Ioi.1 hηt
    have hηs' : max s 0 < ηs := mem_Ioi.1 hηs
    -- the new right endpoint
    obtain ⟨t', ht', hδ⟩ : ∃ t' ∈ rationalTimes T, t ≤ t' ∧ t' < ηt ∧ t' - t < ηs - max s 0 := by
      rcases htT.eq_or_lt with rfl | hlt
      · exact ⟨t, Or.inl ⟨ht0, rfl⟩, le_rfl, hηt', by linarith⟩
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < min T (min ηt (t + (ηs - max s 0)))
          from lt_min hlt (lt_min hηt' (by linarith)))
        refine ⟨q, Or.inr ⟨q, by linarith, hq2.trans_le (min_le_left _ _), rfl⟩, hq1.le,
          hq2.trans_le ((min_le_right _ _).trans (min_le_left _ _)), ?_⟩
        have := hq2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
        linarith
    obtain ⟨hδ1, hδ2, hδ3⟩ := hδ
    have hwt' : w t' = w t := hsubt ⟨hδ1, hδ2⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s + (t' - t) < min t' (s + (ηs - max s 0)) from
      lt_min (by linarith) (by linarith))
    have hqs : s ≤ q := by linarith
    have hqs2 : (q : ℝ) < s + (ηs - max s 0) := hq2.trans_le (min_le_right _ _)
    have hwq : w (max (q : ℝ) 0) = w (max s 0) := by
      refine hsubs ⟨max_le_max hqs le_rfl, ?_⟩
      rcases le_total (q : ℝ) 0 with h0 | h0
      · rw [max_eq_right h0]; linarith [le_max_right s 0]
      · rw [max_eq_left h0]
        have := le_max_left s 0
        linarith
    refine ⟨t', ht', q, by linarith, hq2.trans_le (min_le_left _ _), ?_⟩
    rw [hwt', hwq]; exact hL'
  · rintro ⟨t, ht, q, hq1, hq2, hLt⟩
    obtain ⟨ht0, htT⟩ := rationalTimes_pos ht
    exact (iInf₂_le (f := fun t (_ : t ∈ tfastSet w L) => ENNReal.ofReal t) t
      ⟨ht0, q, hq1, hq2.le, hLt⟩).trans (ENNReal.ofReal_le_ofReal htT)

variable {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m} {W : Ω → ℝ → Fin d → ℤ}

/-- Measurability (c): `τ_fast(L)` is a stopping time. -/
theorem AdaptedCyclic.isStoppingTime_pathTfast (h : AdaptedCyclic f W) {L : ℝ} (hL : 0 < L) :
    IsStoppingTime f (fun ω => pathTfast (W ω) L) := by
  intro i
  have hset : {ω | pathTfast (W ω) L ≤ (i : WithTop ℝ≥0)} =
      ⋃ t ∈ rationalTimes i, ⋃ q : ℚ, ⋃ _ : t - 1 ≤ (q : ℝ) ∧ (q : ℝ) < t,
        {ω | L ≤ ‖W ω t - W ω (max (q : ℝ) 0)‖} := by
    ext ω
    have := pathTfast_le_iff_rational (h.path ω) hL (T := (i : ℝ)) (NNReal.coe_nonneg i)
    simp only [ENNReal.ofReal_coe_nnreal] at this
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    exact this.trans (by simp only [and_assoc])
  have key : MeasurableSet[f i] (⋃ t ∈ rationalTimes i, ⋃ q : ℚ,
      ⋃ _ : t - 1 ≤ (q : ℝ) ∧ (q : ℝ) < t, {ω | L ≤ ‖W ω t - W ω (max (q : ℝ) 0)‖}) := by
    refine MeasurableSet.biUnion (rationalTimes_countable _) fun t ht => ?_
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
    obtain ⟨ht0, htT⟩ := rationalTimes_pos ht
    have := ((h.measurable_at ht0.le htT).prodMk
      (h.measurable_at (le_max_right _ _) (max_le (hq.2.le.trans htT) (ht0.le.trans htT))))
      (Set.to_countable {p : (Fin d → ℤ) × (Fin d → ℤ) | L ≤ ‖p.1 - p.2‖}).measurableSet
    exact this
  exact (congrArg (MeasurableSet[f i]) hset).mpr key

end ElboimSly.Paper
