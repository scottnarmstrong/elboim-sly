/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasFast
public import Mathlib

/-!
# `τ_fast` for right-continuous paths vanishing at `0`

Measurability (c), pathwise consequences of tfast and heavyJ (d).

The statements of `Paper/Heavy/Attained` and `Paper/Heavy/MeasFast` are phrased for `IsCyclicPath`,
but their proofs only use right-continuity and `w 0 = 0`. These are the same statements for such
paths (the regenerated walk driven by a path is not known to satisfy the unit jump condition of
`IsCyclicPath` in the Lean development).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

theorem tfastSet_stable' (hrc : ∀ s : ℝ, 0 ≤ s → ∀ᶠ u in 𝓝[≥] s, w u = w s) (hz : w 0 = 0) {L : ℝ} (hL : 0 < L) :
    ∀ t : ℝ, 0 ≤ t → t ∉ tfastSet w L → ∃ η > 0, ∀ t' ∈ Ico t (t + η), t' ∉ tfastSet w L := by
  intro t ht htS
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hrc t ht)
  refine ⟨u - t, by linarith [mem_Ioi.1 hu], fun t' ht' => ?_⟩
  have ht'u : t' ∈ Ico t u := ⟨ht'.1, by have := ht'.2; linarith⟩
  have hwt' : w t' = w t := hsub ht'u
  rintro ⟨ht'0, s, hs1, hs2, hge⟩
  rcases le_or_gt t s with hts | hts
  · have hs0 : max s 0 = s := max_eq_left (ht.trans hts)
    have : w s = w t := hsub ⟨hts, lt_of_le_of_lt hs2 ht'u.2⟩
    rw [hs0, this, hwt', sub_self, norm_zero] at hge
    linarith
  · rcases eq_or_lt_of_le ht with ht0 | ht0
    · have hs0 : max s 0 = 0 := max_eq_right (by linarith)
      rw [hs0, hwt', ← ht0, hz, sub_self, norm_zero] at hge
      linarith
    · apply htS
      refine ⟨ht0, s, by linarith [ht'.1], hts.le, ?_⟩
      rwa [hwt'] at hge


theorem ofReal_lt_pathTfast_iff' (hrc : ∀ s : ℝ, 0 ≤ s → ∀ᶠ u in 𝓝[≥] s, w u = w s) (hz : w 0 = 0) {L : ℝ} (hL : 0 < L) (T : ℝ) :
    ENNReal.ofReal T < pathTfast w L ↔
      ∀ t : ℝ, 0 < t → t ≤ T → ∀ s : ℝ, t - 1 ≤ s → s ≤ t → ‖w t - w (max s 0)‖ < L := by
  rw [pathTfast_eq, ofReal_lt_iInf_iff (tfastSet_pos w L) (tfastSet_stable' hrc hz hL)]
  constructor
  · intro h t ht0 htT s hs1 hs2
    by_contra hc
    push Not at hc
    exact absurd (h t ⟨ht0, s, hs1, hs2, hc⟩) (not_lt.2 htT)
  · rintro h t ⟨ht0, s, hs1, hs2, hge⟩
    by_contra hc
    exact absurd (h t ht0 (not_lt.1 hc) s hs1 hs2) (not_lt.2 hge)


theorem pathTfast_le_iff_rational' (hrc : ∀ s : ℝ, 0 ≤ s → ∀ᶠ u in 𝓝[≥] s, w u = w s) (hz : w 0 = 0) {L : ℝ} (hL : 0 < L) {T : ℝ}
    (hT : 0 ≤ T) :
    pathTfast w L ≤ ENNReal.ofReal T ↔
      ∃ t ∈ rationalTimes T, ∃ q : ℚ, t - 1 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧
        L ≤ ‖w t - w (max (q : ℝ) 0)‖ := by
  constructor
  · intro h
    have hnot : ¬ ENNReal.ofReal T < pathTfast w L := not_lt.2 h
    rw [ofReal_lt_pathTfast_iff' hrc hz hL] at hnot
    push Not at hnot
    obtain ⟨t, ht0, htT, s, hs1, hs2, hL'⟩ := hnot
    have hst : s < t := by
      rcases hs2.eq_or_lt with rfl | h
      · rw [max_eq_left ht0.le, sub_self, norm_zero] at hL'; linarith
      · exact h
    obtain ⟨ηt, hηt, hsubt⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hrc t ht0.le)
    obtain ⟨ηs, hηs, hsubs⟩ := mem_nhdsGE_iff_exists_Ico_subset.1
      (hrc (max s 0) (le_max_right _ _))
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


end ElboimSly.Paper.Step
