/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.ProcessLaw
public import Mathlib

/-!
# Unit windows of right-continuous paths are seen at rational times

Written proof: used in ES22 Lemma 5.3 (conditions (3), the event `𝒟`) to replace the uncountable
quantifier over windows `[t - 1, t]` by a countable one.

`exists_win_qSet`: for a right-continuous path `x`, a window `(t, s)` with `0 < t ≤ T`,
`t - 1 ≤ s ≤ t` and `R (x t) (x s)` exists iff one exists with `t, s ∈ qSet 0 T`.
-/

@[expose] public section

open Filter Topology Set
open scoped NNReal

namespace ElboimSly.Paper.Escape

variable {d : ℕ}

/-- A right-continuous path is locally constant to the right. -/
theorem exists_Ico_const {x : ℝ≥0 → Fin d → ℤ} (hx : IsRCPath x) (t : ℝ≥0) :
    ∃ u : ℝ≥0, t < u ∧ ∀ v, t ≤ v → v < u → x v = x t := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hx t)
  exact ⟨u, hu, fun v h1 h2 => hsub ⟨h1, h2⟩⟩

theorem exists_rat_nnreal_btwn {a b : ℝ≥0} (h : a < b) :
    ∃ q : ℝ≥0, a < q ∧ q < b ∧ ∃ r : ℚ, (q : ℝ) = r := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (a : ℝ) < b by exact_mod_cast h)
  have hr0 : (0 : ℝ) ≤ r := le_trans a.2 hr1.le
  refine ⟨Real.toNNReal r, ?_, ?_, r, by rw [Real.coe_toNNReal _ hr0]⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hr1
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hr2

theorem mem_qSet_of_rat {T q : ℝ≥0} (hq : q < T) (hr : ∃ r : ℚ, (q : ℝ) = r) : q ∈ qSet 0 T :=
  Or.inl ⟨bot_le, hq.le, hr⟩

/-- Windows of a right-continuous path are seen at test times. -/
theorem exists_win_qSet {x : ℝ≥0 → Fin d → ℤ} (hx : IsRCPath x) {T : ℝ≥0}
    (R : (Fin d → ℤ) → (Fin d → ℤ) → Prop) :
    (∃ t s : ℝ≥0, 0 < t ∧ t ≤ T ∧ s ≤ t ∧ t ≤ s + 1 ∧ R (x t) (x s)) ↔
      ∃ t ∈ qSet 0 T, ∃ s ∈ qSet 0 T, 0 < t ∧ s ≤ t ∧ t ≤ s + 1 ∧ R (x t) (x s) := by
  constructor
  · rintro ⟨t, s, ht0, htT, hst, hts1, hR⟩
    obtain ⟨ut, hut, hxt⟩ := exists_Ico_const hx t
    obtain ⟨us, hus, hxs⟩ := exists_Ico_const hx s
    -- the new right end `t''`
    have key : ∃ t'' ∈ qSet 0 T, t ≤ t'' ∧ t'' < ut ∧ t'' < t + (us - s) ∧ t'' ≤ T := by
      rcases htT.eq_or_lt with rfl | hlt
      · exact ⟨t, Or.inr rfl, le_rfl, hut, lt_add_of_pos_right _ (tsub_pos_of_lt hus), le_rfl⟩
      · have hlt2 : t < min (min ut (t + (us - s))) T :=
          lt_min (lt_min hut (lt_add_of_pos_right _ (tsub_pos_of_lt hus))) hlt
        obtain ⟨q, hq1, hq2, hq3⟩ := exists_rat_nnreal_btwn hlt2
        exact ⟨q, mem_qSet_of_rat (hq2.trans_le (min_le_right _ _)) hq3, hq1.le,
          hq2.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
          hq2.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
          (hq2.trans_le (min_le_right _ _)).le⟩
    obtain ⟨t'', ht''q, htt'', ht''ut, ht''us, ht''T⟩ := key
    have hxt'' : x t'' = x t := hxt t'' htt'' ht''ut
    refine ⟨t'', ht''q, ?_⟩
    rcases hst.eq_or_lt with rfl | hlt
    · refine ⟨t'', ht''q, ht0.trans_le htt'', le_rfl, by simp, ?_⟩
      rw [hxt'']; exact hR
    · -- `s < t`
      have hlo : max s (t'' - 1) < min us t'' := by
        refine max_lt_iff.2 ⟨lt_min hus (hlt.trans_le htt''), ?_⟩
        refine lt_min ?_ ?_
        · have h1 : (t'' : ℝ) < t + (us - s) := by
            have := ht''us
            have e : ((t + (us - s) : ℝ≥0) : ℝ) = t + (us - s) := by
              rw [NNReal.coe_add, NNReal.coe_sub hus.le]
            rw [← e]; exact_mod_cast this
          have h2 : (t : ℝ) ≤ s + 1 := by exact_mod_cast hts1
          have h3 : (t'' - 1 : ℝ≥0) ≤ t'' - 1 := by simp
          have : (↑(t'' - 1) : ℝ) < us := by
            by_cases h : 1 ≤ t''
            · rw [NNReal.coe_sub h]; simp only [NNReal.coe_one]; linarith
            · push Not at h
              rw [tsub_eq_zero_of_le h.le]; exact_mod_cast (bot_le (a := s)).trans_lt hus
          exact_mod_cast this
        · exact tsub_lt_self (ht0.trans_le htt'') one_pos
      obtain ⟨s'', hs1, hs2, hs3⟩ := exists_rat_nnreal_btwn hlo
      have hs''q : s'' ∈ qSet 0 T :=
        mem_qSet_of_rat ((hs2.trans_le (min_le_right _ _)).trans_le ht''T) hs3
      refine ⟨s'', hs''q, ht0.trans_le htt'', (hs2.trans_le (min_le_right _ _)).le, ?_, ?_⟩
      · have h4 : t'' - 1 < s'' := lt_of_le_of_lt (le_max_right _ _) hs1
        have h5 : t'' ≤ s'' + 1 := by
          have := tsub_le_iff_right.1 h4.le
          exact this
        exact h5
      · rw [hxt'', hxs s'' (lt_of_le_of_lt (le_max_left _ _) hs1).le
          (hs2.trans_le (min_le_left _ _))]
        exact hR
  · rintro ⟨t, htq, s, hsq, ht0, hst, hts1, hR⟩
    exact ⟨t, s, ht0, (mem_qSet_Icc bot_le htq).2, hst, hts1, hR⟩

end ElboimSly.Paper.Escape
