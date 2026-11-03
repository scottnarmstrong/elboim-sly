/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFastStat
public import ElboimSly.Foundations.Cyclic.CycFastGlue
public import ElboimSly.Foundations.Cyclic.CycThit
public import Mathlib

/-!
# ES22 Claim 2.3, Steps 0 and 3: the pathwise inclusion

ES22 Claim 2.3, Steps 0 and 3. For a good environment, `t_fast(L) ≤ t` forces a unit
window of some piece with a large deviation:

* Step 0 (`tfast_pair`): `t_fast(L) ≤ t` gives `0 ≤ s ≤ s' ≤ t`, `s' - s ≤ 1`,
  `‖W(s') - W(s)‖ ≥ L`;
* Step 3 (`tfast_mem_window`): by `glued_window` and `window_pairs` this pair lies in one window
  `[m β, (m+1) β]` of one piece `j < ⌊t/β⌋ + 1`, `m < ⌊t/β⌋ + 1`, with an increment `≥ L/2`, and by
  `cover_unit` there is a unit window `a = m β + i` with `i ≤ min(⌊β⌋, ⌊t⌋)` where the shifted
  cyclic walk of piece `j` has sup norm `≥ L/4` on `[0, 2]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
/-- Step 0 of ES22 Claim 2.3. -/
theorem tfast_pair {ν : ℕ → Measure (RingSpace d β)} {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (hrc : ∀ s : ℝ≥0, ∀ᶠ u : ℝ≥0 in 𝓝[≥] s, ElboimSly.regenWalk ν (u : ℝ) =
      ElboimSly.regenWalk ν (s : ℝ))
    (h : ElboimSly.cycTfast ν L ≤ ENNReal.ofReal t) :
    ∃ s s' : ℝ≥0, s ≤ s' ∧ (s' : ℝ) ≤ t ∧ s' - s ≤ 1 ∧
      L ≤ ‖ElboimSly.regenWalk ν (s' : ℝ) - ElboimSly.regenWalk ν (s : ℝ)‖ := by
  set t' : ℝ≥0 := t.toNNReal with ht'
  have ht'c : (t' : ℝ) = t := Real.coe_toNNReal t ht
  obtain ⟨u', hu't, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hrc t')
  have hu'r : t < (u' : ℝ) := by rw [← ht'c]; exact_mod_cast hu't
  have hlt : ElboimSly.cycTfast ν L < ENNReal.ofReal (u' : ℝ) :=
    lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff (by linarith [u'.2])).2 hu'r)
  unfold ElboimSly.cycTfast at hlt
  obtain ⟨t1, hlt1⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hmem, hlt2⟩ := iInf_lt_iff.1 hlt1
  obtain ⟨ht1pos, s, hs1, hs2, hnorm⟩ := hmem
  have ht1u : t1 < (u' : ℝ) := (ENNReal.ofReal_lt_ofReal_iff (by linarith [u'.2])).1 hlt2
  set s1 : ℝ := max s 0 with hs1def
  have hs1nn : 0 ≤ s1 := le_max_right _ _
  have hs1t1 : s1 ≤ t1 := max_le hs2 ht1pos.le
  have hs1low : t1 - 1 ≤ s1 := le_trans hs1 (le_max_left _ _)
  have hcoe1 : ((s1.toNNReal : ℝ≥0) : ℝ) = s1 := Real.coe_toNNReal _ hs1nn
  by_cases hle : t1 ≤ t
  · refine ⟨s1.toNNReal, t1.toNNReal, ?_, ?_, ?_, ?_⟩
    · rw [← NNReal.coe_le_coe, hcoe1, Real.coe_toNNReal _ ht1pos.le]; exact hs1t1
    · rw [Real.coe_toNNReal _ ht1pos.le]; exact hle
    · rw [tsub_le_iff_left, ← NNReal.coe_le_coe, NNReal.coe_add, hcoe1,
        Real.coe_toNNReal _ ht1pos.le]
      push_cast; linarith
    · rw [hcoe1, Real.coe_toNNReal _ ht1pos.le]; exact hnorm
  · rw [not_le] at hle
    have hW1 : ElboimSly.regenWalk ν t1 = ElboimSly.regenWalk ν (t' : ℝ) := by
      have hm : t1.toNNReal ∈ Ico t' u' := by
        refine ⟨?_, ?_⟩
        · rw [← NNReal.coe_le_coe, ht'c, Real.coe_toNNReal _ ht1pos.le]; exact hle.le
        · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht1pos.le]; exact ht1u
      have this : ElboimSly.regenWalk ν ((t1.toNNReal : ℝ≥0) : ℝ) =
          ElboimSly.regenWalk ν (t' : ℝ) := hsub hm
      rwa [Real.coe_toNNReal _ ht1pos.le] at this
    by_cases hs1t : s1 ≤ t
    · refine ⟨s1.toNNReal, t', ?_, ?_, ?_, ?_⟩
      · rw [← NNReal.coe_le_coe, hcoe1, ht'c]; exact hs1t
      · rw [ht'c]
      · rw [tsub_le_iff_left, ← NNReal.coe_le_coe, NNReal.coe_add, hcoe1, ht'c]
        push_cast; linarith
      · rw [hcoe1, ht'c]; rw [ht'c] at hW1; rw [← hW1]; exact hnorm
    · exfalso
      rw [not_le] at hs1t
      have hW2 : ElboimSly.regenWalk ν s1 = ElboimSly.regenWalk ν (t' : ℝ) := by
        have hm : s1.toNNReal ∈ Ico t' u' := by
          refine ⟨?_, ?_⟩
          · rw [← NNReal.coe_le_coe, ht'c, hcoe1]; exact hs1t.le
          · rw [← NNReal.coe_lt_coe, hcoe1]; exact lt_of_le_of_lt hs1t1 ht1u
        have this : ElboimSly.regenWalk ν ((s1.toNNReal : ℝ≥0) : ℝ) =
            ElboimSly.regenWalk ν (t' : ℝ) := hsub hm
        rwa [hcoe1] at this
      rw [hW1, ← hW2, sub_self, norm_zero] at hnorm
      linarith

variable [Fact (0 < β)]

end ElboimSly.Cyclic

end
