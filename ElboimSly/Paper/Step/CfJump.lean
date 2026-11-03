/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPathJump
public import ElboimSly.Foundations.Cyclic.CPathCount
public import ElboimSly.Foundations.Cyclic.DrivenDef
public import Mathlib

/-!
# Discontinuities are the jump times; coincidence-free paths are a measurable condition

For a path with finitely many jumps (`CPath`), `s` is a discontinuity iff `s = ς_{i+1}` for some `i`
(`mem_CDisc_iff_jt`). Hence coincidence-freeness of a regular path is read off the measurable jump
times: `stepBadCF b` is a measurable set of `CPath`s, and a driving path is coincidence-free iff its
`CPath` avoids it (`mem_cycCF_iff_not_badCF`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem cnt_zero' (p : CPath V) : p.cnt 0 = 0 := by
  unfold CPath.cnt
  have : CDisc p.fn ∩ Iic 0 = ∅ := by
    ext r
    simp only [CDisc, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iic, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro h1 h2
    exact absurd h2 (not_le.mpr h1.1)
  rw [this]; simp

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- The discontinuities of a `CPath` are its jump times `ς_{i+1}`. -/
theorem mem_CDisc_iff_jt (p : CPath V) (s : ℝ≥0) :
    s ∈ CDisc p.fn ↔ ∃ i : ℕ, p.jt (i + 1) = (s : ℝ≥0∞) := by
  constructor
  · intro hs
    have hmem : s ∈ CDisc p.fn ∩ Iic s := ⟨hs, le_rfl⟩
    have hfin := p.fin s
    have hcnt : 1 ≤ p.cnt s := by
      unfold CPath.cnt
      exact (Set.ncard_pos hfin).2 ⟨s, hmem⟩
    obtain ⟨i, hi⟩ : ∃ i, p.cnt s = i + 1 := ⟨p.cnt s - 1, by omega⟩
    refine ⟨i, le_antisymm ?_ ?_⟩
    · exact (p.jt_le_iff (i + 1) s).2 hi.ge
    · by_contra hlt
      rw [not_le] at hlt
      have hne : p.jt (i + 1) ≠ ⊤ := ne_top_of_lt (hlt.trans ENNReal.coe_lt_top)
      set c := (p.jt (i + 1)).toNNReal with hc
      have hce : p.jt (i + 1) = (c : ℝ≥0∞) := (ENNReal.coe_toNNReal hne).symm
      have hcs : c < s := by rw [hce] at hlt; exact_mod_cast hlt
      have h1 : i + 1 ≤ p.cnt c := p.cnt_ge_of_jt (lt_top_iff_ne_top.2 hne)
      have h2 : p.cnt c < p.cnt s := by
        unfold CPath.cnt
        refine Set.ncard_lt_ncard ⟨fun r hr => ⟨hr.1, hr.2.trans hcs.le⟩, fun hsub => ?_⟩ hfin
        have := (hsub hmem).2
        exact absurd (this : s ≤ c) (not_le.2 hcs)
      omega
  · rintro ⟨i, hi⟩
    have hfin : p.jt (i + 1) < ⊤ := by rw [hi]; exact ENNReal.coe_lt_top
    have hge : i + 1 ≤ p.cnt s := by
      have := p.cnt_ge_of_jt hfin
      rwa [hi, ENNReal.toNNReal_coe] at this
    have hs0 : 0 < s := by
      rcases eq_or_ne s 0 with h0 | h0
      · rw [h0, cnt_zero'] at hge; omega
      · exact pos_iff_ne_zero.2 h0
    by_contra hnd
    obtain ⟨t, hts, ht⟩ := p.exists_left_gap hs0
    have h1 : p.cnt s ≤ p.cnt t := by
      unfold CPath.cnt
      refine Set.ncard_le_ncard (fun r hr => ⟨hr.1, ?_⟩) (p.fin t)
      by_contra hrt
      have hrt : t < r := not_le.1 hrt
      have hr2 : r ≤ s := hr.2
      rcases lt_or_eq_of_le hr2 with hlt | heq
      · exact ht r hr.1 hrt hlt
      · exact hnd (heq ▸ hr.1)
    have h2 : p.cnt t < i + 1 := p.cnt_lt_of_lt_jt (by rw [hi]; exact_mod_cast hts)
    omega

/-- The measurable set of `CPath`s with a coincidence of jump times at distance `kb`, or a jump
at a time `kb`, `k ≥ 1`. -/
def stepBadCF (b : ℝ≥0) : Set (CPath V) :=
  (⋃ (i : ℕ) (j : ℕ) (k : ℕ), ⋃ (_ : 1 ≤ k),
    {p | p.jt (i + 1) < ⊤ ∧ p.jt (j + 1) = p.jt (i + 1) + (((k : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞)}) ∪
  (⋃ (i : ℕ) (k : ℕ), ⋃ (_ : 1 ≤ k), {p | p.jt (i + 1) = (((k : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞)})

theorem measurableSet_stepBadCF (b : ℝ≥0) : MeasurableSet (stepBadCF (V := V) b) := by
  unfold stepBadCF
  refine MeasurableSet.union ?_ ?_
  · refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
    exact (measurableSet_lt (CPath.measurable_jt (i + 1)) measurable_const).inter
      (measurableSet_eq_fun (CPath.measurable_jt (j + 1))
        ((CPath.measurable_jt (i + 1)).add_const _))
  · refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun _ => ?_
    exact measurableSet_eq_fun (CPath.measurable_jt (i + 1)) measurable_const

end ElboimSly.Paper.Step
