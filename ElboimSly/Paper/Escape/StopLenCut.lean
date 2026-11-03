/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlan
public import ElboimSly.Foundations.Cyclic.CPathJump
public import ElboimSly.Foundations.Cyclic.CycPiece
public import Mathlib

/-!
# Non-anticipation of the stopping length

World-lines, records, exploration plans (stopping length), used in ES22 Lemma 5.5 to see that the cumulative lengths
`Λ_k` of a plan are stopping times of the joint exploration filtration.

`stopLen_cut_le_iff`: for a plan `P`, a record `ρ`, a path `p` and a finite length `r`,
`stopLen (p.cut r) ≤ r ↔ stopLen p ≤ r`.  The stopping length is decided by what happened before it.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The set whose infimum is the stopping length. -/
def stopSet (P : CycPlan I d β) (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d) : Set ℝ≥0∞ :=
  {t | ∃ a : ℕ, 1 ≤ a ∧ p.1.jt a < ⊤ ∧ P.st k (P.hatRec k ρ p a) = true ∧ t = p.1.jt a} ∪
    {t | ∃ a : ℕ, p.1.jt a < ⊤ ∧ t = p.1.jt a + P.dl k (P.hatRec k ρ p a) ∧
      t < p.1.jt (a + 1)}

theorem stopLen_eq_sInf_stopSet (P : CycPlan I d β) (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d) :
    P.stopLen k ρ p = sInf (stopSet P k ρ p) := rfl

theorem jt_cut_of_le (p : CycPath d) {r : ℝ≥0∞} {a : ℕ} (ha : p.1.jt a ≤ r) :
    (p.cut r).1.jt a = p.1.jt a := by
  show (p.1.cut r).jt a = _
  rw [CPath.jt_cut, ite_eq_left ha]

theorem jt_cut_of_not_le (p : CycPath d) {r : ℝ≥0∞} {a : ℕ} (ha : ¬ p.1.jt a ≤ r) :
    (p.cut r).1.jt a = ⊤ := by
  show (p.1.cut r).jt a = _
  rw [CPath.jt_cut, ite_eq_right ha]

/-- Cutting the path at `r` does not change the record at jump times `≤ r`. -/
theorem hatRec_cut_of_le (P : CycPlan I d β) (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d)
    {r : ℝ≥0∞} {a : ℕ} (ha : p.1.jt a ≤ r) :
    P.hatRec k ρ (p.cut r) a = P.hatRec k ρ p a := by
  unfold CycPlan.hatRec
  rw [jt_cut_of_le p ha]
  congr 2
  exact Subtype.ext (CPath.cut_cut p.1 ha)

/-- Membership in the set below the cut level does not depend on the cut. -/
theorem mem_stopSet_cut_iff (P : CycPlan I d β) (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d)
    {r : ℝ≥0} {t : ℝ≥0∞} (ht : t ≤ r) :
    t ∈ stopSet P k ρ (p.cut (r : ℝ≥0∞)) ↔ t ∈ stopSet P k ρ p := by
  have htop : t < ⊤ := lt_of_le_of_lt ht ENNReal.coe_lt_top
  unfold stopSet
  simp only [mem_union, mem_ofPred_eq]
  constructor
  · rintro (⟨a, ha1, hjt, hst, rfl⟩ | ⟨a, hjt, rfl, hlt⟩)
    · have hle : p.1.jt a ≤ r := by
        by_contra h
        rw [jt_cut_of_not_le p h] at hjt
        exact lt_irrefl _ hjt
      rw [jt_cut_of_le p hle] at hjt ⊢
      rw [hatRec_cut_of_le P k ρ p hle] at hst
      exact Or.inl ⟨a, ha1, hjt, hst, rfl⟩
    · have hle : p.1.jt a ≤ r := by
        by_contra h
        rw [jt_cut_of_not_le p h] at hjt
        exact lt_irrefl _ hjt
      rw [jt_cut_of_le p hle] at hjt ht hlt ⊢
      rw [hatRec_cut_of_le P k ρ p hle] at ht hlt ⊢
      refine Or.inr ⟨a, hjt, rfl, ?_⟩
      by_cases h2 : p.1.jt (a + 1) ≤ r
      · rwa [jt_cut_of_le p h2] at hlt
      · rw [not_le] at h2
        exact lt_of_le_of_lt ht h2
  · rintro (⟨a, ha1, hjt, hst, rfl⟩ | ⟨a, hjt, rfl, hlt⟩)
    · have hle : p.1.jt a ≤ r := ht
      refine Or.inl ⟨a, ha1, ?_, ?_, ?_⟩
      · rwa [jt_cut_of_le p hle]
      · rwa [hatRec_cut_of_le P k ρ p hle]
      · rw [jt_cut_of_le p hle]
    · have hle : p.1.jt a ≤ r := le_trans le_self_add ht
      refine Or.inr ⟨a, ?_, ?_, ?_⟩
      · rwa [jt_cut_of_le p hle]
      · rw [jt_cut_of_le p hle, hatRec_cut_of_le P k ρ p hle]
      · by_cases h2 : p.1.jt (a + 1) ≤ r
        · rwa [jt_cut_of_le p h2]
        · rw [jt_cut_of_not_le p h2]
          exact htop

/-- Only finitely many elements of the stopping set lie below any finite level. -/
theorem finite_stopSet_lt (P : CycPlan I d β) (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d)
    (R : ℝ≥0) : (stopSet P k ρ p ∩ Iio (R : ℝ≥0∞)).Finite := by
  set c := p.1.cnt R with hc
  have hle : ∀ a : ℕ, p.1.jt a < (R : ℝ≥0∞) → a ≤ c := fun a ha =>
    (p.1.jt_le_iff a R).1 ha.le
  refine Set.Finite.subset
    (((Set.finite_Iic c).image fun a => p.1.jt a).union
      ((Set.finite_Iic c).image fun a => p.1.jt a + P.dl k (P.hatRec k ρ p a))) ?_
  rintro t ⟨ht, htR⟩
  rcases ht with ⟨a, -, -, -, rfl⟩ | ⟨a, -, rfl, -⟩
  · exact Or.inl ⟨a, hle a htR, rfl⟩
  · exact Or.inr ⟨a, hle a (lt_of_le_of_lt le_self_add htR), rfl⟩

/-- The stopping length is `≤ r` iff the stopping set has an element `≤ r`. -/
theorem stopLen_le_iff_exists (P : CycPlan I d β) (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d)
    (r : ℝ≥0) : P.stopLen k ρ p ≤ r ↔ ∃ t ∈ stopSet P k ρ p, t ≤ r := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    set S := stopSet P k ρ p with hS
    have hr1 : (r : ℝ≥0∞) < ((r + 1 : ℝ≥0) : ℝ≥0∞) := by
      exact_mod_cast lt_add_one r
    have hfin := finite_stopSet_lt P k ρ p (r + 1)
    by_cases hne' : (S ∩ Iio ((r + 1 : ℝ≥0) : ℝ≥0∞)).Nonempty
    · have hm := hne'.csInf_mem hfin
      set m := sInf (S ∩ Iio ((r + 1 : ℝ≥0) : ℝ≥0∞)) with hm_def
      have hmr : (r : ℝ≥0∞) < m := hne m hm.1
      have : sInf S < m := lt_of_le_of_lt h hmr
      obtain ⟨t, htS, htm⟩ := sInf_lt_iff.1 this
      have : t ∈ S ∩ Iio ((r + 1 : ℝ≥0) : ℝ≥0∞) := ⟨htS, lt_trans htm hm.2⟩
      exact absurd (sInf_le this) (not_le.2 htm)
    · rw [not_nonempty_iff_eq_empty] at hne'
      have : ((r + 1 : ℝ≥0) : ℝ≥0∞) ≤ sInf S := by
        refine le_sInf fun t ht => ?_
        by_contra hlt
        rw [not_le] at hlt
        have : t ∈ S ∩ Iio ((r + 1 : ℝ≥0) : ℝ≥0∞) := ⟨ht, hlt⟩
        rw [hne'] at this
        exact this
      exact absurd (lt_of_lt_of_le hr1 this) (not_lt.2 h)
  · rintro ⟨t, ht, htr⟩
    exact (sInf_le ht).trans htr

/-- **Non-anticipation.**  The stopping length of the path cut at `r` is `≤ r` iff the stopping
length of the whole path is. -/
theorem stopLen_cut_le_iff (P : CycPlan I d β) (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d)
    (r : ℝ≥0) : P.stopLen k ρ (p.cut (r : ℝ≥0∞)) ≤ r ↔ P.stopLen k ρ p ≤ r := by
  rw [stopLen_le_iff_exists, stopLen_le_iff_exists]
  constructor
  · rintro ⟨t, ht, htr⟩
    exact ⟨t, (mem_stopSet_cut_iff P k ρ p htr).1 ht, htr⟩
  · rintro ⟨t, ht, htr⟩
    exact ⟨t, (mem_stopSet_cut_iff P k ρ p htr).2 ht, htr⟩

end ElboimSly.Paper.Escape
