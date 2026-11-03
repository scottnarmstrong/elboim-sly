/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Natural
public import Mathlib

/-!
# Natural-valued counts on the good event

Good event and path properties (integrality part).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

/-- `x` is a natural number inside `[0,∞]`. -/
def IsNat (x : ℝ≥0∞) : Prop := ∃ n : ℕ, x = n

theorem IsNat.add {x y : ℝ≥0∞} (hx : IsNat x) (hy : IsNat y) : IsNat (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by push_cast; rfl⟩

theorem IsNat.sub {x y : ℝ≥0∞} (hx : IsNat x) (hy : IsNat y) : IsNat (x - y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a - b, by rw [ENNReal.natCast_sub]⟩

theorem IsNat.ne_top {x : ℝ≥0∞} (hx : IsNat x) : x ≠ ∞ := by
  obtain ⟨a, rfl⟩ := hx; exact ENNReal.natCast_ne_top _

theorem isNat_zero : IsNat 0 := ⟨0, by simp⟩

theorem isNat_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (h : ∀ i ∈ s, IsNat (f i)) :
    IsNat (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isNat_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem IsNat.measure_diff' {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B : Set α}
    (hAB : A ⊆ B) (hA : MeasurableSet A) (hBn : IsNat (μ B)) (hAn : IsNat (μ A)) :
    IsNat (μ (B \ A)) := by
  rw [measure_sdiff hAB hA.nullMeasurableSet hAn.ne_top]
  exact hBn.sub hAn

section Good

variable {d : ℕ} {ν : Measure (Dir d × ℝ)}

theorem measurableSet_rect (v : Dir d) (I : Set ℝ) (hI : MeasurableSet I) :
    MeasurableSet (({v} : Set (Dir d)) ×ˢ I) :=
  (measurableSet_singleton v).prod hI

theorem good_rat (hν : ν ∈ goodSet d) (v : Dir d) (q : ℚ) (hq : 0 < q) : IsNat (cnt ν v q) := by
  have := hν.1
  simp only [mem_iInter, mem_ofPred_eq] at this
  exact this v q hq

/-- Counts `ν ({v} × (0,t])` are natural numbers on the good event. -/
theorem good_cnt (hν : ν ∈ goodSet d) (v : Dir d) (t : ℝ) : IsNat (cnt ν v t) := by
  rcases le_or_gt t 0 with ht | ht
  · simp [cnt, Ioc_eq_empty (not_lt.2 ht), isNat_zero]
  · let s : {q : ℚ // t < q} → Set (Dir d × ℝ) := fun q => ({v} : Set (Dir d)) ×ˢ Ioc 0 (q.1 : ℝ)
    have hnonempty : Nonempty {q : ℚ // t < q} := by
      obtain ⟨q, hq⟩ := exists_rat_gt t; exact ⟨⟨q, hq⟩⟩
    have hs : ∀ i, MeasurableSet (s i) := fun i => measurableSet_rect _ _ measurableSet_Ioc
    have hd : Directed (· ⊇ ·) s := by
      intro i j
      refine ⟨⟨min i.1 j.1, by rw [Rat.cast_min]; exact lt_min i.2 j.2⟩, ?_, ?_⟩
      · exact prod_mono subset_rfl (Ioc_subset_Ioc_right (by exact_mod_cast min_le_left _ _))
      · exact prod_mono subset_rfl (Ioc_subset_Ioc_right (by exact_mod_cast min_le_right _ _))
    have hn : ∀ i, ∃ n : ℕ, ν (s i) = n := fun i =>
      good_rat hν v i.1 (by exact_mod_cast ht.trans i.2)
    obtain ⟨i, hi⟩ := exists_measure_eq_iInter ν s hs hd hn
    have hI : (⋂ j, s j) = ({v} : Set (Dir d)) ×ˢ Ioc 0 t := by
      ext ⟨a, x⟩
      simp only [mem_iInter, mem_prod, mem_singleton_iff, mem_Ioc, s, Subtype.forall]
      constructor
      · intro h
        obtain ⟨q, hq⟩ := exists_rat_gt t
        refine ⟨(h q hq).1, (h q hq).2.1, ?_⟩
        refine le_of_forall_gt_imp_ge_of_dense fun y hy => ?_
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hy
        exact ((h q hq1).2.2).trans hq2.le
      · rintro ⟨h1, h2, h3⟩ q hq
        exact ⟨h1, h2, h3.trans hq.le⟩
    rw [hI] at hi
    unfold cnt; rw [← hi]; exact hn i

/-- Counts of `(a,b]` for `0 ≤ a` are natural numbers on the good event. -/
theorem good_Ioc (hν : ν ∈ goodSet d) (v : Dir d) {a b : ℝ} (ha : 0 ≤ a) :
    IsNat (ν (({v} : Set (Dir d)) ×ˢ Ioc a b)) := by
  rcases le_or_gt b a with hab | hab
  · simp [Ioc_eq_empty (not_lt.2 hab), isNat_zero]
  · have h : ({v} : Set (Dir d)) ×ˢ Ioc a b =
        (({v} : Set (Dir d)) ×ˢ Ioc 0 b) \ (({v} : Set (Dir d)) ×ˢ Ioc 0 a) := by
      ext ⟨x, y⟩
      simp only [mem_prod, mem_Ioc, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, ha.trans_lt h2, h3⟩, fun h => by linarith [h.2.2]⟩
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        refine ⟨h1, ?_, h3⟩
        by_contra h5
        exact h4 ⟨h1, h2, not_lt.1 h5⟩
    rw [h]
    exact IsNat.measure_diff' (prod_mono subset_rfl (Ioc_subset_Ioc_right hab.le))
      (measurableSet_rect _ _ measurableSet_Ioc) (good_cnt hν v b) (good_cnt hν v a)

/-- Total counts as a finite sum of counts. -/
theorem tot_eq_sum (ν : Measure (Dir d × ℝ)) (U : Set ℝ) (hU : MeasurableSet U) :
    tot ν U = ∑ v : Dir d, ν (({v} : Set (Dir d)) ×ˢ U) := by
  unfold tot
  have : (univ : Set (Dir d)) ×ˢ U = ⋃ v ∈ (Finset.univ : Finset (Dir d)),
      ({v} : Set (Dir d)) ×ˢ U := by
    ext ⟨x, y⟩; simp
  rw [this, measure_biUnion_finset]
  · intro a _ b _ hab
    exact Set.disjoint_left.2 fun p hp hq => hab (by
      simp only [mem_prod, mem_singleton_iff] at hp hq; rw [← hp.1, ← hq.1])
  · exact fun v _ => measurableSet_rect _ _ hU

theorem good_tot_Ioc (hν : ν ∈ goodSet d) {a b : ℝ} (ha : 0 ≤ a) : IsNat (tot ν (Ioc a b)) := by
  rw [tot_eq_sum ν _ measurableSet_Ioc]
  exact isNat_finset_sum _ _ fun v _ => good_Ioc hν v ha

/-- Counts of single points `{t}`, `t > 0`. -/
theorem good_singleton (hν : ν ∈ goodSet d) (v : Dir d) {t : ℝ} (ht : 0 < t) :
    IsNat (ν (({v} : Set (Dir d)) ×ˢ {t})) := by
  let s : {q : ℚ // 0 < q ∧ (q : ℝ) < t} → Set (Dir d × ℝ) :=
    fun q => ({v} : Set (Dir d)) ×ˢ Ioc (q.1 : ℝ) t
  have hnonempty : Nonempty {q : ℚ // 0 < q ∧ (q : ℝ) < t} := by
    obtain ⟨q, hq0, hqt⟩ := exists_rat_btwn ht
    exact ⟨⟨q, by exact_mod_cast hq0, hqt⟩⟩
  have hs : ∀ i, MeasurableSet (s i) := fun i => measurableSet_rect _ _ measurableSet_Ioc
  have hd : Directed (· ⊇ ·) s := by
    intro i j
    refine ⟨⟨max i.1 j.1, lt_max_of_lt_left i.2.1, by rw [Rat.cast_max]; exact max_lt i.2.2 j.2.2⟩,
      ?_, ?_⟩
    · exact prod_mono subset_rfl (Ioc_subset_Ioc_left (by exact_mod_cast le_max_left _ _))
    · exact prod_mono subset_rfl (Ioc_subset_Ioc_left (by exact_mod_cast le_max_right _ _))
  have hn : ∀ i, ∃ n : ℕ, ν (s i) = n := fun i =>
    good_Ioc hν v (by exact_mod_cast i.2.1.le)
  obtain ⟨i, hi⟩ := exists_measure_eq_iInter ν s hs hd hn
  have hI : (⋂ j, s j) = ({v} : Set (Dir d)) ×ˢ {t} := by
    ext ⟨a, x⟩
    simp only [mem_iInter, mem_prod, mem_singleton_iff, mem_Ioc, s, Subtype.forall]
    constructor
    · intro h
      obtain ⟨q, hq0, hqt⟩ := exists_rat_btwn ht
      refine ⟨(h q ⟨by exact_mod_cast hq0, hqt⟩).1, ?_⟩
      refine le_antisymm (h q ⟨by exact_mod_cast hq0, hqt⟩).2.2 ?_
      by_contra hx
      rw [not_le] at hx
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt ht hx)
      have := (h q ⟨by exact_mod_cast (le_max_left 0 x).trans_lt hq1, hq2⟩).2.1
      linarith [le_max_right 0 x]
    · rintro ⟨h1, h2⟩ q ⟨_, hq⟩
      exact ⟨h1, by rw [h2]; exact hq, h2.le⟩
  rw [hI] at hi
  rw [← hi]; exact hn i

end Good

end SRW
end ElboimSly
