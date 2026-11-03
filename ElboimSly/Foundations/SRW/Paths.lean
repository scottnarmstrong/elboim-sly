/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Increments
public import Mathlib

/-!
# Path properties of the walk

Good event and path properties, properties (P1) and (P3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

section Paths

variable {d : ℕ} {ν : Measure (Dir d × ℝ)}

theorem good_tot_singleton (hν : ν ∈ goodSet d) {t : ℝ} (ht : 0 < t) : IsNat (tot ν {t}) := by
  rw [tot_eq_sum ν _ (measurableSet_singleton t)]
  exact isNat_finset_sum _ _ fun v _ => good_singleton hν v ht

theorem good_tot_Ioo (hν : ν ∈ goodSet d) {q t : ℝ} (hq : 0 ≤ q) (ht : 0 < t) :
    IsNat (tot ν (Ioo q t)) := by
  rcases le_or_gt t q with hqt | hqt
  · simp [Ioo_eq_empty (not_lt.2 hqt), tot, isNat_zero]
  · have h : (univ : Set (Dir d)) ×ˢ Ioo q t =
        ((univ : Set (Dir d)) ×ˢ Ioc q t) \ ((univ : Set (Dir d)) ×ˢ {t}) := by
      ext ⟨x, y⟩
      simp only [mem_prod, mem_univ, true_and, mem_Ioo, mem_Ioc, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, h2.ne⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_of_le_of_ne h2 h3⟩
    unfold tot
    rw [h]
    exact IsNat.measure_diff' (prod_mono subset_rfl (by simpa using hqt))
      (MeasurableSet.univ.prod (measurableSet_singleton t))
      (good_tot_Ioc hν hq) (good_tot_singleton hν ht)

/-- (P1), right: the walk is constant on a right neighbourhood of `t`. -/
theorem exists_const_right (t : ℝ) (ht : 0 ≤ t) :
    ∃ δ > 0, ∀ u ∈ Ico t (t + δ), walk d ν u = walk d ν t := by
  by_cases hν : ν ∈ goodSet d
  · let s : {q : ℚ // t < q} → Set (Dir d × ℝ) := fun q => (univ : Set (Dir d)) ×ˢ Ioc t (q.1 : ℝ)
    have hnonempty : Nonempty {q : ℚ // t < q} := by
      obtain ⟨q, hq⟩ := exists_rat_gt t; exact ⟨⟨q, hq⟩⟩
    have hs : ∀ i, MeasurableSet (s i) := fun i => MeasurableSet.univ.prod measurableSet_Ioc
    have hd : Directed (· ⊇ ·) s := by
      intro i j
      refine ⟨⟨min i.1 j.1, by rw [Rat.cast_min]; exact lt_min i.2 j.2⟩, ?_, ?_⟩
      · exact prod_mono subset_rfl (Ioc_subset_Ioc_right (by exact_mod_cast min_le_left _ _))
      · exact prod_mono subset_rfl (Ioc_subset_Ioc_right (by exact_mod_cast min_le_right _ _))
    have hn : ∀ i, ∃ n : ℕ, ν (s i) = n := fun i => good_tot_Ioc hν ht
    obtain ⟨i, hi⟩ := exists_measure_eq_iInter ν s hs hd hn
    have hI : (⋂ j, s j) = ∅ := by
      ext ⟨a, x⟩
      simp only [mem_iInter, mem_prod, mem_univ, true_and, mem_Ioc, s, Subtype.forall,
        mem_empty_iff_false, iff_false, not_forall]
      by_cases hx : t < x
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx
        exact ⟨q, by exact_mod_cast hq1, fun h => by linarith [h.2]⟩
      · obtain ⟨q, hq⟩ := exists_rat_gt t
        exact ⟨q, hq, fun h => hx h.1⟩
    rw [hI, measure_empty] at hi
    refine ⟨(i.1 : ℝ) - t, sub_pos.2 i.2, fun u hu => ?_⟩
    have hu2 : u < (i.1 : ℝ) := by linarith [hu.2]
    refine walk_eq_of_tot_eq_zero ht hu.1 ?_
    exact measure_mono_null (prod_mono subset_rfl (Ioc_subset_Ioc_right hu2.le)) hi
  · exact ⟨1, one_pos, fun u _ => by rw [walk_of_not_good hν, walk_of_not_good hν]⟩

/-- (P1), left: the walk is constant on a left neighbourhood of `t`. -/
theorem exists_const_left (t : ℝ) (ht : 0 < t) :
    ∃ δ, 0 < δ ∧ δ < t ∧ (∀ u ∈ Ico (t - δ) t, walk d ν u = walk d ν (t - δ)) ∧
      (ν ∈ goodSet d → tot ν (Ioo (t - δ) t) = 0) := by
  by_cases hν : ν ∈ goodSet d
  · let s : {q : ℚ // 0 < q ∧ (q : ℝ) < t} → Set (Dir d × ℝ) :=
      fun q => (univ : Set (Dir d)) ×ˢ Ioo (q.1 : ℝ) t
    have hnonempty : Nonempty {q : ℚ // 0 < q ∧ (q : ℝ) < t} := by
      obtain ⟨q, hq0, hqt⟩ := exists_rat_btwn ht
      exact ⟨⟨q, by exact_mod_cast hq0, hqt⟩⟩
    have hs : ∀ i, MeasurableSet (s i) := fun i => MeasurableSet.univ.prod measurableSet_Ioo
    have hd : Directed (· ⊇ ·) s := by
      intro i j
      refine ⟨⟨max i.1 j.1, lt_max_of_lt_left i.2.1,
        by rw [Rat.cast_max]; exact max_lt i.2.2 j.2.2⟩, ?_, ?_⟩
      · exact prod_mono subset_rfl (Ioo_subset_Ioo_left (by exact_mod_cast le_max_left _ _))
      · exact prod_mono subset_rfl (Ioo_subset_Ioo_left (by exact_mod_cast le_max_right _ _))
    have hn : ∀ i, ∃ n : ℕ, ν (s i) = n := fun i =>
      good_tot_Ioo hν (by exact_mod_cast i.2.1.le) ht
    obtain ⟨i, hi⟩ := exists_measure_eq_iInter ν s hs hd hn
    have hI : (⋂ j, s j) = ∅ := by
      ext ⟨a, x⟩
      simp only [mem_iInter, mem_prod, mem_univ, true_and, mem_Ioo, s, Subtype.forall,
        mem_empty_iff_false, iff_false, not_forall]
      by_cases hx : x < t
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt ht hx)
        refine ⟨q, ⟨by exact_mod_cast (le_max_left 0 x).trans_lt hq1, hq2⟩, fun h => ?_⟩
        linarith [h.1, le_max_right 0 x]
      · obtain ⟨q, hq0, hqt⟩ := exists_rat_btwn ht
        exact ⟨q, ⟨by exact_mod_cast hq0, hqt⟩, fun h => hx h.2⟩
    rw [hI, measure_empty] at hi
    have hq0 : (0 : ℝ) < i.1 := by exact_mod_cast i.2.1
    refine ⟨t - i.1, sub_pos.2 i.2.2, by linarith, fun u hu => ?_, fun _ => by
      rw [sub_sub_cancel]; exact hi⟩
    rw [sub_sub_cancel] at hu ⊢
    refine walk_eq_of_tot_eq_zero hq0.le hu.1 ?_
    refine measure_mono_null ?_ hi
    exact prod_mono subset_rfl (fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hu.2⟩)
  · exact ⟨t / 2, by positivity, by linarith, fun u _ => by
      rw [walk_of_not_good hν, walk_of_not_good hν], fun h => absurd h hν⟩

end Paths

end SRW
end ElboimSly
