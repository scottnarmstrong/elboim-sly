/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Counts
public import Mathlib

/-!
# Increments of the walk on the good event

Good event and path properties, property (P2) and `X(0) = 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

/-- The natural-number reading of a count. -/
noncomputable def natOf (x : ℝ≥0∞) : ℕ := ⌊x.toReal⌋₊

theorem IsNat.natCast_natOf {x : ℝ≥0∞} (hx : IsNat x) : ((natOf x : ℕ) : ℝ≥0∞) = x := by
  obtain ⟨n, rfl⟩ := hx
  simp [natOf]

section Incr

variable {d : ℕ} {ν : Measure (Dir d × ℝ)}

theorem walk_of_good (hν : ν ∈ goodSet d) (t : ℝ) :
    walk d ν t = ∑ v : Dir d, ((natOf (cnt ν v t) : ℕ) : ℤ) • v.vec := by
  classical
  simp [walk, hν, natOf]

theorem walk_of_not_good (hν : ν ∉ goodSet d) (t : ℝ) : walk d ν t = 0 := by
  classical
  simp [walk, hν]

theorem cnt_zero (ν : Measure (Dir d × ℝ)) (v : Dir d) : cnt ν v 0 = 0 := by
  simp [cnt]

theorem walk_zero (ν : Measure (Dir d × ℝ)) : walk d ν 0 = 0 := by
  classical
  by_cases hν : ν ∈ goodSet d
  · simp [walk_of_good hν, cnt_zero, natOf]
  · exact walk_of_not_good hν 0

theorem cnt_add_Ioc (v : Dir d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    cnt ν v t = cnt ν v s + ν (({v} : Set (Dir d)) ×ˢ Ioc s t) := by
  unfold cnt
  rw [← measure_union]
  · rw [← prod_union, Ioc_union_Ioc_eq_Ioc hs hst]
  · exact Set.disjoint_left.2 fun p hp hq => by
      simp only [mem_prod, mem_Ioc] at hp hq; linarith [hp.2.2, hq.2.1]
  · exact measurableSet_rect _ _ measurableSet_Ioc

theorem natOf_cnt_add (hν : ν ∈ goodSet d) (v : Dir d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    natOf (cnt ν v t) = natOf (cnt ν v s) + natOf (ν (({v} : Set (Dir d)) ×ˢ Ioc s t)) := by
  apply Nat.cast_injective (R := ℝ≥0∞)
  rw [Nat.cast_add, (good_cnt hν v t).natCast_natOf, (good_cnt hν v s).natCast_natOf,
    (good_Ioc hν v hs).natCast_natOf]
  exact cnt_add_Ioc v hs hst

/-- The increment of the walk is the sum of the jumps counted in `(s,t]`. -/
theorem walk_sub_eq (hν : ν ∈ goodSet d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    walk d ν t - walk d ν s =
      ∑ v : Dir d, ((natOf (ν (({v} : Set (Dir d)) ×ˢ Ioc s t)) : ℕ) : ℤ) • v.vec := by
  rw [walk_of_good hν, walk_of_good hν, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [natOf_cnt_add hν v hs hst]
  push_cast
  rw [add_smul]; abel

theorem sum_natAbs_vec (v : Dir d) : ∑ i, (v.vec i).natAbs = 1 := by
  classical
  unfold Dir.vec
  rw [Finset.sum_eq_single v.1]
  · simp only [Pi.single_eq_same]; split_ifs <;> simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

/-- Good event and path properties (P2): the `ℓ¹` size of an increment is at most the number of points
in the window.  -/
theorem walk_sub_l1_le (hν : ν ∈ goodSet d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (((∑ i, (walk d ν t i - walk d ν s i).natAbs : ℕ)) : ℝ≥0∞) ≤ tot ν (Ioc s t) := by
  set m : Dir d → ℕ := fun v => natOf (ν (({v} : Set (Dir d)) ×ˢ Ioc s t)) with hm
  have h1 : ∀ i, (walk d ν t i - walk d ν s i) = ∑ v : Dir d, (m v : ℤ) * v.vec i := by
    intro i
    have := congrFun (walk_sub_eq hν hs hst) i
    simpa [Finset.sum_apply] using this
  have h2 : (∑ i, (walk d ν t i - walk d ν s i).natAbs) ≤ ∑ v : Dir d, m v := by
    calc (∑ i, (walk d ν t i - walk d ν s i).natAbs)
        = ∑ i, (∑ v : Dir d, (m v : ℤ) * v.vec i).natAbs := by simp only [h1]
      _ ≤ ∑ i, ∑ v : Dir d, ((m v : ℤ) * v.vec i).natAbs :=
          Finset.sum_le_sum fun i _ => Int.natAbs_sum_le _ _
      _ = ∑ v : Dir d, ∑ i, ((m v : ℤ) * v.vec i).natAbs := Finset.sum_comm
      _ = ∑ v : Dir d, m v := by
          refine Finset.sum_congr rfl fun v _ => ?_
          simp only [Int.natAbs_mul, Int.natAbs_natCast]
          rw [← Finset.mul_sum, sum_natAbs_vec, mul_one]
  calc (((∑ i, (walk d ν t i - walk d ν s i).natAbs : ℕ)) : ℝ≥0∞)
      ≤ ((∑ v : Dir d, m v : ℕ) : ℝ≥0∞) := by exact_mod_cast h2
    _ = ∑ v : Dir d, ν (({v} : Set (Dir d)) ×ˢ Ioc s t) := by
        push_cast
        exact Finset.sum_congr rfl fun v _ => (good_Ioc hν v hs).natCast_natOf
    _ = tot ν (Ioc s t) := (tot_eq_sum ν _ measurableSet_Ioc).symm

/-- Good event and path properties (P2): if no point falls in `(s,t]` the walk does not move. -/
theorem walk_eq_of_tot_eq_zero {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : tot ν (Ioc s t) = 0) : walk d ν t = walk d ν s := by
  by_cases hν : ν ∈ goodSet d
  · have := walk_sub_l1_le hν hs hst
    rw [h, nonpos_iff_eq_zero] at this
    have h0 : (∑ i, (walk d ν t i - walk d ν s i).natAbs) = 0 := by exact_mod_cast this
    funext i
    have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ _)
    omega
  · rw [walk_of_not_good hν, walk_of_not_good hν]

end Incr

end SRW
end ElboimSly
