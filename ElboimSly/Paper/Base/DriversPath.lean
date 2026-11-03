/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.TwoParticleCount
public import ElboimSly.Foundations.Cyclic.DrivenCf
public import Mathlib

/-!
# Canonical walks are driving paths; jump counts

Supports the pair of driving walks (iii).

* `isDrivingPath_walk`: every path of the canonical walk lies in `Path⁰_d` (this is the
  `IsDrivingPath` of the cyclic chapter, `ElboimSly.Cyclic.walkPath_isDriving`, restated for
  `ElboimSly.Paper.IsDrivingPath`).
* `ncard_jumps_le_tot`: the number of jump times in a bounded set `I` is at most `ν(D × I)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Paper.Base ElboimSly.SRW ElboimSly.Cyclic Function

variable {d : ℕ}

/-- The unit vectors of `ℤ^d` are the vectors of `ℓ¹`-norm `1`. -/
theorem mem_range_vec_of_l1 {v : Fin d → ℤ} (hv : l1 v = 1) : v ∈ Set.range (Dir.vec (d := d)) := by
  classical
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    have : v = 0 := funext h
    rw [this] at hv
    have : l1 (0 : Fin d → ℤ) = 0 := (l1_eq_zero_iff _).2 rfl
    omega
  obtain ⟨i, hi⟩ := hex
  have hsum : |v i| + ∑ j ∈ Finset.univ.erase i, |v j| = 1 := by
    have := Finset.add_sum_erase Finset.univ (fun j => |v j|) (Finset.mem_univ i)
    unfold l1 at hv
    omega
  have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, |v j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hpos : 0 < |v i| := abs_pos.2 hi
  have hone : |v i| = 1 := by omega
  have hzero : ∑ j ∈ Finset.univ.erase i, |v j| = 0 := by omega
  have hothers : ∀ j, j ≠ i → v j = 0 := by
    intro j hj
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (v j))).1 hzero j
      (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
    exact abs_eq_zero.1 this
  rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.1 hone with h | h
  · refine ⟨(i, true), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj; simp [Dir.vec, h]
    · simp [Dir.vec, hj, hothers j hj]
  · refine ⟨(i, false), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj; simp [Dir.vec, h]
    · simp [Dir.vec, hj, hothers j hj]

/-- Bridge from the driving paths of the cyclic chapter. -/
theorem IsDrivingPath.ofCyclic {x : ℝ≥0 → Fin d → ℤ} (hx : ElboimSly.Cyclic.IsDrivingPath x) :
    IsDrivingPath x := by
  have hstep : IsStepPath x := ⟨hx.rc, hx.fin⟩
  refine ⟨hstep, hx.zero, fun r hr => ?_⟩
  have hleft : ElboimSly.Cyclic.leftVal x r = leftLim x r := by
    obtain ⟨c, hc⟩ := hstep.eventually_left_const hr.1
    rw [IsStepPath.leftLim_eq hr.1 hc]
    exact ElboimSly.Cyclic.leftVal_eq_of_eventually hr.1 hc
  have := hx.unit r hr
  rw [hleft] at this
  exact mem_range_vec_of_l1 this

theorem isDrivingPath_walk (ν : Measure (Dir d × ℝ)) :
    IsDrivingPath (fun u : ℝ≥0 => walk d ν (u : ℝ)) :=
  IsDrivingPath.ofCyclic (ElboimSly.Cyclic.walkPath_isDriving ν)

theorem isDrivingPath_canonical {Ω : Type*} (N : Ω → Measure (Dir d × ℝ)) (ω : Ω) :
    IsDrivingPath (canonical d N ω) := isDrivingPath_walk (N ω)

/-- The number of jump times of the walk in a bounded set `I ⊆ [0, ∞)` is at most
`ν(D × I)`. -/
theorem ncard_jumps_le_tot (ν : Measure (Dir d × ℝ)) {T : ℝ≥0} {I : Set ℝ≥0} (hI : I ⊆ Iic T) :
    (((CDisc (fun u : ℝ≥0 => walk d ν (u : ℝ))) ∩ I).ncard : ℝ≥0∞) ≤
      tot ν (((↑) : ℝ≥0 → ℝ) '' I) := by
  classical
  have hreg := ElboimSly.Cyclic.walkPath_isRegPath (d := d) ν
  have hfin : (CDisc (fun u : ℝ≥0 => walk d ν (u : ℝ)) ∩ I).Finite :=
    (hreg.fin T).subset (inter_subset_inter_right _ hI)
  set S := CDisc (fun u : ℝ≥0 => walk d ν (u : ℝ)) ∩ I with hS
  rw [Set.ncard_eq_toFinset_card S hfin]
  have h1 : ((hfin.toFinset.card : ℕ) : ℝ≥0∞) ≤
      ν ((univ : Set (Dir d)) ×ˢ (((↑) : ℝ≥0 → ℝ) '' (hfin.toFinset : Set ℝ≥0))) := by
    have hU : (univ : Set (Dir d)) ×ˢ (((↑) : ℝ≥0 → ℝ) '' (hfin.toFinset : Set ℝ≥0)) =
        ⋃ t ∈ hfin.toFinset, (univ : Set (Dir d)) ×ˢ ({(t : ℝ)} : Set ℝ) := by
      ext ⟨x, y⟩; simp only [mem_prod, mem_univ, true_and, mem_image, Finset.mem_coe,
        mem_iUnion, mem_singleton_iff, exists_prop]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    rw [hU, measure_biUnion_finset]
    · calc ((hfin.toFinset.card : ℕ) : ℝ≥0∞) = ∑ _t ∈ hfin.toFinset, (1 : ℝ≥0∞) := by simp
        _ ≤ _ := Finset.sum_le_sum fun t ht => by
          have hj := ElboimSly.Cyclic.isJump_of_mem_CDisc ν (Set.Finite.mem_toFinset hfin |>.1 ht).1
          exact hj.one_le_tot
    · intro a _ b _ hab
      exact Set.disjoint_left.2 fun p hp hq => hab (by
        simp only [mem_prod, mem_singleton_iff] at hp hq
        exact NNReal.coe_injective (hp.2.symm.trans hq.2))
    · exact fun t _ => MeasurableSet.univ.prod (measurableSet_singleton _)
  refine h1.trans (measure_mono (prod_mono subset_rfl (image_mono ?_)))
  intro t ht
  exact (Set.Finite.mem_toFinset hfin |>.1 ht).2

end ElboimSly.Paper
