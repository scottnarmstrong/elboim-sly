/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.ReversalProc
public import Mathlib

/-!
# Time reversal: the law

Time reversal (a).

For a good realisation `ν` without a point at time `T`, the stopped reversed walk
`(X̂(u ∧ T))_u` equals `pastFun d T (revProc σ T ν)` for the identity permutation, and its negative
for the permutation flipping all signs.  Both processes `revProc σ T N` are Poisson point processes
with the intensity of `N` restricted to `D × (0,T]`, so the law is that of the stopped walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)}
  {P : Measure Ω}

theorem revProc_count (σ : Dir d ≃ Dir d) (T : ℝ) (ν : Measure (Dir d × ℝ)) (w : Dir d)
    (u : ℝ) :
    revProc σ T ν (({w} : Set (Dir d)) ×ˢ Ioc 0 u) =
      ν (({σ.symm w} : Set (Dir d)) ×ˢ (Ico (T - u) T ∩ Ioo 0 T)) := by
  unfold revProc
  have hm := measurable_reflectMap σ T
  have hA : MeasurableSet (({w} : Set (Dir d)) ×ˢ Ioc 0 u) :=
    (measurableSet_singleton w).prod measurableSet_Ioc
  rw [Measure.map_apply hm hA, Measure.restrict_apply (hm hA)]
  congr 1
  ext ⟨v, x⟩
  simp only [reflectMap, Prod.map, mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff,
    mem_univ, true_and, mem_Ioc, mem_Ico, mem_Ioo]
  rw [Equiv.eq_symm_apply, eq_comm]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨h1, ⟨by linarith, h5⟩, h4, h5⟩
  · rintro ⟨h1, ⟨h2, h3⟩, h4, h5⟩
    exact ⟨⟨h1, by linarith, by linarith⟩, h4, h5⟩

theorem pastFun_revProc (σ : Dir d ≃ Dir d) (T : ℝ≥0) (ν : Measure (Dir d × ℝ)) (s : ℝ≥0) :
    pastFun d T (revProc σ T ν) s = ∑ v : Dir d,
      (natOf (ν (({v} : Set (Dir d)) ×ˢ (Ico ((T : ℝ) - ((min s T : ℝ≥0) : ℝ)) T ∩
        Ioo 0 (T : ℝ)))) : ℤ) • (σ v).vec := by
  unfold pastFun
  simp only [revProc_count]
  rw [← Equiv.sum_comp σ]
  simp

theorem measure_eq_of_sub_null {α : Type*} [MeasurableSpace α] {ν : Measure α} {A B C : Set α}
    (hBA : B ⊆ A) (hAB : A ⊆ B ∪ C) (hC : ν C = 0) : ν A = ν B := by
  refine le_antisymm ?_ (measure_mono hBA)
  calc ν A ≤ ν (B ∪ C) := measure_mono hAB
    _ ≤ ν B + ν C := measure_union_le _ _
    _ = ν B := by rw [hC, add_zero]

theorem stopPath_revPath_can_eq {ν : Measure (Dir d × ℝ)} (hν : ν ∈ goodSet d) {T : ℝ≥0}
    (hT0 : tot ν {(T : ℝ)} = 0) :
    stopPath T (revPath T (can d ν)) = pastFun d T (revProc (Equiv.refl _) T ν) := by
  funext s
  rw [pastFun_revProc]
  simp only [Equiv.refl_apply, stopPath]
  set m : ℝ≥0 := min s T with hm
  have hmT : m ≤ T := min_le_right _ _
  have hnull : ∀ v : Dir d, ν (({v} : Set (Dir d)) ×ˢ {(T : ℝ)}) = 0 := fun v =>
    measure_mono_null (prod_mono (subset_univ _) subset_rfl) hT0
  by_cases hlt : m < T
  · have hr : 0 < T - m := tsub_pos_of_lt hlt
    obtain ⟨a, hat, hconst, hnull'⟩ := exists_const_left_nn ν hr
    have e1 : revPath T (can d ν) m = can d ν T - can d ν a := by
      simp only [revPath, ite_eq_left hlt]
      rw [leftLim_eq_of_const hat hconst]
    rw [e1]
    have hcast : ((T - m : ℝ≥0) : ℝ) = (T : ℝ) - m := NNReal.coe_sub hmT
    have haT : (a : ℝ) ≤ T := by
      have := NNReal.coe_lt_coe.2 hat
      rw [hcast] at this
      linarith [NNReal.coe_nonneg m]
    have hpos : (0 : ℝ) < (T : ℝ) - m := by rw [← hcast]; exact_mod_cast hr
    have hrest := walk_sub_eq hν a.2 haT
    have hz := hnull' hν
    simp only [can]
    refine hrest.trans (Finset.sum_congr rfl fun v _ => ?_)
    congr 3
    have hat' : (a : ℝ) < (T : ℝ) - m := by
      have := NNReal.coe_lt_coe.2 hat
      rwa [hcast] at this
    refine measure_eq_of_sub_null (C := ({v} ×ˢ Ioo (a : ℝ) ((T - m : ℝ≥0) : ℝ)) ∪
      ({v} ×ˢ {(T : ℝ)})) ?_ ?_ ?_
    · rintro ⟨v', x⟩ hx
      simp only [mem_prod, mem_singleton_iff, mem_Ioc, mem_inter_iff, mem_Ico,
        mem_Ioo] at hx ⊢
      exact ⟨hx.1, lt_of_lt_of_le hat' hx.2.1.1, hx.2.1.2.le⟩
    · rintro ⟨v', x⟩ hx
      simp only [mem_prod, mem_singleton_iff, mem_Ioc, mem_union, mem_inter_iff, mem_Ico,
        mem_Ioo, hcast] at hx ⊢
      obtain ⟨h1, h2, h3⟩ := hx
      by_cases hx1 : (T : ℝ) - m ≤ x
      · by_cases hx2 : x < T
        · exact Or.inl ⟨h1, ⟨hx1, hx2⟩, by linarith, hx2⟩
        · exact Or.inr (Or.inr ⟨h1, le_antisymm h3 (not_lt.1 hx2)⟩)
      · exact Or.inr (Or.inl ⟨h1, h2, not_le.1 hx1⟩)
    · refine measure_union_null (measure_mono_null (prod_mono (subset_univ _) subset_rfl) hz)
        (hnull v)
  · have hmeq : m = T := le_antisymm hmT (not_lt.1 hlt)
    simp only [revPath, ite_eq_right hlt, can]
    have hrest := walk_sub_eq hν (le_refl (0 : ℝ)) T.2
    rw [walk_zero, sub_zero] at hrest
    refine hrest.trans (Finset.sum_congr rfl fun v _ => ?_)
    congr 3
    rw [hmeq]
    refine measure_eq_of_sub_null (C := {v} ×ˢ {(T : ℝ)}) ?_ ?_ (hnull v)
    · rintro ⟨v', x⟩ hx
      simp only [mem_prod, mem_singleton_iff, mem_Ioc, mem_inter_iff, mem_Ico, mem_Ioo] at hx ⊢
      exact ⟨hx.1, hx.2.2.1, hx.2.2.2.le⟩
    · rintro ⟨v', x⟩ hx
      simp only [mem_prod, mem_singleton_iff, mem_Ioc, mem_union, mem_inter_iff, mem_Ico,
        mem_Ioo] at hx ⊢
      obtain ⟨h1, h2, h3⟩ := hx
      rcases h3.lt_or_eq with h4 | h4
      · exact Or.inl ⟨h1, ⟨by linarith, h4⟩, h2, h4⟩
      · exact Or.inr ⟨h1, h4⟩

end SRW
end ElboimSly
