/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Paths
public import Mathlib

/-!
# Jumps of the walk

Good event and path properties, property (P3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

section Jumps

variable {d : ℕ} {ν : Measure (Dir d × ℝ)}

/-- On the good event every time `t > 0` carries at most one point. -/
theorem good_tot_singleton_le_one (hν : ν ∈ goodSet d) {t : ℝ} (ht : 0 < t) :
    tot ν {t} ≤ 1 := by
  have h2 := hν.2
  simp only [mem_iInter] at h2
  set T : ℕ := ⌈t⌉₊ with hT
  have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.2 (by simpa [hT] using ht)
  obtain ⟨_, hU⟩ := h2 T hT1
  simp only [mem_iUnion, mem_iInter, mem_ofPred_eq] at hU
  obtain ⟨n, hn, hcell⟩ := hU
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have htT : t ≤ T := Nat.le_ceil t
  set x : ℝ := t * n / T with hx
  have hx0 : 0 < x := by positivity
  have hxn : x ≤ n := by
    rw [hx, div_le_iff₀ hTpos]; nlinarith
  set k : ℕ := ⌈x⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by simpa [hk] using hx0)
  have hkn : k ≤ n := Nat.ceil_le.2 (by exact_mod_cast hxn)
  have hk1' : (k : ℝ) - 1 < x := by linarith [Nat.ceil_lt_add_one hx0.le]
  have hk2 : x ≤ k := Nat.le_ceil x
  have hsub : ({t} : Set ℝ) ⊆ Ioc (((k : ℝ) - 1) * T / n) (k * T / n) := by
    intro y hy
    rw [mem_singleton_iff] at hy
    rw [hy]
    constructor
    · rw [div_lt_iff₀ hnpos]
      have h1 : ((k : ℝ) - 1) * T < x * T := mul_lt_mul_of_pos_right hk1' hTpos
      have h2 : x * T = t * n := by rw [hx]; field_simp
      linarith
    · rw [le_div_iff₀ hnpos]
      have h1 : x * T ≤ k * T := mul_le_mul_of_nonneg_right hk2 hTpos.le
      have h2 : x * T = t * n := by rw [hx]; field_simp
      linarith
  exact (measure_mono (prod_mono subset_rfl hsub)).trans (hcell k ⟨hk1, hkn⟩)

theorem sum_smul_vec_cases (j : Dir d → ℕ) (h : ∑ v, j v ≤ 1) :
    ∑ v : Dir d, (j v : ℤ) • v.vec = 0 ∨ ∃ v : Dir d, ∑ w : Dir d, (j w : ℤ) • w.vec = v.vec := by
  classical
  by_cases h0 : ∀ v, j v = 0
  · left; simp [h0]
  · right
    push Not at h0
    obtain ⟨v, hv⟩ := h0
    have hv1 : j v = 1 := by
      have := Finset.single_le_sum (f := j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
      omega
    have hw : ∀ w, w ≠ v → j w = 0 := by
      intro w hwv
      have h2 : j v + j w ≤ ∑ u, j u := by
        have := Finset.sum_le_sum_of_subset (f := j) (Finset.subset_univ {v, w})
        rwa [Finset.sum_pair (Ne.symm hwv)] at this
      omega
    refine ⟨v, ?_⟩
    rw [Finset.sum_eq_single v]
    · simp [hv1]
    · intro w _ hwv; simp [hw w hwv]
    · simp

/-- Left-limit formula: just left of `t` the walk is constant, and the jump at `t` is given by the
points at time exactly `t`. -/
theorem left_jump_formula (hν : ν ∈ goodSet d) {t : ℝ} (ht : 0 < t) :
    ∃ δ, 0 < δ ∧ δ < t ∧ (∀ u ∈ Ico (t - δ) t, walk d ν u = walk d ν (t - δ)) ∧
      walk d ν t - walk d ν (t - δ) =
        ∑ v : Dir d, ((natOf (ν (({v} : Set (Dir d)) ×ˢ {t})) : ℕ) : ℤ) • v.vec := by
  obtain ⟨δ, hδ, hδt, hconst, hnull⟩ := exists_const_left (ν := ν) t ht
  refine ⟨δ, hδ, hδt, hconst, ?_⟩
  have hnull' := hnull hν
  rw [walk_sub_eq hν (by linarith) (by linarith)]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 3
  apply le_antisymm
  · have h1 : ({v} : Set (Dir d)) ×ˢ Ioc (t - δ) t ⊆
        ((univ : Set (Dir d)) ×ˢ Ioo (t - δ) t) ∪ (({v} : Set (Dir d)) ×ˢ {t}) := by
      intro p hp
      simp only [mem_prod, mem_singleton_iff, mem_Ioc, mem_union, mem_univ, true_and,
        mem_Ioo] at hp ⊢
      rcases lt_or_eq_of_le hp.2.2 with h | h
      · exact Or.inl ⟨hp.2.1, h⟩
      · exact Or.inr ⟨hp.1, h⟩
    refine (measure_mono h1).trans ((measure_union_le _ _).trans ?_)
    have : ν ((univ : Set (Dir d)) ×ˢ Ioo (t - δ) t) = 0 := hnull'
    rw [this, zero_add]
  · exact measure_mono (prod_mono subset_rfl (fun y hy => by
      rw [mem_singleton_iff] at hy; rw [hy]; exact ⟨by linarith, le_rfl⟩))

/-- Good event and path properties (P3): a jump of the walk at `t` is a unit step. -/
theorem jump_mem_dir {t : ℝ} (ht : 0 < t) {L : Fin d → ℤ} {δ : ℝ} (hδ : 0 < δ)
    (hL : ∀ u ∈ Ico (t - δ) t, walk d ν u = L) :
    walk d ν t = L ∨ ∃ v : Dir d, walk d ν t - L = v.vec := by
  by_cases hν : ν ∈ goodSet d
  · obtain ⟨δ', hδ', hδ't, hconst, hjump⟩ := left_jump_formula hν ht
    have hu : t - min δ δ' / 2 ∈ Ico (t - δ) t ∩ Ico (t - δ') t := by
      have := min_le_left δ δ'
      have := min_le_right δ δ'
      have := lt_min hδ hδ'
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    have hLeq : L = walk d ν (t - δ') := by
      rw [← hL _ hu.1, hconst _ hu.2]
    have hnat : ∑ v : Dir d, natOf (ν (({v} : Set (Dir d)) ×ˢ {t})) ≤ 1 := by
      have h1 : ((∑ v : Dir d, natOf (ν (({v} : Set (Dir d)) ×ˢ {t})) : ℕ) : ℝ≥0∞) ≤ 1 := by
        push_cast
        have : ∀ v : Dir d, ((natOf (ν (({v} : Set (Dir d)) ×ˢ {t})) : ℕ) : ℝ≥0∞) =
            ν (({v} : Set (Dir d)) ×ˢ {t}) := fun v =>
          (IsNat.natCast_natOf (by
            have := good_singleton hν v ht
            exact this))
        simp only [this]
        rw [← tot_eq_sum ν _ (measurableSet_singleton t)]
        exact good_tot_singleton_le_one hν ht
      exact_mod_cast h1
    rcases sum_smul_vec_cases _ hnat with h | ⟨v, h⟩
    · left
      rw [hLeq]
      have := hjump
      rw [h] at this
      exact sub_eq_zero.1 this
    · right
      exact ⟨v, by rw [hLeq, hjump, h]⟩
  · left
    have h1 : walk d ν t = 0 := walk_of_not_good hν t
    have h2 : L = 0 := by
      rw [← hL (t - δ / 2) ⟨by linarith, by linarith⟩, walk_of_not_good hν]
    rw [h1, h2]

/-- `t` is a jump time of the walk: the left limit differs from the value. -/
def IsJump (ν : Measure (Dir d × ℝ)) (t : ℝ) : Prop :=
  0 < t ∧ ∀ δ > 0, ∃ u ∈ Ico (t - δ) t, walk d ν u ≠ walk d ν t

theorem IsJump.good {t : ℝ} (h : IsJump ν t) : ν ∈ goodSet d := by
  by_contra hν
  obtain ⟨u, _, hu⟩ := h.2 1 one_pos
  exact hu (by rw [walk_of_not_good hν, walk_of_not_good hν])

theorem IsJump.one_le_tot {t : ℝ} (h : IsJump ν t) : 1 ≤ tot ν {t} := by
  have hν := h.good
  by_contra hlt
  rw [not_le] at hlt
  have hz : tot ν {t} = 0 := by
    obtain ⟨n, hn⟩ := good_tot_singleton hν h.1
    rw [hn] at hlt ⊢
    have : n = 0 := by
      by_contra hn0
      have : (1 : ℝ≥0∞) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn0
      exact absurd hlt (not_lt.2 this)
    simp [this]
  obtain ⟨δ, hδ, hδt, hconst, hjump⟩ := left_jump_formula hν h.1
  have hall : ∀ v : Dir d, natOf (ν (({v} : Set (Dir d)) ×ˢ {t})) = 0 := by
    intro v
    have : ν (({v} : Set (Dir d)) ×ˢ {t}) = 0 := by
      refine measure_mono_null (prod_mono (subset_univ _) subset_rfl) ?_
      exact hz
    rw [this]; simp [natOf]
  simp only [hall, Nat.cast_zero, zero_smul, Finset.sum_const_zero, sub_eq_zero] at hjump
  obtain ⟨u, hu, hne⟩ := h.2 δ hδ
  exact hne (by rw [hconst u hu, hjump])

/-- Good event and path properties (P3): there are at most `M((0,T])` jump times in `(0,T]`. -/
theorem jumps_finite_card (T : ℝ) :
    {t : ℝ | t ∈ Ioc 0 T ∧ IsJump ν t}.Finite ∧
      {t : ℝ | t ∈ Ioc 0 T ∧ IsJump ν t}.ncard ≤ natOf (tot ν (Ioc 0 T)) := by
  set S : Set ℝ := {t : ℝ | t ∈ Ioc 0 T ∧ IsJump ν t} with hS
  by_cases hν : ν ∈ goodSet d
  · obtain ⟨n, hn⟩ := good_tot_Ioc hν (a := 0) (b := T) le_rfl
    have hbound : ∀ F : Finset ℝ, (F : Set ℝ) ⊆ S → F.card ≤ n := by
      intro F hF
      have h1 : (F.card : ℝ≥0∞) ≤ ν ((univ : Set (Dir d)) ×ˢ (F : Set ℝ)) := by
        have hU : (univ : Set (Dir d)) ×ˢ (F : Set ℝ) =
            ⋃ t ∈ F, (univ : Set (Dir d)) ×ˢ ({t} : Set ℝ) := by
          ext ⟨x, y⟩; simp
        rw [hU, measure_biUnion_finset]
        · calc (F.card : ℝ≥0∞) = ∑ _t ∈ F, (1 : ℝ≥0∞) := by simp
            _ ≤ _ := Finset.sum_le_sum fun t ht => (hF ht).2.one_le_tot
        · intro a _ b _ hab
          exact Set.disjoint_left.2 fun p hp hq => hab (by
            simp only [mem_prod, mem_singleton_iff] at hp hq; rw [← hp.2, ← hq.2])
        · exact fun t _ => MeasurableSet.univ.prod (measurableSet_singleton t)
      have h2 : ν ((univ : Set (Dir d)) ×ˢ (F : Set ℝ)) ≤ n := by
        rw [← hn]
        exact measure_mono (prod_mono subset_rfl (fun t ht => (hF ht).1))
      exact_mod_cast h1.trans h2
    have hfin : S.Finite := by
      by_contra hinf
      obtain ⟨F, hFS, hF⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
      have := hbound F hFS
      omega
    refine ⟨hfin, ?_⟩
    rw [hn]
    have : (natOf (n : ℝ≥0∞)) = n := by simp [natOf]
    rw [this, Set.ncard_eq_toFinset_card S hfin]
    exact hbound _ (by simp)
  · have : S = ∅ := by
      ext t
      simp only [hS, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ h => hν h.good
    rw [this]
    simp

end Jumps

end SRW
end ElboimSly
