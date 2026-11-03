/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRestrictMeas
public import Mathlib

/-!
# The `num`/`nth` identities for `trunc`

Measurability of record functionals (b), auxiliary. With `P_j(ρ, s) :⇔ j < num ρ ∧ Λ_j(ρ) ≤ s`, the
truncation `trunc s ρ` has exactly the entries `j` with `P_j`, and entry `j` is
`truncEntry s ρ j (ρ.coord j)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

theorem nat_downward (S : Set ℕ) (hd : ∀ i j, i ≤ j → j ∈ S → i ∈ S) :
    (S.Finite → ∀ j, j < S.ncard ↔ j ∈ S) ∧ (S.Infinite → ∀ j, j ∈ S) := by
  classical
  refine ⟨fun hf j => ?_, fun hi j => ?_⟩
  · have hex : ∃ k, k ∉ S := by
      by_contra h
      push Not at h
      exact Set.infinite_univ (hf.subset fun k _ => h k) |>.elim
    set c := Nat.find hex
    have hS : S = Iio c := by
      ext k
      simp only [mem_Iio]
      constructor
      · intro hk
        by_contra hck
        exact Nat.find_spec hex (hd c k (not_lt.mp hck) hk)
      · intro hk
        by_contra hkS
        exact Nat.find_min hex hk hkS
    have hc : S.ncard = c := by
      rw [hS]
      have : Iio c = ((Finset.range c : Finset ℕ) : Set ℕ) := by ext; simp
      rw [this, Set.ncard_coe_finset, Finset.card_range]
    rw [hc, hS]; simp
  · obtain ⟨k, hk, hjk⟩ := hi.exists_gt j
    exact hd j k hjk.le hk

namespace CycRec

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

omit [MeasurableSpace I] in
theorem cum_mono (ρ : CycRec I d) {i j : ℕ} (h : i ≤ j) : ρ.cum i ≤ ρ.cum j :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

omit [MeasurableSpace I] in
theorem lenAt_eq (junk : CycEntry I d) (ρ : CycRec I d) (i : ℕ) :
    ρ.lenAt i = if (i : ℕ∞) < ρ.num then (ρ.coord junk i).len else 0 := by
  rcases ρ with ⟨n, f⟩ | f
  · by_cases h : i < n
    · simp [lenAt, nth, coord, num, h]
    · simp [lenAt, nth, num, h]
  · simp [lenAt, nth, coord, num]

/-- The set of surviving entries. -/
def surv (s : ℝ≥0) (ρ : CycRec I d) : Set ℕ := {k | (k : ℕ∞) < ρ.num ∧ ρ.cum k ≤ s}

omit [MeasurableSpace I] in
theorem surv_downward (s : ℝ≥0) (ρ : CycRec I d) :
    ∀ i j, i ≤ j → j ∈ ρ.surv s → i ∈ ρ.surv s := fun _i _j hij hj =>
  ⟨(Nat.cast_le.mpr hij).trans_lt hj.1, (ρ.cum_mono hij).trans hj.2⟩

open scoped Classical in
omit [MeasurableSpace I] in
theorem trunc_spec (junk : CycEntry I d) (s : ℝ≥0) (ρ : CycRec I d) :
    ∃ m : ℕ∞, (CycRec.trunc s ρ).num = m ∧ (∀ j : ℕ, (j : ℕ∞) < m ↔ j ∈ ρ.surv s) ∧
      (∀ j ∈ ρ.surv s, (CycRec.trunc s ρ).coord junk j =
        CycRec.truncEntry s ρ j (ρ.coord junk j)) ∧
      (∀ j, j ∉ ρ.surv s → (CycRec.trunc s ρ).coord junk j = junk) := by
  rcases ρ with ⟨n, f⟩ | f
  · set ρ : CycRec I d := Sum.inl ⟨n, f⟩ with hρ
    have hS : ρ.surv s = {k | k < n ∧ CycRec.cum ρ k ≤ s} := by
      ext k; simp [CycRec.surv, ρ, CycRec.num]
    have hfin : (ρ.surv s).Finite := (Set.finite_Iio n).subset fun k hk => by
      rw [hS] at hk; exact hk.1
    set m0 := (Finset.univ.filter fun i : Fin n => CycRec.cum ρ i ≤ s).card with hm0
    have hnc : (ρ.surv s).ncard = m0 := by
      have : ρ.surv s = Fin.val '' ((Finset.univ.filter fun i : Fin n => CycRec.cum ρ i ≤ s) :
          Set (Fin n)) := by
        ext k
        simp only [hS, mem_ofPred_eq, mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hk, hc⟩; exact ⟨⟨k, hk⟩, hc, rfl⟩
        · rintro ⟨i, hc, rfl⟩; exact ⟨i.2, hc⟩
      rw [this, Set.ncard_image_of_injective _ Fin.val_injective, Set.ncard_coe_finset]
    have hiff := (nat_downward (ρ.surv s) (CycRec.surv_downward s ρ)).1 hfin
    have hnum : (CycRec.trunc s ρ).num = (m0 : ℕ∞) := by
      simp [CycRec.trunc, CycRec.num, ρ, m0]
    refine ⟨m0, hnum, fun j => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [Nat.cast_lt, ← hnc]; exact hiff j
    · have hjm : j < m0 := by rw [← hnc]; exact (hiff j).2 hj
      have hjn : j < n := by
        have h1 : (j : ℕ∞) < (n : ℕ∞) := hj.1
        exact_mod_cast h1
      have hjm' : j < ({i | CycRec.cum (Sum.inl ⟨n, f⟩ : CycRec I d) ↑i ≤ ↑s} :
          Finset (Fin n)).card := hjm
      rw [hρ]
      simp only [CycRec.coord, CycRec.trunc, CycRec.nth, hjm', hjn, dite_true, Option.getD_some]
      rfl
    · have hjm : ¬ j < m0 := by rw [← hnc]; exact fun h => hj ((hiff j).1 h)
      have hjm' : ¬ j < ({i | CycRec.cum (Sum.inl ⟨n, f⟩ : CycRec I d) ↑i ≤ ↑s} :
          Finset (Fin n)).card := hjm
      rw [hρ]
      simp only [CycRec.coord, CycRec.trunc, CycRec.nth, hjm', dite_false, Option.getD_none]
  · set ρ : CycRec I d := Sum.inr f with hρ
    have hS : ρ.surv s = {k | CycRec.cum ρ k ≤ s} := by
      ext k; simp [CycRec.surv, ρ, CycRec.num]
    by_cases hinf : {k : ℕ | CycRec.cum ρ k ≤ s}.Infinite
    · have hall := (nat_downward (ρ.surv s) (CycRec.surv_downward s ρ)).2 (by rwa [hS])
      refine ⟨⊤, by simp [CycRec.trunc, CycRec.num, ρ, hinf], fun j => ?_, fun j hj => ?_,
        fun j hj => absurd (hall j) hj⟩
      · simp [hall j]
      · simp [CycRec.coord, CycRec.trunc, CycRec.nth, ρ, hinf]
    · have hfin : (ρ.surv s).Finite := by rw [hS]; exact Set.not_infinite.mp hinf
      have hiff := (nat_downward (ρ.surv s) (CycRec.surv_downward s ρ)).1 hfin
      have hnc : (ρ.surv s).ncard = {k : ℕ | CycRec.cum ρ k ≤ s}.ncard := by rw [hS]
      refine ⟨((ρ.surv s).ncard : ℕ), ?_, fun j => ?_, fun j hj => ?_, fun j hj => ?_⟩
      · simp [CycRec.trunc, CycRec.num, ρ, hinf, ← hnc]
      · rw [Nat.cast_lt]; exact hiff j
      · have hjm : j < (ρ.surv s).ncard := (hiff j).2 hj
        rw [hnc] at hjm
        simp [CycRec.coord, CycRec.trunc, CycRec.nth, ρ, hinf, hjm]
      · have hjm : ¬ j < (ρ.surv s).ncard := fun h => hj ((hiff j).1 h)
        rw [hnc] at hjm
        simp [CycRec.coord, CycRec.trunc, CycRec.nth, ρ, hinf, hjm]

end CycRec

end ElboimSly.Cyclic

end
