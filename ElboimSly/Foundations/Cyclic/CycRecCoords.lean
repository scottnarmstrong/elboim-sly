/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRecord
public import Mathlib

/-!
# Coordinates of records

A record is determined by its number of entries `num ρ ∈ ℕ ∪ {∞}` and its coordinates
`coord ρ j` (the entry `j`, a junk entry if there is none). A map into `CycRec` is measurable as soon
as `num` and all the coordinates are (`measurable_cycRec_of_coords`). This is how all the
measurability statements of measurability of record functionals are proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

namespace CycRec

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

/-- The number of entries, in `ℕ ∪ {∞}`. -/
def num : CycRec I d → ℕ∞
  | Sum.inl ⟨n, _⟩ => n
  | Sum.inr _ => ⊤

/-- The entry `j`, or the junk entry `junk` if there is none. -/
def coord (junk : CycEntry I d) (ρ : CycRec I d) (j : ℕ) : CycEntry I d := (ρ.nth j).getD junk

omit [MeasurableSpace I] in
theorem eq_inl_of_num {junk : CycEntry I d} {ρ : CycRec I d} {k : ℕ} (h : ρ.num = k) :
    ρ = Sum.inl ⟨k, fun i : Fin k => ρ.coord junk i⟩ := by
  rcases ρ with ⟨n, f⟩ | f
  · simp only [num, Nat.cast_inj] at h
    subst h
    congr
    funext i
    simp [coord, nth, i.2]
  · simp [num] at h

omit [MeasurableSpace I] in
theorem eq_inr_of_num {junk : CycEntry I d} {ρ : CycRec I d} (h : ρ.num = ⊤) :
    ρ = Sum.inr fun j => ρ.coord junk j := by
  rcases ρ with ⟨n, f⟩ | f
  · simp [num] at h
  · rfl

end CycRec

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

/-- A map into records is measurable as soon as the number of entries and all coordinates are. -/
theorem measurable_cycRec_of_coords {α : Type*} [MeasurableSpace α] (Φ : α → CycRec I d)
    (junk : CycEntry I d) (hnum : Measurable fun a => (Φ a).num)
    (hent : ∀ j, Measurable fun a => (Φ a).coord junk j) : Measurable Φ := by
  intro S hS
  rw [measurableSet_sum_iff] at hS
  obtain ⟨h1, h2⟩ := hS
  have hcov : Φ ⁻¹' S = (⋃ k : ℕ, {a | (Φ a).num = k} ∩ Φ ⁻¹' S) ∪ ({a | (Φ a).num = ⊤} ∩ Φ ⁻¹' S) := by
    ext a
    simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      cases hn : (Φ a).num using ENat.recTopCoe with
      | top => exact Or.inr ⟨rfl, h⟩
      | coe k => exact Or.inl ⟨k, rfl, h⟩
    · rintro (⟨k, _, h⟩ | ⟨_, h⟩) <;> exact h
  rw [hcov]
  refine MeasurableSet.union (MeasurableSet.iUnion fun k => ?_) ?_
  · have hk : MeasurableSet {a | (Φ a).num = k} := hnum (measurableSet_singleton _)
    have hg : Measurable fun a => (fun i : Fin k => (Φ a).coord junk i) :=
      measurable_pi_iff.mpr fun i => hent i
    have hT : MeasurableSet {g : Fin k → CycEntry I d | (Sum.inl ⟨k, g⟩ : CycRec I d) ∈ S} :=
      (MeasurableSpace.measurableSet_iInf.mp h1 k :)
    have : {a | (Φ a).num = k} ∩ Φ ⁻¹' S =
        {a | (Φ a).num = k} ∩ (fun a => (fun i : Fin k => (Φ a).coord junk i)) ⁻¹'
          {g : Fin k → CycEntry I d | (Sum.inl ⟨k, g⟩ : CycRec I d) ∈ S} := by
      ext a
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨hn, h⟩
        refine ⟨hn, ?_⟩
        rw [CycRec.eq_inl_of_num (junk := junk) hn] at h
        exact h
      · rintro ⟨hn, h⟩
        refine ⟨hn, ?_⟩
        rw [CycRec.eq_inl_of_num (junk := junk) hn]
        exact h
    rw [this]
    exact hk.inter (hg hT)
  · have hk : MeasurableSet {a | (Φ a).num = ⊤} := hnum (measurableSet_singleton _)
    have hg : Measurable fun a => (fun j : ℕ => (Φ a).coord junk j) :=
      measurable_pi_iff.mpr fun j => hent j
    have : {a | (Φ a).num = ⊤} ∩ Φ ⁻¹' S =
        {a | (Φ a).num = ⊤} ∩ (fun a => (fun j : ℕ => (Φ a).coord junk j)) ⁻¹'
          {g : ℕ → CycEntry I d | (Sum.inr g : CycRec I d) ∈ S} := by
      ext a
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨hn, h⟩
        refine ⟨hn, ?_⟩
        rw [CycRec.eq_inr_of_num (junk := junk) hn] at h
        exact h
      · rintro ⟨hn, h⟩
        refine ⟨hn, ?_⟩
        rw [CycRec.eq_inr_of_num (junk := junk) hn]
        exact h
    rw [this]
    exact hk.inter (hg h2)

theorem measurable_sigma_of {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {γ : Type*}
    [MeasurableSpace γ] {g : (Σ i, β i) → γ} (h : ∀ i, Measurable fun x : β i => g ⟨i, x⟩) :
    Measurable g := by
  intro B hB
  exact MeasurableSpace.measurableSet_iInf.mpr fun i => h i hB

theorem CycRec.measurable_num : Measurable (CycRec.num : CycRec I d → ℕ∞) := by
  refine measurable_fun_sum ?_ ?_
  · exact measurable_sigma_of fun k => measurable_const
  · exact measurable_const

theorem CycRec.measurable_coord (junk : CycEntry I d) (j : ℕ) :
    Measurable (fun ρ : CycRec I d => CycRec.coord junk ρ j) := by
  refine measurable_fun_sum ?_ ?_
  · refine measurable_sigma_of (β := fun k => Fin k → CycEntry I d) fun k => ?_
    show Measurable fun x : Fin k → CycEntry I d =>
      (CycRec.nth (Sum.inl ⟨k, x⟩ : CycRec I d) j).getD junk
    by_cases h : j < k
    · simp only [CycRec.nth, h, dite_true, Option.getD_some]
      exact measurable_pi_apply _
    · simp only [CycRec.nth, h, dite_false, Option.getD_none]
      exact measurable_const
  · simp only [CycRec.coord, CycRec.nth]
    exact measurable_pi_apply j

/-- Dispatch on a finite value of `num`. -/
theorem measurable_dispatch {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {num : α → ℕ∞} (hnum : Measurable num) {F : ℕ → α → γ} (hF : ∀ k, Measurable (F k)) (c : γ)
    {G : α → γ} (hG : ∀ a, G a = if num a = ⊤ then c else F (num a).toNat a) : Measurable G := by
  have : G = fun a => if num a = ⊤ then c else F (num a).toNat a := funext hG
  rw [this]
  intro B hB
  have : (fun a => if num a = ⊤ then c else F (num a).toNat a) ⁻¹' B =
      ({a | num a = ⊤} ∩ {_a | c ∈ B}) ∪ ⋃ k : ℕ, ({a | num a = k} ∩ F k ⁻¹' B) := by
    ext a
    simp only [mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    by_cases h : num a = ⊤
    · simp [h]
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h
      simp [← hk]
  rw [this]
  refine MeasurableSet.union ((hnum (measurableSet_singleton _)).inter (MeasurableSet.const _))
    (MeasurableSet.iUnion fun k => (hnum (measurableSet_singleton _)).inter (hF k hB))

end ElboimSly.Cyclic

end
