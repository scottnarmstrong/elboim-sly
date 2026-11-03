/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Dissecting
public import ElboimSly.Foundations.PPP.Giry
public import Mathlib

/-!
# Dirac masses

Dirac masses.

* `SepPartSeq.diracSet`: the set `𝔇` described by cell masses; `mem_diracSet_iff` is (a).
* `SepPartSeq.atomMap`: the atom map `ξ : Measure S → S ⊕ Unit`, with `measurable_atomMap` and
  `preimage_atomMap_inl` (b).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

namespace SepPartSeq

variable (P : SepPartSeq S)

/-- The description of `𝔇 = {δ_x}` through cell masses. -/
def diracSet : Set (Measure S) :=
  {ν | ν Set.univ = 1 ∧ ∀ m j, ν (P.cell m j) = 0 ∨ ν (P.cell m j) = 1}

theorem measurableSet_diracSet : MeasurableSet P.diracSet := by
  have : P.diracSet = {ν | ν Set.univ = 1} ∩ ⋂ m, ⋂ j,
      {ν : Measure S | ν (P.cell m j) = 0 ∨ ν (P.cell m j) = 1} := by
    ext ν; simp [diracSet]
  rw [this]
  refine (Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)).inter ?_
  refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun j => ?_
  have h0 := Measure.measurable_coe (P.measurableSet_cell m j) (measurableSet_singleton (0 : ℝ≥0∞))
  have h1 := Measure.measurable_coe (P.measurableSet_cell m j) (measurableSet_singleton (1 : ℝ≥0∞))
  exact h0.union h1

variable {P}

theorem dirac_mem_diracSet (x : S) : Measure.dirac x ∈ P.diracSet := by
  refine ⟨by simp, fun m j => ?_⟩
  rw [Measure.dirac_apply' _ (P.measurableSet_cell m j)]
  by_cases h : x ∈ P.cell m j <;> simp [Set.indicator, h]

theorem unique_cell_of_mass_one {ν : Measure S} (h1 : ν Set.univ = 1) {m j j' : ℕ}
    (hj : ν (P.cell m j) = 1) (hj' : ν (P.cell m j') = 1) : j = j' := by
  by_contra hne
  have hd : Disjoint (P.cell m j) (P.cell m j') := by
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    have a : P.idx m x = j := hx
    have b : P.idx m x = j' := hx'
    omega
  have := measure_union (μ := ν) hd (P.measurableSet_cell m j')
  have h2 : ν (P.cell m j ∪ P.cell m j') ≤ 1 := h1 ▸ measure_mono (Set.subset_univ _)
  rw [this, hj, hj'] at h2
  norm_num at h2

theorem exists_cell_mass_one {ν : Measure S} (h1 : ν Set.univ = 1)
    (h2 : ∀ m j, ν (P.cell m j) = 0 ∨ ν (P.cell m j) = 1) (m : ℕ) : ∃ j, ν (P.cell m j) = 1 := by
  by_contra hno
  push Not at hno
  have hz : ∀ j, ν (P.cell m j) = 0 := fun j => (h2 m j).resolve_right (hno j)
  have : ν Set.univ = 0 := by
    have hU : (Set.univ : Set S) = ⋃ j, P.cell m j := by
      ext x; simp only [Set.mem_univ, Set.mem_iUnion, true_iff]; exact ⟨P.idx m x, rfl⟩
    rw [hU]
    exact measure_iUnion_null hz
  rw [h1] at this; exact one_ne_zero this

/-- Dirac masses (a), hard direction. -/
theorem exists_dirac_of_mem_diracSet {ν : Measure S} (hν : ν ∈ P.diracSet) :
    ∃ x, ν = Measure.dirac x := by
  obtain ⟨h1, h2⟩ := hν
  have : IsProbabilityMeasure ν := ⟨h1⟩
  choose j hj using exists_cell_mass_one h1 h2
  let A : ℕ → Set S := fun m => P.cell m (j m)
  have hnest : Antitone A := by
    refine antitone_nat_of_succ_le fun m => ?_
    intro y hy
    have hy' : P.idx (m + 1) y = j (m + 1) := hy
    have hsub : P.cell (m + 1) (j (m + 1)) ⊆ P.cell m (P.idx m y) := by
      intro z hz
      have : P.idx (m + 1) z = j (m + 1) := hz
      exact P.refine m z y (this.trans hy'.symm)
    have hmass : ν (P.cell m (P.idx m y)) = 1 := by
      have := measure_mono (μ := ν) hsub
      rw [hj (m + 1)] at this
      exact (h2 m _).resolve_left (by intro h0; rw [h0] at this; simp at this)
    have := unique_cell_of_mass_one h1 hmass (hj m)
    show P.idx m y = j m
    exact this
  have hinter : ν (⋂ m, A m) = 1 := by
    rw [hnest.measure_iInter (fun m => (P.measurableSet_cell m _).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    simp [A, hj]
  have hne : (⋂ m, A m).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.1 h] at hinter
    simp at hinter
  obtain ⟨x, hx⟩ := hne
  have hcell : ∀ m, P.cellOf m x = A m := fun m => (P.cell_eq_cellOf (Set.mem_iInter.1 hx m)).symm
  have hsing : ν {x} = 1 := by
    have : ν {x} = ⨅ m, ν (P.cellOf m x) := by
      rw [← (P.cellOf_antitone x).measure_iInter
        (fun m => (P.measurableSet_cellOf m x).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩,
        P.iInter_cellOf x]
    rw [this]; simp [hcell, A, hj]
  refine ⟨x, ?_⟩
  ext B hB
  rw [Measure.dirac_apply' _ hB]
  by_cases hxB : x ∈ B
  · simp only [Set.indicator, hxB, ite_true, Pi.one_apply]
    exact le_antisymm (h1 ▸ measure_mono (Set.subset_univ _))
      (hsing ▸ measure_mono (Set.singleton_subset_iff.2 hxB))
  · simp only [Set.indicator, hxB, ite_false]
    have hcompl : ν {x}ᶜ = 0 := by
      rw [measure_compl (P.measurableSet_singleton' x) (measure_ne_top _ _), h1, hsing]; simp
    exact measure_mono_null (fun y hy => by rintro rfl; exact hxB hy) hcompl

/-- Dirac masses (a). -/
theorem mem_diracSet_iff {ν : Measure S} : ν ∈ P.diracSet ↔ ∃ x, ν = Measure.dirac x :=
  ⟨exists_dirac_of_mem_diracSet, fun ⟨x, hx⟩ => hx ▸ dirac_mem_diracSet x⟩

/-- Dirac masses (b): `x ↦ δ_x` is injective. -/
theorem dirac_injective (P : SepPartSeq S) : Function.Injective (fun x : S => (Measure.dirac x : Measure S)) := by
  intro x y h
  have := congrArg (fun ν : Measure S => ν {x}) h
  simp only [Measure.dirac_apply' _ (P.measurableSet_singleton' x)] at this
  by_contra hne
  simp [Set.indicator, Ne.symm hne] at this

open Classical in
/-- The atom map `ξ : 𝓜(S) → S ⊕ {†}`: `ξ(δ_x) = x` and `ξ(ν) = †` otherwise. -/
noncomputable def atomMap (P : SepPartSeq S) (ν : Measure S) : S ⊕ Unit :=
  if h : ν ∈ P.diracSet then Sum.inl (Classical.choose (mem_diracSet_iff.1 h)) else Sum.inr ()

theorem atomMap_dirac (P : SepPartSeq S) (x : S) : P.atomMap (Measure.dirac x) = Sum.inl x := by
  have h : (Measure.dirac x : Measure S) ∈ P.diracSet := dirac_mem_diracSet x
  rw [atomMap, dite_eq_left h]
  exact congrArg Sum.inl (P.dirac_injective (Classical.choose_spec (mem_diracSet_iff.1 h)).symm)

theorem atomMap_of_not_mem (P : SepPartSeq S) {ν : Measure S} (h : ν ∉ P.diracSet) :
    P.atomMap ν = Sum.inr () := by
  rw [atomMap, dite_eq_right h]

/-- Dirac masses (b): the atom map is measurable. -/
theorem measurable_atomMap (P : SepPartSeq S) : Measurable P.atomMap := by
  intro s hs
  rw [measurableSet_sum_iff] at hs
  obtain ⟨h1, h2⟩ := hs
  have e : P.atomMap ⁻¹' s =
      (P.diracSet ∩ {ν : Measure S | ν (Sum.inl ⁻¹' s) = 1}) ∪
        (P.diracSetᶜ ∩ {_ν : Measure S | Sum.inr () ∈ s}) := by
    ext ν
    by_cases h : ν ∈ P.diracSet
    · obtain ⟨x, rfl⟩ := mem_diracSet_iff.1 h
      have hx : (Measure.dirac x : Measure S) (Sum.inl ⁻¹' s) = 1 ↔ Sum.inl x ∈ s := by
        rw [Measure.dirac_apply' _ h1]
        by_cases hm : Sum.inl x ∈ s <;> simp [Set.indicator, hm]
      simp only [Set.mem_preimage, atomMap_dirac, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_ofPred_eq, h, true_and, not_true_eq_false, false_and, or_false]
      exact hx.symm
    · simp only [Set.mem_preimage, atomMap_of_not_mem P h, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_ofPred_eq, h, not_false_eq_true, true_and, false_and, false_or]
  rw [e]
  refine (P.measurableSet_diracSet.inter (Measure.measurable_coe h1
    (measurableSet_singleton (1 : ℝ≥0∞)))).union (P.measurableSet_diracSet.compl.inter ?_)
  by_cases hm : Sum.inr () ∈ s
  · simp [hm]
  · simp [hm]

end SepPartSeq

end ElboimSly
