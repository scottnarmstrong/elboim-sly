/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Simple
public import Mathlib

/-!
# Simple counting measures: converse and distinct projections

Simple counting measures form a measurable set (c) (converse) and (d), simplicity (e).

* `mem_bSimple_of_count_restrict`: `∑_{x ∈ Λ} δ_x ∈ 𝔐_s` whenever `Λ ∩ Q` is finite for all
  level-`0` cells `Q`.
* `bProj`, `mem_bProj_iff`: the set `𝔐_φ` and its description as "`φ` injective on atoms".
* `ae_mem_bProj`: almost surely distinct atoms have distinct `φ`-values.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ElboimSly

variable {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]

namespace SepPartSeq

theorem exists_separating_level (P : SepPartSeq S) {F : Set S} (hF : F.Finite) :
    ∃ m, ∀ x ∈ F, ∀ y ∈ F, P.idx m x = P.idx m y → x = y := by
  classical
  have : ∀ p : S × S, ∃ m, p.1 ≠ p.2 → P.idx m p.1 ≠ P.idx m p.2 := fun p => by
    by_cases h : p.1 = p.2
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨m, hm⟩ := P.separate _ _ h
      exact ⟨m, fun _ => hm⟩
  choose f hf using this
  refine ⟨(hF.prod hF).toFinset.sup f, fun x hx y hy hxy => ?_⟩
  by_contra hne
  have hle : f (x, y) ≤ (hF.prod hF).toFinset.sup f :=
    Finset.le_sup (f := f) (by simpa using ⟨hx, hy⟩)
  exact hf (x, y) hne (P.idx_eq_of_le hle hxy)

theorem count_restrict_apply_le_one (P : SepPartSeq S) {Λ C : Set S} (hC : MeasurableSet C)
    (hs : (C ∩ Λ).Subsingleton) : (Measure.count.restrict Λ) C ≤ 1 := by
  have := P.measurableSingletonClass
  rw [Measure.restrict_apply hC]
  by_cases hne : (C ∩ Λ).Nonempty
  · obtain ⟨x, hx⟩ := hne
    calc Measure.count (C ∩ Λ) ≤ Measure.count {x} :=
          measure_mono fun y hy => hs hy hx
      _ = 1 := Measure.count_singleton x
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp

variable {P : SepPartSeq S}

theorem measurableSet_of_finite_pieces (P : SepPartSeq S) {Λ : Set S}
    (hΛ : ∀ i, (Λ ∩ P.cell 0 i).Finite) : MeasurableSet Λ := by
  have := P.measurableSingletonClass
  have : Λ = ⋃ i, Λ ∩ P.cell 0 i := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨P.idx 0 x, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  rw [this]
  exact MeasurableSet.iUnion fun i => (hΛ i).measurableSet

/-- Simple counting measures form a measurable set (c), converse. -/
theorem mem_bSimple_of_count_restrict {Λ : Set S} (hΛ : ∀ i, (Λ ∩ P.cell 0 i).Finite) :
    (Measure.count.restrict Λ : Measure S) ∈ P.bSimple := by
  have := P.measurableSingletonClass
  have hm := measurableSet_of_finite_pieces P hΛ
  refine ⟨fun m j => ?_, fun i => ?_⟩
  · have hfin : (P.cell m j ∩ Λ).Finite := by
      by_cases hne : (P.cell m j).Nonempty
      · obtain ⟨x, hx⟩ := hne
        exact (hΛ (P.idx 0 x)).subset fun y hy => ⟨hy.2, P.cell_subset_cell_zero hx hy.1⟩
      · rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp
    refine ⟨hfin.toFinset.card, ?_⟩
    rw [Measure.restrict_apply (P.measurableSet_cell m j), Measure.count_apply_finite' hfin
      (hfin.measurableSet)]
  · obtain ⟨m, hm'⟩ := P.exists_separating_level (hΛ i)
    refine ⟨m, fun j => P.count_restrict_apply_le_one ((P.measurableSet_cell 0 i).inter
      (P.measurableSet_cell m j)) ?_⟩
    intro x hx y hy
    exact hm' x ⟨hx.2, hx.1.1⟩ y ⟨hy.2, hy.1.1⟩ (by
      have a : P.idx m x = j := hx.1.2
      have b : P.idx m y = j := hy.1.2
      rw [a, b])

/-- Simple counting measures form a measurable set (d): `𝔐_φ`. -/
def bProj (P : SepPartSeq S) (P' : SepPartSeq T) (φ : S → T) : Set (Measure S) :=
  P.bSimple ∩ {ν | ∀ i i', ∃ m, ∀ j,
    ν ((P.cell 0 i ∪ P.cell 0 i') ∩ φ ⁻¹' P'.cell m j) ≤ 1}

theorem measurableSet_bProj (P : SepPartSeq S) (P' : SepPartSeq T) {φ : S → T}
    (hφ : Measurable φ) : MeasurableSet (P.bProj P' φ) := by
  refine P.measurableSet_bSimple.inter ?_
  have : {ν : Measure S | ∀ i i', ∃ m, ∀ j,
      ν ((P.cell 0 i ∪ P.cell 0 i') ∩ φ ⁻¹' P'.cell m j) ≤ 1} =
      ⋂ i, ⋂ i', ⋃ m, ⋂ j, (fun ν : Measure S =>
        ν ((P.cell 0 i ∪ P.cell 0 i') ∩ φ ⁻¹' P'.cell m j)) ⁻¹' Set.Iic 1 := by
    ext ν; simp
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun i' => MeasurableSet.iUnion
    fun m => MeasurableSet.iInter fun j => Measure.measurable_coe
      (((P.measurableSet_cell 0 i).union (P.measurableSet_cell 0 i')).inter
        (hφ (P'.measurableSet_cell m j))) measurableSet_Iic

/-- Simple counting measures form a measurable set (d): `𝔐_φ = {ν ∈ 𝔐_s | φ injective on Λ(ν)}`. -/
theorem mem_bProj_iff (P : SepPartSeq S) (P' : SepPartSeq T) {φ : S → T} (hφ : Measurable φ)
    (ν : Measure S) :
    ν ∈ P.bProj P' φ ↔ ν ∈ P.bSimple ∧ Set.InjOn φ (atoms ν) := by
  have := P.measurableSingletonClass
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun x hx y hy hxy => ?_⟩
    by_contra hne
    obtain ⟨m, hm⟩ := h (P.idx 0 x) (P.idx 0 y)
    have hmem : ∀ z, z ∈ ({x, y} : Set S) →
        z ∈ (P.cell 0 (P.idx 0 x) ∪ P.cell 0 (P.idx 0 y)) ∩ φ ⁻¹' P'.cell m (P'.idx m (φ x)) := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨Or.inl rfl, rfl⟩
      · refine ⟨Or.inr rfl, ?_⟩
        show P'.idx m (φ z) = P'.idx m (φ x)
        rw [← hxy]
    have h2 : ν {x, y} ≤ 1 := (measure_mono hmem).trans (hm _)
    have hx1 : ν {x} = 1 := (singleton_eq_zero_or_one hs x).resolve_left hx
    have hy1 : ν {y} = 1 := (singleton_eq_zero_or_one hs y).resolve_left hy
    have : ν {x, y} = 2 := by
      have e : ({x, y} : Set S) = {x} ∪ {y} := rfl
      rw [e, measure_union (Set.disjoint_singleton.2 hne) (measurableSet_singleton y), hx1, hy1]
      norm_num
    rw [this] at h2
    norm_num at h2
  · rintro ⟨hs, hinj⟩
    refine ⟨hs, fun i i' => ?_⟩
    have hF : (atoms ν ∩ (P.cell 0 i ∪ P.cell 0 i')).Finite := by
      rw [Set.inter_union_distrib_left]
      exact (finite_atoms_inter hs i).union (finite_atoms_inter hs i')
    obtain ⟨m, hm⟩ := P'.exists_separating_level (hF.image φ)
    refine ⟨m, fun j => ?_⟩
    have heq := eq_count_restrict_of_mem_bSimple hs
    rw [heq]
    refine P.count_restrict_apply_le_one (((P.measurableSet_cell 0 i).union
      (P.measurableSet_cell 0 i')).inter (hφ (P'.measurableSet_cell m j))) ?_
    intro x hx y hy
    have hxF : x ∈ atoms ν ∩ (P.cell 0 i ∪ P.cell 0 i') := ⟨hx.2, hx.1.1⟩
    have hyF : y ∈ atoms ν ∩ (P.cell 0 i ∪ P.cell 0 i') := ⟨hy.2, hy.1.1⟩
    have hxj : P'.idx m (φ x) = j := hx.1.2
    have hyj : P'.idx m (φ y) = j := hy.1.2
    exact hinj hx.2 hy.2 (hm (φ x) ⟨x, hxF, rfl⟩ (φ y) ⟨y, hyF, rfl⟩ (by rw [hxj, hyj]))

end SepPartSeq

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- Simplicity (e): almost surely distinct atoms have distinct `φ`-values. -/
theorem ae_mem_bProj (h : IsPoissonPointProcess N μ P) (D : SepPartSeq S) (hD : D.IsDissecting μ)
    (hdiff : ∀ x, μ {x} = 0) (D' : SepPartSeq T) {φ : S → T} (hφ : Measurable φ)
    (hnull : ∀ c, μ (φ ⁻¹' {c}) = 0) : ∀ᵐ ω ∂P, N ω ∈ D.bProj D' φ := by
  have hall : ∀ p : ℕ × ℕ, ∀ᵐ ω ∂P, ∃ m, ∀ j : ℕ,
      N ω ((D.cell 0 p.1 ∪ D.cell 0 p.2) ∩ φ ⁻¹' D'.cell m j) ≤ 1 := by
    intro p
    have hA : MeasurableSet (D.cell 0 p.1 ∪ D.cell 0 p.2) :=
      (D.measurableSet_cell 0 p.1).union (D.measurableSet_cell 0 p.2)
    have hμA : μ (D.cell 0 p.1 ∪ D.cell 0 p.2) < ∞ :=
      lt_of_le_of_lt (measure_union_le _ _) (ENNReal.add_lt_top.2 ⟨hD _, hD _⟩)
    refine h.ae_exists_level_le_one (idx := fun m x => D'.idx m (φ x)) hA hμA
      (fun m => (D'.measurable_idx m).comp hφ) (fun m x y hxy => D'.refine m _ _ hxy) ?_
    intro x _
    refine measure_mono_null ?_ (hnull (φ x))
    intro y hy
    have hy' : y ∈ ⋂ m, (fun x => D'.idx m (φ x)) ⁻¹' {D'.idx m (φ x)} := hy.2
    have : φ y ∈ ⋂ m, D'.cellOf m (φ x) := Set.mem_iInter.2 fun m => Set.mem_iInter.1 hy' m
    rw [D'.iInter_cellOf] at this
    exact this
  filter_upwards [h.ae_mem_bSimple D hD hdiff, ae_all_iff.2 hall] with ω h1 h2
  exact ⟨h1, fun i i' => h2 (i, i')⟩

end IsPoissonPointProcess

end ElboimSly
