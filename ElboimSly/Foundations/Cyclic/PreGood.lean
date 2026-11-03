/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.Good
public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSpace
public import ElboimSly.Frozen.Defs.EdgeInstCountable
public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSingletonClass
public import ElboimSly.Foundations.PPP.SimpleSet
public import ElboimSly.Foundations.PPP.SimpleSet2
public import ElboimSly.Foundations.PPP.Simple
public import ElboimSly.Foundations.PPP.DissectingExamples
import Mathlib

/-!
# Good configurations without (G3): the set `PreGood`

Measurability, Step 0 (the sets `𝔐_int`, `𝔐_s`, `𝔐_φ` of simple counting measures form a measurable set).

`PreGood` is the set of measures `ν` on `S_β` that are simple counting measures
(`bSimple` for the dissecting system `ringSeq`), satisfy (G1), and have no two atoms with the same
second coordinate. It is measurable (`measurableSet_preGood`), contains `Good`
(`Good.preGood`), and on it atoms are exactly ring times with mass one.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The dissecting system of `S_β`. -/
noncomputable abbrev ringP (d : ℕ) (β : ℝ) [Fact (0 < β)] : SepPartSeq (RingSpace d β) :=
  ringSeq (Edge d) β

/-- Good configurations without (G3). -/
def PreGood (d : ℕ) (β : ℝ) [Fact (0 < β)] : Set (Measure (RingSpace d β)) :=
  {ν | ν ∈ (ringP d β).bSimple ∧ (∀ e : Edge d, ν ({e} ×ˢ univ) < ⊤) ∧
    InjOn Prod.snd (SepPartSeq.atoms ν)}

theorem good_mem_bInt (hν : Good ν) : ν ∈ (ringP d β).bInt := by
  intro m i
  by_cases hne : ((ringP d β).cell m i).Nonempty
  · obtain ⟨⟨e, θ⟩, hx⟩ := hne
    have hi : i = Nat.pair (encE (Edge d) e) ((circleSeq β).idx m θ) := hx.symm
    have hc : (ringP d β).cell m i = {e} ×ˢ (circleSeq β).cell m ((circleSeq β).idx m θ) := by
      rw [hi]; exact SepPartSeq.prodCount_cell _ _ _ _
    have hlt : ν ((ringP d β).cell m i) < ⊤ :=
      lt_of_le_of_lt (measure_mono (by rw [hc]; exact prod_mono subset_rfl (subset_univ _)))
        (hν.2.1 e)
    rcases hν.1 _ ((ringP d β).measurableSet_cell m i) with h | h
    · exact absurd h hlt.ne
    · exact h
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    exact ⟨0, by simp⟩

theorem finite_atoms_of_le_one (hb : ν ∈ (ringP d β).bInt) (hs : ∀ x, ν {x} ≤ 1) (i : ℕ) :
    (SepPartSeq.atoms ν ∩ (ringP d β).cell 0 i).Finite := by
  have := (ringP d β).measurableSingletonClass
  by_contra hinf
  obtain ⟨n, hn⟩ := hb 0 i
  obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
  have h1 : ν (F : Set (RingSpace d β)) = F.card := by
    rw [SepPartSeq.measure_finset_eq_sum]
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
    · simp
    · intro x hx
      have hxa : x ∈ SepPartSeq.atoms ν := (hFsub hx).1
      rcases SepPartSeq.singleton_eq_zero_or_one_le hb x with h | h
      · exact absurd h hxa
      · exact le_antisymm (hs x) h
  have h2 : ν (F : Set (RingSpace d β)) ≤ ν ((ringP d β).cell 0 i) :=
    measure_mono fun x hx => (hFsub hx).2
  rw [h1, hFcard, hn] at h2
  have : n + 1 ≤ n := by exact_mod_cast h2
  omega

theorem good_mem_bSimple (hν : Good ν) : ν ∈ (ringP d β).bSimple := by
  have := (ringP d β).measurableSingletonClass
  have hb := good_mem_bInt hν
  have hs : ∀ x, ν {x} ≤ 1 := fun x => hν.2.2.1.1 x.1 x.2
  refine ⟨hb, fun i => ?_⟩
  have hF := finite_atoms_of_le_one hb hs i
  obtain ⟨m, hm⟩ := SepPartSeq.exists_separating_level (ringP d β) hF
  refine ⟨m, fun j => ?_⟩
  set B := (ringP d β).cell 0 i ∩ (ringP d β).cell m j with hB
  have hnull := SepPartSeq.measure_cell_diff_atoms hb i
  have hsub : B ⊆ (B ∩ SepPartSeq.atoms ν) ∪ ((ringP d β).cell 0 i \ SepPartSeq.atoms ν) := by
    intro x hx
    by_cases hxa : x ∈ SepPartSeq.atoms ν
    · exact Or.inl ⟨hx, hxa⟩
    · exact Or.inr ⟨hx.1, hxa⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, add_zero]
  by_cases hne : (B ∩ SepPartSeq.atoms ν).Nonempty
  · obtain ⟨x, hxB, hxa⟩ := hne
    have : B ∩ SepPartSeq.atoms ν ⊆ {x} := by
      rintro y ⟨hyB, hya⟩
      exact hm y ⟨hya, hyB.1⟩ x ⟨hxa, hxB.1⟩ (by
        have a : (ringP d β).idx m y = j := hyB.2
        have b : (ringP d β).idx m x = j := hxB.2
        rw [a, b])
    exact (measure_mono this).trans (hs x)
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp

/-- Atoms of a simple measure are ring times of mass one: if `ν B ≠ 0` there is an atom in `B`. -/
theorem exists_atom_of_mem_bSimple (hν : ν ∈ (ringP d β).bSimple) {B : Set (RingSpace d β)}
    (hB : MeasurableSet B) (h : ν B ≠ 0) : ∃ x ∈ B, 1 ≤ ν {x} := by
  have := (SepPartSeq.structure_of_mem_bSimple hν).2.2.2 B hB
  rw [this] at h
  have hne : (B ∩ SepPartSeq.atoms ν).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty.1 hc] at h
    simp at h
  obtain ⟨x, hxB, hxa⟩ := hne
  refine ⟨x, hxB, ?_⟩
  rcases SepPartSeq.singleton_eq_zero_or_one hν x with h0 | h1
  · exact absurd h0 hxa
  · exact h1.ge

theorem good_preGood (hν : Good ν) : ν ∈ PreGood d β := by
  refine ⟨good_mem_bSimple hν, hν.2.1, fun x hx y hy hxy => ?_⟩
  by_contra hne
  have hef : x.1 ≠ y.1 := fun h => hne (Prod.ext h hxy)
  have h1 : y.2 ∈ ringSet ν x.1 := by
    show 1 ≤ ν {(x.1, y.2)}
    rw [show (x.1, y.2) = x from Prod.ext rfl hxy.symm]
    rcases SepPartSeq.singleton_eq_zero_or_one (good_mem_bSimple hν) x with h | h
    · exact absurd h hx
    · exact h.ge
  have h2 : y.2 ∈ ringSet ν y.1 := by
    show 1 ≤ ν {(y.1, y.2)}
    rcases SepPartSeq.singleton_eq_zero_or_one (good_mem_bSimple hν) y with h | h
    · exact absurd h hy
    · exact h.ge
  exact Set.disjoint_left.mp (hν.2.2.1.2 _ _ hef) h1 h2

theorem measurableSet_preGood : MeasurableSet (PreGood d β) := by
  have h1 := (ringP d β).measurableSet_bProj (circleSeq β) (φ := Prod.snd) measurable_snd
  have h2 : MeasurableSet {ν : Measure (RingSpace d β) | ∀ e : Edge d, ν ({e} ×ˢ univ) < ⊤} := by
    have : {ν : Measure (RingSpace d β) | ∀ e : Edge d, ν ({e} ×ˢ univ) < ⊤} =
        ⋂ e : Edge d, (fun ν : Measure (RingSpace d β) => ν ({e} ×ˢ univ)) ⁻¹' Iio ⊤ := by
      ext ν; simp
    rw [this]
    exact MeasurableSet.iInter fun e =>
      Measure.measurable_coe ((measurableSet_singleton e).prod MeasurableSet.univ) measurableSet_Iio
  have : PreGood d β = (ringP d β).bProj (circleSeq β) Prod.snd ∩
      {ν | ∀ e : Edge d, ν ({e} ×ˢ univ) < ⊤} := by
    ext ν
    simp only [PreGood, mem_ofPred_eq, mem_inter_iff]
    rw [SepPartSeq.mem_bProj_iff _ _ measurable_snd]
    tauto
  rw [this]
  exact h1.inter h2

/-- Weak regularity of a configuration: nonzero mass on a measurable set forces an atom of mass
at least one inside it, and every edge has finitely many ring classes. Holds on `PreGood`. -/
def Nice (ν : Measure (RingSpace d β)) : Prop :=
  (∀ B : Set (RingSpace d β), MeasurableSet B → ν B ≠ 0 → ∃ x ∈ B, 1 ≤ ν {x}) ∧
    ∀ e : Edge d, (ringSet ν e).Finite

/-- The set of nice configurations. -/
def NiceSet (d : ℕ) (β : ℝ) [Fact (0 < β)] : Set (Measure (RingSpace d β)) := {ν | Nice ν}

theorem ringSet_finite_of_g1 (hν : ν ∈ PreGood d β) (e : Edge d) : (ringSet ν e).Finite := by
  have hfin : ν ({e} ×ˢ Set.univ) < ⊤ := hν.2.1 e
  exact Measure.finite_const_le_meas_of_disjoint_iUnion ν (ε := 1)
    (ι := AddCircle β) (As := fun θ => {((e, θ) : RingSpace d β)}) zero_lt_one
    (fun θ => measurableSet_singleton _)
    (fun θ θ' h => by
      simp only [Function.onFun, Set.disjoint_singleton]
      intro h'; exact h (by simpa using h'))
    (ne_of_lt (lt_of_le_of_lt (measure_mono (fun p hp => by
      obtain ⟨θ, rfl⟩ := Set.mem_iUnion.mp hp
      exact ⟨rfl, Set.mem_univ _⟩)) hfin))

theorem preGood_nice (hν : ν ∈ PreGood d β) : Nice ν :=
  ⟨fun _ hB h => exists_atom_of_mem_bSimple hν.1 hB h, ringSet_finite_of_g1 hν⟩

theorem good_nice (hν : Good ν) : Nice ν := preGood_nice (good_preGood hν)

end ElboimSly.Cyclic

end
