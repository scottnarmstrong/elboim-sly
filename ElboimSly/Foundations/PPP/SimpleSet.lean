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
# Simple counting measures

Simple counting measures form a measurable set (a), (b) ((i) ⇒ (iii) in the simple case), (c).

For a separating partition sequence `P`:

* `bInt P`: measures with `ν(C) ∈ ℕ` for all cells (`𝔐_int`);
* `bSimple P`: those that are in addition eventually at most one point per level-`0` cell
  (`𝔐_s`);
* `eq_count_restrict_of_mem_bSimple`: every `ν ∈ bSimple P` is `∑_{x ∈ Λ} δ_x`, i.e. the counting
  measure restricted to its set of atoms `Λ = {x | ν {x} ≠ 0}`, and `Λ ∩ Q` is finite for every
  level-`0` cell `Q`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

namespace SepPartSeq

variable (P : SepPartSeq S)

/-- `𝔐_int`: `ν(C) ∈ ℕ` for every cell `C` of every level. -/
def bInt : Set (Measure S) := {ν | ∀ m i, ∃ n : ℕ, ν (P.cell m i) = n}

/-- `𝔐_s`: integer valued and, for each level-`0` cell, at most one atom per cell at some
level. -/
def bSimple : Set (Measure S) :=
  P.bInt ∩ {ν | ∀ i, ∃ m, ∀ j, ν (P.cell 0 i ∩ P.cell m j) ≤ 1}

/-- The set of atoms `Λ(ν) = {x | ν {x} ≠ 0}`. -/
def atoms (ν : Measure S) : Set S := {x | ν {x} ≠ 0}

/-- Simple counting measures form a measurable set (a). -/
theorem measurableSet_bInt : MeasurableSet P.bInt := by
  have : P.bInt = ⋂ m, ⋂ i, (fun ν : Measure S => ν (P.cell m i)) ⁻¹'
      Set.range (Nat.cast : ℕ → ℝ≥0∞) := by
    ext ν; simp [bInt, eq_comm]
  rw [this]
  exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun i =>
    Measure.measurable_coe (P.measurableSet_cell m i) (Set.countable_range _).measurableSet

/-- Simple counting measures form a measurable set (a). -/
theorem measurableSet_bSimple : MeasurableSet P.bSimple := by
  refine P.measurableSet_bInt.inter ?_
  have : {ν : Measure S | ∀ i, ∃ m, ∀ j, ν (P.cell 0 i ∩ P.cell m j) ≤ 1} =
      ⋂ i, ⋃ m, ⋂ j, (fun ν : Measure S => ν (P.cell 0 i ∩ P.cell m j)) ⁻¹' Set.Iic 1 := by
    ext ν; simp
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iUnion fun m => MeasurableSet.iInter fun j =>
    Measure.measurable_coe ((P.measurableSet_cell 0 i).inter (P.measurableSet_cell m j))
      measurableSet_Iic

theorem measurableSingletonClass (P : SepPartSeq S) : MeasurableSingletonClass S := ⟨P.measurableSet_singleton'⟩

variable {P} {ν : Measure S}

theorem measure_singleton_eq_iInf (hν : ν ∈ P.bInt) (x : S) :
    ν {x} = ⨅ m, ν (P.cellOf m x) := by
  have hfin : ν (P.cellOf 0 x) ≠ ∞ := by
    obtain ⟨n, hn⟩ := hν 0 (P.idx 0 x)
    exact (show ν (P.cell 0 (P.idx 0 x)) = n from hn) ▸ ENNReal.natCast_ne_top n
  rw [← (P.cellOf_antitone x).measure_iInter (fun m => (P.measurableSet_cellOf m x).nullMeasurableSet)
    ⟨0, hfin⟩, P.iInter_cellOf x]

theorem singleton_eq_zero_or_one_le (hν : ν ∈ P.bInt) (x : S) : ν {x} = 0 ∨ 1 ≤ ν {x} := by
  by_cases h : ∃ m, ν (P.cellOf m x) = 0
  · left
    obtain ⟨m, hm⟩ := h
    exact le_antisymm (hm ▸ measure_mono (fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]; exact P.mem_cellOf_self m x)) bot_le
  · right
    push Not at h
    rw [measure_singleton_eq_iInf hν]
    refine le_iInf fun m => ?_
    obtain ⟨n, hn⟩ := hν m (P.idx m x)
    have hn' : ν (P.cellOf m x) = n := hn
    rw [hn']
    have : n ≠ 0 := fun h0 => h m (by simp [hn', h0])
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this

theorem singleton_le_one (hν : ν ∈ P.bSimple) (x : S) : ν {x} ≤ 1 := by
  obtain ⟨m, hm⟩ := hν.2 (P.idx 0 x)
  refine le_trans (measure_mono ?_) (hm (P.idx m x))
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact ⟨rfl, rfl⟩

theorem singleton_eq_zero_or_one (hν : ν ∈ P.bSimple) (x : S) : ν {x} = 0 ∨ ν {x} = 1 := by
  rcases singleton_eq_zero_or_one_le hν.1 x with h | h
  · exact Or.inl h
  · exact Or.inr (le_antisymm (singleton_le_one hν x) h)

theorem measure_finset_eq_sum [MeasurableSingletonClass S] (ν : Measure S) (F : Finset S) :
    ν (F : Set S) = ∑ x ∈ F, ν {x} := by
  rw [← sum_measure_singleton]

theorem finite_atoms_inter (hν : ν ∈ P.bSimple) (i : ℕ) : (atoms ν ∩ P.cell 0 i).Finite := by
  have := P.measurableSingletonClass
  by_contra hinf
  obtain ⟨n, hn⟩ := hν.1 0 i
  obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
  have h1 : ν (F : Set S) = F.card := by
    rw [measure_finset_eq_sum]
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
    · simp
    · intro x hx
      have : x ∈ atoms ν := (hFsub hx).1
      rcases singleton_eq_zero_or_one hν x with h | h
      · exact absurd h this
      · exact h
  have h2 : ν (F : Set S) ≤ ν (P.cell 0 i) :=
    measure_mono fun x hx => (hFsub hx).2
  rw [h1, hFcard, hn] at h2
  have : n + 1 ≤ n := by exact_mod_cast h2
  omega

theorem measure_cell_diff_atoms (hν : ν ∈ P.bInt) (i : ℕ) :
    ν (P.cell 0 i \ atoms ν) = 0 := by
  have hsub : P.cell 0 i \ atoms ν ⊆ ⋃ p ∈ {p : ℕ × ℕ | ν (P.cell p.1 p.2) = 0}, P.cell p.1 p.2 := by
    intro x hx
    have hx0 : ν {x} = 0 := by simpa [atoms] using hx.2
    have hex : ∃ m, ν (P.cellOf m x) = 0 := by
      by_contra h
      push Not at h
      have : 1 ≤ ν {x} := by
        rw [measure_singleton_eq_iInf hν]
        refine le_iInf fun m => ?_
        obtain ⟨n, hn⟩ := hν m (P.idx m x)
        have hn' : ν (P.cellOf m x) = n := hn
        rw [hn']
        have : n ≠ 0 := fun h0 => h m (by simp [hn', h0])
        exact_mod_cast Nat.one_le_iff_ne_zero.2 this
      rw [hx0] at this
      simp at this
    obtain ⟨m, hm⟩ := hex
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨(m, P.idx m x), hm, rfl⟩
  refine measure_mono_null hsub ?_
  rw [measure_biUnion_null_iff (Set.to_countable _)]
  intro p hp
  exact hp

/-- Simple counting measures form a measurable set (b), (c): a simple counting measure is the counting measure
restricted to its atoms. -/
theorem eq_count_restrict_of_mem_bSimple (hν : ν ∈ P.bSimple) :
    ν = Measure.count.restrict (atoms ν) := by
  have := P.measurableSingletonClass
  have hfin : ∀ i, MeasurableSet (atoms ν ∩ P.cell 0 i) := fun i =>
    (finite_atoms_inter hν i).measurableSet
  have hatoms : MeasurableSet (atoms ν) := by
    have : atoms ν = ⋃ i, atoms ν ∩ P.cell 0 i := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨fun h => ⟨P.idx 0 x, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
    rw [this]
    exact MeasurableSet.iUnion hfin
  ext A hA
  have hcov : A = ⋃ i, A ∩ P.cell 0 i := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨P.idx 0 x, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun i => A ∩ P.cell 0 i) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hx hx' => hij ?_
    have h1 : P.idx 0 x = i := hx.2
    have h2 : P.idx 0 x = j := hx'.2
    omega
  rw [Measure.restrict_apply hA]
  have hcov2 : A ∩ atoms ν = ⋃ i, (A ∩ atoms ν) ∩ P.cell 0 i := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨P.idx 0 x, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hdisj2 : Pairwise (Function.onFun Disjoint fun i => (A ∩ atoms ν) ∩ P.cell 0 i) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hx hx' => hij ?_
    have h1 : P.idx 0 x = i := hx.2
    have h2 : P.idx 0 x = j := hx'.2
    omega
  conv_lhs => rw [hcov]
  conv_rhs => rw [hcov2]
  rw [measure_iUnion hdisj fun i => hA.inter (P.measurableSet_cell 0 i),
    measure_iUnion hdisj2 fun i => (hA.inter hatoms).inter (P.measurableSet_cell 0 i)]
  refine tsum_congr fun i => ?_
  have hF : ((A ∩ atoms ν) ∩ P.cell 0 i).Finite :=
    (finite_atoms_inter hν i).subset fun x hx => ⟨hx.1.2, hx.2⟩
  have hnull := measure_cell_diff_atoms hν.1 i
  have e : (A ∩ P.cell 0 i) \ (P.cell 0 i \ atoms ν) = (A ∩ atoms ν) ∩ P.cell 0 i := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff, not_and, not_not]
    tauto
  have h1 : ν (A ∩ P.cell 0 i) = ν ((A ∩ atoms ν) ∩ P.cell 0 i) := by
    rw [← e, measure_sdiff_null hnull]
  rw [h1, Measure.count_apply_finite' hF hF.measurableSet]
  have h2 : ν (((A ∩ atoms ν) ∩ P.cell 0 i : Set S)) = ∑ x ∈ hF.toFinset, ν {x} := by
    rw [← measure_finset_eq_sum]; simp
  rw [h2, Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
  · simp
  · intro x hx
    have hxa : x ∈ atoms ν := (Set.Finite.mem_toFinset hF |>.1 hx).1.2
    rcases singleton_eq_zero_or_one hν x with h | h
    · exact absurd h hxa
    · exact h

end SepPartSeq

end ElboimSly
