/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.PppTransport
public import ElboimSly.Foundations.SRW.SrwDef
public import Mathlib

/-!
# The cells `{v} × (l-1, l]` of the base coupling

ES22 (8.3): base coupling with precision n^10 (the partition `S_{(v,l)}`, the masses `λ_{(v,l)}` and the cell
laws `ν_{(v,l)}`), a Poisson point process from cell blocks on any probability space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

variable (d : ℕ)

/-- The index set `𝒦 = D × ℤ` of the cells. -/
abbrev CellIdx : Type := Dir d × ℤ

/-- The cell `S_{(v,l)} = {v} × (l-1, l]`. -/
def cellSet (k : CellIdx d) : Set (Dir d × ℝ) := ({k.1} : Set (Dir d)) ×ˢ Ioc ((k.2 : ℝ) - 1) k.2

/-- The mass `λ_{(v,l)}`: `1` for `l ≥ 1` and `0` otherwise. -/
noncomputable def cellMass (k : CellIdx d) : ℝ≥0 := if 1 ≤ k.2 then 1 else 0

/-- The cell law `ν_{(v,l)}`. -/
noncomputable def cellLaw (k : CellIdx d) : Measure (Dir d × ℝ) :=
  if 1 ≤ k.2 then (Measure.dirac k.1).prod (volume.restrict (Ioc ((k.2 : ℝ) - 1) k.2))
  else Measure.dirac (k.1, 0)

theorem measurableSet_cellSet (k : CellIdx d) : MeasurableSet (cellSet d k) :=
  (measurableSet_singleton _).prod measurableSet_Ioc

theorem pairwise_disjoint_cellSet : Pairwise (Function.onFun Disjoint (cellSet d)) := by
  rintro ⟨v, l⟩ ⟨v', l'⟩ hne
  rw [Function.onFun, Set.disjoint_left]
  rintro ⟨u, x⟩ ⟨hu, hx⟩ ⟨hu', hx'⟩
  simp only [mem_singleton_iff] at hu hu'
  subst hu hu'
  apply hne
  have h1 : (l : ℝ) - 1 < x := hx.1
  have h2 : x ≤ l := hx.2
  have h3 : (l' : ℝ) - 1 < x := hx'.1
  have h4 : x ≤ l' := hx'.2
  have : l = l' := by
    have a : (l : ℝ) < l' + 1 := by linarith
    have b : (l' : ℝ) < l + 1 := by linarith
    have a' : l < l' + 1 := by exact_mod_cast a
    have b' : l' < l + 1 := by exact_mod_cast b
    omega
  rw [this]

theorem iUnion_cellSet : ⋃ k, cellSet d k = univ := by
  refine eq_univ_of_forall fun ⟨v, x⟩ => mem_iUnion.2 ⟨(v, ⌈x⌉), ?_, ?_⟩
  · simp
  · simp only [mem_Ioc]
    exact ⟨Int.ceil_lt_add_one x |> fun h => by linarith, Int.le_ceil x⟩

instance isProbabilityMeasure_cellLaw (k : CellIdx d) : IsProbabilityMeasure (cellLaw d k) := by
  unfold cellLaw
  split_ifs with h
  · have : IsProbabilityMeasure (volume.restrict (Ioc ((k.2 : ℝ) - 1) k.2)) :=
      ⟨by simp⟩
    infer_instance
  · infer_instance

theorem count_restrict_singleton (v : Dir d) :
    (Measure.count : Measure (Dir d)).restrict {v} = Measure.dirac v := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.restrict_apply hs, Measure.dirac_apply' _ hs]
  by_cases h : v ∈ s
  · have : s ∩ {v} = {v} := by simp [h]
    simp [this, h]
  · have : s ∩ {v} = ∅ := by simp [h]
    simp [this, h]

theorem dirac_restrict_singleton (v : Dir d) :
    (Measure.dirac v).restrict {v} = Measure.dirac v := by
  rw [Measure.restrict_eq_self_of_ae_mem]
  exact (ae_dirac_iff (p := fun x => x ∈ ({v} : Set (Dir d))) (measurableSet_singleton v)).2 rfl

theorem cell_restrict (k : CellIdx d) :
    ((cellMass d k : ℝ≥0∞) • cellLaw d k).restrict (cellSet d k) =
      (clockIntensity (Dir d)).restrict (cellSet d k) := by
  unfold cellSet clockIntensity
  by_cases h : 1 ≤ k.2
  · have hl : (0 : ℝ) ≤ (k.2 : ℝ) - 1 := by
      have : (1 : ℝ) ≤ k.2 := by exact_mod_cast h
      linarith
    simp only [cellMass, cellLaw, h, ite_true, ENNReal.coe_one, one_smul]
    have hI : Ioc ((k.2 : ℝ) - 1) k.2 ∩ Ioi 0 = Ioc ((k.2 : ℝ) - 1) k.2 := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi, and_iff_left_iff_imp]
      exact fun hx => by linarith [hx.1]
    rw [← Measure.prod_restrict, ← Measure.prod_restrict, count_restrict_singleton,
      Measure.restrict_restrict measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_self, hI, dirac_restrict_singleton]
  · simp only [cellMass, cellLaw, h, ite_false, ENNReal.coe_zero, zero_smul, Measure.restrict_zero]
    symm
    rw [← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Ioc]
    have hk : (k.2 : ℝ) ≤ 0 := by
      have : k.2 ≤ 0 := by omega
      exact_mod_cast this
    have : Ioc ((k.2 : ℝ) - 1) k.2 ∩ Ioi 0 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ioi, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, h2⟩, h3⟩; linarith
    rw [this]
    simp

end StrongApprox
end ElboimSly
