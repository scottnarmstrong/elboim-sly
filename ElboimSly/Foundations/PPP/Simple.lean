/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.SimpleSet
public import ElboimSly.Foundations.PPP.NoDouble
public import Mathlib

/-!
# Simplicity of Poisson point processes

Simplicity (a)-(d).

For a dissecting system `D` of `(S, μ)` with `μ` diffuse, a Poisson point process `N` is almost
surely in `D.bSimple` (`ae_mem_bSimple`), and every measure in `D.bSimple` is a locally finite
simple counting measure (`SepPartSeq.structure_of_mem_bSimple`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ElboimSly

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

namespace SepPartSeq

variable {P : SepPartSeq S} {ν : Measure S}

theorem measurableSet_atoms (hν : ν ∈ P.bSimple) : MeasurableSet (atoms ν) := by
  have := P.measurableSingletonClass
  have : atoms ν = ⋃ i, atoms ν ∩ P.cell 0 i := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨P.idx 0 x, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  rw [this]
  exact MeasurableSet.iUnion fun i => (finite_atoms_inter hν i).measurableSet

theorem countable_atoms (hν : ν ∈ P.bSimple) : (atoms ν).Countable := by
  have : atoms ν = ⋃ i, atoms ν ∩ P.cell 0 i := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨P.idx 0 x, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  rw [this]
  exact Set.countable_iUnion fun i => (finite_atoms_inter hν i).countable

/-- Simplicity (a)-(c): the structure of a simple counting measure. -/
theorem structure_of_mem_bSimple (hν : ν ∈ P.bSimple) :
    (∀ x, ν {x} = 0 ∨ ν {x} = 1) ∧ (atoms ν).Countable ∧
      (∀ i, (atoms ν ∩ P.cell 0 i).Finite ∧
        ν (P.cell 0 i) = ((atoms ν ∩ P.cell 0 i).ncard : ℝ≥0∞)) ∧
      (∀ A, MeasurableSet A → ν A = ((A ∩ atoms ν).encard : ℝ≥0∞)) := by
  have := P.measurableSingletonClass
  have heq := eq_count_restrict_of_mem_bSimple hν
  refine ⟨singleton_eq_zero_or_one hν, countable_atoms hν, fun i => ⟨finite_atoms_inter hν i, ?_⟩,
    fun A hA => ?_⟩
  · have hF := finite_atoms_inter hν i
    conv_lhs => rw [heq]
    rw [Measure.restrict_apply (P.measurableSet_cell 0 i), Set.inter_comm,
      Measure.count_apply hF.measurableSet, ← Set.Finite.cast_ncard_eq hF]
    simp
  · conv_lhs => rw [heq]
    rw [Measure.restrict_apply hA, Measure.count_apply (hA.inter (measurableSet_atoms hν))]

end SepPartSeq

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- Simplicity: almost surely `N ∈ 𝔐_s`. -/
theorem ae_mem_bSimple (h : IsPoissonPointProcess N μ P) (D : SepPartSeq S)
    (hD : D.IsDissecting μ) (hdiff : ∀ x, μ {x} = 0) : ∀ᵐ ω ∂P, N ω ∈ D.bSimple := by
  have hint : ∀ᵐ ω ∂P, N ω ∈ D.bInt := by
    have := h.ae_forall_natCast_count (A := fun p : ℕ × ℕ => D.cell p.1 p.2)
      (fun p => D.measurableSet_cell p.1 p.2) fun p => SepPartSeq.IsDissecting.measure_cell_lt_top D hD p.1 p.2
    filter_upwards [this] with ω hω m i using hω (m, i)
  have hlev : ∀ i, ∀ᵐ ω ∂P, ∃ m, ∀ j : ℕ, N ω (D.cell 0 i ∩ D.cell m j) ≤ 1 := by
    intro i
    refine h.ae_exists_level_le_one (D.measurableSet_cell 0 i) (hD i) D.measurable_idx D.refine ?_
    intro x hx
    refine measure_mono_null ?_ (hdiff x)
    intro y hy
    have : y ∈ ⋂ m, D.cellOf m x := hy.2
    rw [D.iInter_cellOf x] at this
    exact this
  filter_upwards [hint, ae_all_iff.2 hlev] with ω h1 h2
  exact ⟨h1, h2⟩

end IsPoissonPointProcess

end ElboimSly
