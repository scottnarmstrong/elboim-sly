/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenBasic
public import ElboimSly.Foundations.SRW.Coincidence
import Mathlib

/-!
# Canonical walks are driving paths, and are coincidence-free almost surely

Well-definedness and measurability of the driven construction (c), and the remark of walk driven by X that every path of the
canonical SRW is a driving path (good event and path properties).
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ}

/-- The unit vectors of `ℤ^d` have `ℓ¹`-size `1`. -/
theorem isUnitStep_vec (v : Dir d) : IsUnitStep v.vec := by
  obtain ⟨i, b⟩ := v
  unfold IsUnitStep Dir.vec
  rw [Finset.sum_eq_single i]
  · cases b <;> simp
  · intro j _ hj; simp [hj]
  · simp

/-- A discontinuity time of the walk path (in `ℝ≥0`) is a jump time in the sense of `SRW.IsJump`. -/
theorem isJump_of_mem_CDisc (ν : Measure (Dir d × ℝ)) {s : ℝ≥0}
    (hs : s ∈ CDisc (fun u : ℝ≥0 => walk d ν (u : ℝ))) : IsJump ν (s : ℝ) := by
  refine ⟨by exact_mod_cast hs.1, fun δ hδ => ?_⟩
  by_contra hcon
  push Not at hcon
  apply hs.2
  have hlt : min δ s > 0 := lt_min hδ (by exact_mod_cast hs.1)
  have hmin : ((min δ s : ℝ).toNNReal : ℝ) = min δ s := Real.coe_toNNReal _ hlt.le
  have hpos : (0 : ℝ≥0) < (min δ s : ℝ).toNNReal := by
    rw [← NNReal.coe_lt_coe, hmin]; simpa using hlt
  have hsub : (s - (min δ s : ℝ).toNNReal) < s := by
    refine tsub_lt_self ?_ hpos
    exact_mod_cast hs.1
  filter_upwards [Ioo_mem_nhdsLT hsub] with u hu
  refine hcon (u : ℝ) ⟨?_, ?_⟩
  · have h1 : (s : ℝ) - min δ s < u := by
      have := hu.1
      rw [← NNReal.coe_lt_coe] at this
      rwa [NNReal.coe_sub (by
        rw [← NNReal.coe_le_coe, hmin]; exact (min_le_right _ _)), hmin] at this
    have h2 : (s : ℝ) - δ ≤ (s : ℝ) - min δ s := by linarith [min_le_left δ (s : ℝ)]
    exact le_of_lt (lt_of_le_of_lt h2 h1)
  · exact_mod_cast hu.2

/-- The walk path of any realisation is a regular path. -/
theorem walkPath_isRegPath (ν : Measure (Dir d × ℝ)) :
    IsRegPath (fun u : ℝ≥0 => walk d ν (u : ℝ)) := by
  refine ⟨fun s => ?_, fun T => ?_⟩
  · obtain ⟨δ, hδ, h⟩ := exists_const_right (ν := ν) (s : ℝ) s.2
    have hs : s < s + δ.toNNReal := lt_add_of_pos_right _ (Real.toNNReal_pos.2 hδ)
    filter_upwards [Ico_mem_nhdsGE hs] with u hu
    apply h
    refine ⟨by exact_mod_cast hu.1, ?_⟩
    have := hu.2
    rw [← NNReal.coe_lt_coe, NNReal.coe_add, Real.coe_toNNReal _ hδ.le] at this
    exact this
  · have hJ := (jumps_finite_card (ν := ν) (T : ℝ)).1
    exact (hJ.preimage NNReal.coe_injective.injOn).subset fun s hs =>
      ⟨⟨by exact_mod_cast hs.1.1, by exact_mod_cast hs.2⟩, isJump_of_mem_CDisc ν hs.1⟩

/-- Every path of the canonical walk is a driving path (good event and path properties). -/
theorem walkPath_isDriving (ν : Measure (Dir d × ℝ)) :
    IsDrivingPath (fun u : ℝ≥0 => walk d ν (u : ℝ)) where
  toIsRegPath := walkPath_isRegPath ν
  zero := by simp [walk_zero]
  unit := by
    intro s hs
    have hreg := walkPath_isRegPath (d := d) ν
    have hev := hreg.eventually_leftVal hs.1
    obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hs.1).1 hev
    have hls : (l : ℝ) < s := by exact_mod_cast hl
    have hδ : (0 : ℝ) < ((s : ℝ) - l) / 2 := by linarith
    have hspos : (0 : ℝ) < s := by exact_mod_cast hs.1
    have hj := jump_mem_dir (ν := ν) (t := (s : ℝ)) hspos
      (L := leftVal (fun u : ℝ≥0 => walk d ν (u : ℝ)) s) hδ (fun u hu => by
        have hl0 : (0 : ℝ) ≤ l := l.2
        have hu0 : 0 ≤ u := by linarith [hu.1]
        have hlu : l < u.toNNReal := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0]; linarith [hu.1]
        have hus : u.toNNReal < s := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0]; exact hu.2
        have := hsub ⟨hlu, hus⟩
        simp only [mem_ofPred_eq, Real.coe_toNNReal _ hu0] at this
        exact this)
    rcases hj with h | ⟨v, h⟩
    · exact absurd h (hreg.mem_CDisc_iff.1 hs).2.symm
    · show IsUnitStep (walk d ν (s : ℝ) - leftVal (fun u : ℝ≥0 => walk d ν (u : ℝ)) s)
      rw [h]; exact isUnitStep_vec v

/-- **Well-definedness and measurability of the driven construction (c)**: for the canonical SRW built from a Poisson point process,
almost surely the path is a coincidence-free driving path. -/
theorem ae_canonical_mem_cycCF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (Dir d × ℝ)} (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (β : ℝ≥0) (hβ : 0 < β) : ∀ᵐ ω ∂P, canonical d N ω ∈ CycCF β := by
  have hβr : (0 : ℝ) < β := by exact_mod_cast hβ
  have h1 := ae_no_jump_pair_mul hN hβr
  have h2 : ∀ᵐ ω ∂P, ∀ k : ℕ, 1 ≤ k → ¬ IsJump (N ω) ((k : ℝ) * β) := by
    rw [ae_all_iff]
    intro k
    by_cases hk : 1 ≤ k
    · have hkpos : (0 : ℝ) < (k : ℝ) * β := by
        have : (0 : ℝ) < k := by exact_mod_cast hk
        positivity
      filter_upwards [ae_not_isJump hN hkpos] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hk
  filter_upwards [h1, h2] with ω hω1 hω2
  refine ⟨walkPath_isDriving (N ω), ?_, ?_⟩
  · intro s hs s' hs' k hk heq
    refine hω1 (s : ℝ) (s' : ℝ) (isJump_of_mem_CDisc _ hs) (isJump_of_mem_CDisc _ hs') k hk ?_
    rw [heq]; push_cast; ring
  · intro k hk hmem
    exact hω2 k hk (by simpa using isJump_of_mem_CDisc _ hmem)

end ElboimSly.Cyclic

end
