/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.FixedCounts
public import ElboimSly.Foundations.PPP.Indep
public import Mathlib

/-!
# The one-dimensional law at a fixed time

One-dimensional law at a fixed time; Coordinates (fixed-time form) and local upper bound without constant
for the canonical walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

theorem walk_apply {d : ℕ} {ν : Measure (Dir d × ℝ)} (hν : ν ∈ goodSet d) (t : ℝ) (i : Fin d) :
    walk d ν t i = (natOf (cnt ν (i, true) t) : ℤ) - natOf (cnt ν (i, false) t) := by
  classical
  rw [walk_of_good hν, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [Dir.vec]; ring
  · intro j _ hj
    simp [Dir.vec, Pi.single_eq_of_ne hj.symm]
  · simp

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

/-- The signed count `N_{(i,+)}(t) - N_{(i,-)}(t)`. -/
noncomputable def coordY (N : Ω → Measure (Dir d × ℝ)) (t : ℝ) (i : Fin d) (ω : Ω) : ℤ :=
  (cntN N t (i, true) ω : ℤ) - cntN N t (i, false) ω

theorem walk_ae_eq (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (t : ℝ) :
    ∀ᵐ ω ∂P, ∀ i, walk d (N ω) t i = coordY N t i ω := by
  filter_upwards [ae_good hN] with ω hω i using walk_apply hω t i

theorem measurable_coordY (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (t : ℝ)
    (i : Fin d) : Measurable (coordY N t i) := by
  unfold coordY
  exact (measurable_from_top.comp (measurable_cntN hN t (i, true))).sub
    (measurable_from_top.comp (measurable_cntN hN t (i, false)))

/-- The coordinates at a fixed time are independent. -/
theorem iIndepFun_coordY (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (t : ℝ) :
    iIndepFun (fun i : Fin d => coordY N t i) P := by
  have := hN.isProbabilityMeasure
  refine iIndepFun_blocks (X := fun v : Dir d => cntN N t v)
    (fun v => measurable_cntN hN t v) (iIndepFun_cntN hN t)
    (fun i : Fin d => ({(i, true), (i, false)} : Set (Dir d))) ?_ (fun i => ?_)
  · intro a b hab
    refine Set.disjoint_left.2 fun p hp hq => hab ?_
    simp only [mem_insert_iff, mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with h | h <;> simp_all
  · let m : MeasurableSpace Ω := ⨆ j ∈ ({(i, true), (i, false)} : Set (Dir d)),
      MeasurableSpace.comap (cntN N t j) inferInstance
    have h1 : ∀ j ∈ ({(i, true), (i, false)} : Set (Dir d)), Measurable[m] (cntN N t j) := by
      intro j hj
      exact (comap_measurable (cntN N t j)).mono (le_iSup₂ (f := fun j _ =>
        MeasurableSpace.comap (cntN N t j) inferInstance) j hj) le_rfl
    unfold coordY
    exact (measurable_from_top.comp (h1 (i, true) (by simp))).sub
        (measurable_from_top.comp (h1 (i, false) (by simp)))

end SRW
end ElboimSly
