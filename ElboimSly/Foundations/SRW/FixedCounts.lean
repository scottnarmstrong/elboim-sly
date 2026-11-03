/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.GoodAe
public import ElboimSly.Foundations.SRW.PoissonPmf
public import Mathlib

/-!
# Counts at a fixed time

Count calculus (a), one-dimensional law at a fixed time (independent Poisson counts).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

theorem measurable_natOf : Measurable natOf :=
  Nat.measurable_floor.comp ENNReal.measurable_toReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

/-- The natural-number count `N_v(t)`. -/
noncomputable def cntN (N : Ω → Measure (Dir d × ℝ)) (t : ℝ) (v : Dir d) (ω : Ω) : ℕ :=
  natOf (cnt (N ω) v t)

theorem measurable_cntN (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (t : ℝ)
    (v : Dir d) : Measurable (cntN N t v) :=
  measurable_natOf.comp (hN.measurable_count (measurableSet_rect v _ measurableSet_Ioc))

/-- The counts of the disjoint rectangles `{v} × (0,t]` are independent. -/
theorem iIndepFun_cnt (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (t : ℝ) :
    iIndepFun (fun v : Dir d => fun ω => cnt (N ω) v t) P := by
  have := hN.isProbabilityMeasure
  have hA : ∀ v : Dir d, MeasurableSet (({v} : Set (Dir d)) ×ˢ Ioc 0 t) :=
    fun v => measurableSet_rect v _ measurableSet_Ioc
  have hd : Pairwise (Function.onFun Disjoint fun v : Dir d => ({v} : Set (Dir d)) ×ˢ Ioc 0 t) := by
    intro a b hab
    exact Set.disjoint_left.2 fun p hp hq => hab (by
      simp only [mem_prod, mem_singleton_iff] at hp hq; rw [← hp.1, ← hq.1])
  show iIndepFun (fun (v : Dir d) ω => N ω (({v} : Set (Dir d)) ×ˢ Ioc 0 t)) P
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun v => (hN.measurable_count (hA v)).aemeasurable)]
  have := hN.map_counts_fintype hA hd
  refine this.trans ?_
  congr 1
  funext v
  exact (hN.map_count (hA v)).symm

theorem iIndepFun_cntN (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (t : ℝ) :
    iIndepFun (fun v : Dir d => cntN N t v) P :=
  (iIndepFun_cnt hN t).comp (fun _ => natOf) (fun _ => measurable_natOf)

theorem map_cntN (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {t : ℝ} (_ht : 0 ≤ t)
    (v : Dir d) : P.map (cntN N t v) = poissonMeasure t.toNNReal := by
  have hA : MeasurableSet (({v} : Set (Dir d)) ×ˢ Ioc 0 t) :=
    measurableSet_rect v _ measurableSet_Ioc
  have h1 : cntN N t v = natOf ∘ fun ω => N ω (({v} : Set (Dir d)) ×ˢ Ioc 0 t) := rfl
  rw [h1, ← Measure.map_map measurable_natOf (hN.measurable_count hA), hN.map_count hA,
    clock_single_Ioc v le_rfl, sub_zero]
  show Measure.map natOf (extPoissonMeasure ((t.toNNReal : ℝ≥0) : ℝ≥0∞)) = _
  rw [extPoissonMeasure_coe, Measure.map_map measurable_natOf measurable_natCast_ennreal]
  have : natOf ∘ (Nat.cast : ℕ → ℝ≥0∞) = id := by
    funext n; simp [natOf]
  rw [this, Measure.map_id]

end SRW
end ElboimSly
