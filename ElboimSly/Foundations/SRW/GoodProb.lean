/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Jumps
public import ElboimSly.Foundations.PPP.Finite
public import ElboimSly.Foundations.PPP.PoissonFacts
public import ElboimSly.Foundations.PPP.Law
public import Mathlib

/-!
# The good event is measurable and has probability one

Good event and path properties (measurability and `P(G) = 1`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

section Intensity

variable {d : ℕ}

theorem Ioc_inter_Ioi {a b : ℝ} (ha : 0 ≤ a) : Ioc a b ∩ Ioi 0 = Ioc a b :=
  inter_eq_left.2 (fun x hx => (lt_of_le_of_lt ha hx.1 : (0 : ℝ) < x))

theorem clock_single_Ioc (v : Dir d) {a b : ℝ} (ha : 0 ≤ a) :
    clockIntensity (Dir d) (({v} : Set (Dir d)) ×ˢ Ioc a b) = ENNReal.ofReal (b - a) := by
  unfold clockIntensity
  rw [Measure.prod_prod, Measure.count_singleton, one_mul,
    Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioi ha, Real.volume_Ioc]

theorem clock_univ_Ioc {a b : ℝ} (ha : 0 ≤ a) :
    clockIntensity (Dir d) (univ ×ˢ Ioc a b) =
      (Fintype.card (Dir d) : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  unfold clockIntensity
  rw [Measure.prod_prod, Measure.count_univ, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioi ha, Real.volume_Ioc]
  simp [ENat.card_eq_coe_fintype_card]

end Intensity

section Meas

variable {d : ℕ}

theorem measurable_cnt (v : Dir d) (t : ℝ) : Measurable fun ν : Measure (Dir d × ℝ) => cnt ν v t :=
  Measure.measurable_coe (measurableSet_rect v _ measurableSet_Ioc)

theorem measurable_tot (U : Set ℝ) (hU : MeasurableSet U) :
    Measurable fun ν : Measure (Dir d × ℝ) => tot ν U :=
  Measure.measurable_coe (MeasurableSet.univ.prod hU)

theorem measurableSet_goodSet (d : ℕ) : MeasurableSet (goodSet d) := by
  unfold goodSet
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun q => MeasurableSet.iInter
      fun _ => ?_
    have : {ν : Measure (Dir d × ℝ) | ∃ n : ℕ, cnt ν v q = n} =
        (fun ν => cnt ν v q) ⁻¹' (range (Nat.cast : ℕ → ℝ≥0∞)) := by
      ext ν; simp [eq_comm]
    rw [this]
    exact measurable_cnt v q ((Set.countable_range _).measurableSet)
  · refine MeasurableSet.iInter fun T => MeasurableSet.iInter fun _ => ?_
    refine MeasurableSet.inter (measurableSet_lt (measurable_tot _ measurableSet_Ioc)
      measurable_const) ?_
    refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (measurable_tot _ measurableSet_Ioc) measurable_const

end Meas

end SRW
end ElboimSly
