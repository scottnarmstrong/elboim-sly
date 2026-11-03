/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.SrwLaw
public import ElboimSly.Foundations.PPP.Operations
public import ElboimSly.Foundations.PPP.Restriction
public import Mathlib

/-!
# Time shifts of the driving point process

Count calculus (e), independent stationary increments; Markov property at fixed times (a).

`shiftMeasure a ν` keeps the points of `ν` after time `a` and moves them back by `a`.  For a PPP
with intensity `clockIntensity (Dir d)` and `a ≥ 0` the result is again such a PPP, and the
canonical walk of the shifted process is, almost surely, the shifted increment process of `X`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- Translation of the time coordinate by `-a`. -/
def shiftMap (d : ℕ) (a : ℝ) : Dir d × ℝ → Dir d × ℝ := Prod.map id (· - a)

theorem measurable_shiftMap (d : ℕ) (a : ℝ) : Measurable (shiftMap d a) :=
  measurable_id.prodMap (measurable_id.sub_const a)

/-- Keep the points after time `a`, then move them back by `a`. -/
noncomputable def shiftMeasure (d : ℕ) (a : ℝ) (ν : Measure (Dir d × ℝ)) : Measure (Dir d × ℝ) :=
  (ν.restrict (univ ×ˢ Ioi a)).map (shiftMap d a)

theorem clock_shift {a : ℝ} (ha : 0 ≤ a) :
    ((clockIntensity (Dir d)).restrict (univ ×ˢ Ioi a)).map (shiftMap d a) =
      clockIntensity (Dir d) := by
  unfold clockIntensity shiftMap
  have h1 : (volume : Measure ℝ).map (fun x => x - a) = volume := map_sub_right_eq_self _ a
  have h2 := (measurableEmbedding_subRight a).restrict_map (volume : Measure ℝ) (Ioi 0)
  rw [h1] at h2
  have h3 : (volume.restrict (Ioi a)).map (fun x => x - a) = volume.restrict (Ioi 0) := by
    have : (fun x : ℝ => x - a) ⁻¹' Ioi 0 = Ioi a := by ext x; simp
    rw [h2, this]
  rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.2 (Ioi_subset_Ioi ha)]
  have h4 := Measure.map_prod_map (Measure.count : Measure (Dir d)) (volume.restrict (Ioi a))
    (measurable_id) (measurable_id.sub_const a)
  rw [Measure.map_id] at h4
  simp only [id_eq] at h4
  rw [h3] at h4
  exact h4.symm

end SRW
end ElboimSly
