/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Reversal
public import ElboimSly.Foundations.SRW.MarkovIndep
public import ElboimSly.Foundations.SRW.Symmetry
public import Mathlib

/-!
# Time reversal: the reflected point process

Time reversal (proof of (a), the law).

`revProc σ T ν` is the image of `ν` restricted to `D × (0,T)` under `(v,s) ↦ (σ v, T - s)`.
It is a Poisson point process with intensity `clockIntensity` restricted to `D × (0,T]`, for
every permutation `σ` of the directions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)}
  {P : Measure Ω}

/-- The reflection `(v,s) ↦ (σ v, T - s)`. -/
def reflectMap (d : ℕ) (σ : Dir d ≃ Dir d) (T : ℝ) : Dir d × ℝ → Dir d × ℝ :=
  Prod.map σ (fun s => T - s)

theorem measurable_reflectMap (σ : Dir d ≃ Dir d) (T : ℝ) : Measurable (reflectMap d σ T) :=
  (measurable_of_countable σ).prodMap (measurable_const.sub measurable_id)

/-- The reflected restriction of `ν` to `D × (0,T)`. -/
noncomputable def revProc (σ : Dir d ≃ Dir d) (T : ℝ) (ν : Measure (Dir d × ℝ)) :
    Measure (Dir d × ℝ) :=
  (ν.restrict (univ ×ˢ Ioo 0 T)).map (reflectMap d σ T)

theorem clock_restrict_univ_prod (A : Set ℝ) (hA : MeasurableSet A) :
    (clockIntensity (Dir d)).restrict (univ ×ˢ A) =
      (Measure.count : Measure (Dir d)).prod (volume.restrict (A ∩ Ioi 0)) := by
  unfold clockIntensity
  rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict hA]

theorem clock_restrict_Ioo_eq {T : ℝ} :
    (clockIntensity (Dir d)).restrict (univ ×ˢ Ioo 0 T) =
      (clockIntensity (Dir d)).restrict (univ ×ˢ Ioc 0 T) := by
  rw [clock_restrict_univ_prod _ measurableSet_Ioo, clock_restrict_univ_prod _ measurableSet_Ioc]
  have h1 : Ioo 0 T ∩ Ioi 0 = Ioo 0 T := inter_eq_left.2 fun x hx => hx.1
  have h2 : Ioc 0 T ∩ Ioi 0 = Ioc 0 T := inter_eq_left.2 fun x hx => hx.1
  rw [h1, h2, Measure.restrict_congr_set Ioo_ae_eq_Ioc]

theorem clock_restrict_Ioo_map (σ : Dir d ≃ Dir d) (T : ℝ) :
    ((clockIntensity (Dir d)).restrict (univ ×ˢ Ioo 0 T)).map (reflectMap d σ T) =
      (clockIntensity (Dir d)).restrict (univ ×ˢ Ioc 0 T) := by
  rw [← clock_restrict_Ioo_eq, clock_restrict_univ_prod _ measurableSet_Ioo]
  have h1 : Ioo 0 T ∩ Ioi 0 = Ioo 0 T := inter_eq_left.2 fun x hx => hx.1
  rw [h1]
  refine count_prod_map_invariant _ σ (T := fun s => T - s)
    (measurable_const.sub measurable_id) ?_
  have hmp := ((volume : Measure ℝ).measurePreserving_sub_left T).map_eq
  have hpre : (fun s : ℝ => T - s) ⁻¹' Ioo 0 T = Ioo 0 T := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have := Measure.restrict_map (μ := (volume : Measure ℝ)) (f := fun s : ℝ => T - s)
    (measurable_const.sub measurable_id) (measurableSet_Ioo (a := (0 : ℝ)) (b := T))
  rw [hmp, hpre] at this
  exact this.symm

theorem isPPP_revProc (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (σ : Dir d ≃ Dir d) (T : ℝ) :
    IsPoissonPointProcess (fun ω => revProc σ T (N ω))
      ((clockIntensity (Dir d)).restrict (univ ×ˢ Ioc 0 T)) P := by
  have h := (hN.restrict (MeasurableSet.univ.prod (measurableSet_Ioo (a := (0 : ℝ)) (b := T)))).map_measure
    (measurable_reflectMap σ T)
  rwa [clock_restrict_Ioo_map] at h

end SRW
end ElboimSly
