/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.Section
public import ElboimSly.Foundations.PPP.Operations
public import ElboimSly.Foundations.PPP.ExistenceExamples
public import ElboimSly.Foundations.PPP.Invariance
public import ElboimSly.Foundations.Interchange.LatticeGroup
public import ElboimSly.Foundations.Interchange.SymmCov
public import ElboimSly.Foundations.Interchange.SymmG3
public import ElboimSly.Foundations.Interchange.TrajProps
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import ElboimSly.Foundations.Cyclic.CycEvents
public import Mathlib

/-!
# ES22 Lemma 2.1, Step 1: the recentring maps `φ_z`

ES22 Lemma 2.1, Step 1. For `z = (x, a)` let `φ_z(e, θ) = (e - x, θ - [a])`
(`hitPhi`). Each `φ_z` preserves `μ_β`, and `(z, ν) ↦ (φ_z)_* τ(ν)` is measurable
(`measurable_hitShift`; `τ` makes the measures locally finite, measurability of sections).
For a good configuration `ν`, `W^{(φ_z)_* ν}_{0,0}(s) = W^ν_{x,a}(s) - x` (`cycWalk_map_hitPhi`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `φ_{(x,a)}(e, θ) = (e - x, θ - [a])`. -/
@[irreducible] noncomputable def hitPhi (x : Fin d → ℤ) (a : ℝ) : RingSpace d β → RingSpace d β :=
  Prod.map (edgeEquiv (LatticeAut.translate (-x))) (· + (((-a : ℝ)) : AddCircle β))

theorem measurable_hitPhi_fixed (x : Fin d → ℤ) :
    Measurable fun p : ℝ × RingSpace d β => hitPhi (β := β) x p.1 p.2 := by
  unfold hitPhi
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_from_top (f := edgeEquiv (LatticeAut.translate (-x)))).comp
      (measurable_fst.comp measurable_snd)
  · exact (measurable_snd.comp measurable_snd).add
      ((AddCircle.measurable_mk'.comp measurable_fst.neg))

theorem measurable_hitPhi :
    Measurable fun p : ((Fin d → ℤ) × ℝ) × RingSpace d β => hitPhi (β := β) p.1.1 p.1.2 p.2 := by
  have h : Measurable fun q : (ℝ × RingSpace d β) × (Fin d → ℤ) =>
      hitPhi (β := β) q.2 q.1.1 q.1.2 :=
    measurable_from_prod_countable_left fun x => measurable_hitPhi_fixed x
  have hg : Measurable fun p : ((Fin d → ℤ) × ℝ) × RingSpace d β =>
      ((p.1.2, p.2), p.1.1) :=
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_fst.comp measurable_fst)
  exact Measurable.comp (g := fun q : (ℝ × RingSpace d β) × (Fin d → ℤ) =>
    hitPhi (β := β) q.2 q.1.1 q.1.2) h hg

theorem measurable_hitPhi_at (x : Fin d → ℤ) (a : ℝ) :
    Measurable (hitPhi (β := β) x a) :=
  Measurable.comp (g := fun p : ((Fin d → ℤ) × ℝ) × RingSpace d β =>
    hitPhi (β := β) p.1.1 p.1.2 p.2) (measurable_hitPhi (d := d) (β := β))
    (measurable_prodMk_left (x := (x, a)))

theorem map_hitPhi (x : Fin d → ℤ) (a : ℝ) :
    (ringIntensity d β).map (hitPhi x a) = ringIntensity d β :=
  by unfold hitPhi; exact map_ringIntensity_translate d β _ _

/-- `(φ_z)_* τ(ν)`. -/
noncomputable def hitShift (z : (Fin d → ℤ) × ℝ) (ν : Measure (RingSpace d β)) :
    Measure (RingSpace d β) :=
  (tau (ringIntensity d β) ν).map (hitPhi z.1 z.2)

theorem measurable_hitShift :
    Measurable fun p : ((Fin d → ℤ) × ℝ) × Measure (RingSpace d β) => hitShift p.1 p.2 := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have : (fun p : ((Fin d → ℤ) × ℝ) × Measure (RingSpace d β) => hitShift p.1 p.2 B) =
      fun p => tau (ringIntensity d β) p.2 (Prod.mk p.1 ⁻¹'
        {q : ((Fin d → ℤ) × ℝ) × RingSpace d β | hitPhi q.1.1 q.1.2 q.2 ∈ B}) := by
    funext p
    unfold hitShift
    rw [Measure.map_apply (measurable_hitPhi_at p.1.1 p.1.2) hB]
    rfl
  rw [this]
  exact measurable_tau_section (ringIntensity d β) (measurable_hitPhi hB)

end ElboimSly.Cyclic

end
