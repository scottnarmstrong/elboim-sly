/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.GoodAsSimplex
public import ElboimSly.Frozen.Defs.RingIntensity
public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSingletonClass
public import ElboimSly.Frozen.Defs.EdgeInstCountable
public import Mathlib

/-!
# The circle image of the ordered simplex

Configurations are a.s. good (the set `A_v ⊆ S_β^n`).

For `a < p` and `q ≤ a + β` the interval `[p, q]` embeds in the circle. The set `circleSimplex`
consists of the `n`-tuples of circle points whose representatives in `(a, a + β]` form a strictly
increasing tuple in `[p, q]`. Its `β`-circle volume is at most that of the ordered simplex.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The representative of a point of the circle in `(a, a + β]`. -/
noncomputable def circleRep (β : ℝ) [Fact (0 < β)] (a : ℝ) (θ : AddCircle β) : ℝ :=
  (AddCircle.measurableEquivIoc β a θ : ℝ)

theorem measurable_circleRep (a : ℝ) : Measurable (circleRep β a) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc β a).measurable

theorem circleRep_coe {a x : ℝ} (hx : x ∈ Set.Ioc a (a + β)) : circleRep β a (x : AddCircle β) = x :=
  congrArg Subtype.val (AddCircle.equivIoc_coe_eq (p := β) (a := a) hx)

/-- Circle tuples whose representatives form a strictly increasing tuple in `[p, q]`. -/
def circleSimplex (β : ℝ) [Fact (0 < β)] (a : ℝ) (n : ℕ) (p q : ℝ) :
    Set (Fin n → AddCircle β) :=
  {θ | orderedSimplex n p q (fun i => circleRep β a (θ i))}

theorem measurableSet_circleSimplex (a : ℝ) (n : ℕ) (p q : ℝ) :
    MeasurableSet (circleSimplex β a n p q) :=
  (measurableSet_orderedSimplex n p q).preimage
    (measurable_pi_iff.2 fun i => (measurable_circleRep a).comp (measurable_pi_apply i))

theorem volume_circleSimplex_le (a : ℝ) (n : ℕ) (p q : ℝ) :
    Measure.pi (fun _ : Fin n => (volume : Measure (AddCircle β))) (circleSimplex β a n p q) ≤
      volume (orderedSimplex n p q) := by
  have hmp := measurePreserving_pi (fun _ : Fin n => volume.restrict (Set.Ioc a (a + β)))
    (fun _ : Fin n => (volume : Measure (AddCircle β)))
    (f := fun _ (x : ℝ) => (x : AddCircle β)) (fun _ => AddCircle.measurePreserving_mk β a)
  rw [← hmp.measure_preimage (measurableSet_circleSimplex a n p q).nullMeasurableSet,
    ← Measure.restrict_pi_pi (fun _ : Fin n => (volume : Measure ℝ)) (fun _ => Set.Ioc a (a + β)),
    Measure.restrict_apply (hmp.measurable (measurableSet_circleSimplex a n p q))]
  refine measure_mono ?_
  rintro t ⟨ht1, ht2⟩
  have hbox : ∀ i, t i ∈ Set.Ioc a (a + β) := fun i => ht2 i (Set.mem_univ i)
  have : (fun i => circleRep β a ((t i : ℝ) : AddCircle β)) = t :=
    funext fun i => circleRep_coe (hbox i)
  have h := ht1
  simp only [Set.mem_preimage, circleSimplex, Set.mem_ofPred_eq, this] at h
  exact h

end ElboimSly.Interchange
