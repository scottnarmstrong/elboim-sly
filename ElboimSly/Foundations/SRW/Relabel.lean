/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Symmetry
public import ElboimSly.Foundations.PPP.Restriction
public import Mathlib

/-!
# Restricting and relabelling the driving point process

Coordinates; Independent families (the sub-process construction).

If `f : D → D'` restricts to a bijection from `S ⊆ D` onto `D'`, then
`(N|_{S × ℝ}).map (f × id)` is again a Poisson point process with intensity `clockIntensity D'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

section Count

variable {D D' : Type*} [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D]
  [MeasurableSpace D'] [MeasurableSingletonClass D'] [Countable D']

theorem count_restrict_map {S : Set D} (_hS : MeasurableSet S) {f : D → D'}
    (hinj : Set.InjOn f S) (hsurj : ∀ b, ∃ a ∈ S, f a = b) :
    ((Measure.count : Measure D).restrict S).map f = Measure.count := by
  have hf : Measurable f := measurable_of_countable f
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.map_apply hf (measurableSet_singleton b), Measure.restrict_apply (hf (measurableSet_singleton b))]
  obtain ⟨a, haS, hab⟩ := hsurj b
  have : f ⁻¹' {b} ∩ S = {a} := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact hinj h2 haS (h1.trans hab.symm)
    · rintro rfl; exact ⟨hab, haS⟩
  rw [this, Measure.count_singleton, Measure.count_singleton]

theorem clock_restrict_map {S : Set D} (hS : MeasurableSet S) {f : D → D'}
    (hinj : Set.InjOn f S) (hsurj : ∀ b, ∃ a ∈ S, f a = b) :
    ((clockIntensity D).restrict (S ×ˢ univ)).map (Prod.map f id) = clockIntensity D' := by
  have hf : Measurable f := measurable_of_countable f
  unfold clockIntensity
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    ← Measure.map_prod_map _ _ hf measurable_id, count_restrict_map hS hinj hsurj, Measure.map_id]

end Count

variable {D D' : Type*} [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D]
  [MeasurableSpace D'] [MeasurableSingletonClass D'] [Countable D']
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (D × ℝ)}

/-- Restrict a point process to `S × ℝ` and relabel by `f`. -/
noncomputable def relabel (S : Set D) (f : D → D') (ν : Measure (D × ℝ)) : Measure (D' × ℝ) :=
  (ν.restrict (S ×ˢ univ)).map (Prod.map f id)

theorem relabel_ppp (h : IsPoissonPointProcess N (clockIntensity D) P) {S : Set D}
    (hS : MeasurableSet S) {f : D → D'} (hinj : Set.InjOn f S) (hsurj : ∀ b, ∃ a ∈ S, f a = b) :
    IsPoissonPointProcess (fun ω => relabel S f (N ω)) (clockIntensity D') P := by
  have hf : Measurable f := measurable_of_countable f
  have := (h.restrict (hS.prod MeasurableSet.univ)).map_measure (hf.prodMap (measurable_id : Measurable (id : ℝ → ℝ)))
  rwa [clock_restrict_map hS hinj hsurj] at this

omit [MeasurableSingletonClass D'] [Countable D'] in
theorem measurable_relabel (S : Set D) (hS : MeasurableSet S) (f : D → D') :
    Measurable (relabel (D' := D') S f) :=
  (measurable_map_measure ((measurable_of_countable f).prodMap measurable_id)).comp
    (measurable_restrict_measure (hS.prod MeasurableSet.univ))

end SRW
end ElboimSly
