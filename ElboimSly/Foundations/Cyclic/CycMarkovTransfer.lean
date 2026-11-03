/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMarkovRegion
public import ElboimSly.Foundations.Cyclic.CycMultiStop
public import Mathlib

/-!
# Transfer between `Unit × S_β` and `S_β`

The explored region of the plan `𝒫_W` for `liftU ∘ N` is `{} × ℛ_{(0,T]}(W)`, and the glued
environment `Ñ` of the plan is `liftU` of the glued environment of `S_β`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]

theorem cycRegionAt_markov (N : Ω → Measure (RingSpace d β)) (s : ℝ≥0) (ω : Ω) :
    cycRegionAt (onePlan d β) (cycNgood fun ω => liftU (N ω)) s ω =
      {()} ×ˢ cycRegion β (fun r => markovW N ω r) 0 (s : ℝ) := by
  unfold cycRegionAt
  rw [show cycNgood (fun ω => liftU (N ω)) ω = liftU (markovNgood N ω) from
    (liftU_markovNgood N ω).symm, trunc_envFinal_onePlan, region_inl_one,
    region_markovEntry (good_markovNgood N ω)]
  rfl

theorem cycRegionStop_markov (N : Ω → Measure (RingSpace d β)) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    cycRegionStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T ω =
      {()} ×ˢ markovRegion N T ω := by
  unfold cycRegionStop markovRegion
  cases hh : T ω using WithTop.recTopCoe with
  | top => simp
  | coe t =>
    simp only [WithTop.recTopCoe_coe]
    exact cycRegionAt_markov N t ω

theorem compl_unit_prod (A : Set (RingSpace d β)) :
    ({()} ×ˢ A : Set (Unit × RingSpace d β))ᶜ = {()} ×ˢ Aᶜ := by
  ext x; obtain ⟨⟨⟩, y⟩ := x; simp

theorem measurableSet_markovRegion (N : Ω → Measure (RingSpace d β))
    (T : Ω → WithTop ℝ≥0) (ω : Ω) : MeasurableSet (markovRegion N T ω) := by
  have h : MeasurableSet (cycRegionStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T ω) := by
    unfold cycRegionStop
    cases hh : T ω using WithTop.recTopCoe with
    | top => simp
    | coe t =>
      exact measurableSet_cycRegionAt (onePlan d β) (CycPlan.junk (onePlan d β)) t ω _
  rw [cycRegionStop_markov] at h
  have := h.preimage (measurable_prodMk_left (x := ()))
  convert this using 1
  ext x; simp

theorem tilde_markov (N N' : Ω → Measure (RingSpace d β)) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    tildeMeasure (fun ω => liftU (N ω)) (fun ω => liftU (N' ω))
      (cycRegionStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T) ω =
      liftU (tildeMeasure N N' (markovRegion N T) ω) := by
  unfold tildeMeasure
  rw [cycRegionStop_markov, compl_unit_prod]
  have hadd : ∀ a b : Measure (RingSpace d β), liftU (a + b) = liftU a + liftU b := fun a b =>
    Measure.map_add _ _ measurable_prodMk_left
  rw [hadd, liftU_restrict, liftU_restrict]

end ElboimSly.Cyclic

end
