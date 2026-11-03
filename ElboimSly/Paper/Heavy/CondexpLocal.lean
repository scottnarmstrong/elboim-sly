/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Localizing conditional expectations at stopping times

Localizing conditional expectations at stopping times (supplement to ES22 §6).

For stopping times `S, T` of a filtration (values in `[0, ∞]`) and `Λ = {S = T}`:
`Λ ∈ ℱ_S ∩ ℱ_T`, the traces of `ℱ_S` and `ℱ_T` on `Λ` coincide, and
`E[Y | ℱ_S] = E[Y | ℱ_T]` a.e. on `Λ`.

The conditional-expectation statement is proved for every `Y` (it is trivial for non-integrable
`Y`, where both sides are `0`), so the integrability hypothesis of the written proof is not needed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ElboimSly.Paper

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {f : Filtration ℝ≥0 m0}
  {S T : Ω → WithTop ℝ≥0}

/-- `Λ = {S = T}` is measurable for both `ℱ_S` and `ℱ_T`. -/
theorem measurableSet_eq_stopping_time_both (hS : IsStoppingTime f S) (hT : IsStoppingTime f T) :
    MeasurableSet[hS.measurableSpace] {ω | S ω = T ω} ∧
      MeasurableSet[hT.measurableSpace] {ω | S ω = T ω} := by
  refine ⟨hS.measurableSet_eq_stopping_time hT, ?_⟩
  have := hT.measurableSet_eq_stopping_time hS
  simpa only [eq_comm] using this

/-- The trace of `ℱ_S` on `{S = T}` is contained in the trace of `ℱ_T`. -/
theorem measurableSet_inter_eq_of_stopping_time (hS : IsStoppingTime f S)
    (hT : IsStoppingTime f T) {A : Set Ω} (hA : MeasurableSet[hS.measurableSpace] A) :
    MeasurableSet[hT.measurableSpace] (A ∩ {ω | S ω = T ω}) := by
  have h1 : MeasurableSet[(hS.min hT).measurableSpace] (A ∩ {ω | S ω ≤ T ω}) :=
    hS.measurableSet_inter_le hT A hA
  have h2 : MeasurableSet[hT.measurableSpace] (A ∩ {ω | S ω ≤ T ω}) :=
    ((hS.measurableSet_min_iff hT _).1 h1).2
  have h3 : MeasurableSet[hT.measurableSpace] {ω | T ω ≤ S ω} :=
    hT.measurableSet_le_stopping_time hS
  have : A ∩ {ω | S ω = T ω} = (A ∩ {ω | S ω ≤ T ω}) ∩ {ω | T ω ≤ S ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, le_antisymm_iff]
    tauto
  rw [this]
  exact h2.inter h3

theorem measurableSet_eq_inter_of_stopping_time (hS : IsStoppingTime f S)
    (hT : IsStoppingTime f T) (t : Set Ω)
    (h : MeasurableSet[hS.measurableSpace] ({ω | S ω = T ω} ∩ t)) :
    MeasurableSet[hT.measurableSpace] ({ω | S ω = T ω} ∩ t) := by
  have := measurableSet_inter_eq_of_stopping_time hS hT h
  rwa [show ({ω | S ω = T ω} ∩ t) ∩ {ω | S ω = T ω} = {ω | S ω = T ω} ∩ t by
    ext ω; simp only [mem_inter_iff, mem_ofPred_eq]; tauto] at this

/-- Localizing conditional expectations at stopping times: `E[Y | ℱ_S] = E[Y | ℱ_T]` a.e. on `{S = T}`. -/
theorem condExp_stopping_time_ae_eq_restrict_eq_stopping_time {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hS : IsStoppingTime f S) (hT : IsStoppingTime f T) (Y : Ω → E) :
    μ[Y | hS.measurableSpace] =ᵐ[μ.restrict {ω | S ω = T ω}] μ[Y | hT.measurableSpace] := by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on hS.measurableSpace_le
    hT.measurableSpace_le (measurableSet_eq_stopping_time_both hS hT).1 fun t => ?_
  have hsym : {ω | T ω = S ω} = {ω | S ω = T ω} := by ext ω; exact eq_comm
  refine ⟨measurableSet_eq_inter_of_stopping_time hS hT t, fun h => ?_⟩
  have := measurableSet_eq_inter_of_stopping_time hT hS t
  rw [hsym] at this
  exact this h

end ElboimSly.Paper
