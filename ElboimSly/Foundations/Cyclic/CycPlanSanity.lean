/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import Mathlib

/-!
# Non-vacuity of the plan and record definitions

A concrete one-walk plan over a single copy (`I = Unit`) whose environment record, in the empty
(good) environment `ν = 0`, is a one-entry record that is a world-line (`p(0) = u`) of length `∞`.
This exercises `CycPlan`, `stopLen`, `cycFinal`, `envPath`, `CycRec.nth`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem good_zero : Good (0 : Measure (RingSpace d β)) := by
  have hring : ∀ e : Edge d, ringSet (0 : Measure (RingSpace d β)) e = ∅ := fun e => by
    ext θ; simp [ringSet]
  refine ⟨fun A _ => Or.inr ⟨0, by simp⟩, fun e => by simp, ⟨fun e θ => by simp, fun e f _ => ?_⟩,
    fun y j => ⟨1, ?_, ?_⟩⟩
  · rw [hring, hring]; exact disjoint_empty _
  · rintro ⟨v, t, -, -, -, h⟩
    obtain ⟨e, -, he⟩ := h 0
    simp [Rings, hring] at he
  · rintro ⟨v, t, -, -, -, h⟩
    obtain ⟨e, -, he⟩ := h 0
    simp [Rings, hring] at he

/-- A one-walk plan: start at `0`, phase `0`, forward, never stop. -/
noncomputable def onePlan (d : ℕ) (β : ℝ) : CycPlan Unit d β where
  K := 1
  start _ _ := ((), 0, 0, true)
  dl _ _ := ⊤
  st _ _ := false
  measurable_start _ := measurable_const
  measurable_dl _ := measurable_const
  measurable_st _ := measurable_const

omit [Fact (0 < β)] in
theorem onePlan_stopLen (k : ℕ) (ρ : CycRecN Unit d k) (p : CycPath d) :
    (onePlan d β).stopLen k ρ p = ⊤ := by
  unfold CycPlan.stopLen
  convert sInf_empty
  ext t
  simp only [onePlan, mem_union, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, -, -, h, -⟩; exact absurd h (by simp)
  · rintro ⟨a, -, rfl, hlt⟩; simp at hlt

end ElboimSly.Cyclic

end
