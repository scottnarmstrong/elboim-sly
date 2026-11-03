/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.RingSpace
import Mathlib

/-!
# Arcs of the circle `ℝ/βℤ`

Measurability, Step 1 (the Borel arcs `[(q, c]]`).

`arc q c = {[u] : q < u ≤ c}` is the image of `(q, c]` in `AddCircle β`. It is a Borel set (the
preimage of `Iic c` under the measurable representative map in `(q, q + β]`), and it is the whole
circle as soon as `c ≥ q + β`.
-/

@[expose] public section

open MeasureTheory Set

namespace ElboimSly.Cyclic

variable {β : ℝ} [Fact (0 < β)]

/-- The representative of `θ` in `(q, q + β]`. -/
noncomputable def arcRep (β : ℝ) [Fact (0 < β)] (q : ℝ) (θ : AddCircle β) : ℝ :=
  (AddCircle.equivIoc β q θ : ℝ)

theorem measurable_arcRep (q : ℝ) : Measurable (arcRep β q) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc β q).measurable

theorem arcRep_mem (q : ℝ) (θ : AddCircle β) : q < arcRep β q θ ∧ arcRep β q θ ≤ q + β :=
  (AddCircle.equivIoc β q θ).2

theorem coe_arcRep (q : ℝ) (θ : AddCircle β) : ((arcRep β q θ : ℝ) : AddCircle β) = θ :=
  AddCircle.coe_equivIoc

theorem arcRep_le_self {q u : ℝ} (hu : q < u) : arcRep β q (u : AddCircle β) ≤ u := by
  by_cases h : u ≤ q + β
  · have := AddCircle.equivIoc_coe_eq (p := β) (a := q) (x := u) ⟨hu, h⟩
    simp [arcRep, this]
  · exact (arcRep_mem q _).2.trans (not_le.mp h).le

/-- The arc `[(q, c]] = {[u] : q < u ≤ c}`. -/
def arc (β : ℝ) [Fact (0 < β)] (q c : ℝ) : Set (AddCircle β) := {θ | arcRep β q θ ≤ c}

theorem measurableSet_arc (q c : ℝ) : MeasurableSet (arc β q c) :=
  measurable_arcRep q measurableSet_Iic

theorem mem_arc_iff {q c : ℝ} {θ : AddCircle β} :
    θ ∈ arc β q c ↔ ∃ u : ℝ, q < u ∧ u ≤ c ∧ (u : AddCircle β) = θ := by
  constructor
  · intro h
    exact ⟨arcRep β q θ, (arcRep_mem q θ).1, h, coe_arcRep q θ⟩
  · rintro ⟨u, hqu, huc, rfl⟩
    exact (arcRep_le_self hqu).trans huc

end ElboimSly.Cyclic

end
