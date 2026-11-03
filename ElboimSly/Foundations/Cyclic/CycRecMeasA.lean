/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRingMeas2
public import ElboimSly.Foundations.Cyclic.CycPlan
public import Mathlib

/-!
# Measurability of record functionals (a)

Measurability of record functionals (a). The indicator of the explored region, the ring measure and the
number of known rings are measurable functions of the record.

* `CycRec.measurableSet_region_all`: `(ρ, x) ↦ 1{x ∈ R(ρ)}`;
* `CycRec.measurable_rm`: `ρ ↦ RM(ρ)`;
* `CycRec.measurable_ringCard`, `CycRec.measurable_ringNcard`: `ρ ↦ #Ring(ρ)`.

The written proof restricts `RM` and `#Ring` to records of finite total length. We prove them on all
records (a stronger statement), so no finiteness hypothesis is needed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

/-- Measurability of record functionals (a): the region indicator `(ρ, x) ↦ 1{x ∈ R(ρ)}`. -/
theorem CycRec.measurableSet_region_all :
    MeasurableSet {z : CycRec I d × (I × RingSpace d β) | z.2 ∈ z.1.region β} := by
  rcases isEmpty_or_nonempty (I × RingSpace d β) with h | ⟨⟨ι, x⟩⟩
  · have : IsEmpty (CycRec I d × (I × RingSpace d β)) := ⟨fun z => h.false z.2⟩
    rw [Set.eq_empty_of_isEmpty {z : CycRec I d × (I × RingSpace d β) | z.2 ∈ z.1.region β}]
    exact MeasurableSet.empty
  · have : Nonempty (CycEntry I d) := ⟨((ι, 0, 0, true), CycPath.const 0)⟩
    exact measurableSet_region

omit [Fact (0 < β)] in
/-- Measurability of record functionals (a): `ρ ↦ RM(ρ)` is measurable. -/
theorem CycRec.measurable_rm : Measurable fun ρ : CycRec I d => ρ.rm β := by
  rcases isEmpty_or_nonempty (I × RingSpace d β) with h | ⟨⟨ι, x⟩⟩
  · exact measurable_of_subsingleton_codomain _
  · have : Nonempty (CycEntry I d) := ⟨((ι, 0, 0, true), CycPath.const 0)⟩
    exact measurable_rm_aux x.1 ((ι, 0, 0, true), CycPath.const 0)

omit [Fact (0 < β)] in
/-- Measurability of record functionals (a): `ρ ↦ #Ring(ρ) ∈ ℕ∞`. -/
theorem CycRec.measurable_ringCard : Measurable fun ρ : CycRec I d => (ρ.ringSet β).encard := by
  rcases isEmpty_or_nonempty (I × RingSpace d β) with h | ⟨⟨ι, x⟩⟩
  · have : ∀ ρ : CycRec I d, ρ.ringSet β = ∅ := fun ρ => Set.eq_empty_of_isEmpty _
    simp only [this, Set.encard_empty]
    exact measurable_const
  · have : Nonempty (CycEntry I d) := ⟨((ι, 0, 0, true), CycPath.const 0)⟩
    exact _root_.ElboimSly.Cyclic.measurable_ringCard x.1 ((ι, 0, 0, true), CycPath.const 0)

omit [Fact (0 < β)] in
/-- Measurability of record functionals (a): `ρ ↦ #Ring(ρ) ∈ ℕ` (the count, `0` if infinite). -/
theorem CycRec.measurable_ringNcard : Measurable fun ρ : CycRec I d => (ρ.ringSet β).ncard := by
  have h1 : Measurable fun n : ℕ∞ => n.toNat := measurable_of_countable _
  exact h1.comp (CycRec.measurable_ringCard (β := β))

end ElboimSly.Cyclic

end
