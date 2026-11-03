/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycStepCoords
public import Mathlib

/-!
# Measurability of `ρ ↦ ρ|s`

Measurability of record functionals (b), first half. `restrictLast` preserves `num` and changes only the
last coordinate of a finite record.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

omit [MeasurableSpace I] in
theorem CycRec.num_restrictLast (s : ℝ≥0) (ρ : CycRec I d) :
    (CycRec.restrictLast s ρ).num = ρ.num := by
  rcases ρ with ⟨n, f⟩ | f
  · cases n <;> simp [CycRec.restrictLast, CycRec.num]
  · simp [CycRec.restrictLast, CycRec.num]

open scoped Classical in
omit [MeasurableSpace I] in
theorem CycRec.coord_restrictLast (junk : CycEntry I d) (s : ℝ≥0) (ρ : CycRec I d) (j : ℕ) :
    (CycRec.restrictLast s ρ).coord junk j =
      if (j : ℕ∞) + 1 = ρ.num then (ρ.coord junk j).cut s else ρ.coord junk j := by
  rcases ρ with ⟨n, f⟩ | f
  · cases n with
    | zero => simp [CycRec.restrictLast, CycRec.coord, CycRec.nth, CycRec.num]
    | succ n =>
      simp only [CycRec.restrictLast, CycRec.coord, CycRec.nth, CycRec.num]
      by_cases hj : j < n + 1
      · simp only [hj, dite_true, Option.getD_some]
        by_cases hjn : j = n
        · subst hjn
          have : (⟨j, hj⟩ : Fin (j + 1)) = Fin.last j := rfl
          rw [this, Function.update_self]
          simp
        · have : (⟨j, hj⟩ : Fin (n + 1)) ≠ Fin.last n := fun h => hjn (by simpa using congrArg Fin.val h)
          rw [Function.update_of_ne this]
          have : ¬ ((j : ℕ∞) + 1 = (n + 1 : ℕ)) := by
            intro h
            apply hjn
            have : ((j + 1 : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := by push_cast; exact h
            exact by exact_mod_cast (Nat.succ_injective (by exact_mod_cast this))
          rw [ite_eq_right this]
      · have : ¬ ((j : ℕ∞) + 1 = (n + 1 : ℕ)) := by
          intro h
          have : ((j + 1 : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := by push_cast; exact h
          have := Nat.cast_injective this
          omega
        simp only [hj, dite_false, Option.getD_none]
        rw [ite_eq_right this]
  · simp [CycRec.restrictLast, CycRec.coord, CycRec.nth, CycRec.num]

theorem measurable_entry_cut :
    Measurable (fun q : CycEntry I d × ℝ≥0∞ => (q.1.1, q.1.2.cut q.2) ) :=
  (measurable_fst.comp measurable_fst).prodMk (measurable_cycPath_cut.comp
    (((measurable_snd.comp measurable_fst)).prodMk measurable_snd))

/-- Measurability of record functionals (b): `(ρ, s) ↦ ρ|s` is measurable. -/
theorem measurable_restrictLast [Nonempty (CycEntry I d)] :
    Measurable (fun q : CycRec I d × ℝ≥0 => CycRec.restrictLast q.2 q.1) := by
  obtain ⟨junk⟩ := ‹Nonempty (CycEntry I d)›
  have hnum : Measurable fun q : CycRec I d × ℝ≥0 => q.1.num := CycRec.measurable_num.comp measurable_fst
  refine measurable_cycRec_of_coords _ junk ?_ fun j => ?_
  · simp only [CycRec.num_restrictLast]; exact hnum
  · simp only [CycRec.coord_restrictLast]
    have hset : MeasurableSet {q : CycRec I d × ℝ≥0 | (j : ℕ∞) + 1 = q.1.num} := by
      have := hnum (measurableSet_singleton ((j : ℕ∞) + 1))
      convert this using 1
      ext q; simp [eq_comm]
    have hc : Measurable fun q : CycRec I d × ℝ≥0 => q.1.coord junk j :=
      (CycRec.measurable_coord junk j).comp measurable_fst
    refine Measurable.ite hset ?_ hc
    exact measurable_entry_cut.comp (hc.prodMk (measurable_coe_nnreal_ennreal.comp measurable_snd))

end ElboimSly.Cyclic

end
