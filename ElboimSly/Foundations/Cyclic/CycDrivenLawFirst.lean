/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFinalSpec
public import ElboimSly.Foundations.Cyclic.CycFinalNth
public import ElboimSly.Foundations.Cyclic.CycRegionMeas
public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import Mathlib

/-!
# The first world-line of a final record

Driven and environment walks agree in law (proof: the first world-line of the final record of `𝒫₁`).

* `CycPlan.coord_cycFinal_zero`: if `0 < K`, the first coordinate of the final record is the
  first step of the recursion, `nextEntry path 0 `.
* `firstPiece`: the pair `(ς, p)` (length and path function) of the first coordinate of a record,
  a measurable function of the record.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

namespace CycPlan

variable (P : CycPlan I d β) (path : PathRule I d)

open scoped Classical in
omit [Fact (0 < β)] in
/-- If the plan has at least one walk, the first coordinate of the final record is the first step. -/
theorem coord_cycFinal_zero (hK : 0 < P.K) :
    (P.cycFinal path).coord P.junk 0 = P.nextEntry path 0 Fin.elim0 := by
  have h0 : ¬ P.Ended (P.cycState path 0) := by
    show ¬ P.Ended CycRec.empty
    rintro (h | ⟨h, _⟩)
    · exact absurd hK (not_lt.2 (by simpa using h))
    · omega
  have h1 : (P.cycState path 1).coord P.junk 0 = P.nextEntry path 0 Fin.elim0 := by
    rw [cycState_succ]
    show (P.cycStep path (Sum.inl ⟨0, Fin.elim0⟩)).coord P.junk 0 = _
    have h0' : ¬ P.Ended (Sum.inl ⟨0, Fin.elim0⟩ : CycRec I d) := h0
    simp only [cycStep, ite_eq_right h0']
    simp [CycRec.coord, CycRec.nth, CycRec.snoc, nextEntry]
    rfl
  rw [← h1]
  unfold cycFinal
  split_ifs with hh
  · have hall : ∀ i < Nat.find hh, ¬ P.Ended (P.cycState path i) := fun i hi => Nat.find_min hh hi
    have hpos : 0 < Nat.find hh := by
      rcases Nat.eq_zero_or_pos (Nat.find hh) with h | h
      · exact absurd (h ▸ Nat.find_spec hh) h0
      · exact h
    exact P.coord_cycState_lt path _ hall hpos 1 hpos (by omega)
  · rfl

end CycPlan

/-- The length and path function of the first coordinate of a record. -/
noncomputable def firstPiece (junk : CycEntry I d) (ρ : CycRec I d) :
    ℝ≥0∞ × (ℝ≥0 → Fin d → ℤ) :=
  ((ρ.coord junk 0).len, (ρ.coord junk 0).path.fn)

theorem measurable_firstPiece [MeasurableSingletonClass I] [Countable I] (junk : CycEntry I d) :
    Measurable (firstPiece junk) :=
  (measurable_entry_len.comp (CycRec.measurable_coord junk 0)).prodMk
    (measurable_pi_iff.2 fun s =>
      (CPath.measurable_eval s).comp (measurable_entry_path.comp (CycRec.measurable_coord junk 0)))

end ElboimSly.Cyclic

end
