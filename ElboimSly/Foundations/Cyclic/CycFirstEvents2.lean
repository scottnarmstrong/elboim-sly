/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFirstEvents
public import ElboimSly.Foundations.Cyclic.CycTruncSpec
public import Mathlib

/-!
# Basic properties of world-lines (d): events of a truncated record, and counting

Basic properties of world-lines (d). The events of `Trunc_s(ρ)` are the events of `ρ` in global time
`≤ s`, and in a driven final record with one driver the number of classes of `Rec(s)` is at most the
number of jumps of the driver in `(0, s]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [MeasurableSpace I] in
theorem CycEntry.len_cut (e : CycEntry I d) (t : ℝ≥0∞) : (e.cut t).len = t := CPath.cut_len _ _

omit [MeasurableSpace I] in
theorem CycEntry.path_cut (e : CycEntry I d) (t : ℝ≥0∞) : (e.cut t).path = e.path.cut t := rfl

omit [MeasurableSpace I] in
theorem CycEntry.data_cut (e : CycEntry I d) (t : ℝ≥0∞) : (e.cut t).data = e.data := rfl

omit [MeasurableSpace I] in
theorem CycRec.cum_succ_eq (junk : CycEntry I d) (ρ : CycRec I d) (k : ℕ) (hk : (k : ℕ∞) < ρ.num) :
    ρ.cum (k + 1) = ρ.cum k + (ρ.coord junk k).len := by
  unfold CycRec.cum
  rw [Finset.sum_range_succ, CycRec.lenAt_eq junk ρ k, ite_eq_left hk]

namespace CycPlan

variable (P : CycPlan I d β) {J : Type*} (jx : ∀ k : ℕ, CycRecN I d k → J) (X : J → CycPath d)

end CycPlan

namespace CycPlan

variable (P : CycPlan I d β) {J : Type*} (jx : ∀ k : ℕ, CycRecN I d k → J) (X : J → CycPath d)

end CycPlan

namespace CycPlan

variable (P : CycPlan I d β) {J : Type*} (jx : ∀ k : ℕ, CycRecN I d k → J) (X : J → CycPath d)

end CycPlan

end ElboimSly.Cyclic

end
