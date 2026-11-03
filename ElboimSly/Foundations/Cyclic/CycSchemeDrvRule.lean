/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeGenLim
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvSrw
public import ElboimSly.Foundations.Cyclic.CycFirstEvents
public import Mathlib

/-!
# The driving scheme (c): the driven path rule and the invariant `GAt`

The driving scheme (c). `drule P jx X` is the path rule of the driven recursion
(world-lines of a plan; joint exploration filtration (b)): walk `k + 1` after the record `ρ` follows the driven path for the region and the
known rings of `ρ`, driven by `X (jx k ρ)` from the offset `drvOffset jx ρ (jx k ρ)`. The final record
of the recursion is `P.drivenFinal jx X` (`drivenFinal_eq_cycFinal`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {J : Type*}

/-- The path rule of the driven recursion. -/
noncomputable def drule (P : CycPlan I d β) (jx : ∀ k : ℕ, CycRecN I d k → J) (X : J → CycPath d) :
    PathRule I d :=
  fun k ρ => drivenPath β (CycRec.region β (Sum.inl ⟨k, ρ⟩)) (CycRec.ringSet β (Sum.inl ⟨k, ρ⟩))
    (P.start k ρ) (X (jx k ρ)).1 (drvOffset jx ρ (jx k ρ))

theorem drivenFinal_eq_cycFinal (P : CycPlan I d β) (jx : ∀ k : ℕ, CycRecN I d k → J)
    (X : J → CycPath d) : P.drivenFinal jx X = P.cycFinal (drule P jx X) := rfl

omit [MeasurableSpace I] in
theorem drivenPath_fn_zero (R Q : Set (I × RingSpace d β)) (δ : CycData I d)
    (X : CPath (Fin d → ℤ)) (a : ℝ≥0) : (drivenPath β R Q δ X a).1.fn 0 = δ.start := by
  classical
  unfold drivenPath
  by_cases h : ∃ p : CycPath d, IsDriven β R Q δ X a p.1
  · rw [dite_eq_left h]
    exact h.choose_spec.2.1
  · rw [dite_eq_right h]
    rfl

namespace CycSchemeGen

open CycSchemeEnv in
theorem zeroRule_drule (P : CycPlan I d β) (jx : ∀ k : ℕ, CycRecN I d k → J) (X : J → CycPath d) :
    ZeroRule P (drule P jx X) := by
  intro k ρ
  refine Prod.ext rfl (Subtype.ext (CPath.ext' ?_ (funext fun t => ?_)))
  · show ((CycPath.const (P.start k ρ).start).1.cut 0).len =
      (((drule P jx X) k ρ).1.cut ((0 : ℝ≥0) : ℝ≥0∞)).len
    rw [CPath.cut_len, CPath.cut_len]; simp
  show ((CycPath.const (P.start k ρ).start).1.cut 0).fn t =
    (((drule P jx X) k ρ).1.cut ((0 : ℝ≥0) : ℝ≥0∞)).fn t
  rw [CPath.cut_fn, CPath.cut_fn]
  simp only [ENNReal.coe_zero, min_zero, ENNReal.toNNReal_zero]
  have := drivenPath_fn_zero (CycRec.region β (Sum.inl ⟨k, ρ⟩))
    (CycRec.ringSet β (Sum.inl ⟨k, ρ⟩)) (P.start k ρ) (X (jx k ρ)).1 (drvOffset jx ρ (jx k ρ))
  show _ = (drivenPath β _ _ _ _ _).1.fn 0
  rw [this]
  rfl

end CycSchemeGen

end ElboimSly.Cyclic

end
