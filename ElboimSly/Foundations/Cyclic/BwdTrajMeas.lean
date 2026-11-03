/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.BwdBridge
import Mathlib

/-!
# Measurability of backward trajectories

Measurability ("and so is the analogous map for backward trajectories").
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem measurable_reflectGood :
    Measurable (fun ν : GoodSet d β => (⟨reflectMeasure β ν.1, good_reflectMeasure ν.2⟩ : GoodSet d β)) :=
  Measurable.subtype_mk (measurable_reflectMeasure.comp measurable_subtype_coe)

theorem measurable_bstepT (z : Fin d → ℤ) :
    Measurable (fun p : GoodSet d β × ℝ => bstepT p.1.1 z p.2) :=
  ((measurable_stepT z).comp
    ((measurable_reflectGood.comp measurable_fst).prodMk measurable_snd.neg)).neg

theorem measurable_bstepW (z : Fin d → ℤ) :
    Measurable (fun p : GoodSet d β × ℝ => bstepW p.1.1 z p.2) :=
  (measurable_stepW z).comp
    ((measurable_reflectGood.comp measurable_fst).prodMk measurable_snd.neg)

theorem measurable_bstart (y : Fin d → ℤ) :
    Measurable (fun p : GoodSet d β × ℝ => bstart p.1.1 y p.2) :=
  (measurable_stepT y).min (measurable_snd.add measurable_const)

theorem measurable_bseq (y : Fin d → ℤ) (k : ℕ) :
    Measurable (fun p : GoodSet d β × ℝ => bseq p.1.1 y p.2 k) := by
  have hG : Measurable (fun s : (GoodSet d β × ℝ) × (Fin d → ℤ) =>
      ((bstepT s.1.1.1 s.2 s.1.2, bstepW s.1.1.1 s.2 s.1.2) : ℝ × (Fin d → ℤ))) :=
    measurable_from_prod_countable_left fun z => (measurable_bstepT z).prodMk (measurable_bstepW z)
  induction k with
  | zero => exact (measurable_bstart y).prodMk measurable_const
  | succ k ih => exact hG.comp ((measurable_fst.prodMk ih.fst).prodMk ih.snd)

/-- `(ν, b, r) ↦ η^ν_{y,b}(r)` is measurable on the good configurations. -/
theorem measurable_bwdTraj (y : Fin d → ℤ) :
    Measurable (fun q : GoodSet d β × ℝ × ℝ => bwdTraj q.1.2 y q.2.1 q.2.2) := by
  refine measurable_to_countable' fun y' => ?_
  have hF : ∀ k, Measurable (fun q : GoodSet d β × ℝ × ℝ => bseq q.1.1 y q.2.1 k) := fun k =>
    (measurable_bseq y k).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hM : Measurable (fun q : GoodSet d β × ℝ × ℝ => min q.2.2 q.2.1) :=
    (measurable_snd.comp measurable_snd).min (measurable_fst.comp measurable_snd)
  have : (fun q : GoodSet d β × ℝ × ℝ => bwdTraj q.1.2 y q.2.1 q.2.2) ⁻¹' {y'} =
      ⋃ k : ℕ, ({q | (bseq q.1.1 y q.2.1 (k + 1)).1 ≤ min q.2.2 q.2.1} ∩
        {q | min q.2.2 q.2.1 < (bseq q.1.1 y q.2.1 k).1} ∩
        {q | (bseq q.1.1 y q.2.1 k).2 = y'}) := by
    ext ⟨⟨ν, hν⟩, b, r⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨k, h1, h2⟩ := exists_bblock hν y b r
      exact ⟨k, ⟨h1, h2⟩, (bwdTraj_eq_bseq hν y b r h1 h2).symm.trans h⟩
    · rintro ⟨k, ⟨h1, h2⟩, h3⟩
      exact (bwdTraj_eq_bseq hν y b r h1 h2).trans h3
  rw [this]
  refine MeasurableSet.iUnion fun k => ?_
  exact ((measurableSet_le ((hF (k + 1)).fst) hM).inter (measurableSet_lt hM ((hF k).fst))).inter
    (measurableSet_eq_fun (hF k).snd measurable_const)

end ElboimSly.Cyclic

end
