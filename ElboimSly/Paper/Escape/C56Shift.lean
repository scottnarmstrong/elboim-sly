/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Phases
public import ElboimSly.Paper.Escape.RelaxedClosed
public import Mathlib

/-!
# Translation invariance of relaxed times (for ES22 Claim 5.6)

`W_v = v + W`: relaxedness, the relaxed set and the times `ζ_i` do not see the shift by `v`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

theorem visitedSet_add_const (v : Fin d → ℤ) (w : ℝ → Fin d → ℤ) (a t : ℝ) :
    visitedSet (fun s => v + w s) a t = (fun x => v + x) '' visitedSet w a t := by
  unfold visitedSet
  rw [← Set.image_comp]; rfl

theorem isHeavy_add_const (v : Fin d → ℤ) (w : ℝ → Fin d → ℤ) (a t r : ℝ) (x : Fin d → ℤ) :
    IsHeavy (fun s => v + w s) a t (v + x) r ↔ IsHeavy w a t x r := by
  unfold IsHeavy
  refine and_congr Iff.rfl ?_
  rw [visitedSet_add_const]
  have e : {y : Fin d → ℤ | ‖y - (v + x)‖ ≤ r} ∩ (fun x => v + x) '' visitedSet w a t =
      (fun x => v + x) '' ({y : Fin d → ℤ | ‖y - x‖ ≤ r} ∩ visitedSet w a t) := by
    rw [Set.image_inter (add_right_injective v)]
    congr 1
    ext y
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · intro h
      refine ⟨y - v, ?_, by abel⟩
      have : y - v - x = y - (v + x) := by abel
      rw [this]; exact h
    · rintro ⟨z, hz, rfl⟩
      have : v + z - (v + x) = z - x := by abel
      rw [this]; exact hz
  rw [e, Set.ncard_image_of_injective _ (add_right_injective v)]

theorem isRelaxedTimeWrt_add_const (v : Fin d → ℤ) {β : ℝ} (w : ℝ → Fin d → ℤ) (a t : ℝ) :
    IsRelaxedTimeWrt β (fun s => v + w s) a t ↔ IsRelaxedTimeWrt β w a t := by
  unfold IsRelaxedTimeWrt
  refine and_congr ?_ ?_
  · refine forall_congr' fun r => imp_congr_right fun _ => not_congr ?_
    exact isHeavy_add_const v w a t r (w t)
  · refine forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun _ => ?_
    have : v + w t - (v + w s) = w t - w s := by abel
    simp only [this]

theorem relaxedSet_add_const (v : Fin d → ℤ) (β : ℝ) (w : ℝ → Fin d → ℤ) (a : ℝ) :
    relaxedSet β (fun s => v + w s) a = relaxedSet β w a := by
  ext s
  simp only [relaxedSet, mem_ofPred_eq, isRelaxedTimeWrt_add_const]

theorem escZetaStep_add_const {k : ℕ} (v : Fin (k + 2) → ℤ) (β : ℝ) (w : ℝ → Fin (k + 2) → ℤ)
    (lo hi prev : ℝ) :
    escZetaStep β (fun s => v + w s) lo hi prev = escZetaStep β w lo hi prev := by
  unfold escZetaStep
  rw [relaxedSet_add_const]

end ElboimSly.Paper.Escape

end
