/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.TrajMeas
public import ElboimSly.Foundations.Interchange.BackwardExistence
public import ElboimSly.Foundations.Interchange.SymmG3
public import ElboimSly.Foundations.Interchange.SymmCov
import Mathlib

/-!
# Measurability of the backward trajectory

Measurability, Step 3 (the mirrored recursion).

The mirrored step is obtained from the forward step of the reflected configuration:
`bstepT ν z t = - stepT (ϱ_*ν) z (-t)`, `bstepW ν z t = stepW (ϱ_*ν) z (-t)`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The previous ring time at `z` before `t` (dummy value `t - 1`). -/
noncomputable def bstepT (ν : Measure (RingSpace d β)) (z : Fin d → ℤ) (t : ℝ) : ℝ :=
  - stepT (reflectMeasure β ν) z (-t)

/-- The position before the jump. -/
noncomputable def bstepW (ν : Measure (RingSpace d β)) (z : Fin d → ℤ) (t : ℝ) : Fin d → ℤ :=
  stepW (reflectMeasure β ν) z (-t)

omit [Fact (0 < β)] in
theorem ringAt_reflect (z : Fin d → ℤ) (u : ℝ) :
    RingAt (reflectMeasure β ν) z (-u) ↔ RingAt ν z u := by
  unfold RingAt
  simp only [rings_reflectMeasure, neg_neg]

theorem bstep_spec (hν : Good ν) (z : Fin d → ℤ) (t : ℝ) :
    bstepT ν z t < t ∧ (∀ u, bstepT ν z t < u → u < t → ¬ RingAt ν z u) ∧
      SwapRule ν (bstepT ν z t) z (bstepW ν z t) ∧
      ((∃ e : Edge d, e.1 = s(z, bstepW ν z t) ∧ Rings ν e (bstepT ν z t)) ∨
        (bstepT ν z t = t - 1 ∧ bstepW ν z t = z ∧ ∀ u, ¬ RingAt ν z u)) := by
  obtain ⟨h1, h2, h3, h4⟩ := step_spec (good_reflectMeasure hν) z (-t)
  set T := stepT (reflectMeasure β ν) z (-t) with hT
  refine ⟨by simp only [bstepT]; linarith, fun u hu hu' hr => ?_, ?_, ?_⟩
  · simp only [bstepT] at hu
    exact h2 (-u) (by linarith) (by linarith) ((ringAt_reflect z u).mpr hr)
  · simp only [bstepT, bstepW]
    rw [← hT]
    have := (swapRule_reflectMeasure_iff (ν := ν) (t := T)).mp h3
    exact this
  · rcases h4 with ⟨e, he, hr⟩ | ⟨a, b, c⟩
    · refine Or.inl ⟨e, he, ?_⟩
      simp only [bstepT]
      rw [← hT]
      exact (rings_reflectMeasure ν e T).mp hr
    · refine Or.inr ⟨by simp only [bstepT]; linarith, b, fun u hr => ?_⟩
      exact c (-u) ((ringAt_reflect z u).mpr hr) |> fun h => h

end ElboimSly.Cyclic

end
