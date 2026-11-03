/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycHitCoupleDrivenRegen
public import Mathlib

/-!
# Driving paths and the regenerated walk driven by a path

Driving paths; the regenerated walk driven by a path (ES22 §2, ES22 §2).

A driving path is an `IsDrivingPath` (right-continuous, finitely many jumps on bounded intervals,
`x 0 = 0`, jumps of `ℓ¹`-size `1`). `StepPath d` is their set; `stepShift a x = θ_a x`;
`stepReg β x` is the regenerated walk driven by `x`, `stepSigma β x i` its regeneration times,
`stepAlpha β x t` the last regeneration time at or before `t`; `StepCF β` the coincidence-free paths.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- Driving paths; the regenerated walk driven by a path: the set of driving paths. -/
def StepPath (d : ℕ) : Set (ℝ≥0 → Fin d → ℤ) := {x | Cyclic.IsDrivingPath x}

/-- `θ_a x = x(a + ·) - x(a)`. -/
def stepShift (a : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ := Cyclic.shiftPath x a

/-- The regenerated walk driven by `x` (construction (iii) of the constructions of the regenerated walk). -/
noncomputable def stepReg (β : ℝ) (x : ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ :=
  Cyclic.drivenRegenFrom β.toNNReal x

/-- Its regeneration times `σ_i`. -/
noncomputable def stepSigma (β : ℝ) (x : ℝ≥0 → Fin d → ℤ) : ℕ → ℝ≥0∞ :=
  Cyclic.drivenSigma β.toNNReal x

/-- `α(t)`, the last regeneration time at or before `t`. -/
noncomputable def stepAlpha (β : ℝ) (x : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : ℝ≥0 :=
  Cyclic.drivenRegenAlpha β.toNNReal x t

/-- Coincidence-free driving paths `CF_β`. -/
def StepCF (β : ℝ) : Set (ℝ≥0 → Fin d → ℤ) := Cyclic.CycCF (d := d) (β := β.toNNReal)

theorem stepShift_mem {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ StepPath d) (a : ℝ≥0) :
    stepShift a x ∈ StepPath d :=
  Cyclic.isDrivingPath_shiftPath hx a

end ElboimSly.Paper
