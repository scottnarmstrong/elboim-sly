/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.PathConvert
public import ElboimSly.Frozen.Defs.InterchangePi
import Mathlib

/-!
# Trajectories as functions

Existence and uniqueness of trajectories.

For a good configuration, `fwdTrajFn hν x a` is the forward trajectory from `(x, a)` and
`bwdTrajFn hν y b` the backward trajectory to `(y, b)`, both chosen from the frozen
`existsUnique_trajectories`. The real-time versions are `fwdTraj` and `bwdTraj`:
`fwdTraj hν x a t = γ_{x,a}(t)` and `bwdTraj hν y b t = η_{y,b}(t)`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The forward trajectory from `(x, a)` as a half-line path (`γ s` is the position at `a + s`). -/
noncomputable def fwdTrajFn (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) : ℝ≥0 → Fin d → ℤ :=
  Classical.choose ((existsUnique_trajectories ν hν).1 x a).exists

/-- The backward trajectory to `(y, b)` as a half-line path (`η s` is the position at `b - s`). -/
noncomputable def bwdTrajFn (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) : ℝ≥0 → Fin d → ℤ :=
  Classical.choose ((existsUnique_trajectories ν hν).2 y b).exists

theorem fwdTrajFn_spec (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) :
    IsForwardTrajectory ν x a (fwdTrajFn hν x a) :=
  Classical.choose_spec ((existsUnique_trajectories ν hν).1 x a).exists

theorem bwdTrajFn_spec (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) :
    IsBackwardTrajectory ν y b (bwdTrajFn hν y b) :=
  Classical.choose_spec ((existsUnique_trajectories ν hν).2 y b).exists

theorem fwdTrajFn_eq (hν : Good ν) {x : Fin d → ℤ} {a : ℝ} {γ : ℝ≥0 → Fin d → ℤ}
    (h : IsForwardTrajectory ν x a γ) : γ = fwdTrajFn hν x a :=
  ((existsUnique_trajectories ν hν).1 x a).unique h (fwdTrajFn_spec hν x a)

theorem bwdTrajFn_eq (hν : Good ν) {y : Fin d → ℤ} {b : ℝ} {η : ℝ≥0 → Fin d → ℤ}
    (h : IsBackwardTrajectory ν y b η) : η = bwdTrajFn hν y b :=
  ((existsUnique_trajectories ν hν).2 y b).unique h (bwdTrajFn_spec hν y b)

/-- The forward trajectory `γ^ν_{x,a}` as a function of real time. -/
noncomputable def fwdTraj (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) : ℝ → Fin d → ℤ :=
  fwdReal a (fwdTrajFn hν x a)

/-- The backward trajectory `η^ν_{y,b}` as a function of real time. -/
noncomputable def bwdTraj (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) : ℝ → Fin d → ℤ :=
  bwdReal b (bwdTrajFn hν y b)

theorem fwdTraj_isPathOn (hν : Good ν) (x : Fin d → ℤ) (a b : ℝ) :
    IsPathOn ν a b (fwdTraj hν x a) :=
  IsForwardPath.toPathOn (fwdTrajFn_spec hν x a).1 b

theorem bwdTraj_isPathOn (hν : Good ν) (y : Fin d → ℤ) (a b : ℝ) :
    IsPathOn ν a b (bwdTraj hν y b) :=
  IsBackwardPath.toPathOn (bwdTrajFn_spec hν y b).1 a

theorem fwdTraj_self (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) : fwdTraj hν x a a = x := by
  have := (fwdTrajFn_spec hν x a).2
  simpa [fwdTraj, fwdReal] using this

theorem bwdTraj_self (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) : bwdTraj hν y b b = y := by
  have := (bwdTrajFn_spec hν y b).2
  simpa [bwdTraj, bwdReal] using this

/-- `π_s x` is the forward trajectory from `(x, 0)` at time `s`. -/
theorem interchangePi_eq (hν : Good ν) (s : ℝ≥0) (x : Fin d → ℤ) :
    interchangePi ν s x = fwdTraj hν x 0 s := by
  simp [interchangePi, fwdTraj, fwdReal, fwdTrajFn, hν]

theorem fwdTraj_eq_of_isPathOn (hν : Good ν) {x : Fin d → ℤ} {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → Fin d → ℤ} (hf : IsPathOn ν a b f) (h0 : f a = x) :
    ∀ t ∈ Set.Icc a b, f t = fwdTraj hν x a t :=
  hf.eq_of_left hab (fwdTraj_isPathOn hν x a b) (h0.trans (fwdTraj_self hν x a).symm)

theorem bwdTraj_eq_of_isPathOn (hν : Good ν) {y : Fin d → ℤ} {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → Fin d → ℤ} (hf : IsPathOn ν a b f) (h0 : f b = y) :
    ∀ t ∈ Set.Icc a b, f t = bwdTraj hν y b t :=
  hf.eq_of_right hν hab (bwdTraj_isPathOn hν y a b) (h0.trans (bwdTraj_self hν y b).symm)

end ElboimSly.Interchange
