/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.TrajApi
import Mathlib

/-!
# `π_s` is a permutation

pi_s is a permutation.

For good `ν` and `s ≥ 0`, `π_s` is a bijection of `ℤᵈ` with inverse `y ↦ η^ν_{y,s}(0)`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- `π_s` applied to the start of the backward trajectory to `(y, s)` is `y`. -/
theorem interchangePi_bwd (hν : Good ν) (s : ℝ≥0) (y : Fin d → ℤ) :
    interchangePi ν s (bwdTraj hν y s 0) = y := by
  rw [interchangePi_eq hν]
  have hs : (0 : ℝ) ≤ s := s.coe_nonneg
  have h := (fwdTraj_isPathOn hν (bwdTraj hν y s 0) 0 s).eq_of_left hs
    (bwdTraj_isPathOn hν y 0 s)
    (by rw [fwdTraj_self])
  rw [h s ⟨hs, le_rfl⟩, bwdTraj_self]

/-- The backward trajectory from `π_s x` returns to `x`. -/
theorem bwd_interchangePi (hν : Good ν) (s : ℝ≥0) (x : Fin d → ℤ) :
    bwdTraj hν (interchangePi ν s x) s 0 = x := by
  have hs : (0 : ℝ) ≤ s := s.coe_nonneg
  have h := (fwdTraj_isPathOn hν x 0 s).eq_of_right hν hs
    (bwdTraj_isPathOn hν (interchangePi ν s x) 0 s)
    (by rw [bwdTraj_self, interchangePi_eq hν])
  rw [← h 0 ⟨le_rfl, hs⟩, fwdTraj_self]

/-- pi_s is a permutation. For good `ν` and `s ≥ 0`, `π_s` is a bijection of `ℤᵈ`. -/
theorem interchangePi_bijective (hν : Good ν) (s : ℝ≥0) :
    Function.Bijective (interchangePi ν s) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun y => bwdTraj hν y s 0, fun x => bwd_interchangePi hν s x, interchangePi_bwd hν s⟩

/-- `π_s` as a permutation of `ℤᵈ`. -/
noncomputable def interchangePerm (hν : Good ν) (s : ℝ≥0) : Equiv.Perm (Fin d → ℤ) :=
  Equiv.ofBijective _ (interchangePi_bijective hν s)

end ElboimSly.Interchange
