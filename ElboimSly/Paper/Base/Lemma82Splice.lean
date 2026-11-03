/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import ElboimSly.Foundations.Interchange.TrajProps
public import Mathlib

/-!
# Splicing and periodicity of the cyclic walks

ES22 Lemma 8.2, "A splicing fact" and "Setup" (periodicity, restriction, restart, periodicity (b), (c)).

* `cycWalk_splice`: for good `ν`, `x ∈ ℤ^d`, `c ≤ c'` and `z := η^ν_{x,c'}(c)`, we have
  `W^ν_{z,c}(c' - c + s) = W^ν_{x,c'}(s)` for all `s ≥ 0`.
* `cycWalk_add_zsmul`: `W^ν_{u,q + kβ}(s) = W^ν_{u,q}(s)` for `s ≥ 0`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The position at time `c` of the backward trajectory through `(x, c')`. -/
theorem cycWalk_neg_eq_bwdTraj (hν : Good ν) (x : Fin d → ℤ) {c c' : ℝ} (hcc' : c ≤ c') :
    cycWalk ν x c' (c - c') = bwdTraj hν x c' c := by
  rw [cycWalk_of_nonpos hν x c' (by linarith)]
  congr 1
  ring

/-- **Splicing**: `W_{z,c}(c' - c + s) = W_{x,c'}(s)` for `z = η_{x,c'}(c)`. -/
theorem cycWalk_splice (hν : Good ν) (x : Fin d → ℤ) {c c' : ℝ} (hcc' : c ≤ c') {s : ℝ}
    (hs : 0 ≤ s) :
    cycWalk ν (cycWalk ν x c' (c - c')) c (c' - c + s) = cycWalk ν x c' s := by
  set z := bwdTraj hν x c' c with hz
  rw [cycWalk_neg_eq_bwdTraj hν x hcc', cycWalk_of_nonneg hν z c (by linarith),
    cycWalk_of_nonneg hν x c' hs]
  have h1 : fwdTraj hν z c c' = x := by
    have h := fwdTraj_eq_of_isPathOn hν hcc' (bwdTraj_isPathOn hν x c c') rfl c'
      ⟨hcc', le_rfl⟩
    rw [bwdTraj_self] at h
    exact h.symm
  have h2 := fwdTraj_restart hν z hcc' (t := c' + s) (by linarith)
  rw [h1] at h2
  rw [show c + (c' - c + s) = c' + s by ring]
  exact h2

/-- Periodicity: shifting the starting phase by a multiple of `β` does not change the walk. -/
theorem cycWalk_add_zsmul (hν : Good ν) (u : Fin d → ℤ) (q : ℝ) (k : ℤ) {s : ℝ} (hs : 0 ≤ s) :
    cycWalk ν u (q + k * β) s = cycWalk ν u q s := by
  rw [cycWalk_of_nonneg hν u _ hs, cycWalk_of_nonneg hν u q hs]
  have := fwdTraj_add_zsmul hν u q k (t := q + s) (by linarith)
  rw [show q + k * β + s = q + s + k * β by ring]
  exact this

end ElboimSly.Paper

end
