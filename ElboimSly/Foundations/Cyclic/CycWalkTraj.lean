/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.CycWalk
public import ElboimSly.Foundations.Interchange.TrajProps
public import ElboimSly.Foundations.Interchange.PiBij
public import ElboimSly.Foundations.Interchange.CycleDef
import Mathlib

/-!
# The cyclic walk on good configurations

Cyclic walk; Agreement with the source definition.

On a good configuration the `Classical.epsilon` choices in `cycWalk` are the forward and backward
trajectories `fwdTraj`, `bwdTraj` of `Foundations/Interchange/TrajApi`. Then
Agreement with the source definition: `W(kβ + s) = π_s (π_β^k 0)` for `k : ℤ` and `s ∈ [0, β)`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- On a good configuration, `cycWalk` at a nonnegative time is the forward trajectory. -/
theorem cycWalk_of_nonneg (hν : Good ν) (u : Fin d → ℤ) (q : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    cycWalk ν u q s = fwdTraj hν u q (q + s) := by
  have hex : ∃ γ : ℝ≥0 → Fin d → ℤ, IsForwardTrajectory ν u q γ :=
    ⟨_, fwdTrajFn_spec hν u q⟩
  have h := Classical.epsilon_spec hex
  have h2 := fwdTrajFn_eq hν h
  simp only [cycWalk, hs, ite_true, fwdTraj, fwdReal]
  rw [h2]
  congr 1
  simp

/-- On a good configuration, `cycWalk` at a nonpositive time is the backward trajectory. -/
theorem cycWalk_of_nonpos (hν : Good ν) (u : Fin d → ℤ) (q : ℝ) {s : ℝ} (hs : s ≤ 0) :
    cycWalk ν u q s = bwdTraj hν u q (q + s) := by
  rcases hs.lt_or_eq with hs | rfl
  · have hex : ∃ η : ℝ≥0 → Fin d → ℤ, IsBackwardTrajectory ν u q η :=
      ⟨_, bwdTrajFn_spec hν u q⟩
    have h := Classical.epsilon_spec hex
    have h2 := bwdTrajFn_eq hν h
    simp only [cycWalk, not_le.mpr hs, ite_false, bwdTraj, bwdReal]
    rw [h2]
    congr 1
    simp
  · rw [cycWalk_of_nonneg hν u q le_rfl]
    simp [fwdTraj_self, bwdTraj_self]

/-- `W_{u,q}(0) = u`. -/
theorem cycWalk_zero (hν : Good ν) (u : Fin d → ℤ) (q : ℝ) : cycWalk ν u q 0 = u := by
  rw [cycWalk_of_nonneg hν u q le_rfl, add_zero, fwdTraj_self]

variable (ν) in
/-- The interchange map at a real time (`π_s` for `s ≥ 0`). -/
noncomputable def piReal (s : ℝ) (x : Fin d → ℤ) : Fin d → ℤ := interchangePi ν s.toNNReal x

theorem cycWalk_add_step (hν : Good ν) (k : ℤ) {s : ℝ} (hs0 : 0 ≤ s) (_hsβ : s ≤ β)
    (hk : 0 ≤ k ∨ (k : ℝ) * β + s ≤ 0) :
    cycWalk ν 0 0 (k * β + s) = piReal ν s (cycWalk ν 0 0 (k * β)) := by
  have hβ : 0 < β := Fact.out
  rcases hk with hk | hk
  · have hkβ : (0 : ℝ) ≤ k * β := mul_nonneg (by exact_mod_cast hk) hβ.le
    rw [cycWalk_of_nonneg hν 0 0 (by linarith), cycWalk_of_nonneg hν 0 0 hkβ, zero_add, zero_add,
      piReal, interchangePi_eq hν]
    have h1 := fwdTraj_restart hν 0 (a := 0) (c := k * β) hkβ (t := k * β + s) (by linarith)
    rw [h1]
    have h2 := fwdTraj_add_zsmul hν (fwdTraj hν 0 0 (k * β)) 0 k (t := s) hs0
    simp only [zero_add] at h2
    rw [Real.toNNReal_of_nonneg hs0]
    simp only [fwdTraj, fwdReal, NNReal.coe_mk] at h2 ⊢
    convert h2 using 2; simp [add_comm]
  · have hkβ : (k : ℝ) * β ≤ 0 := by linarith
    rw [cycWalk_of_nonpos hν 0 0 hk, cycWalk_of_nonpos hν 0 0 hkβ, zero_add, zero_add, piReal,
      interchangePi_eq hν]
    set y := bwdTraj hν 0 0 (k * β) with hy
    have hb : IsPathOn ν (k * β) (k * β + s) (bwdTraj hν 0 0) :=
      (bwdTraj_isPathOn hν 0 (k * β) 0).mono le_rfl (by linarith)
    have hf := fwdTraj_isPathOn hν y (k * β) (k * β + s)
    have := hb.eq_of_left (by linarith) hf (by rw [fwdTraj_self])
    rw [this (k * β + s) ⟨by linarith, le_rfl⟩]
    have h2 := fwdTraj_add_zsmul hν y 0 k (t := s) hs0
    simp only [zero_add] at h2
    rw [Real.toNNReal_of_nonneg hs0]
    simp only [fwdTraj, fwdReal, NNReal.coe_mk] at h2 ⊢
    convert h2 using 2; simp [add_comm]

end ElboimSly.Cyclic

end
