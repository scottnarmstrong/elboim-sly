/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.StepSpec
public import ElboimSly.Foundations.Interchange.TrajApi
import Mathlib

/-!
# The forward trajectory is the iterated jump sequence

Measurability, Step 2.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

theorem fseq_strictMono (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) :
    StrictMono (fun k => (fseq ν x a k).1) := (fwdSeq_fseq hν x a).strictMono

theorem fseq_unbounded (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) :
    ∀ T, ∃ k, T < (fseq ν x a k).1 := (fwdSeq_fseq hν x a).unbounded hν

theorem fwdTrajFn_eq_fwdPath (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) :
    fwdTrajFn hν x a = fwdPath a (fun k => (fseq ν x a k).1) (fun k => (fseq ν x a k).2) := by
  have h := fwdSeq_fseq hν x a
  have hun := fseq_unbounded hν x a
  symm
  refine fwdTrajFn_eq hν ⟨fwdPath_isForwardPath h.strictMono h.t_zero hun h.gap h.swap, ?_⟩
  rw [fwdPath_eq (k := 0) h.strictMono (by simp [h.t_zero]) (by simpa [h.t_zero] using h.lt 0)]
  exact h.z_zero

/-- On the block `t_k ≤ max r a < t_{k+1}`, the forward trajectory sits at `z_k`. -/
theorem fwdTraj_eq_fseq (hν : Good ν) (x : Fin d → ℤ) (a r : ℝ) {k : ℕ}
    (h1 : (fseq ν x a k).1 ≤ max r a) (h2 : max r a < (fseq ν x a (k + 1)).1) :
    fwdTraj hν x a r = (fseq ν x a k).2 := by
  have hmono := fseq_strictMono hν x a
  simp only [fwdTraj, fwdReal, fwdTrajFn_eq_fwdPath hν x a]
  have e : a + ((r - a).toNNReal : ℝ) = max r a := by
    rw [Real.coe_toNNReal', max_comm]; ring_nf
    rw [max_comm]; simp [max_def]; split_ifs <;> linarith
  exact fwdPath_eq hmono (by rw [e]; exact h1) (by rw [e]; exact h2)

theorem exists_block (hν : Good ν) (x : Fin d → ℤ) (a r : ℝ) :
    ∃ k, (fseq ν x a k).1 ≤ max r a ∧ max r a < (fseq ν x a (k + 1)).1 := by
  classical
  have hex : ∃ k, max r a < (fseq ν x a (k + 1)).1 := by
    obtain ⟨k, hk⟩ := fseq_unbounded hν x a (max r a)
    have hm := fseq_strictMono hν x a
    cases k with
    | zero => exact ⟨0, by simpa using lt_of_lt_of_le hk (hm.monotone (Nat.zero_le 1))⟩
    | succ k => exact ⟨k, hk⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  cases h : Nat.find hex with
  | zero => simp [fseq]
  | succ k =>
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    exact not_lt.mp this

end ElboimSly.Cyclic

end
