/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.BwdMeas
import Mathlib

/-!
# The backward trajectory is the iterated backward jump sequence, and is measurable

Measurability, Step 3.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The starting gap time `c ∈ (b, b + 1]` at which `y` does not ring on `(b, c)`. -/
noncomputable def bstart (ν : Measure (RingSpace d β)) (y : Fin d → ℤ) (b : ℝ) : ℝ :=
  min (stepT ν y b) (b + 1)

/-- The iterated backward jump sequence. -/
noncomputable def bseq (ν : Measure (RingSpace d β)) (y : Fin d → ℤ) (b : ℝ) :
    ℕ → ℝ × (Fin d → ℤ)
  | 0 => (bstart ν y b, y)
  | k + 1 => (bstepT ν (bseq ν y b k).2 (bseq ν y b k).1,
      bstepW ν (bseq ν y b k).2 (bseq ν y b k).1)

theorem bseq_gap (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) :
    b < bstart ν y b ∧ bstart ν y b ≤ b + 1 ∧
      ∀ u, b < u → u < bstart ν y b → ¬ RingAt ν y u := by
  obtain ⟨h1, h2, -, -⟩ := step_spec hν y b
  refine ⟨lt_min h1 (by linarith), min_le_right _ _, fun u hu hu' hr => ?_⟩
  exact h2 u hu (lt_of_lt_of_le hu' (min_le_left _ _)) hr

theorem bwdSeq_bseq (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) :
    BwdSeq ν b y (fun k => (bseq ν y b k).1) (fun k => (bseq ν y b k).2) := by
  obtain ⟨hbc, hcb, hc⟩ := bseq_gap hν y b
  refine ⟨hbc, ?_, rfl, fun k => (bstep_spec hν _ _).1, fun k => (bstep_spec hν _ _).2.1,
    fun k => (bstep_spec hν _ _).2.2.1, fun k => ?_⟩
  · obtain ⟨h1, -, -, h4⟩ := bstep_spec hν y (bstart ν y b)
    show bstepT ν y (bstart ν y b) ≤ b
    rcases h4 with ⟨e, he, her⟩ | ⟨h, -, -⟩
    · by_contra hlt
      exact hc _ (not_le.mp hlt) h1 ⟨e, by
        unfold Edge.Mem; rw [he]; exact Sym2.mem_mk_left _ _, her⟩
    · linarith
  · rcases (bstep_spec hν (bseq ν y b k).2 (bseq ν y b k).1).2.2.2 with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩

theorem bwdTrajFn_eq_bwdPath (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) :
    bwdTrajFn hν y b = bwdPath b (fun k => (bseq ν y b k).1) (fun k => (bseq ν y b k).2) := by
  have h := bwdSeq_bseq hν y b
  have hun := h.unbounded hν
  symm
  refine bwdTrajFn_eq hν ⟨bwdPath_isBackwardPath hν h.strictAnti h.t_zero hun h.gap h.swap, ?_⟩
  rw [bwdPath_eq (k := 0) h.strictAnti (by simpa using h.t_zero) (by simpa using h.t_one)]
  exact h.z_zero

theorem bwdTraj_eq_bseq (hν : Good ν) (y : Fin d → ℤ) (b r : ℝ) {k : ℕ}
    (h1 : (bseq ν y b (k + 1)).1 ≤ min r b) (h2 : min r b < (bseq ν y b k).1) :
    bwdTraj hν y b r = (bseq ν y b k).2 := by
  have hanti := (bwdSeq_bseq hν y b).strictAnti
  simp only [bwdTraj, bwdReal, bwdTrajFn_eq_bwdPath hν y b]
  have e : (((b - r).toNNReal : ℝ≥0) : ℝ) = b - min r b := by
    rw [Real.coe_toNNReal']
    rcases le_total r b with h | h
    · rw [max_eq_left (by linarith), min_eq_left h]
    · rw [max_eq_right (by linarith), min_eq_right h]; ring
  exact bwdPath_eq hanti (by rw [e]; linarith) (by rw [e]; linarith)

theorem exists_bblock (hν : Good ν) (y : Fin d → ℤ) (b r : ℝ) :
    ∃ k, (bseq ν y b (k + 1)).1 ≤ min r b ∧ min r b < (bseq ν y b k).1 := by
  classical
  have hs := bwdSeq_bseq hν y b
  have hex : ∃ k, (bseq ν y b (k + 1)).1 ≤ min r b := by
    obtain ⟨k, hk⟩ := hs.unbounded hν (min r b)
    cases k with
    | zero =>
      exfalso
      have := hs.t_zero
      have h2 := min_le_right r b
      linarith
    | succ k => exact ⟨k, hk.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  cases h : Nat.find hex with
  | zero => exact lt_of_le_of_lt (min_le_right _ _) hs.t_zero
  | succ k =>
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    exact not_le.mp this

end ElboimSly.Cyclic

end
