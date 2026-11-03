/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.ForwardPath
public import ElboimSly.Frozen.Defs.IsBackwardTrajectory
import Mathlib

/-!
# Piecewise constant backward paths

Existence and uniqueness of trajectories (backward construction). A piecewise constant path with value `z k` for
`s ∈ (b - t k, b - t (k+1)]`, where the times `t k` are strictly decreasing and unbounded below,
`t 0 > b` and `t 1 ≤ b`, and the swap rule holds at each `t (k+1)`, is a backward `ν`-path.
Here `η s` is the position at time `b - s`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal Classical

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The piecewise constant path with value `z k` at `s` with `b - t k < s ≤ b - t (k+1)`. -/
noncomputable def bwdPath (b : ℝ) (t : ℕ → ℝ) (z : ℕ → Fin d → ℤ) (s : ℝ≥0) : Fin d → ℤ :=
  if h : ∃ k, (s : ℝ) ≤ b - t (k + 1) then z (Nat.find h) else z 0

section

variable {b : ℝ} {t : ℕ → ℝ} {z : ℕ → Fin d → ℤ}

theorem bwdPath_eq (ht : StrictAnti t) {s : ℝ≥0} {k : ℕ} (h1 : b - t k < s)
    (h2 : (s : ℝ) ≤ b - t (k + 1)) : bwdPath b t z s = z k := by
  have h : ∃ k, (s : ℝ) ≤ b - t (k + 1) := ⟨k, h2⟩
  simp only [bwdPath, h, ↓reduceDIte]
  congr 1
  refine (Nat.find_eq_iff h).mpr ⟨h2, fun m hm => not_le.mpr ?_⟩
  have := ht.antitone (by omega : m + 1 ≤ k)
  linarith

theorem bwd_exists_block (_ht : StrictAnti t) (ht0 : b < t 0) (hun : ∀ T, ∃ k, t k < T)
    (s : ℝ≥0) : ∃ k, b - t k < s ∧ (s : ℝ) ≤ b - t (k + 1) := by
  have h : ∃ k, (s : ℝ) ≤ b - t (k + 1) := by
    obtain ⟨k', hk'⟩ := hun (b - s)
    rcases k' with _ | k
    · linarith [s.coe_nonneg]
    · exact ⟨k, by linarith⟩
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  rcases hk : Nat.find h with _ | m
  · linarith [s.coe_nonneg]
  · have := Nat.find_min h (show m < Nat.find h by omega)
    exact not_le.mp this

theorem bwdPath_leftCont (ht : StrictAnti t) (ht0 : b < t 0) (hun : ∀ T, ∃ k, t k < T)
    (s : ℝ≥0) : ∀ᶠ u in 𝓝[≤] s, bwdPath b t z u = bwdPath b t z s := by
  obtain ⟨k, h1, h2⟩ := bwd_exists_block ht ht0 hun s
  have hev := ev_coe_gt h1
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin (a := s) (s := Set.Iic s)]
    with u hu hu'
  have hsu : (u : ℝ) ≤ s := NNReal.coe_le_coe.mpr hu'
  rw [bwdPath_eq ht (k := k) hu (by linarith), bwdPath_eq ht h1 h2]

/-- The right limit of `bwdPath` at `s` on a block. -/
theorem bwdPath_isRightLimit (ht : StrictAnti t) {s : ℝ≥0} {k : ℕ} (h1 : b - t k ≤ s)
    (h2 : (s : ℝ) < b - t (k + 1)) : IsRightLimit (bwdPath b t z) s (z k) := by
  have hev := ev_coe_lt h2
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin (a := s) (s := Set.Ioi s)]
    with u hu hu'
  have hsu : (s : ℝ) < u := NNReal.coe_lt_coe.mpr hu'
  exact bwdPath_eq ht (by linarith) hu.le

theorem bwd_exists_block_right (ht : StrictAnti t) (ht0 : b < t 0) (hun : ∀ T, ∃ k, t k < T)
    (s : ℝ≥0) :
    (∃ k, b - t k < s ∧ (s : ℝ) < b - t (k + 1)) ∨ ∃ k, (s : ℝ) = b - t (k + 1) := by
  obtain ⟨k, h1, h2⟩ := bwd_exists_block ht ht0 hun s
  rcases eq_or_lt_of_le h2 with h | h
  · exact Or.inr ⟨k, h⟩
  · exact Or.inl ⟨k, h1, h⟩

theorem bwdPath_rightLimit_exists (ht : StrictAnti t) (ht0 : b < t 0)
    (hun : ∀ T, ∃ k, t k < T) (s : ℝ≥0) : ∃ w, IsRightLimit (bwdPath b t z) s w := by
  rcases bwd_exists_block_right ht ht0 hun s with ⟨k, h1, h2⟩ | ⟨k, h⟩
  · exact ⟨_, bwdPath_isRightLimit ht h1.le h2⟩
  · exact ⟨_, bwdPath_isRightLimit ht (k := k + 1) h.ge
      (by linarith [ht (Nat.lt_succ_self (k + 1))])⟩

theorem bwdPath_jump_time (ht : StrictAnti t) (ht0 : b < t 0) (hun : ∀ T, ∃ k, t k < T)
    {s : ℝ≥0} {w : Fin d → ℤ} (hw : IsRightLimit (bwdPath b t z) s w)
    (hne : w ≠ bwdPath b t z s) : ∃ k, (s : ℝ) = b - t (k + 1) := by
  rcases bwd_exists_block_right ht ht0 hun s with ⟨k, h1, h2⟩ | h
  · exact absurd ((IsRightLimit.unique hw (bwdPath_isRightLimit ht h1.le h2)).trans
      (bwdPath_eq ht h1 h2.le).symm) hne
  · exact h

omit [Fact (0 < β)] in
theorem bwdPath_isBackwardPath (hν : Good ν) (ht : StrictAnti t) (ht0 : b < t 0)
    (hun : ∀ T, ∃ k, t k < T)
    (hgap : ∀ k u, t (k + 1) < u → u < t k → ¬ RingAt ν (z k) u)
    (hsw : ∀ k, SwapRule ν (t (k + 1)) (z k) (z (k + 1))) :
    IsBackwardPath ν b (bwdPath b t z) := by
  refine ⟨bwdPath_leftCont ht ht0 hun, bwdPath_rightLimit_exists ht ht0 hun, fun T => ?_,
    fun s w hw => ?_⟩
  · obtain ⟨N, hN⟩ := hun (b - T)
    refine ((Set.finite_lt_nat N).image (fun k : ℕ => (b - t (k + 1)).toNNReal)).subset ?_
    rintro s ⟨hsT, w, hw, hne⟩
    obtain ⟨k, hk⟩ := bwdPath_jump_time ht ht0 hun hw hne
    have hsT' : (s : ℝ) ≤ T := NNReal.coe_le_coe.mpr hsT
    have hkN : k + 1 < N := ht.lt_iff_gt.mp (by linarith)
    refine ⟨k, (by show k < N; omega), ?_⟩
    simp only
    rw [← hk, Real.toNNReal_coe]
  · rcases bwd_exists_block_right ht ht0 hun s with ⟨k, h1, h2⟩ | ⟨k, h⟩
    · rw [IsRightLimit.unique hw (bwdPath_isRightLimit ht h1.le h2), bwdPath_eq ht h1 h2.le]
      exact swapRule_self (hgap k _ (by linarith) (by linarith [(NNReal.coe_nonneg s)]))
    · have hk : b - t k < s := by
        have := ht (Nat.lt_succ_self k); linarith
      have h3 := bwdPath_isRightLimit (z := z) ht (k := k + 1) h.ge
        (by linarith [ht (Nat.lt_succ_self (k + 1))])
      rw [IsRightLimit.unique hw h3, bwdPath_eq ht hk h.le, show b - (s : ℝ) = t (k + 1) by linarith]
      exact SwapRule.symm hν (hsw k)

end

end ElboimSly.Interchange
