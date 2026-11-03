/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.Swap
public import ElboimSly.Frozen.Defs.IsForwardTrajectory
import Mathlib

/-!
# Piecewise constant forward paths

Existence and uniqueness of trajectories (construction). A piecewise constant path with values `z k` on
`[t k, t (k+1))`, where the times `t k` are strictly increasing and unbounded and the swap rule
holds at each `t (k+1)`, is a forward `ν`-path. Here `γ s` is the position at time `a + s`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal Classical

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The piecewise constant path with value `z k` at times `a + s ∈ [t k, t (k+1))`. -/
noncomputable def fwdPath (a : ℝ) (t : ℕ → ℝ) (z : ℕ → Fin d → ℤ) (s : ℝ≥0) : Fin d → ℤ :=
  if h : ∃ k, a + s < t (k + 1) then z (Nat.find h) else z 0

section

variable {a : ℝ} {t : ℕ → ℝ} {z : ℕ → Fin d → ℤ}

theorem fwdPath_eq (ht : StrictMono t) {s : ℝ≥0} {k : ℕ} (h1 : t k ≤ a + s)
    (h2 : a + s < t (k + 1)) : fwdPath a t z s = z k := by
  have h : ∃ k, a + s < t (k + 1) := ⟨k, h2⟩
  simp only [fwdPath, h, ↓reduceDIte]
  congr 1
  refine (Nat.find_eq_iff h).mpr ⟨h2, fun m hm => not_lt.mpr ?_⟩
  exact (ht.monotone (by omega : m + 1 ≤ k)).trans h1

theorem exists_block (_ht : StrictMono t) (ht0 : t 0 = a) (hun : ∀ T, ∃ k, T < t k) (s : ℝ≥0) :
    ∃ k, t k ≤ a + s ∧ a + s < t (k + 1) := by
  have h : ∃ k, a + s < t (k + 1) := by
    obtain ⟨k', hk'⟩ := hun (a + s)
    rcases k' with _ | k
    · rw [ht0] at hk'; linarith [s.coe_nonneg]
    · exact ⟨k, hk'⟩
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  rcases hk : Nat.find h with _ | m
  · rw [ht0]; linarith [s.coe_nonneg]
  · have := Nat.find_min h (show m < Nat.find h by omega)
    exact not_lt.mp this

theorem ev_coe_lt {s : ℝ≥0} {c : ℝ} (h : (s : ℝ) < c) : ∀ᶠ u : ℝ≥0 in 𝓝 s, (u : ℝ) < c :=
  (NNReal.continuous_coe.tendsto s).eventually (gt_mem_nhds h)

theorem ev_coe_gt {s : ℝ≥0} {c : ℝ} (h : c < (s : ℝ)) : ∀ᶠ u : ℝ≥0 in 𝓝 s, c < (u : ℝ) :=
  (NNReal.continuous_coe.tendsto s).eventually (lt_mem_nhds h)

theorem fwdPath_rightCont (ht : StrictMono t) (ht0 : t 0 = a) (hun : ∀ T, ∃ k, T < t k)
    (s : ℝ≥0) : ∀ᶠ u in 𝓝[≥] s, fwdPath a t z u = fwdPath a t z s := by
  obtain ⟨k, h1, h2⟩ := exists_block ht ht0 hun s
  have hev := ev_coe_lt (show (s : ℝ) < t (k + 1) - a by linarith)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin (a := s) (s := Set.Ici s)]
    with u hu hu'
  have hsu : (s : ℝ) ≤ u := NNReal.coe_le_coe.mpr hu'
  rw [fwdPath_eq ht (k := k) (by linarith) (by linarith), fwdPath_eq ht h1 h2]

/-- The left limit of `fwdPath` at `s` on a block. -/
theorem fwdPath_isLeftLimit (ht : StrictMono t) (_ht0 : t 0 = a) (_hun : ∀ T, ∃ k, T < t k)
    {s : ℝ≥0} {k : ℕ} (h1 : t k < a + s) (h2 : a + s ≤ t (k + 1)) :
    IsLeftLimit (fwdPath a t z) s (z k) := by
  have hev := ev_coe_gt (show t k - a < (s : ℝ) by linarith)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin (a := s) (s := Set.Iio s)]
    with u hu hu'
  have hsu : (u : ℝ) < s := NNReal.coe_lt_coe.mpr hu'
  exact fwdPath_eq ht (by linarith) (by linarith)

/-- Dichotomy for the position of `a + s` relative to the break times. -/
theorem exists_block_left (ht : StrictMono t) (ht0 : t 0 = a) (hun : ∀ T, ∃ k, T < t k)
    {s : ℝ≥0} (hs : 0 < s) :
    (∃ k, t k < a + s ∧ a + s < t (k + 1)) ∨ ∃ k, a + s = t (k + 1) := by
  obtain ⟨k, h1, h2⟩ := exists_block ht ht0 hun s
  rcases eq_or_lt_of_le h1 with h | h
  · right
    rcases k with _ | m
    · rw [ht0] at h
      have : (s : ℝ) = 0 := by linarith
      exact absurd (NNReal.coe_eq_zero.mp this) hs.ne'
    · exact ⟨m, h.symm⟩
  · exact Or.inl ⟨k, h, h2⟩

theorem fwdPath_leftLimit_exists (ht : StrictMono t) (ht0 : t 0 = a) (hun : ∀ T, ∃ k, T < t k)
    {s : ℝ≥0} (hs : 0 < s) : ∃ w, IsLeftLimit (fwdPath a t z) s w := by
  rcases exists_block_left ht ht0 hun hs with ⟨k, h1, h2⟩ | ⟨k, h⟩
  · exact ⟨_, fwdPath_isLeftLimit ht ht0 hun h1 h2.le⟩
  · exact ⟨_, fwdPath_isLeftLimit ht ht0 hun (k := k) (by linarith [ht (Nat.lt_succ_self k)])
      h.le⟩

theorem fwdPath_jump_time (ht : StrictMono t) (ht0 : t 0 = a) (hun : ∀ T, ∃ k, T < t k)
    {s : ℝ≥0} (hs : 0 < s) {w : Fin d → ℤ} (hw : IsLeftLimit (fwdPath a t z) s w)
    (hne : w ≠ fwdPath a t z s) : ∃ k, a + s = t (k + 1) := by
  rcases exists_block_left ht ht0 hun hs with ⟨k, h1, h2⟩ | h
  · exact absurd ((IsLeftLimit.unique hs hw (fwdPath_isLeftLimit ht ht0 hun h1 h2.le)).trans
      (fwdPath_eq ht h1.le h2).symm) hne
  · exact h

omit [Fact (0 < β)] in
theorem fwdPath_isForwardPath (ht : StrictMono t) (ht0 : t 0 = a) (hun : ∀ T, ∃ k, T < t k)
    (hgap : ∀ k u, t k < u → u < t (k + 1) → ¬ RingAt ν (z k) u)
    (hsw : ∀ k, SwapRule ν (t (k + 1)) (z k) (z (k + 1))) :
    IsForwardPath ν a (fwdPath a t z) := by
  refine ⟨fwdPath_rightCont ht ht0 hun, fun s hs => fwdPath_leftLimit_exists ht ht0 hun hs,
    fun T => ?_, fun s hs w hw => ?_⟩
  · obtain ⟨N, hN⟩ := hun (a + T)
    refine ((Set.finite_lt_nat N).image (fun k : ℕ => (t (k + 1) - a).toNNReal)).subset ?_
    rintro s ⟨hs, hsT, w, hw, hne⟩
    obtain ⟨k, hk⟩ := fwdPath_jump_time ht ht0 hun hs hw hne
    have hsT' : (s : ℝ) ≤ T := NNReal.coe_le_coe.mpr hsT
    have hkN : k + 1 < N := ht.lt_iff_lt.mp (by linarith)
    refine ⟨k, (by show k < N; omega), ?_⟩
    simp only
    rw [← show (s : ℝ) = t (k + 1) - a by linarith, Real.toNNReal_coe]
  · rcases exists_block_left ht ht0 hun hs with ⟨k, h1, h2⟩ | ⟨k, h⟩
    · rw [IsLeftLimit.unique hs hw (fwdPath_isLeftLimit ht ht0 hun h1 h2.le), fwdPath_eq ht h1.le h2]
      exact swapRule_self (hgap k _ h1 h2)
    · have hk : t k < a + s := by linarith [ht (Nat.lt_succ_self k)]
      rw [IsLeftLimit.unique hs hw (fwdPath_isLeftLimit ht ht0 hun hk h.le), h,
        fwdPath_eq ht (k := k + 1) h.ge (by linarith [ht (Nat.lt_succ_self (k + 1))])]
      exact hsw k

end

end ElboimSly.Interchange
