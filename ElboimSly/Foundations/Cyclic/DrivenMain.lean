/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenClosing
public import ElboimSly.Foundations.Cyclic.DrivenMeas
public import ElboimSly.Foundations.Cyclic.DrivenWd
public import ElboimSly.Foundations.Cyclic.DrivenCf
import Mathlib

/-!
# The driven construction: main statements

Closing for the driven walk (closing for the driven walk), and
Well-definedness and measurability of the driven construction (b): `ℱ_t`-measurability of `w^X(t ∧ treg^X)` and `{treg^X ≤ t}`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {x y : ℝ≥0 → Fin d → ℤ} {β : ℝ≥0}

/-- The driven walk is a solution of (D1)--(D3) up to its closing time. -/
theorem drivenSol (hx : IsRegPath x) (hβ : 0 < β) : DrivenSol β x (drivenWalk β x) :=
  ⟨hβ, drivenWalk_isRegPath hx hβ, drivenWalk_zero hx hβ,
    fun _ ht _ => drivenWalk_D123 hx hβ ht⟩

/-- **Closing for the driven walk**, parts (a)--(e).  Let `x` be a driving path satisfying
condition (i) of `CycCF`, `w = w^x`, `τ = treg^x`.
(a) every jump of `w` at a time `t ≤ τ` is a (D2) jump (then `x` jumps at `t` and `w` has no jump in
`t - βℤ_{≥1}`) or a (D1) jump across the same edge as the jump at `t - kβ`; the jumps of `w` at two
times of one class cross one edge; a jump with no earlier jump in its class is a (D2) jump; and
(D1) never applies at a jump time of `x`.
(b) `w(s) ≠ w(s')` and `w(s-) ≠ w(s'-)` for `s - s' ∈ βℤ_{≥1}`.
(c) at most one `k` satisfies the condition of (D1).
(d) each class contains at most two jumps of `w` in `(0, t]`, `t ≤ τ`, one from each endpoint of its
edge.
(e) neither the precedence of (D1) over (D2) nor the least-index convention is ever used. -/
theorem drivenWalk_closing (hx : IsDrivingPath x) (hβ : 0 < β)
    (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β) :
    -- (a)
    (∀ t : ℝ≥0, t ∈ CDisc (drivenWalk β x) → (t : ℝ≥0∞) ≤ drivenTreg β x →
      (t ∈ CDisc x ∧ ∀ k, IsDelayIdx β t k → t - k * β ∉ CDisc (drivenWalk β x)) ∨
      (∃ k, IsDelayIdx β t k ∧ t - k * β ∈ CDisc (drivenWalk β x) ∧
        drivenWalk β x t = leftVal (drivenWalk β x) (t - k * β) ∧
        leftVal (drivenWalk β x) t = drivenWalk β x (t - k * β))) ∧
    (∀ (t : ℝ≥0) (k : ℕ), t ∈ CDisc (drivenWalk β x) → t + k * β ∈ CDisc (drivenWalk β x) →
      ((t + k * β : ℝ≥0) : ℝ≥0∞) ≤ drivenTreg β x →
      ({leftVal (drivenWalk β x) (t + k * β), drivenWalk β x (t + k * β)} :
          Set (Fin d → ℤ)) =
        {leftVal (drivenWalk β x) t, drivenWalk β x t}) ∧
    (∀ t : ℝ≥0, t ∈ CDisc (drivenWalk β x) → (t : ℝ≥0∞) ≤ drivenTreg β x →
      (∀ k, IsDelayIdx β t k → t - k * β ∉ CDisc (drivenWalk β x)) → t ∈ CDisc x) ∧
    (∀ t : ℝ≥0, t ∈ CDisc x → (t : ℝ≥0∞) ≤ drivenTreg β x →
      ∀ k, ¬ ForcedAt β (drivenWalk β x) t k) ∧
    -- (b)
    (∀ (s s' : ℝ≥0) (k : ℕ), 1 ≤ k → s = s' + k * β → (s : ℝ≥0∞) < drivenTreg β x →
      drivenWalk β x s ≠ drivenWalk β x s') ∧
    (∀ (s s' : ℝ≥0) (k : ℕ), 0 < s' → 1 ≤ k → s = s' + k * β → (s : ℝ≥0∞) ≤ drivenTreg β x →
      leftVal (drivenWalk β x) s ≠ leftVal (drivenWalk β x) s') ∧
    -- (c)
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ drivenTreg β x → ∀ k1 k2 : ℕ,
      ForcedAt β (drivenWalk β x) t k1 → ForcedAt β (drivenWalk β x) t k2 → k1 = k2) ∧
    -- (d)
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ drivenTreg β x → ∀ t0 : ℝ≥0,
      {s : ℝ≥0 | s ∈ CDisc (drivenWalk β x) ∧ s ≤ t ∧ ∃ j : ℤ, (s : ℝ) = t0 + j * β}.ncard
        ≤ 2) ∧
    (∀ (s s' : ℝ≥0) (k : ℕ), s ∈ CDisc (drivenWalk β x) → 1 ≤ k → s' = s + k * β →
      (s' : ℝ≥0∞) ≤ drivenTreg β x →
      leftVal (drivenWalk β x) s' ≠ leftVal (drivenWalk β x) s) ∧
    -- (e)
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ drivenTreg β x →
      (t ∈ CDisc x → ∀ k, ¬ ForcedAt β (drivenWalk β x) t k) ∧
      ∀ k1 k2 : ℕ, ForcedAt β (drivenWalk β x) t k1 → ForcedAt β (drivenWalk β x) t k2 →
        k1 = k2) := by
  have S := drivenSol hx.toIsRegPath hβ
  exact ⟨fun _ hj ht => S.closing_a_cases hi hj ht,
    fun _ _ ht ht' hτ => S.edge_eq hi ht ht' hτ,
    fun _ hj ht hno => S.closing_a_earliest hi hj ht hno,
    fun _ hxt ht k => S.closing_a_no_forced hi hxt ht k,
    fun _ _ _ hk hs hτ => S.closing_b_ne hi hk hs hτ,
    fun _ _ _ hs' hk hs hτ => S.closing_b_left_ne hi hs' hk hs hτ,
    fun _ ht _ _ h1 h2 => S.closing_c hi ht h1 h2,
    fun _ ht t0 => S.closing_d_card hi ht t0,
    fun _ _ _ hs hk hs' hτ => S.closing_d_endpoints hi hs hk hs' hτ,
    fun _ ht => S.closing_e hi ht⟩

/-! ### `ℱ_t`-measurability -/

/-- Truncation of a path at time `t`. -/
def stopPath (x : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : ℝ≥0 → Fin d → ℤ := fun s => x (min s t)

theorem stopPath_isRegPath (hx : IsRegPath x) (t : ℝ≥0) : IsRegPath (stopPath x t) := by
  refine ⟨fun s => ?_, fun T => ?_⟩
  · rcases lt_or_ge s t with hst | hst
    · filter_upwards [hx.rc s, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hst)] with u hu hut
      have h1 : min u t = u := min_eq_left (le_of_lt hut)
      have h2 : min s t = s := min_eq_left hst.le
      simp only [stopPath, h1, h2]
      exact hu
    · filter_upwards [self_mem_nhdsWithin (s := Set.Ici s)] with u hu
      simp only [stopPath, min_eq_right (hst.trans hu), min_eq_right hst]
  · refine (hx.fin T).subset fun s hs => ?_
    have hst : s ≤ t := by
      by_contra hlt
      rw [not_le] at hlt
      apply hs.1.2
      filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
      simp only [stopPath, min_eq_right hu.1.le, min_eq_right hlt.le]
    refine ⟨(mem_CDisc_congr (fun u hu => ?_)).1 hs.1, hs.2⟩
    simp only [stopPath, min_eq_left (hu.trans hst)]

end ElboimSly.Cyclic

end
