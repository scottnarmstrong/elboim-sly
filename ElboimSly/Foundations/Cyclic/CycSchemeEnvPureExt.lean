/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvCore
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFront
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvCur
public import ElboimSly.Foundations.Cyclic.CycSchemeRegion
public import ElboimSly.Foundations.Cyclic.CycLines
public import Mathlib

/-!
# The records of the scheme extend each other, for every history

The environment scheme of a plan; Several walks explored one after another (b). "Each record `ρ_{j+1}` of the
environment scheme is `ρ_j` (if ended), or `ρ_j` with its last entry replaced by an entry of which it
is an initial piece, possibly followed by a new entry of length `0`." This is a property of the pure
update, true for *every* history, not only on the good event of the environment scheme (b)
(`CycScheme.extends_upd`, `CycScheme.extends_stateAt`). It is what makes the limit map of
Measurability of record functionals (e) applicable to `η ↦ ρ_j(η)` on all of `ℋ_∞`.

The point is the step with `s* = 0`: there the update must not move the path, which holds because
`h_fr > 0` for a finite record (the clock values of its rings are finite) and a fresh event needs
`0 < r' ≤ h`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

theorem CPath.jt_zero_eq {V : Type*} (p : CPath V) : p.jt 0 = 0 :=
  le_antisymm ((p.jt_le_iff 0 0).2 (Nat.zero_le _)) bot_le

theorem CPath.left_zero_eq_fn (p : CPath (Fin d → ℤ)) : p.left 0 = p.fn 0 := by
  rw [CPath.left_zero]
  unfold CPath.jv
  rw [CPath.jt_zero_eq]
  rfl

/-- Extending by the current value does not change the value at the current time. -/
theorem CPath.extVal_self (p : CPath (Fin d → ℤ)) (hp : p.UnitJumps) (T : ℝ≥0) :
    p.extVal T (p.fn T) = p.fn T := by
  classical
  unfold CPath.extVal
  by_cases hT : 0 < T
  · by_cases hd : T ∈ CDisc p.fn
    · have := hp T hd
      rw [ite_eq_left ⟨hT, this⟩]
    · rw [p.left_eq_fn_of_notMem hT hd]
      simp
  · have : T = 0 := le_antisymm (not_lt.1 hT) bot_le
    subst this
    rw [ite_eq_right (by simp), p.left_zero_eq_fn]

/-- Extending a path of length `t₀` by `s` is an extension of it, if the new value is the current
one when `s = 0`. -/
theorem CPath.isPiece_extend (p : CPath (Fin d → ℤ)) (hp : p.UnitJumps) {t₀ s : ℝ≥0}
    (hlen : p.len = t₀) {v : Fin d → ℤ} (hv : s = 0 → v = p.fn t₀) :
    p.IsPiece (p.extend (t₀ + s) v) := by
  refine ⟨?_, ?_⟩
  · rw [CPath.extend_len, hlen]; exact_mod_cast le_self_add
  · refine CPath.ext' (by rw [CPath.cut_len]) (funext fun t => ?_)
    rw [CPath.cut_fn]
    have h1 := congrArg (fun q : CPath (Fin d → ℤ) => q.fn t) (CPath.cut_len_self p)
    simp only [CPath.cut_fn] at h1
    rw [← h1]
    set t' := (min (t : ℝ≥0∞) p.len).toNNReal with ht'
    have ht'le : t' ≤ t₀ := by
      rw [ht']
      have : min (t : ℝ≥0∞) p.len ≤ p.len := min_le_right _ _
      rw [hlen] at this ⊢
      exact ENNReal.toNNReal_mono ENNReal.coe_ne_top this
    by_cases hlt : t' < t₀ + s
    · rw [CPath.extend_fn_of_lt _ _ _ hlt]
    · have hs : s = 0 := by
        by_contra hs0
        exact hlt (lt_of_le_of_lt ht'le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hs0)))
      subst hs
      have hteq : t' = t₀ := le_antisymm ht'le (by simpa using not_lt.1 hlt)
      have hv' := hv rfl
      subst hv'
      rw [CPath.extend_fn_of_le _ _ _ (not_lt.1 hlt), add_zero, hteq]
      exact (p.extVal_self hp t₀).symm

end ElboimSly.Cyclic

end
