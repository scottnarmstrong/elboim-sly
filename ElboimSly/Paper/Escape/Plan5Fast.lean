/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5Meas
public import ElboimSly.Paper.Heavy.Attained
public import Mathlib

/-!
# Condition (3) between two events

The walks W_i and the stopping times tau_i: "between events the running window maximum is constant, while the
threshold `ln² max(t, ln β)` is continuous and nondecreasing in `t`, so (3) can first hold only at
an event".  Pathwise form: if a cyclic path `w₂` agrees with `w₁` on `[0, ς]` and is constant on
`[ς, t]`, and `τ_fast(w₁; L₁) > ς`, `L₁ ≤ L₂`, then `τ_fast(w₂; L₂) > t`.
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

theorem lt_pathTfast_of_const {w₁ w₂ : ℝ → Fin d → ℤ} (hw₁ : IsCyclicPath w₁)
    (hw₂ : IsCyclicPath w₂) {ς t L₁ L₂ : ℝ} (hς : 0 ≤ ς) (hςt : ς ≤ t) (hL₁ : 0 < L₁)
    (hL : L₁ ≤ L₂) (hag : ∀ x, 0 ≤ x → x ≤ ς → w₁ x = w₂ x)
    (hconst : ∀ x, ς ≤ x → x ≤ t → w₂ x = w₂ ς)
    (H : ENNReal.ofReal ς < pathTfast w₁ L₁) : ENNReal.ofReal t < pathTfast w₂ L₂ := by
  have hL₂ : 0 < L₂ := lt_of_lt_of_le hL₁ hL
  rw [ofReal_lt_pathTfast_iff hw₁ hL₁] at H
  rw [ofReal_lt_pathTfast_iff hw₂ hL₂]
  intro t' ht'0 ht't s hs1 hs2
  rcases le_or_gt t' ς with h1 | h1
  · have hmax : max s 0 ≤ ς := max_le (hs2.trans h1) hς
    rw [← hag t' ht'0.le h1, ← hag (max s 0) (le_max_right _ _) hmax]
    exact (H t' ht'0 h1 s hs1 hs2).trans_le hL
  · rw [hconst t' h1.le ht't]
    rcases le_or_gt s ς with h2 | h2
    · have hmax : max s 0 ≤ ς := max_le h2 hς
      rw [← hag (max s 0) (le_max_right _ _) hmax]
      rcases hς.eq_or_lt with h0 | h0
      · subst h0
        have hs0 : max s 0 = 0 := le_antisymm (max_le h2 le_rfl) (le_max_right _ _)
        rw [hs0, hag 0 le_rfl le_rfl]
        simpa using hL₂
      · have := H ς h0 le_rfl s (by linarith) h2
        rw [hag ς hς le_rfl] at this
        exact this.trans_le hL
    · have hs3 : w₂ (max s 0) = w₂ ς := by
        rw [max_eq_left (by linarith)]
        exact hconst s h2.le (hs2.trans ht't)
      rw [hs3]
      simpa using hL₂

end ElboimSly.Paper.Escape
