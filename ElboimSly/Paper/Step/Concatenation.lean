/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Concatenation of paths

Concatenation (ES22 §7, ES22 §7).

For paths `w₁ : [0, s₁] → ℤ^d` and `w₂ : [0, s₂] → ℤ^d` with `w₂(0) = 0`, the concatenation
`w₁ ⌢ w₂ : [0, s₁ + s₂] → ℤ^d` is `w₁(s)` for `s ≤ s₁` and `w₁(s₁) + w₂(s - s₁)` for
`s₁ ≤ s ≤ s₁ + s₂`.  The same formula with `s₂ = ∞` defines `w₁ ⌢ w₂` on `[0, ∞)`.

Paths on `[0, s]` are represented by functions `ℝ≥0 → V`, of which only the values on `[0, s]`
are used; `stepCat s₁ w₁ w₂` is the concatenation, and agrees with the written proof's on
`[0, s₁ + s₂]` (and on `[0, ∞)` when `w₂` is a path on `[0, ∞)`).  `stepCatList` is the iterated
concatenation `w₁ ⌢ ⋯ ⌢ w_ℓ`, defined recursively as in the written proof; `stepCat_assoc` shows
that the bracketing is immaterial.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ElboimSly.Paper

variable {V : Type*}

section Add

variable [Add V]

open Classical in
/-- Concatenation: the concatenation `w₁ ⌢ w₂` of `w₁` on `[0, s₁]` and
`w₂` (with `w₂(0) = 0`). -/
noncomputable def stepCat (s₁ : ℝ≥0) (w₁ w₂ : ℝ≥0 → V) : ℝ≥0 → V :=
  fun s => if s ≤ s₁ then w₁ s else w₁ s₁ + w₂ (s - s₁)

theorem stepCat_of_le {s₁ s : ℝ≥0} (w₁ w₂ : ℝ≥0 → V) (h : s ≤ s₁) :
    stepCat s₁ w₁ w₂ s = w₁ s := by
  simp [stepCat, h]

/-- Away from the junction the second summand is `w₁(s₁) + w₂(s - s₁)`. -/
theorem stepCat_of_gt {s₁ s : ℝ≥0} (w₁ w₂ : ℝ≥0 → V) (h : s₁ < s) :
    stepCat s₁ w₁ w₂ s = w₁ s₁ + w₂ (s - s₁) := by
  simp [stepCat, not_le.2 h]

end Add

/-- Associativity: `(w₁ ⌢ w₂) ⌢ w₃ = w₁ ⌢ (w₂ ⌢ w₃)`, for `w₂` starting at `0`. -/
theorem stepCat_assoc [AddMonoid V] (s₁ s₂ : ℝ≥0) (w₁ w₂ w₃ : ℝ≥0 → V) (h0 : w₂ 0 = 0) :
    stepCat (s₁ + s₂) (stepCat s₁ w₁ w₂) w₃ = stepCat s₁ w₁ (stepCat s₂ w₂ w₃) := by
  funext s
  by_cases h1 : s ≤ s₁
  · rw [stepCat_of_le _ _ (h1.trans le_self_add), stepCat_of_le _ _ h1, stepCat_of_le _ _ h1]
  · have h1' : s₁ < s := not_le.1 h1
    rw [stepCat_of_gt _ _ h1']
    by_cases h2 : s ≤ s₁ + s₂
    · rw [stepCat_of_le _ _ h2, stepCat_of_gt _ _ h1',
        stepCat_of_le (s := s - s₁) _ _ (by rw [tsub_le_iff_left]; exact h2)]
    · have h2' : s₁ + s₂ < s := not_le.1 h2
      have e1 : stepCat s₁ w₁ w₂ (s₁ + s₂) = w₁ s₁ + w₂ s₂ := by
        rcases eq_or_ne s₂ 0 with rfl | hs₂
        · rw [add_zero, stepCat_of_le _ _ le_rfl, h0, add_zero]
        · rw [stepCat_of_gt _ _ (lt_add_of_pos_right s₁ (pos_iff_ne_zero.2 hs₂)),
            add_tsub_cancel_left]
      have e2 : stepCat s₂ w₂ w₃ (s - s₁) = w₂ s₂ + w₃ (s - s₁ - s₂) := by
        rw [stepCat_of_gt _ _ (by rw [lt_tsub_iff_left]; exact h2')]
      rw [stepCat_of_gt _ _ h2', e1, e2, add_assoc, tsub_tsub]

/-- The iterated concatenation `w₁ ⌢ ⋯ ⌢ w_ℓ` of paths with lengths `s₁, …, s_ℓ`, defined
recursively as `w₁ ⌢ (w₂ ⌢ ⋯)`.  (The length of the last path is not used.) -/
noncomputable def stepCatList [Add V] [Zero V] : List (ℝ≥0 × (ℝ≥0 → V)) → (ℝ≥0 → V)
  | [] => fun _ => 0
  | [p] => p.2
  | p :: q :: rest => stepCat p.1 p.2 (stepCatList (q :: rest))

end ElboimSly.Paper
