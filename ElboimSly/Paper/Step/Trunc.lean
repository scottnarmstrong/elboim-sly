/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Truncation of extended times at a level `T`
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

/-- `x ∧ T`, as a non-negative real. -/
noncomputable def trT (T : ℝ≥0) (x : WithTop ℝ≥0) : ℝ≥0 := (min x (T : WithTop ℝ≥0)).untopD 0

theorem trT_coe (T z : ℝ≥0) : trT T (z : WithTop ℝ≥0) = min z T := by
  unfold trT
  rw [← WithTop.coe_min]
  rfl

theorem trT_top (T : ℝ≥0) : trT T ⊤ = T := by
  unfold trT
  rw [min_eq_right le_top]
  rfl

theorem coe_trT (T : ℝ≥0) (x : WithTop ℝ≥0) : ((trT T x : ℝ≥0) : WithTop ℝ≥0) = min x T := by
  cases x using WithTop.recTopCoe with
  | top => rw [trT_top, min_eq_right le_top]
  | coe z => rw [trT_coe, WithTop.coe_min]

theorem trT_le (T : ℝ≥0) (x : WithTop ℝ≥0) : trT T x ≤ T := by
  have := coe_trT T x
  have h2 : ((trT T x : ℝ≥0) : WithTop ℝ≥0) ≤ T := this ▸ min_le_right _ _
  exact WithTop.coe_le_coe.1 h2

theorem trT_mono (T : ℝ≥0) {x y : WithTop ℝ≥0} (h : x ≤ y) : trT T x ≤ trT T y := by
  refine WithTop.coe_le_coe.1 ?_
  rw [coe_trT, coe_trT]
  exact min_le_min h le_rfl

theorem trT_le_self (T : ℝ≥0) (x : WithTop ℝ≥0) : ((trT T x : ℝ≥0) : WithTop ℝ≥0) ≤ x := by
  rw [coe_trT]; exact min_le_left _ _

theorem trT_eq_of_lt {T : ℝ≥0} {x : WithTop ℝ≥0} (h : (T : WithTop ℝ≥0) < x) : trT T x = T := by
  cases x using WithTop.recTopCoe with
  | top => exact trT_top T
  | coe z => rw [trT_coe]; exact min_eq_right (WithTop.coe_lt_coe.1 h).le

theorem trT_eq_of_le {T z : ℝ≥0} {x : WithTop ℝ≥0} (hx : x = z) (h : z ≤ T) : trT T x = z := by
  rw [hx, trT_coe]; exact min_eq_left h

end ElboimSly.Paper.Step
