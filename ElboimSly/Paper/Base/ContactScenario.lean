/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.TwoParticleCount
public import ElboimSly.Paper.Base.Hitting
public import Mathlib

/-!
# The escape scenario: a deterministic statement

Contacts are few (ii), "The scenario prevents a further contact".

Let `x₁, x₂, y` be as in `TwoParticleData`, `D = y - a - x₁`, `Z = x₂ - x₁`.  Suppose that at a
time `κ₀`, `D(κ₀) = y₀` with `y₀ ≠ 0` and `y₀ + v₀ ≠ 0`; that on `[κ₀, κ₀ + 1]` the path `x₁` is
constant and `x₂ - x₂(κ₀)` takes values in `{0, v₀}` with value `v₀` at `κ₀ + 1`; and that
afterwards `y₀ + v₀ + Z(κ₀ + 1 + u) - Z(κ₀ + 1)` has norm at least `2` for all `u ≥ 0`.  Then
`‖D(s)‖ ≥ 2` for all `s ≥ κ₀ + 1`.
-/

@[expose] public section

open Set Filter Topology Function
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base

variable {d : ℕ} {a b : Fin d → ℤ} {x₁ x₂ y : ℝ≥0 → Fin d → ℤ}

/-- If `x₁` does not jump at `r`, then `y` follows `x₂` unless the new position is `0`. -/
theorem TwoParticleData.step_no_jump₁ (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b) {r : ℝ≥0}
    (hr : 0 < r) (h1 : r ∉ CDisc x₁)
    (h2 : leftLim y r - (a + leftLim x₁ r) + (x₂ r - leftLim x₂ r) ≠ 0) :
    y r = leftLim y r + (x₂ r - leftLim x₂ r) := by
  have hw := h.leftLim_ne hab hr
  rw [h.hy.rule r hr]
  have c : ¬ (r ∈ CDisc x₁ ∧ (leftLim y r = a + leftLim x₁ r ∨ leftLim y r = a + x₁ r)) :=
    fun hc => h1 hc.1
  by_cases hc2 : r ∈ CDisc x₂
  · exact twoStep_F2 a x₁ x₂ r _ c ⟨hc2, fun e => hw e.symm, fun e => h2 (by rw [e]; abel)⟩
  · rw [twoStep_of_notMem a h1 hc2, h.hx₂.leftLim_of_notMem hr hc2]; simp

/-- Phase 1: while `x₁` is constant and `x₂ - x₂(κ₀) ∈ {0, v₀}`, `D = y₀ + (x₂ - x₂(κ₀))`. -/
theorem TwoParticleData.phase1 (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b)
    {κ₀ : ℝ≥0} {y₀ v₀ : Fin d → ℤ} (hD : y κ₀ - (a + x₁ κ₀) = y₀) (hy0 : y₀ ≠ 0)
    (hy0' : y₀ + v₀ ≠ 0) (hx1 : ∀ s, κ₀ ≤ s → s ≤ κ₀ + 1 → x₁ s = x₁ κ₀)
    (hx2 : ∀ s, κ₀ ≤ s → s ≤ κ₀ + 1 → x₂ s - x₂ κ₀ = 0 ∨ x₂ s - x₂ κ₀ = v₀) :
    ∀ s, κ₀ ≤ s → s ≤ κ₀ + 1 → y s - (a + x₁ s) = y₀ + (x₂ s - x₂ κ₀) := by
  refine real_induction (Q := fun s => κ₀ ≤ s → s ≤ κ₀ + 1 →
    y s - (a + x₁ s) = y₀ + (x₂ s - x₂ κ₀)) ?_ ?_ ?_
  · intro h1 _
    have : κ₀ = 0 := le_antisymm h1 bot_le
    subst this
    simpa using hD
  · intro r hr hev h1 h2
    rcases h1.eq_or_lt with rfl | hlt
    · simpa using hD
    · have hI : Ioo κ₀ r ∈ 𝓝[<] r := Ioo_mem_nhdsLT hlt
      have hx1ev : ∀ᶠ u in 𝓝[<] r, x₁ u = x₁ κ₀ := by
        filter_upwards [hI] with u hu using hx1 u hu.1.le (hu.2.le.trans h2)
      have hl1 : leftLim x₁ r = x₁ κ₀ := IsStepPath.leftLim_eq hr hx1ev
      have hn1 : r ∉ CDisc x₁ := by
        intro hc
        have := (h.hx₁.step.mem_CDisc_iff hr).1 hc
        exact this (by rw [hl1, hx1 r hlt.le h2])
      have hl1' : x₁ r = leftLim x₁ r := (h.hx₁.leftLim_of_notMem hr hn1).symm
      have := neBot_nhdsLT_of_pos hr
      obtain ⟨u, hu1, hu2, hu3, hu4, hu5⟩ := (hev.and ((h.hy.step.eventually_left_leftLim hr).and
        ((h.hx₁.step.eventually_left_leftLim hr).and ((h.hx₂.step.eventually_left_leftLim hr).and
          hI)))).exists
      have hQu := hu1 hu5.1.le (hu5.2.le.trans h2)
      have key : leftLim y r - (a + leftLim x₁ r) = y₀ + (leftLim x₂ r - x₂ κ₀) := by
        rw [← hu2, ← hu3, ← hu4]; exact hQu
      have hnz : leftLim y r - (a + leftLim x₁ r) + (x₂ r - leftLim x₂ r) ≠ 0 := by
        rw [key]
        have : y₀ + (leftLim x₂ r - x₂ κ₀) + (x₂ r - leftLim x₂ r) = y₀ + (x₂ r - x₂ κ₀) := by
          abel
        rw [this]
        rcases hx2 r hlt.le h2 with e | e
        · rw [e]; simpa using hy0
        · rw [e]; exact hy0'
      have hy := h.step_no_jump₁ hab hr hn1 hnz
      rw [hy, hl1']
      rw [show leftLim y r + (x₂ r - leftLim x₂ r) - (a + leftLim x₁ r) =
        leftLim y r - (a + leftLim x₁ r) + (x₂ r - leftLim x₂ r) by abel, key]
      abel
  · intro r hr
    rcases lt_or_ge r κ₀ with hlt | hge
    · filter_upwards [Ico_mem_nhdsGE hlt] with u hu h1
      exact absurd hu.2 (not_lt.2 h1)
    · rcases le_or_gt r (κ₀ + 1) with hle | hgt
      · filter_upwards [h.hy.step.rc r, h.hx₁.step.rc r, h.hx₂.step.rc r] with u e1 e2 e3 _ _
        rw [e1, e2, e3]; exact hr hge hle
      · filter_upwards [self_mem_nhdsWithin (a := r) (s := Ici r)] with u hu _ h2
        exact absurd (lt_of_lt_of_le hgt hu) (not_lt.2 h2)

/-- Phase 2: once `‖D‖ ≥ 2` along the future, `D` follows `Z = x₂ - x₁`. -/
theorem TwoParticleData.phase2 (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b)
    {t₀ : ℝ≥0} {c : Fin d → ℤ} (hc : y t₀ - (a + x₁ t₀) = c)
    (hesc : ∀ s, t₀ ≤ s → 2 ≤ ‖c + ((x₂ s - x₁ s) - (x₂ t₀ - x₁ t₀))‖) :
    ∀ s, t₀ ≤ s → y s - (a + x₁ s) = c + ((x₂ s - x₁ s) - (x₂ t₀ - x₁ t₀)) := by
  refine real_induction (Q := fun s => t₀ ≤ s →
    y s - (a + x₁ s) = c + ((x₂ s - x₁ s) - (x₂ t₀ - x₁ t₀))) ?_ ?_ ?_
  · intro h1
    have : t₀ = 0 := le_antisymm h1 bot_le
    subst this
    simpa using hc
  · intro r hr hev h1
    rcases h1.eq_or_lt with rfl | hlt
    · simpa using hc
    · have hI : Ioo t₀ r ∈ 𝓝[<] r := Ioo_mem_nhdsLT hlt
      have := neBot_nhdsLT_of_pos hr
      obtain ⟨u, hu1, hu2, hu3, hu4, hu5⟩ := (hev.and ((h.hy.step.eventually_left_leftLim hr).and
        ((h.hx₁.step.eventually_left_leftLim hr).and ((h.hx₂.step.eventually_left_leftLim hr).and
          hI)))).exists
      have hQu := hu1 hu5.1.le
      have key : leftLim y r - (a + leftLim x₁ r) =
          c + ((leftLim x₂ r - leftLim x₁ r) - (x₂ t₀ - x₁ t₀)) := by
        rw [← hu2, ← hu3, ← hu4]; exact hQu
      have hfar : 2 ≤ l1 (leftLim y r - (a + leftLim x₁ r)) := by
        have h2 := hesc u hu5.1.le
        have h3 : (2 : ℝ) ≤ ((l1 (leftLim y r - (a + leftLim x₁ r)) : ℤ) : ℝ) := by
          refine h2.trans ((le_of_eq ?_).trans (norm_le_l1 _))
          rw [key, ← hu3, ← hu4]
        exact_mod_cast h3
      have := (h.far hab hr hfar).2
      rw [sub_eq_iff_eq_add] at this
      rw [this, key]
      abel
  · intro r hr
    rcases lt_or_ge r t₀ with hlt | hge
    · filter_upwards [Ico_mem_nhdsGE hlt] with u hu h1
      exact absurd hu.2 (not_lt.2 h1)
    · filter_upwards [h.hy.step.rc r, h.hx₁.step.rc r, h.hx₂.step.rc r] with u e1 e2 e3 _
      rw [e1, e2, e3]; exact hr hge

end ElboimSly.Paper
