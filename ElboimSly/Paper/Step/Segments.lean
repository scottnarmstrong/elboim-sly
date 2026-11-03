/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Windows
public import ElboimSly.Paper.Step.Concatenation
public import Mathlib

/-!
# A driving path from independent segments

A driving path from independent segments. The path `Γ(w)` built from `ℓ` segments of length `T`, with the
recursion `Γ_{ℓ+1}(w) = w_0 ⌢ Γ_ℓ(w_1, w_2, …)` (the iterated concatenation of
Concatenation). Segments are indexed from `0`.

* `stepGamma_windows`: `Γ_ℓ` of the windows of a path `X` with `X 0 = 0` is `X(· ∧ ℓT)`.
* `measurable_stepGamma`: `Γ_ℓ` is measurable.
* `stepGamma_shift`: `θ_T Γ_{ℓ+1}(w) = Γ_ℓ(w_1, …)`.
* `map_stepGamma`: if `w_0, …, w_{ℓ-1}` are independent with the law of the first window, then
  `Γ_ℓ(w)` has the law of `X(· ∧ ℓT)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.SRW
open scoped NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The path built from segments `w 0, …, w (ℓ-1)` of length `T`. -/
noncomputable def stepGamma (T : ℝ≥0) :
    ℕ → (ℕ → ℝ≥0 → Fin d → ℤ) → ℝ≥0 → Fin d → ℤ
  | 0, _ => fun _ => 0
  | ℓ + 1, w => stepCat T (w 0) (stepGamma T ℓ fun i => w (i + 1))

theorem stepGamma_apply_zero (T : ℝ≥0) (ℓ : ℕ) {w : ℕ → ℝ≥0 → Fin d → ℤ}
    (h0 : ∀ i, w i 0 = 0) : stepGamma T ℓ w 0 = 0 := by
  cases ℓ with
  | zero => rfl
  | succ ℓ =>
    simp only [stepGamma]
    rw [stepCat_of_le _ _ zero_le]
    exact h0 0

theorem stepGamma_shift (T : ℝ≥0) (ℓ : ℕ) {w : ℕ → ℝ≥0 → Fin d → ℤ} (h0 : ∀ i, w i 0 = 0) :
    (fun u => stepGamma T (ℓ + 1) w (T + u) - stepGamma T (ℓ + 1) w T) =
      stepGamma T ℓ fun i => w (i + 1) := by
  funext u
  have e : ∀ s, stepGamma T (ℓ + 1) w s =
      stepCat T (w 0) (stepGamma T ℓ fun i => w (i + 1)) s := fun _ => rfl
  rw [e, e, stepCat_of_le _ _ (le_refl T)]
  rcases eq_or_ne u 0 with rfl | hu
  · rw [add_zero, stepCat_of_le _ _ (le_refl T), sub_self,
      stepGamma_apply_zero T ℓ (fun i => h0 (i + 1))]
  · have h1 : T + u - T = u := add_tsub_cancel_left T u
    rw [stepCat_of_gt _ _ (lt_add_of_pos_right T (pos_iff_ne_zero.2 hu)), h1]
    abel

theorem measurable_stepGamma (T : ℝ≥0) (ℓ : ℕ) :
    Measurable (stepGamma (d := d) T ℓ) := by
  induction ℓ with
  | zero => exact measurable_const
  | succ ℓ ih =>
    refine measurable_pi_iff.2 fun s => ?_
    have hshift : Measurable fun w : ℕ → ℝ≥0 → Fin d → ℤ => fun i => w (i + 1) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply (i + 1)
    by_cases hs : s ≤ T
    · simp only [stepGamma, stepCat_of_le _ _ hs]
      exact (measurable_pi_apply s).comp (measurable_pi_apply 0)
    · simp only [stepGamma, stepCat_of_gt _ _ (not_le.1 hs)]
      refine Measurable.add ?_ ?_
      · exact (measurable_pi_apply T).comp (measurable_pi_apply 0)
      · exact (measurable_pi_apply (s - T)).comp (ih.comp hshift)

/-- `Γ_ℓ` of the windows of a path `X` with `X 0 = 0` is `X(· ∧ ℓT)`. -/
theorem stepGamma_windows (T : ℝ≥0) (ℓ : ℕ) (X : PathSpace d) (hX : X 0 = 0) :
    stepGamma T ℓ (fun j => stepWin ((j : ℝ≥0) * T) T X) = SRW.stopPath ((ℓ : ℝ≥0) * T) X := by
  induction ℓ generalizing X with
  | zero => funext s; simp [stepGamma, SRW.stopPath, hX]
  | succ ℓ ih =>
    have hth0 : SRW.theta T X 0 = 0 := by simp [SRW.theta]
    have hshift : (fun i : ℕ => stepWin (((i + 1 : ℕ) : ℝ≥0) * T) T X) =
        fun i : ℕ => stepWin ((i : ℝ≥0) * T) T (SRW.theta T X) := by
      funext i u
      simp only [stepWin, SRW.stopPath, SRW.theta]
      have : T + ((i : ℝ≥0) * T + min u T) = (((i + 1 : ℕ) : ℝ≥0) * T) + min u T := by
        push_cast; ring
      rw [this, show T + (i : ℝ≥0) * T = ((i + 1 : ℕ) : ℝ≥0) * T by push_cast; ring]
      abel
    simp only [stepGamma]
    rw [hshift, ih _ hth0]
    funext s
    simp only [Nat.cast_zero, zero_mul]
    by_cases hs : s ≤ T
    · rw [stepCat_of_le _ _ hs]
      simp only [stepWin, SRW.stopPath, SRW.theta, zero_add, hX, sub_zero]
      have : s ≤ ((ℓ + 1 : ℕ) : ℝ≥0) * T := hs.trans (le_mul_of_one_le_left zero_le (by exact_mod_cast Nat.le_add_left 1 ℓ))
      rw [min_eq_left hs, min_eq_left this]
    · rw [stepCat_of_gt _ _ (not_le.1 hs)]
      simp only [stepWin, SRW.stopPath, SRW.theta, zero_add, hX, sub_zero, min_self]
      have h2 : T + min (s - T) ((ℓ : ℝ≥0) * T) = min s (((ℓ + 1 : ℕ) : ℝ≥0) * T) := by
        have e1 : T + (s - T) = s := add_tsub_cancel_of_le (not_le.1 hs).le
        have e2 : T + (ℓ : ℝ≥0) * T = ((ℓ + 1 : ℕ) : ℝ≥0) * T := by push_cast; ring
        rw [← e2, ← min_add_add_left, e1]
      rw [← h2]
      abel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

/-- The law of `Γ_ℓ` of the windows of an SRW is the law of the SRW stopped at `ℓT`. -/
theorem map_stepGamma_windows (_hZ : IsSRW P Z) (hZ0 : ∀ ω, Z ω 0 = 0) (T : ℝ≥0) (ℓ : ℕ) :
    P.map (fun ω => stepGamma T ℓ fun j => stepWin ((j : ℝ≥0) * T) T (Z ω)) =
      P.map (fun ω => SRW.stopPath ((ℓ : ℝ≥0) * T) (Z ω)) := by
  congr 1
  funext ω
  exact stepGamma_windows T ℓ (Z ω) (hZ0 ω)

end ElboimSly.Paper
