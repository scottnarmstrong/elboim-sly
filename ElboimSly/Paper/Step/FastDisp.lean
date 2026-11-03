/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TfastRat
public import ElboimSly.Paper.Heavy.FastDisplacement
public import ElboimSly.Paper.Step.RelaxedAdapted
public import Mathlib

/-!
# Fast displacement for the driven regenerated walk

Pathwise consequences of tfast and heavyJ (b), ES22 Lemma 7.1 Step 5.

Before `τ_fast`, the displacement over `[u, u']` is at most `L (u' - u + 1)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- Pathwise consequences of tfast and heavyJ (b), for any path. -/
theorem norm_sub_lt_of_lt_pathTfast' {w : ℝ → Fin d → ℤ} {L : ℝ} (hL : 0 < L) {u u' : ℝ}
    (hu : 0 ≤ u) (huu : u < u') (h : ENNReal.ofReal u' < pathTfast w L) :
    ‖w u' - w u‖ < L * ⌈u' - u⌉₊ := by
  refine chain_bound (fun a b => ‖w b - w a‖) L hL (fun v => ENNReal.ofReal v < pathTfast w L)
    ?_ ?_ ?_ ⌈u' - u⌉₊ u u' hu huu (Nat.le_ceil _) h
  · intro a r v _ _ _
    have := norm_sub_le_norm_sub_add_norm_sub (w v) (w r) (w a)
    show ‖w v - w a‖ ≤ ‖w r - w a‖ + ‖w v - w r‖
    linarith
  · intro a v hav hv
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hav) hv
  · intro a v ha hav hv1 hP
    by_contra hge
    push Not at hge
    have hmem : v ∈ {t : ℝ | 0 < t ∧ ∃ s : ℝ, t - 1 ≤ s ∧ s ≤ t ∧ L ≤ ‖w t - w (max s 0)‖} :=
      ⟨by linarith, a, by linarith, hav.le, by rwa [max_eq_left ha]⟩
    exact absurd (iInf₂_le (f := fun t (_ : t ∈ _) => ENNReal.ofReal t) v hmem |>.trans_lt hP)
      (lt_irrefl _)

/-- Displacement bound on `[0, T]` for a `ℝ≥0`-indexed path with `τ_fast > T`. -/
theorem fast_disp {W : ℝ≥0 → Fin d → ℤ} {L : ℝ} (hL : 0 < L) {T : ℝ≥0}
    (h : ENNReal.ofReal (T : ℝ) < pathTfast (stepExt W) L) :
    ∀ u u' : ℝ≥0, u ≤ u' → u' ≤ T → ‖W u' - W u‖ ≤ L * ((u' : ℝ) - u + 1) := by
  intro u u' huu hu'T
  rcases huu.eq_or_lt with rfl | hlt
  · simp only [sub_self, norm_zero]
    nlinarith [hL]
  · have h' : ENNReal.ofReal (u' : ℝ) < pathTfast (stepExt W) L :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by exact_mod_cast hu'T)) h
    have := norm_sub_lt_of_lt_pathTfast' (w := stepExt W) hL (u := (u : ℝ)) (u' := (u' : ℝ))
      u.2 (by exact_mod_cast hlt) h'
    simp only [stepExt, Real.toNNReal_coe] at this
    refine this.le.trans ?_
    have hx : (0 : ℝ) ≤ (u' : ℝ) - u := by
      have : (u : ℝ) ≤ u' := by exact_mod_cast huu
      linarith
    have := Nat.ceil_lt_add_one hx
    exact mul_le_mul_of_nonneg_left (by linarith) hL.le

end ElboimSly.Paper.Step
