/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Elementary inequalities for the Chernoff bound of the clocks

Chernoff bound for the clocks, Steps 1 and 2 (pointwise parts)
(Part II).
-/

@[expose] public section

open Real

namespace ElboimSly.StrongApprox

/-- Chernoff bound for the clocks, Step 1: `e^v ≤ 1 + v + (v²/2) e^{|v|}`. -/
lemma exp_le_quad (v : ℝ) : Real.exp v ≤ 1 + v + v ^ 2 / 2 * Real.exp |v| := by
  rcases le_total 0 v with hv | hv
  · -- `g(v) = 1 + v + v²/2 e^v - e^v ≥ 0` on `[0,∞)`
    rw [abs_of_nonneg hv]
    set g : ℝ → ℝ := fun v => 1 + v + v ^ 2 / 2 * Real.exp v - Real.exp v with hg
    have hderiv : ∀ x, HasDerivAt g (1 + x * Real.exp x + x ^ 2 / 2 * Real.exp x - Real.exp x) x := by
      intro x
      have h1 : HasDerivAt (fun v : ℝ => 1 + v) 1 x := by
        simpa using (hasDerivAt_id x).const_add 1
      have h2 : HasDerivAt (fun v : ℝ => v ^ 2 / 2 * Real.exp v)
          (x * Real.exp x + x ^ 2 / 2 * Real.exp x) x := by
        have := ((hasDerivAt_pow 2 x).div_const 2).mul (Real.hasDerivAt_exp x)
        convert this using 1
        simp
      have := (h1.add h2).sub (Real.hasDerivAt_exp x)
      convert this using 1
      ring
    have hmono : MonotoneOn g (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
        (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := hx
      rw [(hderiv x).deriv]
      have : (1 - x) * Real.exp x ≤ 1 := by
        rcases le_or_gt x 1 with h | h
        · have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
          calc (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
                mul_le_mul_of_nonneg_right h1 (Real.exp_pos x).le
            _ = 1 := by rw [← Real.exp_add]; simp
        · nlinarith [Real.exp_pos x]
      nlinarith [Real.exp_pos x, sq_nonneg x, mul_nonneg (sq_nonneg x) (Real.exp_pos x).le]
    have h0 : g 0 = 0 := by simp [hg]
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hv) hv
    rw [h0] at this
    simp only [hg] at this
    linarith
  · rw [abs_of_nonpos hv]
    have hexp : 0 < Real.exp (-v) := Real.exp_pos _
    set h : ℝ → ℝ := fun v => 1 + v + v ^ 2 / 2 - Real.exp v with hh
    have hderiv : ∀ x, HasDerivAt h (1 + x - Real.exp x) x := by
      intro x
      have h1 : HasDerivAt (fun v : ℝ => 1 + v + v ^ 2 / 2) (1 + x) x := by
        have a : HasDerivAt (fun v : ℝ => 1 + v) 1 x := by
          simpa using (hasDerivAt_id x).const_add 1
        have b : HasDerivAt (fun v : ℝ => v ^ 2 / 2) x x := by
          simpa using ((hasDerivAt_pow 2 x).div_const 2)
        exact a.add b
      have := h1.sub (Real.hasDerivAt_exp x)
      exact this
    have hanti : AntitoneOn h (Set.Iic 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Iic 0)
        (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
        (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [(hderiv x).deriv]
      linarith [Real.add_one_le_exp x]
    have h0 : h 0 = 0 := by simp [hh]
    have := hanti (Set.mem_Iic.2 hv) (Set.mem_Iic.2 le_rfl) hv
    rw [h0] at this
    simp only [hh] at this
    have hnn : 0 ≤ v ^ 2 / 2 * (Real.exp (-v) - 1) := by
      apply mul_nonneg (by positivity)
      linarith [Real.add_one_le_exp (-v)]
    nlinarith

end ElboimSly.StrongApprox
