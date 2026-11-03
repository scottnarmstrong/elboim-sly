/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import Mathlib

/-!
# Elementary asymptotics for the self-intersection claim

ES22 Claim 9.4, Step 5.

* `tendsto_rpow_mul_exp_neg_rpow`: `x^s e^{-c x^e} → 0`;
* `exists_decay_bound`: `x^k e^{-c x^e} ≤ C e^{-x^a}` for all `x ≥ 1`, when `0 < c`, `a < e`.
-/

@[expose] public section

open Filter Topology Set

namespace ElboimSly.Brownian

lemma rpow_sq' {r : ℝ} (hr : 0 ≤ r) (a : ℝ) : (r ^ a) ^ 2 = r ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; congr 1; push_cast; ring

/-- `x^s e^{-c x^e} → 0` as `x → ∞`, for `c, e > 0`. -/
lemma tendsto_rpow_mul_exp_neg_rpow (s : ℝ) {c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    Tendsto (fun x : ℝ => x ^ s * Real.exp (-c * x ^ e)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / e) c hc
  have h2 := h1.comp (tendsto_rpow_atTop he)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp]
  rw [← Real.rpow_mul hx.le, mul_div_cancel₀ _ he.ne']

/-- A uniform bound `x^k e^{-c x^e} ≤ C e^{-x^a}` for `x ≥ 1`, when `a < e`. -/
lemma exists_decay_bound (k : ℝ) {c e a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hae : a < e) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → x ^ k * Real.exp (-c * x ^ e) ≤ C * Real.exp (-x ^ a) := by
  set g : ℝ → ℝ := fun x => x ^ k * Real.exp (-c * x ^ e + x ^ a) with hg
  have hge : 0 < e := lt_of_le_of_lt ha hae
  -- `g → 0`
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 := tendsto_rpow_mul_exp_neg_rpow k (c := c / 2) (by positivity) hge
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_nonneg _)
    · have h2 : Tendsto (fun x : ℝ => x ^ (e - a)) atTop atTop :=
        tendsto_rpow_atTop (by linarith)
      filter_upwards [eventually_gt_atTop 0, h2.eventually_ge_atTop (2 / c)] with x hx hx2
      have hxe : x ^ e = x ^ a * x ^ (e - a) := by
        rw [← Real.rpow_add hx]; congr 1; ring
      have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hx.le _
      have : x ^ a ≤ c / 2 * x ^ e := by
        rw [hxe]
        have : 2 / c * x ^ a ≤ x ^ (e - a) * x ^ a := mul_le_mul_of_nonneg_right hx2 hxa
        have h3 : x ^ a = c / 2 * (2 / c * x ^ a) := by field_simp
        nlinarith [mul_pos hc hc]
      simp only [hg]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hx.le _)
      nlinarith
  -- a bound on `[1, ∞)`
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (zero_lt_one' ℝ)))
  set T' : ℝ := max T 1 with hT'
  have hcont : ContinuousOn g (Set.Icc 1 T') := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h1 : ContinuousAt (fun x : ℝ => x ^ k) x := Real.continuousAt_rpow_const x k (Or.inl hx0)
    have h2 : ContinuousAt (fun x : ℝ => x ^ e) x := Real.continuousAt_rpow_const x e (Or.inl hx0)
    have h3 : ContinuousAt (fun x : ℝ => x ^ a) x := Real.continuousAt_rpow_const x a (Or.inl hx0)
    exact (h1.mul (Real.continuous_exp.continuousAt.comp
      ((continuousAt_const.mul h2).add h3))).continuousWithinAt
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C0 1, fun x hx => ?_⟩
  have hgx : g x ≤ max C0 1 := by
    by_cases hxT : x ≤ T'
    · exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC0 x ⟨hx, hxT⟩)) |>.trans (le_max_left _ _)
    · push Not at hxT
      exact (hT x (le_trans (le_max_left _ _) hxT.le)).le.trans (le_max_right _ _)
  have : x ^ k * Real.exp (-c * x ^ e) = g x * Real.exp (-x ^ a) := by
    simp only [hg, mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hgx (Real.exp_nonneg _)

end ElboimSly.Brownian
