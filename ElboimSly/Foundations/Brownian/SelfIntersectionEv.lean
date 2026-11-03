/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionNum
public import ElboimSly.Foundations.Brownian.SelfIntersectionAsymp

import Mathlib

/-!
# The thresholds (L1)-(L5) hold for large `t`

ES22 Claim 9.4, "Parameters": "Since `r^{1/2} p(r) → 0` as `r → ∞`, there is
`t₀`...". We show `SiGood ζ t` holds eventually as `t → ∞`.
-/

@[expose] public section

open Filter Topology Set

namespace ElboimSly.Brownian

/-- `siP` as a function of `r = siR ζ t`. -/
noncomputable def fP (ζ r : ℝ) : ℝ :=
  r ^ 2 * ((Real.pi * r ^ (2 - 2 * ζ)) ^ (-(5 : ℝ) / 2) *
      (r ^ (2 + 3 * ζ) * (6 * r ^ ((1 : ℝ) / 50)) ^ 5) +
    10 * Real.exp (-(r ^ (1 + ζ)) ^ 2 / (8 * r ^ 2))) +
    20 * (⌈r ^ 2⌉₊ : ℝ) * Real.exp (-(r ^ ((1 : ℝ) / 50)) ^ 2 / 16)

section Terms

variable {ζ : ℝ}

/-- First term: `r^{1/2} · r² (π K)^{-5/2} M (6ρ)^5 = c · r^{-2/5 + 8ζ}`. -/
lemma term1_eq {r : ℝ} (hr : 0 < r) :
    r ^ ((1 : ℝ) / 2) * (r ^ 2 * ((Real.pi * r ^ (2 - 2 * ζ)) ^ (-(5 : ℝ) / 2) *
      (r ^ (2 + 3 * ζ) * (6 * r ^ ((1 : ℝ) / 50)) ^ 5))) =
      (Real.pi ^ (-(5 : ℝ) / 2) * 6 ^ 5) * r ^ (-(2 : ℝ) / 5 + 8 * ζ) := by
  have h1 : (Real.pi * r ^ (2 - 2 * ζ)) ^ (-(5 : ℝ) / 2) =
      Real.pi ^ (-(5 : ℝ) / 2) * r ^ ((2 - 2 * ζ) * (-(5 : ℝ) / 2)) := by
    rw [Real.mul_rpow Real.pi_pos.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
  have h2 : (6 * r ^ ((1 : ℝ) / 50)) ^ 5 = 6 ^ 5 * r ^ ((1 : ℝ) / 10) := by
    rw [mul_pow, ← Real.rpow_natCast (r ^ ((1 : ℝ) / 50)) 5, ← Real.rpow_mul hr.le]
    congr 2; push_cast; norm_num
  have h3 : r ^ 2 = r ^ (2 : ℝ) := (Real.rpow_two r).symm
  rw [h1, h2, h3]
  have : r ^ ((1 : ℝ) / 2) * (r ^ (2 : ℝ) * (Real.pi ^ (-(5 : ℝ) / 2) *
      r ^ ((2 - 2 * ζ) * (-(5 : ℝ) / 2)) * (r ^ (2 + 3 * ζ) * (6 ^ 5 * r ^ ((1 : ℝ) / 10))))) =
      (Real.pi ^ (-(5 : ℝ) / 2) * 6 ^ 5) * (r ^ ((1 : ℝ) / 2) * r ^ (2 : ℝ) *
        r ^ ((2 - 2 * ζ) * (-(5 : ℝ) / 2)) * r ^ (2 + 3 * ζ) * r ^ ((1 : ℝ) / 10)) := by ring
  rw [this, ← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr]
  congr 2; ring

lemma term2_eq {r : ℝ} (hr : 0 < r) :
    r ^ ((1 : ℝ) / 2) * (r ^ 2 * (10 * Real.exp (-(r ^ (1 + ζ)) ^ 2 / (8 * r ^ 2)))) =
      10 * (r ^ ((5 : ℝ) / 2) * Real.exp (-(1 / 8) * r ^ (2 * ζ))) := by
  have h1 : (r ^ (1 + ζ)) ^ 2 = r ^ 2 * r ^ (2 * ζ) := by
    rw [rpow_sq' hr.le, show 2 * (1 + ζ) = 2 + 2 * ζ by ring, Real.rpow_add hr, Real.rpow_two]
  have h2 : -(r ^ (1 + ζ)) ^ 2 / (8 * r ^ 2) = -(1 / 8) * r ^ (2 * ζ) := by
    rw [h1]; field_simp
  have h3 : r ^ ((1 : ℝ) / 2) * r ^ 2 = r ^ ((5 : ℝ) / 2) := by
    rw [← Real.rpow_two, ← Real.rpow_add hr]; norm_num
  rw [h2]
  calc _ = (r ^ ((1 : ℝ) / 2) * r ^ 2) * (10 * Real.exp (-(1 / 8) * r ^ (2 * ζ))) := by ring
    _ = _ := by rw [h3]; ring

end Terms

lemma fP_tendsto {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 100) :
    Tendsto (fun r : ℝ => r ^ ((1 : ℝ) / 2) * fP ζ r) atTop (𝓝 0) := by
  -- the three terms
  have hu1 : Tendsto (fun r : ℝ => r ^ ((1 : ℝ) / 2) * (r ^ 2 *
      ((Real.pi * r ^ (2 - 2 * ζ)) ^ (-(5 : ℝ) / 2) *
        (r ^ (2 + 3 * ζ) * (6 * r ^ ((1 : ℝ) / 50)) ^ 5)))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (2 : ℝ) / 5 - 8 * ζ) (by linarith)).const_mul
      (Real.pi ^ (-(5 : ℝ) / 2) * 6 ^ 5)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    rw [term1_eq hr]
    congr 2; ring
  have hu2 : Tendsto (fun r : ℝ => r ^ ((1 : ℝ) / 2) * (r ^ 2 *
      (10 * Real.exp (-(r ^ (1 + ζ)) ^ 2 / (8 * r ^ 2))))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_rpow ((5 : ℝ) / 2) (c := 1 / 8) (e := 2 * ζ)
      (by norm_num) (by linarith)).const_mul 10
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    rw [term2_eq hr]
  have hu3 : Tendsto (fun r : ℝ => r ^ ((1 : ℝ) / 2) * (20 * (⌈r ^ 2⌉₊ : ℝ) *
      Real.exp (-(r ^ ((1 : ℝ) / 50)) ^ 2 / 16))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_rpow ((5 : ℝ) / 2) (c := 1 / 16) (e := (1 : ℝ) / 25)
      (by norm_num) (by norm_num)).const_mul 40
    rw [mul_zero] at h
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [eventually_gt_atTop 0] with r hr
      positivity
    · filter_upwards [eventually_ge_atTop 1] with r hr
      have hr0 : 0 < r := by linarith
      have hceil : (⌈r ^ 2⌉₊ : ℝ) ≤ 2 * r ^ 2 := by
        have := (Nat.ceil_lt_add_one (sq_nonneg r)).le
        nlinarith
      have he : -(r ^ ((1 : ℝ) / 50)) ^ 2 / 16 = -(1 / 16) * r ^ ((1 : ℝ) / 25) := by
        rw [rpow_sq' hr0.le]; ring_nf
      rw [he]
      have h5 : r ^ ((1 : ℝ) / 2) * r ^ 2 = r ^ ((5 : ℝ) / 2) := by
        rw [← Real.rpow_two, ← Real.rpow_add hr0]; norm_num
      calc r ^ ((1 : ℝ) / 2) * (20 * (⌈r ^ 2⌉₊ : ℝ) * Real.exp (-(1 / 16) * r ^ ((1 : ℝ) / 25)))
          ≤ r ^ ((1 : ℝ) / 2) * (20 * (2 * r ^ 2) * Real.exp (-(1 / 16) * r ^ ((1 : ℝ) / 25))) := by
            gcongr
        _ = 40 * (r ^ ((1 : ℝ) / 2) * r ^ 2) * Real.exp (-(1 / 16) * r ^ ((1 : ℝ) / 25)) := by
            ring
        _ = 40 * (r ^ ((5 : ℝ) / 2) * Real.exp (-(1 / 16) * r ^ ((1 : ℝ) / 25))) := by
            rw [h5]; ring
  have hsum := (hu1.add hu2).add hu3
  rw [add_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with r
  unfold fP
  ring

lemma fP_eventually {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 100) :
    ∀ᶠ r : ℝ in atTop, fP ζ r ≤ r ^ (-(1 : ℝ) / 2) := by
  filter_upwards [(fP_tendsto hζ hζ1).eventually (gt_mem_nhds (zero_lt_one' ℝ)),
    eventually_gt_atTop 0] with r h hr
  have e : r ^ (-(1 : ℝ) / 2) * r ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hr]; norm_num
  have hpos : 0 < r ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hr _
  calc fP ζ r = r ^ (-(1 : ℝ) / 2) * (r ^ ((1 : ℝ) / 2) * fP ζ r) := by rw [← mul_assoc, e, one_mul]
    _ ≤ r ^ (-(1 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left h.le hpos.le
    _ = _ := mul_one _

/-- The thresholds (L1)-(L5) hold for all large `t`. -/
theorem siGood_eventually {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 100) :
    ∀ᶠ t : ℝ in atTop, SiGood ζ t := by
  have hR : Tendsto (siR ζ) atTop atTop := tendsto_rpow_atTop (by linarith)
  have hL1 : ∀ᶠ r : ℝ in atTop, 2 ≤ r ^ (2 - 2 * ζ) :=
    (tendsto_rpow_atTop (by linarith : 0 < 2 - 2 * ζ)).eventually_ge_atTop 2
  have hL2 : ∀ᶠ r : ℝ in atTop, 2 + 4 * r ^ ((1 : ℝ) / 50) ≤ r ^ (1 + ζ) := by
    filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 49 / 50)).eventually_ge_atTop 6,
      eventually_ge_atTop 1] with r h6 hr
    have hr0 : 0 < r := by linarith
    have h1 : 1 ≤ r ^ ((1 : ℝ) / 50) := Real.one_le_rpow hr (by norm_num)
    have h2 : r = r ^ ((1 : ℝ) / 50) * r ^ ((49 : ℝ) / 50) := by
      rw [← Real.rpow_add hr0]; norm_num
    have h3 : r ≤ r ^ (1 + ζ) := by
      calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
        _ ≤ r ^ (1 + ζ) := Real.rpow_le_rpow_of_exponent_le hr (by linarith)
    nlinarith
  have hL4 : ∀ᶠ t : ℝ in atTop, 4 ≤ t ^ (3 / 20 * ζ) :=
    (tendsto_rpow_atTop (by positivity : 0 < 3 / 20 * ζ)).eventually_ge_atTop 4
  have hL5 : ∀ᶠ t : ℝ in atTop, 4 ≤ t ^ (ζ ^ 2 - ζ ^ 3) :=
    (tendsto_rpow_atTop (by nlinarith : 0 < ζ ^ 2 - ζ ^ 3)).eventually_ge_atTop 4
  filter_upwards [hR.eventually hL1, hR.eventually hL2, hR.eventually (fP_eventually hζ hζ1),
    hL4, hL5] with t h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end ElboimSly.Brownian
