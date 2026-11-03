/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BlockProbShift
public import ElboimSly.Paper.Step.Lemma78Attain
public import ElboimSly.Paper.Step.Lemma78CoupleDet
public import Mathlib

/-!
# Closing of the second walk of Lemma 7.8

Closing (b) for `w₂ = W₂ - u`: if `W₂(kβ) = u` for some `k ≥ 1` then
`W₂(r + kβ) = W₂(r)` for all `r ≥ 0`. This is the instance `Step78Closing` of the hypothesis of
`Step78Data.lt_treg_of_relaxed`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Paper.Heavy

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- **closing (b), in the frame of `N`.** -/
theorem step78_cycWalk_period {μ : Measure (RingSpace d β)} (hμ : Good μ) (u : Fin d → ℤ)
    (q : ℝ) {k : ℕ} (hk : 1 ≤ k) (h : cycWalk μ u q ((k : ℝ) * β) = u) {r : ℝ} (hr : 0 ≤ r) :
    cycWalk μ u q (r + k * β) = cycWalk μ u q r := by
  have hβ : 0 < β := Fact.out
  have hkβ : (0 : ℝ) ≤ k * β := by positivity
  have hg := good_shiftEnv (u := u) (q := q) hμ
  have hper : ((piBeta hg) ^ (k : ℤ)) 0 = 0 := by
    rw [← cycWalk_nat_mul hg, cycWalk_shiftEnv hμ u q hkβ, h, sub_self]
  have hr' : 0 ≤ r + k * β := by linarith
  have hw : cycWalk (shiftEnv u q μ) 0 0 (r + k * β) = cycWalk (shiftEnv u q μ) 0 0 r := by
    obtain ⟨j, r0, hr0, hrβ, rfl⟩ := exists_int_add (β := β) r
    have e : (j : ℝ) * β + r0 + k * β = ((j + k : ℤ) : ℝ) * β + r0 := by push_cast; ring
    rw [e, cycWalk_eq_pi hg (j + k) hr0 hrβ, cycWalk_eq_pi hg j hr0 hrβ, zpow_add,
      Equiv.Perm.mul_apply, hper]
  have h1 := cycWalk_shiftEnv hμ u q hr'
  have h2 := cycWalk_shiftEnv hμ u q hr
  rw [hw, h2] at h1
  exact (sub_left_inj.1 h1).symm

end ElboimSly.Paper.Step

end
