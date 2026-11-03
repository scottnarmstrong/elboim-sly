/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# The large-`n` numerics of Lemma 7.1

ES22 Lemma 7.1, Step 6 ("for `n` large").

* `exists_poly_lt_rpow`: `8 n⁶ < 4^{nε}` for large `n`;
* `exists_const_mul_pow_le_exp`: `Q 16ⁿ ≤ e^{c n³}` for large `n`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Step

theorem exists_poly_lt_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 8 * (n : ℝ) ^ 6 < ((4 : ℝ) ^ ε) ^ n := by
  have hr : 1 < (4 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 6 hr
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 8 by
    norm_num)))
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  have hpos : 0 < ((4 : ℝ) ^ ε) ^ n := by positivity
  rw [div_lt_iff₀ hpos] at h
  linarith

theorem exists_const_mul_pow_le_exp {c : ℝ} (hc : 0 < c) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Q * (16 : ℝ) ^ n ≤ Real.exp (c * (n : ℝ) ^ 3) := by
  refine ⟨⌈(Real.log Q + Real.log 16) / c⌉₊ + 1, fun n hn => ?_⟩
  have hQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have h16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by omega) hn : 1 ≤ n)
  have hNn : (⌈(Real.log Q + Real.log 16) / c⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hceil := Nat.le_ceil ((Real.log Q + Real.log 16) / c)
  have h1 : (Real.log Q + Real.log 16) / c ≤ n := by linarith
  have h2 : Real.log Q + Real.log 16 ≤ c * n := by
    rw [div_le_iff₀ hc] at h1; linarith
  have e16 : (16 : ℝ) ^ n = Real.exp (n * Real.log 16) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have eQ : Q = Real.exp (Real.log Q) := (Real.exp_log (by linarith)).symm
  rw [e16]
  conv_lhs => rw [eQ]
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h3 : c * (n : ℝ) ^ 3 = (c * n) * (n * n) := by ring
  have h4 : (n : ℝ) * n ≥ n := by nlinarith
  nlinarith [mul_nonneg hQ0 (sub_nonneg.2 hn1), mul_le_mul_of_nonneg_left h4 (by positivity :
    0 ≤ c * (n : ℝ))]

end ElboimSly.Paper.Step
