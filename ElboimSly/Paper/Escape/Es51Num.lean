/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# ES22 Theorem 5.1: the final numerics

ES22 Theorem 5.1 proof, last display: for `n` large,
`e^{-4^n} + (21d)^d 4^{d(n+1)} e^{-c₅₂ n³} ≤ e^{-c₅₁ n³}` with `c₅₁ = c₅₂/2`.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

theorem four_pow_ge_poly {n : ℕ} : (n : ℝ) ^ 4 / 24 ≤ 4 ^ n := by
  have h1 : (n : ℝ) ^ 4 / (Nat.factorial 4 : ℕ) ≤ Real.exp n :=
    Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) 4
  have h2 : Real.exp (n : ℝ) ≤ 4 ^ n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by
      have := Real.exp_one_lt_d9; linarith) n
  have h3 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h3] at h1
  exact h1.trans h2

/-- The real inequality behind ES22 Theorem 5.1. -/
theorem thm51_real {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {n : ℕ} {tn : ℝ}
    (hn0 : 2000 ≤ n) (hn1 : 2 * (96 * (d : ℝ) ^ 2 + 3 * d + 1) / c ≤ n)
    (hn2 : 24 * (c / 2 + 1) ≤ n) (htn1 : (4 : ℝ) ^ n ≤ tn) (htn2 : tn ≤ 4 ^ (n + 1)) (K : ℕ)
    (hK : (K : ℝ) ≤ 10 * d * tn + 1) :
    Real.exp (-tn) + (2 * K + 2 : ℝ) ^ d * Real.exp (-(c * (n : ℝ) ^ 3)) ≤
      Real.exp (-(c / 2 * (n : ℝ) ^ 3)) := by
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn0
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  set E := Real.exp (-(c / 2 * (n : ℝ) ^ 3)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.add_one_le_exp (1 : ℝ)
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  -- first term
  have hterm1 : Real.exp (-tn) ≤ E / 2 := by
    have h4 : (n : ℝ) ^ 4 / 24 ≤ tn := (four_pow_ge_poly).trans htn1
    have h5 : (c / 2 * (n : ℝ) ^ 3 + 1) ≤ tn := by
      have : 24 * (c / 2 + 1) * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_right hn2 hn3.le
        nlinarith
      have hn31 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
      nlinarith
    calc Real.exp (-tn) ≤ Real.exp (-(c / 2 * (n : ℝ) ^ 3 + 1)) := Real.exp_le_exp.2 (by linarith)
      _ = E * Real.exp (-1) := by rw [hE, ← Real.exp_add]; congr 1; ring
      _ ≤ E * (1 / 2) := by gcongr
      _ = E / 2 := by ring
  -- second term
  have hterm2 : (2 * K + 2 : ℝ) ^ d * Real.exp (-(c * (n : ℝ) ^ 3)) ≤ E / 2 := by
    have htn0 : 1 ≤ tn := le_trans (one_le_pow₀ (by norm_num)) htn1
    have hb : (2 * K + 2 : ℝ) ≤ 96 * d * 4 ^ n := by
      have h1 : (2 * K + 2 : ℝ) ≤ 24 * d * tn := by nlinarith
      have h2 : (24 * d * tn : ℝ) ≤ 96 * d * 4 ^ n := by
        have : tn ≤ 4 * 4 ^ n := by rw [pow_succ] at htn2; linarith
        nlinarith
      exact h1.trans h2
    have hexp : (96 * d * 4 ^ n : ℝ) ≤ Real.exp (96 * d) * Real.exp (3 * n) := by
      have h1 : (96 * (d : ℝ)) ≤ Real.exp (96 * d) := by linarith [Real.add_one_le_exp (96 * (d : ℝ))]
      have h2 : (4 : ℝ) ^ n ≤ Real.exp (3 * n) := by
        have : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
        calc (4 : ℝ) ^ n ≤ Real.exp 3 ^ n := pow_le_pow_left₀ (by norm_num) this n
          _ = Real.exp (3 * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
      calc (96 * d * 4 ^ n : ℝ) = (96 * d) * 4 ^ n := by ring
        _ ≤ Real.exp (96 * d) * Real.exp (3 * n) := by gcongr
    have hpow : (2 * K + 2 : ℝ) ^ d ≤ Real.exp (d * (96 * d + 3 * n)) := by
      calc (2 * K + 2 : ℝ) ^ d ≤ (Real.exp (96 * d) * Real.exp (3 * n)) ^ d :=
            pow_le_pow_left₀ (by positivity) (hb.trans hexp) d
        _ = Real.exp (d * (96 * d + 3 * n)) := by
            rw [← Real.exp_add, ← Real.exp_nat_mul]
    have hcn : 2 * (96 * (d : ℝ) ^ 2 + 3 * d + 1) ≤ c * n := by
      have := (div_le_iff₀ hc).1 hn1; linarith
    have hpoly : (d : ℝ) * (96 * d + 3 * n) + 1 ≤ c / 2 * (n : ℝ) ^ 3 := by
      have h1 : (d : ℝ) * (96 * d + 3 * n) + 1 ≤ (96 * (d : ℝ) ^ 2 + 3 * d + 1) * n := by
        nlinarith
      have h2 : (96 * (d : ℝ) ^ 2 + 3 * d + 1) * n * (n : ℝ) ^ 2 * 2 ≤ c * n * (n : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_right hcn (by positivity : (0 : ℝ) ≤ n * (n : ℝ) ^ 2)
        nlinarith
      have h3 : (96 * (d : ℝ) ^ 2 + 3 * d + 1) * n ≤ (96 * (d : ℝ) ^ 2 + 3 * d + 1) * n * (n : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by linarith)
        have h0 : 0 ≤ (96 * (d : ℝ) ^ 2 + 3 * d + 1) * n := by positivity
        nlinarith
      nlinarith
    calc (2 * K + 2 : ℝ) ^ d * Real.exp (-(c * (n : ℝ) ^ 3))
        ≤ Real.exp (d * (96 * d + 3 * n)) * Real.exp (-(c * (n : ℝ) ^ 3)) := by gcongr
      _ = Real.exp (d * (96 * d + 3 * n) - c * (n : ℝ) ^ 3) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(c / 2 * (n : ℝ) ^ 3) - 1) := Real.exp_le_exp.2 (by nlinarith)
      _ = E * Real.exp (-1) := by rw [hE, ← Real.exp_add]; congr 1
      _ ≤ E * (1 / 2) := by gcongr
      _ = E / 2 := by ring
  linarith

end ElboimSly.Paper.Escape
