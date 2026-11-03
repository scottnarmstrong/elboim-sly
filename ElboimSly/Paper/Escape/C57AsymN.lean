/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Blocks
public import Mathlib

/-!
# `n`-asymptotics for the thresholds of ES22 Claim 5.7

ES22 Claim 5.7 (choice of `β₅₇`).

For `n` large: the level `j = j_n` is large, `j ≤ n`, and `(2n)^5 ≤ 4^n`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Escape

open ElboimSly.Paper

theorem le_escJ_of_pow_le {J n : ℕ} (h : 2 ^ J ≤ n) (_hn : 1 ≤ n) : J ≤ escJ n := by
  have h1 : n ^ 20 ≤ 2 ^ escJ n := le_two_pow_escJ n
  have h2 : n ≤ n ^ 20 := Nat.le_self_pow (by norm_num) n
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (h.trans (h2.trans h1))

theorem exists_pow_lt_two_pow (m : ℕ) : ∃ N : ℕ, ∀ n ≥ N, n ^ m < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt m (by norm_num : (1 : ℝ) < 2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [div_lt_one (by positivity)] at this
  exact_mod_cast this

theorem exists_const_mul_pow_lt (m a : ℕ) : ∃ N : ℕ, ∀ n ≥ N, a * n ^ m < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt m (by norm_num : (1 : ℝ) < 2)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (h.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (a + 1))))
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [div_lt_iff₀ (by positivity)] at this
  have h2 : (a : ℝ) * (n : ℝ) ^ m < 2 ^ n := by
    have ha : (0 : ℝ) < a + 1 := by positivity
    have : ((n : ℝ) ^ m) * (a + 1) < 2 ^ n := by
      calc ((n : ℝ) ^ m) * (a + 1) = (a + 1) * (n : ℝ) ^ m := by ring
        _ < 2 ^ n := by
          have := this
          field_simp at this
          linarith
    nlinarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) m]
  exact_mod_cast h2

/-- All `n`-conditions of ES22 Claim 5.7 hold for `n ≥ N`. -/
theorem asym_n (n₀ : ℕ) (c : ℝ) (hc : 0 < c) : ∃ N : ℕ, 3 ≤ N ∧ ∀ n ≥ N,
    n₀ + 1 ≤ escJ n ∧ 40 ≤ escJ n ∧ escJ n ≤ n ∧
    Real.exp (-((escJ n - 1 : ℕ) : ℝ) ^ 2) ≤ c / 4 ∧ 32 * (n : ℝ) ^ 5 ≤ 4 ^ n := by
  obtain ⟨M, hM⟩ := eventually_atTop.1
    ((Real.tendsto_exp_neg_atTop_nhds_zero).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < c / 4)))
  obtain ⟨N1, hN1⟩ := exists_pow_lt_two_pow 21
  obtain ⟨N2, hN2⟩ := exists_const_mul_pow_lt 5 32
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, max M 1 ≤ M' := ⟨⌈max M 1⌉₊, Nat.le_ceil _⟩
  refine ⟨max (max (max N1 N2) 3) (2 ^ (n₀ + 1 + 40 + M' + 2)), by omega, fun n hn => ?_⟩
  obtain ⟨⟨⟨hnN1, hnN2⟩, hn3⟩, hnJ⟩ := max_le_iff.1 hn |>.imp (fun h => max_le_iff.1 h |>.imp
    (fun h' => max_le_iff.1 h') id) id
  have hj : n₀ + 1 + 40 + M' + 2 ≤ escJ n := le_escJ_of_pow_le hnJ (by omega)
  have hjn : escJ n ≤ n := by
    have h1 := two_pow_escJ_lt (n := n) (by omega)
    have h2 := hN1 n hnN1
    have h3 : 2 * n ^ 20 ≤ n ^ 21 := by
      rw [pow_succ]; nlinarith [pow_pos (by omega : 0 < n) 20, hn3]
    exact ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by omega)).le
  refine ⟨by omega, by omega, hjn, ?_, ?_⟩
  · have hm : (M' : ℝ) ≤ ((escJ n - 1 : ℕ) : ℝ) := by
      have : M' ≤ escJ n - 1 := by omega
      exact_mod_cast this
    have hM1 : (1 : ℝ) ≤ M' := le_trans (le_max_right _ _) hM'
    have hMM : M ≤ ((escJ n - 1 : ℕ) : ℝ) := le_trans (le_max_left _ _) (hM'.trans hm)
    have h := hM _ hMM
    have : -((escJ n - 1 : ℕ) : ℝ) ^ 2 ≤ -((escJ n - 1 : ℕ) : ℝ) := by nlinarith
    exact (Real.exp_le_exp.2 this).trans h.le
  · have h := hN2 n hnN2
    have : (32 : ℝ) * (n : ℝ) ^ 5 < 2 ^ n := by exact_mod_cast h
    have h4 : (2 : ℝ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    linarith

theorem asym_eps {j : ℕ} (hj : 40 ≤ j) :
    ((4 : ℝ) ^ j) ^ (41 / 100 : ℝ) < (2 : ℝ) ^ j / 64 := by
  set y : ℝ := (2 : ℝ) ^ j with hy
  have hy40 : (2 : ℝ) ^ 40 ≤ y := pow_le_pow_right₀ (by norm_num) hj
  have hy0 : 0 < y := by positivity
  have h4 : ((4 : ℝ) ^ j) ^ (41 / 100 : ℝ) = y ^ (41 / 50 : ℝ) := by
    have : (4 : ℝ) ^ j = y ^ (2 : ℝ) := by
      rw [Real.rpow_two, hy, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, ← Real.rpow_mul hy0.le]; norm_num
  have hs : y = y ^ (41 / 50 : ℝ) * y ^ (9 / 50 : ℝ) := by
    rw [← Real.rpow_add hy0]; norm_num
  have h64 : (64 : ℝ) < y ^ (9 / 50 : ℝ) := by
    have h1 : ((2 : ℝ) ^ 40) ^ (9 / 50 : ℝ) ≤ y ^ (9 / 50 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hy40 (by norm_num)
    have h2 : (64 : ℝ) < ((2 : ℝ) ^ 40) ^ (9 / 50 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : (64 : ℝ) = 2 ^ (6 : ℝ) := by norm_num
      rw [this]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    linarith
  have hp : 0 < y ^ (41 / 50 : ℝ) := Real.rpow_pos_of_pos hy0 _
  rw [h4, lt_div_iff₀ (by norm_num)]
  nlinarith

end ElboimSly.Paper.Escape
