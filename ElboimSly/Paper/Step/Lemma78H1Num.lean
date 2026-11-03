/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Numerics for the event cH_1

The "`n` large" inequalities of the `Osc_1` argument: `4 t_n^{θ_H} ≤ 1.9^n` (as `4^{θ_H} < 1.9`),
and `4d ⌈t_n / 3.6^n⌉ exp(-(1.9^n/2)²/(64 · 3.6^n)) ≤ exp(-n³)` (as `1.9²/3.6 > 1`).
-/

@[expose] public section

open Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

theorem h1_four_rpow_lt : (4 : ℝ) ^ ((41 : ℝ) / 100) < 19 / 10 := by
  have h100 : ((4 : ℝ) ^ ((41 : ℝ) / 100)) ^ 100 = 4 ^ 41 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hcon
  push Not at hcon
  have := pow_le_pow_left₀ (by norm_num) hcon 100
  rw [h100] at this
  norm_num at this

theorem h1_eventually_theta :
    ∀ᶠ n : ℕ in atTop, 4 * ((4 : ℝ) ^ (n + 1)) ^ ((41 : ℝ) / 100) ≤ (19 / 10 : ℝ) ^ n := by
  set b : ℝ := (4 : ℝ) ^ ((41 : ℝ) / 100) with hb
  have hb0 : 0 < b := by positivity
  have hb1 := h1_four_rpow_lt
  have hq : b / (19 / 10) < 1 := by rw [div_lt_one (by norm_num)]; exact hb1
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb0.le (by norm_num)) hq
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * b) by positivity))
  filter_upwards [hev] with n hn
  have e : ((4 : ℝ) ^ (n + 1)) ^ ((41 : ℝ) / 100) = b ^ (n + 1) := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [e]
  rw [div_pow, div_lt_iff₀ (by positivity)] at hn
  have : 4 * b ^ (n + 1) = 4 * b * b ^ n := by ring
  rw [this]
  have h5 : 4 * b * b ^ n < (19 / 10 : ℝ) ^ n := by
    calc 4 * b * b ^ n < 4 * b * (1 / (4 * b) * (19 / 10) ^ n) := by gcongr
      _ = (19 / 10 : ℝ) ^ n := by field_simp
  exact h5.le

theorem h1_eventually_exp (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, (4 * d * ⌈(4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n⌉₊ : ℝ) *
      Real.exp (-((19 / 10 : ℝ) ^ n / 2) ^ 2 / (16 * 2 ^ 2 * (36 / 10 : ℝ) ^ n)) ≤
        Real.exp (-(n : ℝ) ^ 3) := by
  set a : ℝ := (19 / 10) ^ 2 / (36 / 10) with ha
  have ha1 : 1 < a := by rw [ha]; norm_num
  have e1 := (tendsto_pow_const_div_const_pow_of_one_lt 3 ha1).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 1024 by norm_num))
  have e2 : ∀ᶠ n : ℕ in atTop, (20 * d : ℝ) ≤ Real.exp n :=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [e1, e2, eventually_ge_atTop 1] with n h1 h2 hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [div_lt_iff₀ (by positivity)] at h1
  have hexp : -((19 / 10 : ℝ) ^ n / 2) ^ 2 / (16 * 2 ^ 2 * (36 / 10 : ℝ) ^ n) =
      -(a ^ n / 256) := by
    have : a ^ n = ((19 / 10 : ℝ) ^ n) ^ 2 / (36 / 10 : ℝ) ^ n := by
      rw [ha, div_pow, ← pow_mul, mul_comm 2 n, pow_mul]
    rw [this]
    field_simp
    ring
  rw [hexp]
  have hceil : (⌈(4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n⌉₊ : ℝ) ≤ 5 * (10 / 9 : ℝ) ^ n := by
    have hc := Nat.ceil_lt_add_one
      (show (0 : ℝ) ≤ (4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n by positivity)
    have : (4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n = 4 * (10 / 9 : ℝ) ^ n := by
      have h9 : (10 / 9 : ℝ) ^ n = 4 ^ n / (36 / 10 : ℝ) ^ n := by
        rw [← div_pow]; norm_num
      rw [h9, pow_succ]
      field_simp
    rw [this] at hc ⊢
    have : (1 : ℝ) ≤ (10 / 9 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    linarith
  have hexp9 : (10 / 9 : ℝ) ^ n ≤ Real.exp n := by
    calc (10 / 9 : ℝ) ^ n ≤ (Real.exp 1) ^ n := by
          gcongr
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
      _ = Real.exp n := by rw [← Real.exp_nat_mul]; simp
  have hlhs : (4 * d * ⌈(4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n⌉₊ : ℝ) ≤
      Real.exp n * Real.exp n := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc (4 * d * ⌈(4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n⌉₊ : ℝ)
        ≤ 4 * d * (5 * (10 / 9 : ℝ) ^ n) := by gcongr
      _ = (20 * d) * (10 / 9 : ℝ) ^ n := by ring
      _ ≤ Real.exp n * Real.exp n := by gcongr
  have hn3' : (n : ℝ) ^ 3 ≤ a ^ n / 1024 := by linarith
  have hn3 : 2 * (n : ℝ) ≤ a ^ n / 512 := by
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1'
    have : (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith
    linarith
  calc (4 * d * ⌈(4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n⌉₊ : ℝ) * Real.exp (-(a ^ n / 256))
      ≤ (Real.exp n * Real.exp n) * Real.exp (-(a ^ n / 256)) := by gcongr
    _ = Real.exp (2 * n - a ^ n / 256) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(n : ℝ) ^ 3) := by
        apply Real.exp_le_exp.2
        linarith

end ElboimSly.Paper.Step

end
