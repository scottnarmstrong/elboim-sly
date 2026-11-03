/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.DensityAux
public import Mathlib

/-!
# The two asymptotic estimates of density of the explored walks around p_i

With `K = 3^d · 6 · 33^d` and `m = 2d + 2`:

* `caseA_arith`: for `n ≥ N₁` and `r ≥ n^17/7`, `n^3 · K · (4n^20)² (ln 4n^20)^m ≤ r^{8/3}/2`
  (the exponents `43 < 136/3`);
* `caseB_arith`: for `r ≥ Y₀` and `x ≤ r^{3/20}`, `x · K · (3r)² (ln 3r)^m ≤ r^{8/3}/2`
  (the exponents `2.15 < 8/3`).
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper

/-- The constant `K = 3^d · C_vis`, `C_vis = 6 · 33^d`. -/
noncomputable def densK (d : ℕ) : ℝ := 3 ^ d * (6 * 33 ^ d)

lemma densK_pos (d : ℕ) : 0 < densK d := by unfold densK; positivity

lemma log_four_n20 {n : ℝ} (hn : 4 ≤ n) : Real.log (4 * n ^ 20) ≤ 21 * Real.log n := by
  have hn0 : 0 < n := by linarith
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have : Real.log 4 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  push_cast; linarith

theorem caseA_arith (d : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 4 ≤ n → ∀ r : ℝ, (n : ℝ) ^ 17 / 7 ≤ r →
      (n : ℝ) ^ 3 * densK d * ((4 * (n : ℝ) ^ 20) ^ 2 * Real.log (4 * (n : ℝ) ^ 20) ^ (2 * d + 2)) ≤
        r ^ (8 / 3 : ℝ) / 2 := by
  set K := densK d with hK
  have hK0 : 0 < K := densK_pos d
  set m := 2 * d + 2 with hm
  set ε : ℝ := 1 / (2 * 7 ^ (8 / 3 : ℝ) * 16 * K * 21 ^ m) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨X, hX⟩ := eventually_atTop.1 (eventually_log_le (m : ℝ) (7 / 3) ε (by norm_num) hε0)
  refine ⟨max 4 ⌈X⌉₊, fun n hn hn4 r hr => ?_⟩
  have hnX : X ≤ n := le_trans (Nat.le_ceil X) (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 := hX n hnX
  rw [Real.rpow_natCast] at h1
  have h2 : Real.log (4 * (n : ℝ) ^ 20) ^ m ≤ (21 * Real.log n) ^ m :=
    pow_le_pow_left₀ (Real.log_nonneg (by have := one_le_pow₀ (n := 20) (show (1 : ℝ) ≤ n by linarith); linarith)) (log_four_n20 hn4r) m
  have hrpow : ((n : ℝ) ^ 17 / 7) ^ (8 / 3 : ℝ) ≤ r ^ (8 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hr (by norm_num)
  have hlhs : ((n : ℝ) ^ 17 / 7) ^ (8 / 3 : ℝ) = (n : ℝ) ^ (136 / 3 : ℝ) / 7 ^ (8 / 3 : ℝ) := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hn43 : (n : ℝ) ^ (136 / 3 : ℝ) = (n : ℝ) ^ 43 * (n : ℝ) ^ (7 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  have h7 : (0 : ℝ) < 7 ^ (8 / 3 : ℝ) := by positivity
  calc (n : ℝ) ^ 3 * K * ((4 * (n : ℝ) ^ 20) ^ 2 * Real.log (4 * (n : ℝ) ^ 20) ^ m)
      ≤ (n : ℝ) ^ 3 * K * ((4 * (n : ℝ) ^ 20) ^ 2 * (21 * Real.log n) ^ m) := by gcongr
    _ = 16 * K * 21 ^ m * (n : ℝ) ^ 43 * Real.log n ^ m := by
        rw [mul_pow 21]; ring
    _ ≤ 16 * K * 21 ^ m * (n : ℝ) ^ 43 * (ε * (n : ℝ) ^ (7 / 3 : ℝ)) := by gcongr
    _ = (n : ℝ) ^ (136 / 3 : ℝ) / (2 * 7 ^ (8 / 3 : ℝ)) := by
        rw [hn43, hε]; field_simp
    _ ≤ r ^ (8 / 3 : ℝ) / 2 := by
        have hz : (n : ℝ) ^ (136 / 3 : ℝ) / 7 ^ (8 / 3 : ℝ) ≤ r ^ (8 / 3 : ℝ) := by
          rw [← hlhs]; exact hrpow
        rw [div_le_iff₀ h7] at hz
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hz]

theorem caseB_arith (d : ℕ) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ r : ℝ, Y ≤ r → ∀ x : ℝ, 0 ≤ x → x ≤ r ^ (3 / 20 : ℝ) →
      x * densK d * ((3 * r) ^ 2 * Real.log (3 * r) ^ (2 * d + 2)) ≤ r ^ (8 / 3 : ℝ) / 2 := by
  set K := densK d with hK
  have hK0 : 0 < K := densK_pos d
  set m := 2 * d + 2 with hm
  set ε : ℝ := 1 / (36 * K) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨X, hX⟩ := eventually_atTop.1 (eventually_log_le (m : ℝ) (1 / 2) ε (by norm_num) hε0)
  refine ⟨max 1 X, le_max_left _ _, fun r hr x hx0 hxr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : 0 < r := by linarith
  have h3r : X ≤ 3 * r := by
    have := le_trans (le_max_right _ _) hr; linarith
  have h1 := hX (3 * r) h3r
  rw [Real.rpow_natCast] at h1
  have h3 : (3 * r) ^ (1 / 2 : ℝ) ≤ 2 * r ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hr0.le]
    have : (3 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      calc (3 : ℝ) ^ (1 / 2 : ℝ) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hr0.le _)
  have hlogpos : 0 ≤ Real.log (3 * r) ^ m := pow_nonneg (Real.log_nonneg (by linarith)) _
  have hpow : r ^ (3 / 20 : ℝ) * r ^ (2 : ℕ) * r ^ (1 / 2 : ℝ) ≤ r ^ (8 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr0, ← Real.rpow_add hr0]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
  calc x * K * ((3 * r) ^ 2 * Real.log (3 * r) ^ m)
      ≤ r ^ (3 / 20 : ℝ) * K * ((3 * r) ^ 2 * (ε * (3 * r) ^ (1 / 2 : ℝ))) := by gcongr
    _ ≤ r ^ (3 / 20 : ℝ) * K * ((3 * r) ^ 2 * (ε * (2 * r ^ (1 / 2 : ℝ)))) := by gcongr
    _ = (18 * K * ε) * (r ^ (3 / 20 : ℝ) * r ^ (2 : ℕ) * r ^ (1 / 2 : ℝ)) := by ring
    _ ≤ (18 * K * ε) * r ^ (8 / 3 : ℝ) := by gcongr
    _ = r ^ (8 / 3 : ℝ) / 2 := by rw [hε]; field_simp; ring

end ElboimSly.Paper
