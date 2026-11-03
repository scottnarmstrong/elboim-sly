/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Blocks
public import Mathlib

/-!
# Elementary facts about `j_n` and `I_*`

Scale and the constant γ; The points p_i.
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

open ElboimSly.Paper

theorem escJ_real_bounds {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ 20 ≤ 2 ^ escJ n ∧ (2 : ℝ) ^ escJ n < 2 * (n : ℝ) ^ 20 := by
  refine ⟨?_, ?_⟩
  · exact_mod_cast le_two_pow_escJ n
  · exact_mod_cast two_pow_escJ_lt hn

theorem escJ_ge_twenty {n : ℕ} (hn : 2 ≤ n) : 20 ≤ escJ n := by
  by_contra h
  push Not at h
  have h1 := le_two_pow_escJ n
  have h2 : 2 ^ escJ n ≤ 2 ^ 19 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ 20 ≤ n ^ 20 := Nat.pow_le_pow_left hn 20
  have : (2 : ℕ) ^ 19 < 2 ^ 20 := by norm_num
  omega

theorem escJ_le_twenty_mul {n : ℕ} (hn : 2 ≤ n) : escJ n ≤ 20 * n := by
  by_contra h
  push Not at h
  have h1 := two_pow_escJ_lt hn
  have h2 : 2 ^ (20 * n + 1) ≤ 2 ^ escJ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : n < 2 ^ n := Nat.lt_two_pow_self
  have h4 : n ^ 20 < (2 ^ n) ^ 20 := Nat.pow_lt_pow_left h3 (by norm_num)
  have h5 : (2 ^ n) ^ 20 = 2 ^ (20 * n) := by rw [← pow_mul]; ring_nf
  have h6 : 2 ^ (20 * n + 1) = 2 * 2 ^ (20 * n) := by rw [pow_succ]; ring
  omega

theorem escIstar_le (n j : ℕ) : escIstar n j ≤ n ^ 3 := Nat.findGreatest_le _

theorem escIstar_spec (n j : ℕ) : 16 * (escIstar n j * escLambda n) ≤ 3 * 2 ^ j := by
  unfold escIstar
  by_cases h : ∃ i, i ≤ n ^ 3 ∧ (1 ≤ i ∧ 16 * (i * escLambda n) ≤ 3 * 2 ^ j)
  · have := Nat.findGreatest_spec (P := fun i => 1 ≤ i ∧ 16 * (i * escLambda n) ≤ 3 * 2 ^ j)
      (m := h.choose) h.choose_spec.1 h.choose_spec.2
    exact this.2
  · push Not at h
    have : Nat.findGreatest (fun i => 1 ≤ i ∧ 16 * (i * escLambda n) ≤ 3 * 2 ^ j) (n ^ 3) = 0 := by
      apply Nat.findGreatest_eq_zero_iff.2
      intro i _ hile hP
      exact absurd hP.2 (not_le.2 (h i hile hP.1))
    rw [this]; simp

theorem escIstar_ge {n : ℕ} (hn : 2 ≤ n) :
    9 * n ^ 3 / 16 ≤ escIstar n (escJ n) := by
  unfold escIstar
  refine Nat.le_findGreatest ?_ ?_
  · omega
  · have h2 : 8 ≤ n ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    refine ⟨?_, ?_⟩
    · omega
    · have hl : escLambda n ≤ n ^ 17 / 3 := le_rfl
      have h20 := le_two_pow_escJ n
      -- `16 (⌊9n³/16⌋ λ) ≤ 9 n³ · n^17 / 3 = 3 n^20`
      have h1 : 16 * (9 * n ^ 3 / 16) ≤ 9 * n ^ 3 := Nat.mul_div_le _ _
      have h3 : 3 * (n ^ 17 / 3) ≤ n ^ 17 := Nat.mul_div_le _ _
      calc 16 * (9 * n ^ 3 / 16 * escLambda n) = (16 * (9 * n ^ 3 / 16)) * escLambda n := by ring
        _ ≤ (9 * n ^ 3) * escLambda n := Nat.mul_le_mul_right _ h1
        _ = 3 * (n ^ 3 * (3 * escLambda n)) := by ring
        _ ≤ 3 * (n ^ 3 * n ^ 17) := by
            refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
            exact h3
        _ = 3 * n ^ 20 := by ring
        _ ≤ 3 * 2 ^ escJ n := Nat.mul_le_mul_left _ h20

end ElboimSly.Paper.Escape
