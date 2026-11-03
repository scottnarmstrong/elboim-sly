/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Asymptotic helpers for constants and thresholds of the base

Constants and thresholds of the base (existence of `n_K(d)` and `β_0(d)`).

* `exists_poly_le_exp`: a polynomial is eventually dominated by `e^{κ t}`.
* `exists_nat_poly_le`: a polynomial of lower degree is eventually dominated by `n^m`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper

theorem exists_poly_le_exp (k : ℕ) (κ C : ℝ) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → C * t ^ k ≤ Real.exp (κ * t) := by
  set C' : ℝ := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  set M : ℝ := C' * (k.factorial : ℝ) * (2 / κ) ^ k with hM
  have hMpos : 0 < M := by
    have : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    positivity
  refine ⟨max 0 ((2 / κ) * Real.log M), fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have ht1 : (2 / κ) * Real.log M ≤ t := (le_max_right _ _).trans ht
  have hx : 0 ≤ κ * t / 2 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (κ * t / 2) hx k
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : t ^ k ≤ (2 / κ) ^ k * (k.factorial : ℝ) * Real.exp (κ * t / 2) := by
    have h3 : (κ * t / 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (κ * t / 2) := by
      have := (div_le_iff₀ hfac).1 h1
      linarith [mul_comm (k.factorial : ℝ) (Real.exp (κ * t / 2))]
    have h4 : t = (2 / κ) * (κ * t / 2) := by field_simp
    calc t ^ k = ((2 / κ) * (κ * t / 2)) ^ k := by rw [← h4]
      _ = (2 / κ) ^ k * (κ * t / 2) ^ k := mul_pow _ _ _
      _ ≤ (2 / κ) ^ k * ((k.factorial : ℝ) * Real.exp (κ * t / 2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have h5 : M ≤ Real.exp (κ * t / 2) := by
    calc M = Real.exp (Real.log M) := (Real.exp_log hMpos).symm
      _ ≤ Real.exp (κ * t / 2) := Real.exp_le_exp.2 (by
          have : Real.log M ≤ κ * t / 2 := by
            have h6 := mul_le_mul_of_nonneg_left ht1 hκ.le
            have e : κ * ((2 / κ) * Real.log M) = 2 * Real.log M := by field_simp
            linarith
          exact this)
  have htk : 0 ≤ t ^ k := by positivity
  calc C * t ^ k ≤ C' * t ^ k := mul_le_mul_of_nonneg_right hCC' htk
    _ ≤ C' * ((2 / κ) ^ k * (k.factorial : ℝ) * Real.exp (κ * t / 2)) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = M * Real.exp (κ * t / 2) := by rw [hM]; ring
    _ ≤ Real.exp (κ * t / 2) * Real.exp (κ * t / 2) :=
        mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = Real.exp (κ * t) := by rw [← Real.exp_add]; congr 1; ring

/-- A cubic polynomial is eventually dominated by `n^4`. -/
theorem exists_nat_poly_le (A B C : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A + B * (n : ℝ) + C * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
  refine ⟨⌈|A| + |B| + |C| + 3⌉₊ + 1, fun n hn => ?_⟩
  have hn' : |A| + |B| + |C| + 3 ≤ (n : ℝ) := by
    have h1 : |A| + |B| + |C| + 3 ≤ (⌈|A| + |B| + |C| + 3⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈|A| + |B| + |C| + 3⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith [abs_nonneg A, abs_nonneg B, abs_nonneg C]
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
  have hnp : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have hA : A ≤ |A| * (n : ℝ) ^ 3 := by
    calc A ≤ |A| := le_abs_self A
      _ = |A| * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (abs_nonneg A)
  have hB : B * n ≤ |B| * (n : ℝ) ^ 3 := by
    calc B * n ≤ |B| * n := mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hnp (abs_nonneg B)
  have hC : C * (n : ℝ) ^ 3 ≤ |C| * (n : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hlast : (|A| + |B| + |C|) * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
    calc (|A| + |B| + |C|) * (n : ℝ) ^ 3 ≤ (n : ℝ) * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (n : ℝ) ^ 4 := by ring
  nlinarith

end ElboimSly.Paper
