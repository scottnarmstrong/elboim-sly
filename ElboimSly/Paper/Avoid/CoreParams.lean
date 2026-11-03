/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IndDelta
public import ElboimSly.Frozen.Defs.IndThetaH
public import Mathlib

/-!
# ES22 §4, Lemma 4.1 (core form): the choice of `β_{41}` and the exponent arithmetic

ES22 Lemma 4.1, first paragraph of the proof.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace ElboimSly.Paper

theorem avoid_indDelta_pos {d : ℕ} (hd : 1 ≤ d) : 0 < indDelta d := by
  unfold indDelta
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem indDelta_le {d : ℕ} (hd : 5 ≤ d) : indDelta d ≤ 1 / 75000 := by
  unfold indDelta
  have : (25 : ℝ) ≤ (d : ℝ) ^ 2 := by
    have : (5 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The size conditions on `β`. -/
theorem exists_beta41 {d : ℕ} (hd : 5 ≤ d) (n₀ : ℕ) :
    ∃ β41 : ℝ, (10 : ℝ) ^ 14 ≤ β41 ∧ ∀ β : ℝ, β41 ≤ β →
      (4 : ℝ) ^ (n₀ + 1) ≤ β ^ indDelta d / 2 ∧ (3 : ℝ) ^ (6 * d + 15) ≤ β ^ indDelta d / 2 ∧
        β ^ (3 * indDelta d) ≤ β / 2 := by
  have hδ := avoid_indDelta_pos (d := d) (by omega)
  have hδ' := indDelta_le hd
  set M : ℝ := 2 * max ((4 : ℝ) ^ (n₀ + 1)) ((3 : ℝ) ^ (6 * d + 15)) with hM
  have hM0 : 0 < M := by positivity
  refine ⟨max ((10 : ℝ) ^ 14) (M ^ (1 / indDelta d)), le_max_left _ _, fun β hβ => ?_⟩
  have hβ1 : (10 : ℝ) ^ 14 ≤ β := (le_max_left _ _).trans hβ
  have hβ2 : M ^ (1 / indDelta d) ≤ β := (le_max_right _ _).trans hβ
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ1
  have hβδ : M ≤ β ^ indDelta d := by
    calc M = (M ^ (1 / indDelta d)) ^ indDelta d := by
          rw [← Real.rpow_mul hM0.le, one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      _ ≤ β ^ indDelta d := Real.rpow_le_rpow (by positivity) hβ2 hδ.le
  refine ⟨?_, ?_, ?_⟩
  · have : 2 * (4 : ℝ) ^ (n₀ + 1) ≤ M := by rw [hM]; gcongr; exact le_max_left _ _
    linarith
  · have : 2 * (3 : ℝ) ^ (6 * d + 15) ≤ M := by rw [hM]; gcongr; exact le_max_right _ _
    linarith
  · have h1 : (1 : ℝ) ≤ β := le_trans (by norm_num) hβ1
    have h2 : β ^ (3 * indDelta d) ≤ β ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    have h3 : (2 : ℝ) ≤ β ^ ((1 : ℝ) / 2) := by
      have : (10 : ℝ) ^ 7 ≤ β ^ ((1 : ℝ) / 2) := by
        calc (10 : ℝ) ^ 7 = ((10 : ℝ) ^ 14) ^ ((1 : ℝ) / 2) := by
              rw [← Real.sqrt_eq_rpow, show (10 : ℝ) ^ 14 = ((10 : ℝ) ^ 7) ^ 2 by norm_num]
              exact (Real.sqrt_sq (by positivity)).symm
          _ ≤ β ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hβ1 (by norm_num)
      linarith [show (2 : ℝ) ≤ 10 ^ 7 by norm_num]
    have h4 : β = β ^ ((1 : ℝ) / 2) * β ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hβ0]; norm_num
    calc β ^ (3 * indDelta d) ≤ β ^ ((1 : ℝ) / 2) := h2
      _ ≤ β / 2 := by
          nlinarith [Real.rpow_pos_of_pos hβ0 ((1 : ℝ) / 2)]

/-- `β^{3δ} ≤ 4ⁿ` and `β^δ / 2 ≤ 4ⁿ` from `β < 4^{n+1}`. -/
theorem beta_pow_le {d : ℕ} (hd : 5 ≤ d) {β : ℝ} (hβ1 : 1 ≤ β) {n : ℕ} (hn : 1 ≤ n)
    (hβn : β < (4 : ℝ) ^ (n + 1)) : β ^ (3 * indDelta d) ≤ (4 : ℝ) ^ n := by
  have hδ := avoid_indDelta_pos (d := d) (by omega)
  have hδ' := indDelta_le hd
  have hβ0 : 0 < β := by linarith
  calc β ^ (3 * indDelta d) ≤ ((4 : ℝ) ^ (n + 1)) ^ (3 * indDelta d) :=
        Real.rpow_le_rpow hβ0.le hβn.le (by linarith)
    _ = (4 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * (3 * indDelta d)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    _ ≤ (4 : ℝ) ^ (n : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        push_cast
        nlinarith
    _ = (4 : ℝ) ^ n := Real.rpow_natCast _ _

/-- Exponent arithmetic for ES22 Claim 4.3 at `t = β^{3δ}`, `L = t^{θ_H}`:
`L^{d-2} t^{-(d-2)/2} ≤ β^{-δ/30}`. -/
theorem claim3_exponent {d : ℕ} (hd : 5 ≤ d) {β : ℝ} (hβ1 : 1 ≤ β) :
    ((β ^ (3 * indDelta d)) ^ indThetaH) ^ (d - 2) *
        (β ^ (3 * indDelta d)) ^ (-((d - 2 : ℕ) : ℝ) / 2) ≤ β ^ (-indDelta d / 30) := by
  have hδ := avoid_indDelta_pos (d := d) (by omega)
  have hβ0 : 0 < β := by linarith
  have hm : (3 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := by
    have : 3 ≤ d - 2 := by omega
    exact_mod_cast this
  have hθ : indThetaH = 41 / 100 := rfl
  set t := β ^ (3 * indDelta d) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hβ0 _
  have e1 : (t ^ indThetaH) ^ (d - 2) = t ^ (indThetaH * ((d - 2 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
  rw [e1, ← Real.rpow_add ht0, ht, ← Real.rpow_mul hβ0.le]
  apply Real.rpow_le_rpow_of_exponent_le hβ1
  rw [hθ]
  nlinarith

end ElboimSly.Paper

end
