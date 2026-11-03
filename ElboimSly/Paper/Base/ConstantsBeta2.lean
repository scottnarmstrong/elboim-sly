/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ConstantsBeta
public import Mathlib

/-!
# The threshold `β_0(d)`: condition (B2)

Constants and thresholds of the base, "Existence of `β_0(d)`".
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper

theorem exists_B2 {d : ℕ} (hd : 1 ≤ d) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ t →
      2 * (n : ℝ) ^ 10 ≤ (⌊Real.exp (indDelta d * t)⌋₊ : ℝ) ∧
        (5 * (n : ℝ) ^ 10) ^ ((5 * d : ℝ) / 2) < (⌊Real.exp (indDelta d * t)⌋₊ : ℝ) := by
  have hδ := indDelta_pos hd
  obtain ⟨Ta, ha⟩ := exists_poly_le_exp 10 (indDelta d) 3 hδ
  obtain ⟨Tb, hb⟩ := exists_poly_le_exp (30 * d) (indDelta d) ((5 : ℝ) ^ (3 * d) + 1) hδ
  refine ⟨max 1 (max Ta Tb), le_max_left _ _, fun t ht n hn1 hnt => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have hta : Ta ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htb : Tb ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set x := Real.exp (indDelta d * t) with hx
  have hfl : x - 1 < (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x; linarith
  have hn10 : (n : ℝ) ^ 10 ≤ t ^ 10 := pow_le_pow_left₀ (by positivity) hnt 10
  have ht10 : (1 : ℝ) ≤ t ^ 10 := one_le_pow₀ ht1
  constructor
  · have h1 := ha t hta
    have : 2 * (n : ℝ) ^ 10 ≤ x - 1 := by linarith
    linarith
  · have hbase : (1 : ℝ) ≤ 5 * (n : ℝ) ^ 10 := by
      have : (1 : ℝ) ≤ (n : ℝ) ^ 10 := one_le_pow₀ hnr
      linarith
    have hq : ((5 * d : ℝ) / 2) ≤ ((3 * d : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have h1 : (5 * (n : ℝ) ^ 10) ^ ((5 * d : ℝ) / 2) ≤ (5 * (n : ℝ) ^ 10) ^ (3 * d) := by
      calc (5 * (n : ℝ) ^ 10) ^ ((5 * d : ℝ) / 2) ≤ (5 * (n : ℝ) ^ 10) ^ (((3 * d : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hbase hq
        _ = (5 * (n : ℝ) ^ 10) ^ (3 * d) := Real.rpow_natCast _ _
    have h2 : (5 * (n : ℝ) ^ 10) ^ (3 * d) ≤ (5 : ℝ) ^ (3 * d) * t ^ (30 * d) := by
      calc (5 * (n : ℝ) ^ 10) ^ (3 * d) ≤ (5 * t ^ 10) ^ (3 * d) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = (5 : ℝ) ^ (3 * d) * t ^ (30 * d) := by
            rw [mul_pow, ← pow_mul]; ring_nf
    have h3 := hb t htb
    have ht30 : (1 : ℝ) ≤ t ^ (30 * d) := one_le_pow₀ ht1
    have : (5 : ℝ) ^ (3 * d) * t ^ (30 * d) ≤ x - 1 := by nlinarith
    calc (5 * (n : ℝ) ^ 10) ^ ((5 * d : ℝ) / 2) ≤ _ := h1.trans h2
      _ ≤ x - 1 := this
      _ < _ := hfl

end ElboimSly.Paper
