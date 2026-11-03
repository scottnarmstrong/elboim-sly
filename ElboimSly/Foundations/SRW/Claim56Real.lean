/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Real-variable estimates for Claim 5.6, event `𝓑_0`
-/

@[expose] public section

open Set
open scoped NNReal Real

namespace ElboimSly
namespace SRW

/-- Part A, increasing case. -/
theorem partA_up {v p : ℤ} {δ s₀ : ℝ} {ℓ : ℕ} (hℓ : s₀ + 2 ≤ ℓ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ s₀)
    (hpl : (p : ℝ) ≤ v + δ + 1 / 2) (hpg : (v : ℝ) + δ + 1 / 2 < p + 1) :
    v ≤ p ∧ p ≤ v + ℓ - 1 := by
  constructor
  · have : (v : ℝ) - 1 < p := by linarith
    have : v - 1 < p := by exact_mod_cast this
    omega
  · have : (p : ℝ) < v + ℓ - 1 := by linarith
    have : p < v + ℓ - 1 := by exact_mod_cast this
    omega

/-- Part A, decreasing case. -/
theorem partA_down {v p : ℤ} {δ s₀ : ℝ} {ℓ : ℕ} (hℓ : s₀ + 2 ≤ ℓ) (hδ0 : δ < 0) (hδ : -s₀ ≤ δ)
    (hpl : (p : ℝ) ≤ v + δ + 1 / 2) (hpg : (v : ℝ) + δ + 1 / 2 < p + 1) :
    v - ℓ + 1 ≤ p ∧ p ≤ v := by
  constructor
  · have : (v : ℝ) - ℓ < p := by linarith
    have : v - ℓ < p := by exact_mod_cast this
    omega
  · have : (p : ℝ) < v + 1 := by linarith
    have : p < v + 1 := by exact_mod_cast this
    omega

/-- Margins of `f` inside `B^-`: offsets of `f` in a coordinate. -/
theorem margin_coord {P s₀ N L e lam : ℝ} (hP : 8 ≤ P) (_hs₀ : 288 ≤ s₀) (hN1 : P * s₀ ≤ N)
    (hL1 : N / 2 ≤ L) (he0 : 0 ≤ e) (he1 : e ≤ L - 1) (hlam0 : 1 / P ≤ lam) (hlam1 : lam ≤ 1) :
    s₀ / 4 ≤ e + lam * (L / 2 - e) ∧ e + lam * (L / 2 - e) ≤ L - s₀ / 4 := by
  have hP0 : 0 < P := by linarith
  have hlamP : 1 ≤ lam * P := by
    calc 1 = 1 / P * P := by field_simp
      _ ≤ lam * P := by gcongr
  have hLP : P * s₀ ≤ L * 2 := by linarith
  have hL0 : 0 < L := by nlinarith
  have hlamL : s₀ / 4 ≤ lam * (L / 2) := by
    have : s₀ / 4 ≤ (lam * P) * (L / 2) / P := by
      rw [le_div_iff₀ hP0]
      nlinarith
    calc s₀ / 4 ≤ (lam * P) * (L / 2) / P := this
      _ = lam * (L / 2) := by field_simp
  constructor
  · have : e + lam * (L / 2 - e) = (1 - lam) * e + lam * (L / 2) := by ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.2 hlam1) he0]
  · have : e + lam * (L / 2 - e) = L - ((1 - lam) * (L - e) + lam * (L / 2)) := by ring
    rw [this]
    have h1 : 0 ≤ (1 - lam) * (L - e) := mul_nonneg (sub_nonneg.2 hlam1) (by linarith)
    linarith

/-- The distance `|q - v|` in a coordinate. -/
theorem dist_centre {L e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ L - 1) : |L / 2 - e| ≤ L / 2 := by
  rw [abs_le]; constructor <;> linarith

/-- Lipschitz bound for the interpolation in a coordinate. -/
theorem f_lip {P s₀ N L e lam lam' s s' : ℝ} (hP : 0 < P) (hs₀ : 0 < s₀) (hN2 : N ≤ 2 * P * s₀)
    (hL2 : L ≤ N) (he0 : 0 ≤ e) (he1 : e ≤ L - 1) (hlam : lam - lam' ≤ (s - s') / (P * s₀ ^ 2))
    (hlam' : lam' ≤ lam) (hss : s' ≤ s) :
    |lam * (L / 2 - e) - lam' * (L / 2 - e)| ≤ (s - s') / s₀ := by
  have hd : |L / 2 - e| ≤ P * s₀ := by
    have := dist_centre he0 he1
    linarith
  have e1 : lam * (L / 2 - e) - lam' * (L / 2 - e) = (lam - lam') * (L / 2 - e) := by ring
  rw [e1, abs_mul, abs_of_nonneg (sub_nonneg.2 hlam')]
  calc (lam - lam') * |L / 2 - e| ≤ ((s - s') / (P * s₀ ^ 2)) * (P * s₀) := by
        apply mul_le_mul hlam hd (abs_nonneg _)
        have : 0 ≤ s - s' := by linarith
        positivity
    _ = (s - s') / s₀ := by field_simp

end SRW
end ElboimSly
