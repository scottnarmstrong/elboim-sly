/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Poisson probabilities: mode and the Stirling upper bound

Poisson facts (a), (b).  `po r n = e^{-r} r^n / n!`.
-/

@[expose] public section

open Real Nat

namespace ElboimSly
namespace SRW

/-- The Poisson probability `po_r(n) = e^{-r} r^n / n!`. -/
noncomputable def po (r : ℝ) (n : ℕ) : ℝ := Real.exp (-r) * r ^ n / n !

theorem po_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ po r n := by
  unfold po; positivity

theorem po_succ (r : ℝ) (n : ℕ) : po r (n + 1) = po r n * r / (n + 1) := by
  unfold po
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- Poisson facts (a): the mode. -/
theorem po_le_po_floor {r : ℝ} (hr : 0 ≤ r) (m : ℕ) : po r m ≤ po r ⌊r⌋₊ := by
  have hup : ∀ k, k + 1 ≤ ⌊r⌋₊ → po r k ≤ po r (k + 1) := by
    intro k hk
    have hk' : ((k : ℝ) + 1) ≤ r := by
      have := (Nat.le_floor_iff hr).1 hk
      exact_mod_cast this
    rw [po_succ]
    have hp := po_nonneg hr k
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hdown : ∀ k, ⌊r⌋₊ ≤ k → po r (k + 1) ≤ po r k := by
    intro k hk
    have hk' : r < (k : ℝ) + 1 := by
      have := Nat.lt_floor_add_one r
      have h2 : (⌊r⌋₊ : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [po_succ]
    have hp := po_nonneg hr k
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h1 : ∀ k, m ≤ k → k ≤ ⌊r⌋₊ → po r m ≤ po r k := by
    intro k hmk
    induction hmk with
    | refl => intro _; exact le_rfl
    | step hk ih => intro hle; exact (ih (by omega)).trans (hup _ hle)
  have h2 : ∀ k, ⌊r⌋₊ ≤ k → po r k ≤ po r ⌊r⌋₊ := by
    intro k hk
    induction hk with
    | refl => exact le_rfl
    | step hk ih => exact (hdown _ hk).trans ih
  rcases le_total m ⌊r⌋₊ with h | h
  · exact h1 _ h le_rfl
  · exact h2 m h

/-- Poisson facts (b): `po_r(n) ≤ (2πn)^{-1/2}` for `n ≥ 1`. -/
theorem po_le_inv_sqrt {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 1 ≤ n) :
    po r n ≤ 1 / √(2 * π * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hst := Stirling.le_factorial_stirling n
  have hpos : 0 < √(2 * π * n) * (n / Real.exp 1) ^ n := by positivity
  have hfac : 0 < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have key : r ^ n ≤ Real.exp (r - n) * n ^ n := by
    have h1 : r / n ≤ Real.exp (r / n - 1) := by
      have := Real.add_one_le_exp (r / n - 1)
      linarith
    have h2 : (r / n) ^ n ≤ Real.exp (r / n - 1) ^ n := pow_le_pow_left₀ (by positivity) h1 n
    rw [← Real.exp_nat_mul, div_pow] at h2
    have h3 : (n : ℝ) * (r / n - 1) = r - n := by field_simp
    rw [h3, div_le_iff₀ (by positivity)] at h2
    exact h2
  unfold po
  calc Real.exp (-r) * r ^ n / n ! ≤ Real.exp (-r) * r ^ n /
        (√(2 * π * n) * (n / Real.exp 1) ^ n) :=
        div_le_div_of_nonneg_left (by positivity) hpos hst
    _ ≤ Real.exp (-r) * (Real.exp (r - n) * n ^ n) /
        (√(2 * π * n) * (n / Real.exp 1) ^ n) := by
        gcongr
    _ = 1 / √(2 * π * n) := by
        rw [div_pow, ← Real.exp_nat_mul]
        have : Real.exp (-r) * Real.exp (r - n) = Real.exp (-n) := by
          rw [← Real.exp_add]; ring_nf
        have h4 : Real.exp (-r) * (Real.exp (r - n) * (n : ℝ) ^ n) =
            Real.exp (-n) * (n : ℝ) ^ n := by rw [← mul_assoc, this]
        rw [h4]
        have hs : (0 : ℝ) < √(2 * π * n) := by positivity
        rw [Real.exp_neg, mul_one]
        field_simp

/-- The bound used for local upper bound without constant: `po_t(m) ≤ (π t)^{-1/2}` for `t ≥ 1`. -/
theorem po_le_inv_sqrt_pi_mul {t : ℝ} (ht : 1 ≤ t) (m : ℕ) : po t m ≤ 1 / √(π * t) := by
  have ht0 : 0 ≤ t := by linarith
  have hn : 1 ≤ ⌊t⌋₊ := by rw [Nat.one_le_floor_iff]; exact ht
  refine (po_le_po_floor ht0 m).trans ((po_le_inv_sqrt ht0 hn).trans ?_)
  have h1 : t ≤ 2 * (⌊t⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one t
    have h2 : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hn
    linarith
  apply one_div_le_one_div_of_le (by positivity)
  apply Real.sqrt_le_sqrt
  nlinarith [Real.pi_pos]

end SRW
end ElboimSly
