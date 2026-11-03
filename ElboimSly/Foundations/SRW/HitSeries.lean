/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# A tail estimate for `∑ k^{-p}` and a lattice point count

Used in hitting a box after a given time.
-/

@[expose] public section

open Set Filter Finset
open scoped Real

namespace ElboimSly
namespace SRW

/-- `q k^{-(q+1)} ≤ (k-1)^{-q} - k^{-q}` for `k ≥ 2` and `q > 0`. -/
theorem telescoping_step {q : ℝ} (hq : 0 < q) {k : ℕ} (hk : 2 ≤ k) :
    q * (k : ℝ) ^ (-(q + 1)) ≤ ((k : ℝ) - 1) ^ (-q) - (k : ℝ) ^ (-q) := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have h1 : (1 - 1 / (k : ℝ)) ≤ Real.exp (-(1 / (k : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (k : ℝ)))
    linarith
  have h2 : (1 - 1 / (k : ℝ)) ^ q ≤ Real.exp (-q / k) := by
    calc (1 - 1 / (k : ℝ)) ^ q ≤ (Real.exp (-(1 / (k : ℝ)))) ^ q :=
          Real.rpow_le_rpow (by
            have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hk0]; exact hk1.le
            linarith) h1 hq.le
      _ = Real.exp (-q / k) := by
          rw [← Real.exp_mul]; congr 1; ring
  have h3 : 1 + q / k ≤ Real.exp (q / k) := by
    have := Real.add_one_le_exp (q / k); linarith
  have h4 : (1 - 1 / (k : ℝ)) ^ q * (1 + q / k) ≤ 1 := by
    calc (1 - 1 / (k : ℝ)) ^ q * (1 + q / k) ≤ Real.exp (-q / k) * Real.exp (q / k) := by
          gcongr
      _ = 1 := by
          rw [← Real.exp_add]
          have : -q / (k : ℝ) + q / k = 0 := by ring
          rw [this, Real.exp_zero]
  have e1 : (1 - 1 / (k : ℝ)) = ((k : ℝ) - 1) / k := by field_simp
  rw [e1, Real.div_rpow hk2.le hk0.le] at h4
  have hkq : (0 : ℝ) < (k : ℝ) ^ q := Real.rpow_pos_of_pos hk0 q
  have h5 : ((k : ℝ) - 1) ^ q * (1 + q / k) ≤ (k : ℝ) ^ q := by
    have := mul_le_mul_of_nonneg_right h4 hkq.le
    rwa [div_mul_eq_mul_div, div_mul_cancel₀ _ hkq.ne', one_mul] at this
  -- divide by (k-1)^q k^q
  have hk1q : (0 : ℝ) < ((k : ℝ) - 1) ^ q := Real.rpow_pos_of_pos hk2 q
  have e2 : ((k : ℝ) - 1) ^ (-q) = (((k : ℝ) - 1) ^ q)⁻¹ := Real.rpow_neg hk2.le q
  have e3 : (k : ℝ) ^ (-q) = ((k : ℝ) ^ q)⁻¹ := Real.rpow_neg hk0.le q
  have e4 : (k : ℝ) ^ (-(q + 1)) = ((k : ℝ) ^ q)⁻¹ * (k : ℝ)⁻¹ := by
    rw [Real.rpow_neg hk0.le, Real.rpow_add hk0, Real.rpow_one, mul_inv]
  rw [e2, e3, e4]
  rw [← sub_nonneg]
  have : (((k : ℝ) - 1) ^ q)⁻¹ - ((k : ℝ) ^ q)⁻¹ - q * (((k : ℝ) ^ q)⁻¹ * (k : ℝ)⁻¹) =
      ((k : ℝ) ^ q - ((k : ℝ) - 1) ^ q * (1 + q / k)) / (((k : ℝ) - 1) ^ q * (k : ℝ) ^ q) := by
    field_simp
    ring
  rw [this]
  apply div_nonneg (by linarith) (by positivity)

theorem tail_Ioc {q : ℝ} (hq : 0 < q) {K : ℕ} (hK : 1 ≤ K) :
    ∀ n : ℕ, K ≤ n → ∑ k ∈ Finset.Ioc K n, (k : ℝ) ^ (-(q + 1)) ≤
      ((K : ℝ) ^ (-q) - (n : ℝ) ^ (-q)) / q := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn]
    have := telescoping_step hq (show 2 ≤ n + 1 by omega)
    push_cast at this ⊢
    rw [add_sub_cancel_right] at this
    have h2 : (n + 1 : ℝ) ^ (-(q + 1)) ≤ ((n : ℝ) ^ (-q) - (n + 1 : ℝ) ^ (-q)) / q := by
      rw [le_div_iff₀ hq]; linarith
    calc _ ≤ ((K : ℝ) ^ (-q) - (n : ℝ) ^ (-q)) / q +
          ((n : ℝ) ^ (-q) - (n + 1 : ℝ) ^ (-q)) / q := by gcongr
      _ = _ := by ring

/-- Partial sums of the tail of `∑ k^{-p}`: for `p ≥ 3/2` and `K ≥ 1`,
`∑_{K ≤ k < N} k^{-p} ≤ 3 K^{1-p}`. -/
theorem sum_rpow_tail_le {p : ℝ} (hp : 3 / 2 ≤ p) {K : ℕ} (hK : 1 ≤ K) (N : ℕ) :
    ∑ k ∈ (range N).filter (K ≤ ·), (k : ℝ) ^ (-p) ≤ 3 * (K : ℝ) ^ (1 - p) := by
  set q : ℝ := p - 1 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set n := max K N with hn
  have hKn : K ≤ n := le_max_left _ _
  have hsub : (range N).filter (K ≤ ·) ⊆ Finset.Icc K n := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    exact ⟨hk.2, by have := le_max_right K N; omega⟩
  have hIcc : Finset.Icc K n = insert K (Finset.Ioc K n) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  have hnn : ∀ k ∈ Finset.Icc K n, 0 ≤ (k : ℝ) ^ (-p) := fun k _ => by positivity
  calc ∑ k ∈ (range N).filter (K ≤ ·), (k : ℝ) ^ (-p)
      ≤ ∑ k ∈ Finset.Icc K n, (k : ℝ) ^ (-p) := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => by positivity)
    _ = (K : ℝ) ^ (-p) + ∑ k ∈ Finset.Ioc K n, (k : ℝ) ^ (-p) := by
        rw [hIcc, Finset.sum_insert (by simp)]
    _ ≤ (K : ℝ) ^ (-p) + ((K : ℝ) ^ (-q) - (n : ℝ) ^ (-q)) / q := by
        have e : -p = -(q + 1) := by rw [hq]; ring
        rw [e]
        gcongr
        exact tail_Ioc hq0 hK n hKn
    _ ≤ 3 * (K : ℝ) ^ (1 - p) := by
        have hA : (0 : ℝ) < (K : ℝ) ^ (1 - p) := Real.rpow_pos_of_pos hK0 _
        have e1 : (K : ℝ) ^ (-p) = (K : ℝ) ^ (1 - p) / K := by
          rw [Real.rpow_sub hK0, Real.rpow_one, Real.rpow_neg hK0.le]
          field_simp
        have e2 : (K : ℝ) ^ (-q) = (K : ℝ) ^ (1 - p) := by
          congr 1; rw [hq]; ring
        have hKge : (1 : ℝ) ≤ K := by exact_mod_cast hK
        have h1 : (K : ℝ) ^ (-p) ≤ (K : ℝ) ^ (1 - p) := by
          rw [e1]; exact div_le_self hA.le hKge
        have h2 : ((K : ℝ) ^ (-q) - (n : ℝ) ^ (-q)) / q ≤ 2 * (K : ℝ) ^ (1 - p) := by
          have hn0 : 0 ≤ (n : ℝ) ^ (-q) := by positivity
          rw [div_le_iff₀ hq0, e2]
          have hq5 : (1 / 2 : ℝ) ≤ q := by rw [hq]; linarith
          nlinarith
        linarith

/-- The box of integer points within sup-distance `< R` of `c`. -/
noncomputable def ballBox {d : ℕ} (c : Fin d → ℤ) (R : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (c i - (⌈R⌉₊ - 1 : ℕ)) (c i + (⌈R⌉₊ - 1 : ℕ))

theorem mem_ballBox {d : ℕ} {c z : Fin d → ℤ} {R : ℝ} (h : ‖fun i => ((z i - c i : ℤ) : ℝ)‖ < R) :
    z ∈ ballBox c R := by
  rw [ballBox, Fintype.mem_piFinset]
  intro i
  have h1 : |((z i - c i : ℤ) : ℝ)| < R := by
    have := norm_le_pi_norm (fun i => ((z i - c i : ℤ) : ℝ)) i
    rw [Real.norm_eq_abs] at this
    exact lt_of_le_of_lt this h
  have hR : 0 < R := lt_of_le_of_lt (abs_nonneg _) h1
  have h2 : (|z i - c i| : ℤ) < ⌈R⌉₊ := by
    have : ((|z i - c i| : ℤ) : ℝ) < ⌈R⌉₊ := by
      rw [Int.cast_abs]; exact lt_of_lt_of_le h1 (Nat.le_ceil R)
    exact_mod_cast this
  rw [Finset.mem_Icc]
  have hc : 1 ≤ ⌈R⌉₊ := Nat.one_le_iff_ne_zero.2 (by simpa using hR)
  have := abs_lt.1 (show |z i - c i| < ((⌈R⌉₊ : ℤ)) from h2) |> fun _ => h2
  rcases abs_cases (z i - c i) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega

theorem card_ballBox_le {d : ℕ} (c : Fin d → ℤ) {R : ℝ} (hR : 0 < R) :
    ((ballBox c R).card : ℝ) ≤ (2 * R + 1) ^ d := by
  rw [ballBox, Fintype.card_piFinset]
  simp only [Int.card_Icc]
  have hc : 1 ≤ ⌈R⌉₊ := Nat.one_le_iff_ne_zero.2 (by simpa using hR)
  have hlt : (⌈R⌉₊ : ℝ) < R + 1 := Nat.ceil_lt_add_one hR.le
  have e : ∀ i : Fin d, ((c i + (⌈R⌉₊ - 1 : ℕ) + 1 - (c i - (⌈R⌉₊ - 1 : ℕ))).toNat : ℝ) ≤ 2 * R + 1 := by
    intro i
    have : (c i + (⌈R⌉₊ - 1 : ℕ) + 1 - (c i - (⌈R⌉₊ - 1 : ℕ))) = ((2 * (⌈R⌉₊ - 1) + 1 : ℕ) : ℤ) := by
      push_cast; omega
    rw [this, Int.toNat_natCast]
    push_cast [Nat.cast_sub hc]
    linarith
  rw [Nat.cast_prod]
  calc ∏ i : Fin d, ((c i + (⌈R⌉₊ - 1 : ℕ) + 1 - (c i - (⌈R⌉₊ - 1 : ℕ))).toNat : ℝ)
      ≤ ∏ _i : Fin d, (2 * R + 1) := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => e i)
    _ = _ := by simp

end SRW
end ElboimSly
