/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.EscapeParams
public import Mathlib

/-!
# Numerical parameters of escape from the boundary
-/

@[expose] public section

open Set Filter
open scoped NNReal

namespace ElboimSly
namespace SRW

theorem exists_ell_ge (L : ℝ) : ∃ i, L ≤ ell i := by
  have h := tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 37 / 36 by norm_num)
  obtain ⟨i, hi⟩ := (h.eventually_ge_atTop (L / 72)).exists
  exact ⟨i, by unfold ell; linarith⟩

theorem q_pow_256 : (1100 : ℝ) ≤ (37 / 36 : ℝ) ^ 256 := by norm_num

theorem escape_params {L : ℤ} (hL : 6000 ≤ L) :
    ∃ I : ℕ, 1 ≤ I ∧ ell (I - 1) < (L : ℝ) / 40 ∧ (L : ℝ) / 40 ≤ ell I ∧
      (tau (I + 1) : ℝ) ≤ (L : ℝ) ^ 2 / 20000 ∧ 1 ≤ (tau (I + 1) : ℝ) ∧
      (1100 : ℝ) ^ (I - 1) ≤ (L : ℝ) ^ 256 := by
  have hLr : (6000 : ℝ) ≤ L := by exact_mod_cast hL
  have hex := exists_ell_ge ((L : ℝ) / 40)
  classical
  set I := Nat.find hex with hI
  have hIspec : (L : ℝ) / 40 ≤ ell I := Nat.find_spec hex
  have hI1 : 1 ≤ I := by
    by_contra h
    have : I = 0 := by omega
    rw [this, ell_zero] at hIspec
    linarith
  have hlt : ell (I - 1) < (L : ℝ) / 40 := by
    have := Nat.find_min hex (show I - 1 < I by omega)
    exact not_le.1 this
  refine ⟨I, hI1, hlt, hIspec, ?_, ?_, ?_⟩
  · -- upper bound on tau
    rw [coe_tau_succ]
    set q : ℝ := 37 / 36 with hq
    have hell : ∀ i, (ell i / 18) ^ 2 = 16 * (q ^ 2) ^ i := by
      intro i; rw [hq]; unfold ell; rw [← pow_mul, mul_comm 2 i, pow_mul]; ring_nf
    simp_rw [hell]
    rw [← Finset.mul_sum, geom_sum_eq (by norm_num [hq])]
    have hqI : q ^ I = ell I / 72 := by rw [hq]; unfold ell; field_simp
    have hell1 : ell I = q * ell (I - 1) := by
      have := ell_succ (I - 1)
      rw [show I - 1 + 1 = I by omega] at this
      rw [this]
    have hqI' : q ^ I < q * (L / 40) / 72 := by
      rw [hqI, hell1]
      have : q * ell (I - 1) < q * (L / 40) := by gcongr
      linarith
    have hx : (q ^ 2) ^ I = (q ^ I) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    have hqpos : 0 < q ^ I := by positivity
    have hsum : (q ^ 2) ^ I - 1 ≥ -1 := by
      have : 0 < (q ^ 2) ^ I := by positivity
      linarith
    have hq2 : q ^ 2 - 1 = 73 / 1296 := by norm_num [hq]
    rw [hq2, hx]
    have hb : (q ^ I) ^ 2 ≤ (q * (L / 40) / 72) ^ 2 := by gcongr
    have : 16 * (((q ^ I) ^ 2 - 1) / (73 / 1296)) ≤ 16 * ((q ^ I) ^ 2 / (73 / 1296)) := by
      gcongr; linarith
    have hq' : q = 37 / 36 := rfl
    have h5 : (q * (L / 40) / 72) ^ 2 = (37 / 36) ^ 2 * (L : ℝ) ^ 2 / 2880 ^ 2 := by
      rw [hq']; ring
    have h6 : 16 * ((q ^ I) ^ 2 / (73 / 1296)) ≤
        16 * ((37 / 36) ^ 2 * (L : ℝ) ^ 2 / 2880 ^ 2 / (73 / 1296)) := by
      gcongr
      rw [← h5]; exact hb
    have h7 : (1 : ℝ) + 16 * ((37 / 36) ^ 2 * (L : ℝ) ^ 2 / 2880 ^ 2 / (73 / 1296)) ≤
        (L : ℝ) ^ 2 / 20000 := by
      have : (36000000 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
      norm_num
      nlinarith
    linarith
  · rw [coe_tau_succ]
    have : 0 ≤ ∑ i ∈ Finset.range I, (ell i / 18) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  · have hq1 : (37 / 36 : ℝ) ^ (I - 1) < L / 2880 := by
      have : ell (I - 1) = 72 * (37 / 36 : ℝ) ^ (I - 1) := rfl
      linarith
    have hL1 : (37 / 36 : ℝ) ^ (I - 1) ≤ L := by linarith
    calc (1100 : ℝ) ^ (I - 1) ≤ ((37 / 36 : ℝ) ^ 256) ^ (I - 1) := by gcongr; exact q_pow_256
      _ = ((37 / 36 : ℝ) ^ (I - 1)) ^ 256 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (L : ℝ) ^ 256 := by gcongr

end SRW
end ElboimSly
