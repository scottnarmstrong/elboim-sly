/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Data.Nat.Choose.Central

/-!
# Stirling bounds

Stirling bounds (Part I).
-/

@[expose] public section

open Filter Topology Finset
open scoped Real Nat

namespace ElboimSly
namespace StrongApprox

/-- Stirling bounds. The Stirling sequence `n!/(√(2n)(n/e)^n)` (Mathlib's
`Stirling.stirlingSeq`). -/
noncomputable abbrev saSt (n : ℕ) : ℝ := Stirling.stirlingSeq n

theorem saSt_pos {n : ℕ} (hn : 1 ≤ n) : 0 < saSt n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact Stirling.stirlingSeq'_pos k

/-- Stirling bounds, lower bound. -/
theorem sqrt_pi_le_saSt {n : ℕ} (hn : 1 ≤ n) : √π ≤ saSt n :=
  Stirling.sqrt_pi_le_stirlingSeq (by omega)

theorem log_saSt_telescope {n : ℕ} (hn : 1 ≤ n) (d : ℕ) :
    Real.log (saSt n) - Real.log (saSt (n + d)) ≤ 1 / (12 * n) - 1 / (12 * ((n + d : ℕ) : ℝ)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := Stirling.log_stirlingSeq_sdiff_le (n + d)
    have hn' : (0 : ℝ) < ((n + d : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + d)
    have e : 1 / (12 * ((n + d : ℕ) : ℝ) * (((n + d : ℕ) : ℝ) + 1)) =
        1 / (12 * ((n + d : ℕ) : ℝ)) - 1 / (12 * ((n + (d + 1) : ℕ) : ℝ)) := by
      push_cast; field_simp; ring
    show Real.log (saSt n) - Real.log (saSt (n + (d + 1))) ≤ _
    have : saSt (n + (d + 1)) = saSt (n + d + 1) := rfl
    rw [this]
    simp only [saSt] at *
    rw [e] at h
    linarith

/-- Stirling bounds, upper bound. -/
theorem saSt_le {n : ℕ} (hn : 1 ≤ n) : saSt n ≤ √π * Real.exp (1 / (12 * n)) := by
  have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hlim : Tendsto (fun N => Real.log (saSt N)) atTop (𝓝 (Real.log (√π))) :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi).log hpi.ne'
  have h : Real.log (saSt n) - 1 / (12 * n) ≤ Real.log (√π) := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
    have := log_saSt_telescope hn d
    have h2 : (0 : ℝ) ≤ 1 / (12 * ((n + d : ℕ) : ℝ)) := by positivity
    linarith
  have hs := saSt_pos hn
  calc saSt n = Real.exp (Real.log (saSt n)) := (Real.exp_log hs).symm
    _ ≤ Real.exp (Real.log (√π) + 1 / (12 * n)) := Real.exp_le_exp.2 (by linarith)
    _ = √π * Real.exp (1 / (12 * n)) := by rw [Real.exp_add, Real.exp_log hpi]

theorem central_binom_eq {k : ℕ} (hk : 1 ≤ k) :
    √(π * k) * ((2 * k).choose k : ℝ) / 4 ^ k = √π * saSt (2 * k) / saSt k ^ 2 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs2 := saSt_pos (n := 2 * k) (by omega)
  have hs1 := saSt_pos hk
  have hch : ((2 * k).choose k : ℝ) * (k ! : ℝ) * (k ! : ℝ) = ((2 * k)! : ℝ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial k k
    rw [← two_mul] at this
    exact_mod_cast this
  have e1 : ((2 * k)! : ℝ) = saSt (2 * k) * (√(2 * ((2 * k : ℕ) : ℝ)) * (((2 * k : ℕ) : ℝ) / Real.exp 1) ^ (2 * k)) := by
    simp only [saSt, Stirling.stirlingSeq]
    have : √(2 * ((2 * k : ℕ) : ℝ)) * (((2 * k : ℕ) : ℝ) / Real.exp 1) ^ (2 * k) ≠ 0 := by
      have : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
      positivity
    field_simp
  have e2 : (k ! : ℝ) = saSt k * (√(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) := by
    simp only [saSt, Stirling.stirlingSeq]
    have : √(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k ≠ 0 := by positivity
    field_simp
  have e3 : √(2 * ((2 * k : ℕ) : ℝ)) = 2 * √(k : ℝ) := by
    rw [show 2 * ((2 * k : ℕ) : ℝ) = 2 ^ 2 * k by push_cast; ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have e4 : (((2 * k : ℕ) : ℝ) / Real.exp 1) ^ (2 * k) = 4 ^ k * ((k : ℝ) / Real.exp 1) ^ (2 * k) := by
    rw [show (((2 * k : ℕ) : ℝ) / Real.exp 1) = 2 * ((k : ℝ) / Real.exp 1) by push_cast; ring,
      mul_pow, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
  have e5 : √(2 * (k : ℝ)) ^ 2 = 2 * k := Real.sq_sqrt (by positivity)
  have e6 : √(k : ℝ) ^ 2 = k := Real.sq_sqrt hk'.le
  have e7 : √(π * k) = √π * √(k : ℝ) := Real.sqrt_mul Real.pi_pos.le _
  rw [e3, e4] at e1
  have hpos : (0 : ℝ) < ((k : ℝ) / Real.exp 1) ^ k := by positivity
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk'
  have hs2k : 0 < √(2 * (k : ℝ)) := Real.sqrt_pos.2 (by positivity)
  rw [e7]
  have hfac : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have : ((2 * k).choose k : ℝ) = ((2 * k)! : ℝ) / ((k ! : ℝ) * (k ! : ℝ)) := by
    rw [eq_div_iff (by positivity)]; rw [← hch]; ring
  rw [this, e1, e2]
  rw [pow_mul] at *
  field_simp
  rw [e5, e6]
  have h8 : ((k : ℝ) ^ 2 / Real.exp 1 ^ 2) ^ k = (((k : ℝ) / Real.exp 1) ^ k) ^ 2 := by
    rw [← div_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [h8]; ring

/-- Stirling bounds, the central binomial coefficient, lower bound. -/
theorem exp_neg_le_central_binom {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (-(1 / (6 * k))) ≤ √(π * k) * ((2 * k).choose k : ℝ) / 4 ^ k := by
  rw [central_binom_eq hk]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := sqrt_pi_le_saSt (n := 2 * k) (by omega)
  have h2 := saSt_le hk
  have h3 := sqrt_pi_le_saSt hk
  have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hs1 := saSt_pos hk
  have hsq : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have h4 : saSt k ^ 2 ≤ π * Real.exp (1 / (6 * k)) := by
    calc saSt k ^ 2 ≤ (√π * Real.exp (1 / (12 * k))) ^ 2 := by gcongr
      _ = π * Real.exp (1 / (6 * k)) := by
        rw [mul_pow, hsq, ← Real.exp_nat_mul]; congr 2; push_cast; field_simp; ring
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * saSt k ^ 2 ≤ π * Real.exp (1 / (6 * k)) := by linarith
    _ = √π * √π * Real.exp (1 / (6 * k)) := by rw [← sq, hsq]
    _ ≤ _ := by gcongr

/-- Stirling bounds, the central binomial coefficient, upper bound. -/
theorem central_binom_le_exp {k : ℕ} (hk : 1 ≤ k) :
    √(π * k) * ((2 * k).choose k : ℝ) / 4 ^ k ≤ Real.exp (1 / (24 * k)) := by
  rw [central_binom_eq hk]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := saSt_le (n := 2 * k) (by omega)
  have h3 := sqrt_pi_le_saSt hk
  have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hs1 := saSt_pos hk
  have hsq : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have e : Real.exp (1 / (12 * ((2 * k : ℕ) : ℝ))) = Real.exp (1 / (24 * k)) := by
    congr 1; push_cast; field_simp; ring
  rw [e] at h1
  rw [div_le_iff₀ (by positivity)]
  have h5 : π ≤ saSt k ^ 2 := by rw [← hsq]; gcongr
  calc √π * saSt (2 * k) ≤ √π * (√π * Real.exp (1 / (24 * k))) := by gcongr
    _ = π * Real.exp (1 / (24 * k)) := by rw [← mul_assoc, ← sq, hsq]
    _ ≤ _ := by nlinarith [Real.exp_pos (1 / (24 * (k : ℝ)))]

end StrongApprox
end ElboimSly
