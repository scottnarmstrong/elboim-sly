/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56Small
public import Mathlib

/-!
# Geometry of Claim 5.6

Geometry of Claim 5.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- The parameter `τ = 4^{-m} t`. -/
noncomputable def claimTau (m : ℕ) (t : ℝ) : ℝ := t / 4 ^ m

/-- The radius `r₀ = √τ / 32`. -/
noncomputable def claimR0 (m : ℕ) (t : ℝ) : ℝ := √(claimTau m t) / 32

/-- The centre `q = u + (N_j/4)(1, 2,..., 2)` of `B^-`. -/
noncomputable def claimQ (j : ℕ) (u : Fin d → ℤ) : Fin d → ℝ := fun i =>
  (u i : ℝ) + (2 : ℝ) ^ j / 4 * (if i.val = 0 then 1 else 2)

/-- `f_v(s) = √(2s/t) q + (1 - √(2s/t)) v`, for `s ∈ [0, t/2]`. -/
noncomputable def claimFv (j : ℕ) (u : Fin d → ℤ) (t : ℝ) (v : Fin d → ℤ) (s : ℝ) : Fin d → ℝ :=
  fun i => √(2 * s / t) * claimQ j u i + (1 - √(2 * s / t)) * (v i : ℝ)

/-- `f^w(s) = √(2(t-s)/t) q + (1 - √(2(t-s)/t)) w`, for `s ∈ [t/2, t]`. -/
noncomputable def claimFw (j : ℕ) (u : Fin d → ℤ) (t : ℝ) (w : Fin d → ℤ) (s : ℝ) : Fin d → ℝ :=
  fun i => √(2 * (t - s) / t) * claimQ j u i + (1 - √(2 * (t - s) / t)) * (w i : ℝ)

/-- The standing hypotheses of geometry of Claim 5.6. -/
structure Claim56Geom (d j : ℕ) (t : ℝ) (m : ℕ) : Prop where
  d_pos : 1 ≤ d
  j_pos : 1 ≤ j
  t_lo : ((2 : ℝ) ^ j) ^ 2 / 4 ≤ t
  t_hi : t ≤ ((2 : ℝ) ^ j) ^ 2
  m_ge : 3 ≤ m
  four_m : (4 : ℝ) ^ m ≤ t
  tau_ge : 288 ≤ √(claimTau m t)

/-- Basic consequences of the geometry hypotheses. -/
theorem Claim56Geom.facts {j : ℕ} {t : ℝ} {m : ℕ} (G : Claim56Geom d j t m) :
    ∃ s P N : ℝ, s = √(claimTau m t) ∧ P = 2 ^ m ∧ N = 2 ^ j ∧ 288 ≤ s ∧ 8 ≤ P ∧
      t = P ^ 2 * s ^ 2 ∧ P * s ≤ N ∧ N ≤ 2 * P * s ∧ claimTau m t = s ^ 2 := by
  have hτ0 : 0 ≤ claimTau m t := by
    unfold claimTau
    have : (0 : ℝ) < 4 ^ m := by positivity
    have h4 : (4 : ℝ) ^ m ≤ t := G.four_m
    exact div_nonneg (by linarith) this.le
  refine ⟨√(claimTau m t), 2 ^ m, 2 ^ j, rfl, rfl, rfl, G.tau_ge, ?_, ?_, ?_, ?_, ?_⟩
  · calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) G.m_ge
  · rw [Real.sq_sqrt hτ0]
    unfold claimTau
    have : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    field_simp
  · have hN : 0 < (2 : ℝ) ^ j := by positivity
    have h1 : t = ((2 : ℝ) ^ m) ^ 2 * (√(claimTau m t)) ^ 2 := by
      rw [Real.sq_sqrt hτ0]
      unfold claimTau
      have : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this]; field_simp
    have h2 := G.t_hi
    rw [h1, ← mul_pow] at h2
    exact le_of_sq_le_sq (by linarith) (by positivity)
  · have h1 : t = ((2 : ℝ) ^ m) ^ 2 * (√(claimTau m t)) ^ 2 := by
      rw [Real.sq_sqrt hτ0]
      unfold claimTau
      have : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this]; field_simp
    have h2 := G.t_lo
    rw [h1] at h2
    have : (2 ^ j : ℝ) ^ 2 ≤ (2 * 2 ^ m * √(claimTau m t)) ^ 2 := by nlinarith
    exact le_of_sq_le_sq this (by positivity)
  · exact Real.sq_sqrt hτ0 |>.symm

end SRW
end ElboimSly
