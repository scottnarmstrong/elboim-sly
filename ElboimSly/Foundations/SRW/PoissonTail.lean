/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.PoissonPmf
public import ElboimSly.Foundations.StrongApprox.Poisson
public import ElboimSly.Foundations.PPP.PoissonFacts
public import ElboimSly.Foundations.PPP.PoissonMoments
public import Mathlib

/-!
# Poisson facts: lower bound, Chernoff, two points, moments

Poisson facts (c), (d), (e), (f).  Parts (a) and (b) are in `PoissonPmf.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real Nat
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

/-- Factorial bound from the monotone Stirling sequence: `m! ≤ e √m (m/e)^m` for `m ≥ 1`. -/
theorem factorial_le_stirling {m : ℕ} (hm : 1 ≤ m) :
    (m ! : ℝ) ≤ Real.exp 1 * √m * ((m : ℝ) / Real.exp 1) ^ m := by
  have hanti : Stirling.stirlingSeq m ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le k)
    simpa [Function.comp] using this
  rw [Stirling.stirlingSeq_one] at hanti
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold Stirling.stirlingSeq at hanti
  have hpos : 0 < √(2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m := by positivity
  rw [div_le_iff₀ hpos] at hanti
  have h2 : √(2 * (m : ℝ)) = √2 * √m := Real.sqrt_mul (by norm_num) _
  have hs2 : (0 : ℝ) < √2 := by positivity
  calc (m ! : ℝ) ≤ Real.exp 1 / √2 * (√(2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m) := hanti
    _ = Real.exp 1 * √m * ((m : ℝ) / Real.exp 1) ^ m := by
        rw [h2]; field_simp

/-- Poisson facts (c): the lower bound. -/
theorem po_ge {r : ℝ} (hr : 0 < r) (m : ℕ) :
    Real.exp (-((m : ℝ) - r) ^ 2 / r) / (Real.exp 1 * √(max (m : ℝ) 1)) ≤ po r m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [po, Nat.cast_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one,
      max_eq_right zero_le_one, Real.sqrt_one]
    have : -((0 : ℝ) - r) ^ 2 / r = -r := by field_simp; ring
    rw [this, div_le_iff₀ (Real.exp_pos 1)]
    have := Real.exp_pos (-r)
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    nlinarith
  · have hm1 : 1 ≤ m := hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [max_eq_left (by exact_mod_cast hm1)]
    have hf := factorial_le_stirling hm1
    have hs : (0 : ℝ) < √m := by positivity
    have hpow : (0 : ℝ) < ((m : ℝ) / Real.exp 1) ^ m := by positivity
    -- exponent estimate
    have hlog : Real.log (r * Real.exp 1 / m) ≥ 2 - (m : ℝ) / r := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (m : ℝ) / r by positivity)
      rw [Real.log_div hm0.ne' hr.ne'] at h
      rw [Real.log_div (by positivity) hm0.ne', Real.log_mul hr.ne' (Real.exp_pos 1).ne',
        Real.log_exp]
      linarith
    have hA : Real.exp (-((m : ℝ) - r) ^ 2 / r) ≤
        Real.exp (-r) * (r * Real.exp 1 / m) ^ m := by
      rw [← Real.exp_log (show 0 < r * Real.exp 1 / m by positivity), ← Real.exp_nat_mul,
        ← Real.exp_add]
      apply Real.exp_le_exp.2
      have : (m : ℝ) * Real.log (r * Real.exp 1 / m) ≥ m * (2 - m / r) :=
        mul_le_mul_of_nonneg_left hlog hm0.le
      have e2 : -((m : ℝ) - r) ^ 2 / r = -r + m * (2 - m / r) := by field_simp; ring
      linarith
    have hB : (r * Real.exp 1 / m) ^ m = r ^ m / ((m : ℝ) / Real.exp 1) ^ m := by
      rw [← div_pow]; congr 1; field_simp
    rw [hB] at hA
    have hfpos : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    unfold po
    rw [div_le_div_iff₀ (by positivity) hfpos]
    calc Real.exp (-((m : ℝ) - r) ^ 2 / r) * (m ! : ℝ)
        ≤ (Real.exp (-r) * (r ^ m / ((m : ℝ) / Real.exp 1) ^ m)) *
            (Real.exp 1 * √m * ((m : ℝ) / Real.exp 1) ^ m) := by
          exact mul_le_mul hA hf hfpos.le (by positivity)
      _ = Real.exp (-r) * r ^ m * (Real.exp 1 * √m) := by
          field_simp

section Variable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Ω → ℕ} {r : ℝ≥0}

theorem poisson_integrable_exp (hP : HasLaw P (poissonMeasure r) μ) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * (P ω : ℝ))) μ := by
  have h := (StrongApprox.poisson_integrable_mgf hP θ).const_mul (Real.exp (θ * r))
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [← Real.exp_add]; congr 1; ring

/-- Poisson facts (f): the exponential moment of a Poisson variable. -/
theorem poisson_mgf_eq (hP : HasLaw P (poissonMeasure r) μ) (θ : ℝ) :
    ∫ ω, Real.exp (θ * (P ω : ℝ)) ∂μ = Real.exp (r * (Real.exp θ - 1)) := by
  have h : ∀ ω, Real.exp (θ * (P ω : ℝ)) =
      Real.exp (θ * r) * Real.exp (θ * ((P ω : ℝ) - r)) := fun ω => by
    rw [← Real.exp_add]; congr 1; ring
  simp_rw [h]
  rw [integral_const_mul, StrongApprox.poisson_integral_mgf hP, ← Real.exp_add]
  congr 1; ring

/-- Poisson facts (d): Chernoff. -/
theorem poisson_chernoff (hP : HasLaw P (poissonMeasure r) μ) [IsProbabilityMeasure μ] {θ : ℝ}
    (hθ : 0 ≤ θ) (a : ℝ) :
    μ.real {ω | a ≤ (P ω : ℝ)} ≤ Real.exp (r * (Real.exp θ - 1) - θ * a) := by
  have := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => (P ω : ℝ)) a hθ
    (poisson_integrable_exp hP θ)
  rw [mgf, poisson_mgf_eq hP] at this
  refine this.trans (le_of_eq ?_)
  rw [← Real.exp_add]; congr 1; ring

/-- Poisson facts (d), the special case `θ = 1`. -/
theorem poisson_chernoff_one (hP : HasLaw P (poissonMeasure r) μ) [IsProbabilityMeasure μ]
    (a : ℝ) : μ.real {ω | a ≤ (P ω : ℝ)} ≤ Real.exp ((Real.exp 1 - 1) * r - a) := by
  have := poisson_chernoff hP zero_le_one a
  convert this using 2; ring

theorem poisson_mean (hP : HasLaw P (poissonMeasure r) μ) : ∫ ω, (P ω : ℝ) ∂μ = r := by
  have h := hP.integral_comp (f := fun n : ℕ => (n : ℝ)) Measurable.of_discrete.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, integral_poissonMeasure]
  have := hasSum_poisson_descFactorial r 1
  simp only [Nat.descFactorial_one, pow_one] at this
  simp only [smul_eq_mul]
  exact this.tsum_eq

theorem poisson_second (hP : HasLaw P (poissonMeasure r) μ) :
    ∫ ω, (P ω : ℝ) ^ 2 ∂μ = r + (r : ℝ) ^ 2 := by
  have h := hP.integral_comp (f := fun n : ℕ => (n : ℝ) ^ 2)
    Measurable.of_discrete.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, integral_poissonMeasure]
  have h1 := hasSum_poisson_descFactorial r 1
  have h2 := hasSum_poisson_descFactorial r 2
  simp only [Nat.descFactorial_one, pow_one] at h1
  have := h2.add h1
  have e : ∀ n : ℕ, Real.exp (-r) * (r : ℝ) ^ n / n ! * (n.descFactorial 2 : ℝ) +
      Real.exp (-r) * (r : ℝ) ^ n / n ! * (n : ℝ) =
      (Real.exp (-r) * (r : ℝ) ^ n / n !) • ((n : ℝ) ^ 2) := by
    intro n
    rcases n with _ | n
    · simp
    · rw [smul_eq_mul, ← mul_add]
      congr 1
      rw [Nat.descFactorial_succ]
      rcases n with _ | n
      · simp
      · rw [Nat.descFactorial_succ]; simp; ring
  simp_rw [← e]
  rw [this.tsum_eq]; ring

end Variable

end SRW
end ElboimSly
