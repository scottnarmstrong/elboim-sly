/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Chernoff
public import ElboimSly.Foundations.SRW.Moments
public import ElboimSly.Foundations.SRW.Law1d
public import Mathlib

/-!
# Moments of a simple random walk coordinate (the σ-estimate, Case 2)

Moments and exponential moments; The σ-estimate, Case 2. For a coordinate `Z = X_i(T)` of an SRW
with `T ≥ 1`: `E Z² = 2T` and `E Z⁴ ≤ 355 T²` (via `y⁴ ≤ 24 (e^y + e^{-y})` and
`E e^{±λ Z} = e^{2T(cosh λ - 1)}`, `λ = T^{-1/2}`; the written proof's `150` becomes `355` because
we use `cosh λ - 1 ≤ λ²` from the library instead of `0.55 λ²`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}

theorem pow_four_le_exp (y : ℝ) : y ^ 4 ≤ 24 * (Real.exp y + Real.exp (-y)) := by
  have h := Real.pow_div_factorial_le_exp |y| (abs_nonneg y) 4
  have h4 : |y| ^ 4 = y ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h4, hf] at h
  have h24 : y ^ 4 ≤ 24 * Real.exp |y| := by linarith
  have hexp : Real.exp |y| ≤ Real.exp y + Real.exp (-y) := by
    rcases abs_cases y with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; linarith [Real.exp_pos (-y)]
    · rw [h1]; linarith [Real.exp_pos y]
  linarith

/-- `E Z⁴ ≤ 355 T²` for a coordinate of an SRW at time `T ≥ 1`. -/
theorem srw_coord_fourth (hY : IsSRW P Y) (i : Fin d) {T : ℝ≥0} (hT : 1 ≤ (T : ℝ)) :
    Integrable (fun ω => (Y ω T i : ℝ) ^ 4) P ∧ ∫ ω, (Y ω T i : ℝ) ^ 4 ∂P ≤ 355 * (T : ℝ) ^ 2 := by
  have hc := hY.coord i
  set lam : ℝ := (Real.sqrt T)⁻¹ with hlam
  have hT0 : (0 : ℝ) < T := by linarith
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hT0
  have hs1 : 1 ≤ Real.sqrt (T : ℝ) := by
    rw [Real.one_le_sqrt]; exact hT
  have hlam0 : 0 < lam := inv_pos.2 hs
  have hlam1 : lam ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hlam2 : lam ^ 2 = (T : ℝ)⁻¹ := by
    rw [hlam, inv_pow, Real.sq_sqrt hT0.le]
  have hZm : Measurable fun ω => (Y ω T i : ℝ) := (measurable_eval_real T i).comp hY.1
  have hI1 := hc.integrable_exp_eval1 T lam
  have hI2 := hc.integrable_exp_eval1 T (-lam)
  have hdom : ∀ ω, (Y ω T i : ℝ) ^ 4 ≤ 24 / lam ^ 4 *
      (Real.exp (lam * (Y ω T i : ℝ)) + Real.exp (-lam * (Y ω T i : ℝ))) := by
    intro ω
    have h := pow_four_le_exp (lam * (Y ω T i : ℝ))
    have e : (-(lam * (Y ω T i : ℝ))) = -lam * (Y ω T i : ℝ) := by ring
    rw [e, mul_pow] at h
    have hl4 : 0 < lam ^ 4 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hl4]
    linarith
  have hint : Integrable (fun ω => (Y ω T i : ℝ) ^ 4) P := by
    refine Integrable.mono' ((hI1.add hI2).const_mul (24 / lam ^ 4))
      (hZm.pow_const 4).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hdom ω
  refine ⟨hint, ?_⟩
  have hm1 : ∫ ω, Real.exp (lam * (Y ω T i : ℝ)) ∂P = Real.exp (2 * T * (Real.cosh lam - 1)) :=
    hc.mgf_eval1 T lam
  have hm2 : ∫ ω, Real.exp (-lam * (Y ω T i : ℝ)) ∂P =
      Real.exp (2 * T * (Real.cosh (-lam) - 1)) := hc.mgf_eval1 T (-lam)
  have hcosh : Real.cosh lam - 1 ≤ lam ^ 2 := by
    have := cosh_sub_one_le hlam0.le hlam1
    exact this
  have hexp : Real.exp (2 * T * (Real.cosh lam - 1)) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.2
    have : 2 * (T : ℝ) * (Real.cosh lam - 1) ≤ 2 * T * lam ^ 2 :=
      mul_le_mul_of_nonneg_left hcosh (by positivity)
    rw [hlam2] at this
    have e : 2 * (T : ℝ) * (T : ℝ)⁻¹ = 2 := by field_simp
    linarith
  have hcosh' : Real.cosh (-lam) = Real.cosh lam := Real.cosh_neg lam
  calc ∫ ω, (Y ω T i : ℝ) ^ 4 ∂P ≤ ∫ ω, 24 / lam ^ 4 *
        (Real.exp (lam * (Y ω T i : ℝ)) + Real.exp (-lam * (Y ω T i : ℝ))) ∂P :=
        integral_mono hint ((hI1.add hI2).const_mul _) hdom
    _ = 24 / lam ^ 4 * (Real.exp (2 * T * (Real.cosh lam - 1)) +
          Real.exp (2 * T * (Real.cosh lam - 1))) := by
        rw [integral_const_mul, integral_add hI1 hI2, hm1, hm2, hcosh']
    _ ≤ 24 / lam ^ 4 * (Real.exp 2 + Real.exp 2) := by gcongr
    _ = 48 * Real.exp 2 * (T : ℝ) ^ 2 := by
        have : lam ^ 4 = ((T : ℝ)⁻¹) ^ 2 := by rw [← hlam2]; ring
        rw [this]; field_simp; ring
    _ ≤ 355 * (T : ℝ) ^ 2 := by
        have h1 : Real.exp 2 ≤ 7.39 := by
          have := Real.exp_one_lt_d9
          have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
          rw [h2]
          nlinarith [Real.exp_pos 1]
        have : (0 : ℝ) ≤ (T : ℝ) ^ 2 := by positivity
        nlinarith

end ElboimSly.Paper.Step
