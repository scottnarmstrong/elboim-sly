/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.TreeError
public import ElboimSly.Foundations.StrongApprox.TreeSplit
public import ElboimSly.Foundations.StrongApprox.BinomialFacts
public import ElboimSly.Foundations.StrongApprox.Poisson

/-!
# Exponential moments along a path

Exponential moments along a path. The one-level estimate (Step 2, with Young's inequality in place
of Cauchy--Schwarz, constant `κ = 5`) and the successive integration (Step 3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly
namespace StrongApprox

/-- The exponent `θ_* = 1/(8 c_T)`. -/
noncomputable def theta0 : ℝ := 1 / (8 * cT)

theorem cT_pos : 0 < cT := by unfold cT; norm_num

theorem theta0_pos : 0 < theta0 := by unfold theta0; have := cT_pos; positivity

theorem six_theta0_le : 6 * theta0 ≤ 1 / 2 := by
  unfold theta0 cT
  rw [show 6 * (1 / (8 * (2000000000 + 1 / 4 : ℝ))) = 6 / (8 * (2000000000 + 1 / 4)) from by ring]
  rw [div_le_iff₀ (by norm_num)]; norm_num

theorem theta0_cT : theta0 * cT = 1 / 8 := by
  unfold theta0; have := cT_pos; field_simp

theorem theta0_le : theta0 ≤ 1 / 12 := by
  have := six_theta0_le; linarith

theorem integrable_exp_quarter_sq :
    Integrable (fun y : ℝ => Real.exp (1 / 4 * y ^ 2)) saN ∧
      ∫ y, Real.exp (1 / 4 * y ^ 2) ∂saN ≤ 2 := by
  have h := integral_exp_sq_saN (c := 1 / 4) (by norm_num) (by norm_num)
  have hv : (√(1 - 2 * (1 / 4 : ℝ)))⁻¹ ≤ 2 := by
    have : (1 / 2 : ℝ) ≤ √(1 - 2 * (1 / 4)) := Real.le_sqrt_of_sq_le (by norm_num)
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hpos : 0 < (√(1 - 2 * (1 / 4 : ℝ)))⁻¹ := by
    apply inv_pos.2; apply Real.sqrt_pos.2; norm_num
  refine ⟨?_, h ▸ hv⟩
  by_contra hn
  rw [integral_undef hn] at h
  linarith

/-- Exponential moments along a path, Step 2 (one level). -/
theorem one_level {m : ℕ} {χ : ℝ → ℕ} (hχ : HasLaw χ (binomial m sahalf) saN)
    (hm : Measurable χ) :
    ∫⁻ y, ENNReal.ofReal
      (Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 + cT * y ^ 2))) ∂saN ≤ 5 := by
  obtain ⟨hi1, hv1⟩ := binomial_exp_sqrt_sq_le hχ hm (c := 6 * theta0)
    (by have := theta0_pos; positivity) six_theta0_le
  obtain ⟨hi2, hv2⟩ := integrable_exp_quarter_sq
  have hpt : ∀ y, Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 + cT * y ^ 2)) ≤
      (Real.exp (6 * theta0 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2) +
        Real.exp (1 / 4 * y ^ 2)) / 2 := by
    intro y
    have e1 : Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 + cT * y ^ 2)) =
        Real.exp (3 * theta0 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2) * Real.exp (1 / 8 * y ^ 2) := by
      rw [← Real.exp_add]; congr 1
      have := theta0_cT
      nlinarith
    have e2 : Real.exp (6 * theta0 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2) =
        Real.exp (3 * theta0 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e3 : Real.exp (1 / 4 * y ^ 2) = Real.exp (1 / 8 * y ^ 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e1, e2, e3]
    nlinarith [sq_nonneg (Real.exp (3 * theta0 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2) -
      Real.exp (1 / 8 * y ^ 2))]
  have hint : Integrable (fun y => (Real.exp (6 * theta0 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2) +
        Real.exp (1 / 4 * y ^ 2)) / 2) saN := (hi1.add hi2).div_const 2
  calc _ ≤ ∫⁻ y, ENNReal.ofReal ((Real.exp (6 * theta0 *
          (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2) + Real.exp (1 / 4 * y ^ 2)) / 2) ∂saN :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpt y)
    _ = ENNReal.ofReal (∫ y, (Real.exp (6 * theta0 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2) +
          Real.exp (1 / 4 * y ^ 2)) / 2 ∂saN) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun y => by positivity)).symm
    _ ≤ ENNReal.ofReal 5 := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_div, integral_add hi1 hi2]
        linarith
    _ = 5 := by simp

/-- Generic successive-integration step. -/
theorem level_gen (n : ℕ) (m : ℕ) {χ : ℝ → ℕ} (hχ : HasLaw χ (binomial m sahalf) saN)
    (hm : Measurable χ) (H : ℕ → DT n → ℝ)
    (hH : ∀ m', ∫⁻ e, ENNReal.ofReal (Real.exp (theta0 * H m' e)) ∂(muDT n) ≤ 5 ^ n) :
    ∫⁻ y, ∫⁻ e, ENNReal.ofReal (Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 +
        cT * y ^ 2 + H (χ y) e))) ∂(muDT n) ∂saN ≤ 5 ^ (n + 1) := by
  have h1 : ∀ y, ∫⁻ e, ENNReal.ofReal (Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 +
        cT * y ^ 2 + H (χ y) e))) ∂(muDT n) ≤
      ENNReal.ofReal (Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 +
        cT * y ^ 2))) * 5 ^ n := by
    intro y
    have : ∀ e, ENNReal.ofReal (Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 +
        cT * y ^ 2 + H (χ y) e))) =
        ENNReal.ofReal (Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 +
        cT * y ^ 2))) * ENNReal.ofReal (Real.exp (theta0 * H (χ y) e)) := by
      intro e
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
    simp_rw [this]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right (hH _) _
  calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 +
        cT * y ^ 2))) * 5 ^ n ∂saN := lintegral_mono h1
    _ = (∫⁻ y, ENNReal.ofReal (Real.exp (theta0 * (3 * (√(χ y : ℝ) - √((m : ℝ) / 2)) ^ 2 +
        cT * y ^ 2))) ∂saN) * 5 ^ n := by
        rw [lintegral_mul_const' _ _ (by simp)]
    _ ≤ 5 * 5 ^ n := mul_le_mul_left (one_level hχ hm) _
    _ = 5 ^ (n + 1) := by rw [pow_succ']

theorem lintegral_fst_le (n : ℕ) (g : DT n → ℝ≥0∞) :
    ∫⁻ e, g e.1 ∂((muDT n).prod (muDT n)) ≤ ∫⁻ e, g e ∂(muDT n) := by
  refine (lintegral_prod_le _).trans ?_
  simp

theorem lintegral_snd_le (n : ℕ) (g : DT n → ℝ≥0∞) :
    ∫⁻ e, g e.2 ∂((muDT n).prod (muDT n)) ≤ ∫⁻ e, g e ∂(muDT n) := by
  refine (lintegral_prod_le _).trans ?_
  simp

/-- Exponential moments along a path, Step 3: `E exp(θ Θ) ≤ κ^n`, uniformly in the start count. -/
theorem theta_moment (n : ℕ) (m : ℕ) (j : ℕ) :
    ∫⁻ d, ENNReal.ofReal (Real.exp (theta0 * Theta n m d j)) ∂(muDT n) ≤ 5 ^ n := by
  induction n generalizing m j with
  | zero =>
    simp only [Theta, mul_zero, Real.exp_zero, ENNReal.ofReal_one, lintegral_const, one_mul,
      pow_zero]
    exact (measure_univ (μ := muDT 0)).le
  | succ n ih =>
    have hid : HasLaw (fun y : ℝ => y) saN saN := HasLaw.id
    have hmq : Measurable (saq m) := (saq_monotone m).measurable
    have hmr : Measurable (fun y : ℝ => m - saq m y) := hmq.const_sub m
    change ∫⁻ d, _ ∂(saN.prod ((muDT n).prod (muDT n))) ≤ _
    refine (lintegral_prod_le _).trans ?_
    by_cases hlt : j < 2 ^ n
    · have := level_gen n m (χ := saq m) (hasLaw_saq hid m) hmq
        (fun m' e => Theta n m' e j) (fun m' => ih m' j)
      refine le_trans (lintegral_mono fun y => ?_) this
      simp only [Theta, hlt, ↓reduceIte]
      exact lintegral_fst_le n (fun d => ENNReal.ofReal (Real.exp (theta0 * (3 * (√(saq m y : ℝ) -
        √((m : ℝ) / 2)) ^ 2 + cT * y ^ 2 + Theta n (saq m y) d j))))
    · have := level_gen n m (χ := fun y => m - saq m y) (hasLaw_sub_saq hid m) hmr
        (fun m' e => Theta n m' e (j - 2 ^ n)) (fun m' => ih m' _)
      refine le_trans (lintegral_mono fun y => ?_) this
      simp only [Theta, hlt, ↓reduceIte]
      exact lintegral_snd_le n (fun d => ENNReal.ofReal (Real.exp (theta0 * (3 * (√((m - saq m y : ℕ) : ℝ) -
        √((m : ℝ) / 2)) ^ 2 + cT * y ^ 2 + Theta n (m - saq m y) d (j - 2 ^ n)))))

end StrongApprox
end ElboimSly
