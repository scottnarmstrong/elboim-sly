/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib

/-!
# One-dimensional Gaussian bounds

One-dimensional Gaussian bounds, parts (a), (d), (e) (parts (b), (c) are not used by the
Brownian-motion API of this directory).

All statements are for a real random variable `X` with `HasLaw X (gaussianReal 0 v) P`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}

/-- One-dimensional Gaussian bounds (a). `P(X ≥ a) ≤ exp(-a²/(2v))` for `a ≥ 0`, `v ≠ 0`. -/
theorem real_ge_le_exp_of_hasLaw [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) (hv : v ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    P.real {ω | a ≤ X ω} ≤ Real.exp (-a ^ 2 / (2 * v)) := by
  have hvpos : (0 : ℝ) < v := by positivity
  have hint : Integrable (fun ω => Real.exp ((a / v) * X ω)) P :=
    hX.integrable_comp (f := fun x => Real.exp ((a / v) * x))
      (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (a / v))
  refine (measure_ge_le_exp_mul_mgf a (by positivity) hint).trans ?_
  rw [mgf_gaussianReal hX, ← Real.exp_add]
  apply le_of_eq
  congr 1
  field_simp
  ring

/-- One-dimensional Gaussian bounds (a), as a bound on the measure. -/
theorem measure_ge_le_exp_of_hasLaw [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) (hv : v ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | a ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * v))) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal (real_ge_le_exp_of_hasLaw hX hv ha)

/-- One-dimensional Gaussian bounds (d), the half-line bound: `P(X ≥ 0) ≥ 1/2`. -/
theorem half_le_measure_nonneg_of_hasLaw [IsProbabilityMeasure P] (_hm : Measurable X)
    (hX : HasLaw X (gaussianReal 0 v) P) : (1 / 2 : ℝ≥0∞) ≤ P {ω | 0 ≤ X ω} := by
  have hneg : HasLaw (fun ω => -X ω) (gaussianReal 0 v) P := by
    have := gaussianReal_neg hX
    simpa [Pi.neg_def] using this
  have e : P {ω | X ω ≤ 0} = P {ω | 0 ≤ X ω} := by
    have a1 : P {ω | 0 ≤ -X ω} = gaussianReal 0 v {x | 0 ≤ x} :=
      hneg.measure_eq (p := fun x => 0 ≤ x) (measurableSet_le measurable_const measurable_id)
    have a2 : P {ω | 0 ≤ X ω} = gaussianReal 0 v {x | 0 ≤ x} :=
      hX.measure_eq (p := fun x => 0 ≤ x) (measurableSet_le measurable_const measurable_id)
    rw [a2, ← a1]
    congr 1
    ext ω; simp
  have hu : (1 : ℝ≥0∞) ≤ P {ω | 0 ≤ X ω} + P {ω | X ω ≤ 0} := by
    calc (1 : ℝ≥0∞) = P Set.univ := (measure_univ).symm
      _ ≤ P ({ω | 0 ≤ X ω} ∪ {ω | X ω ≤ 0}) := by
          refine measure_mono fun ω _ => ?_
          rcases le_total 0 (X ω) with h | h
          · exact Or.inl h
          · exact Or.inr h
      _ ≤ _ := measure_union_le _ _
  rw [e, ← two_mul] at hu
  calc (1 / 2 : ℝ≥0∞) = 2⁻¹ * 1 := by simp
    _ ≤ 2⁻¹ * (2 * P {ω | 0 ≤ X ω}) := by gcongr
    _ = P {ω | 0 ≤ X ω} := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- The elementary inequality `y⁴ ≤ 24 (e^y + e^{-y})`. -/
lemma pow_four_le_exp_add (y : ℝ) : y ^ 4 ≤ 24 * (Real.exp y + Real.exp (-y)) := by
  have h := Real.pow_div_factorial_le_exp |y| (abs_nonneg y) 4
  have h4 : y ^ 4 = |y| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac] at h
  have : |y| ^ 4 ≤ 24 * Real.exp |y| := by
    rw [div_le_iff₀ (by norm_num)] at h
    linarith
  have h2 : Real.exp |y| ≤ Real.exp y + Real.exp (-y) := by
    rcases abs_cases y with ⟨e, _⟩ | ⟨e, _⟩
    · rw [e]; linarith [Real.exp_pos (-y)]
    · rw [e]; linarith [Real.exp_pos y]
  rw [h4]
  nlinarith [Real.exp_pos y, Real.exp_pos (-y)]

/-- One-dimensional Gaussian bounds (e): `E X⁴ ≤ 80 v²`. -/
theorem integral_pow_four_le_of_hasLaw [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) : ∫ ω, X ω ^ 4 ∂P ≤ 80 * (v : ℝ) ^ 2 := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var] at hX
    have := hX.ae_eq_of_dirac
    have h0 : ∫ ω, X ω ^ 4 ∂P = ∫ ω, (0 : ℝ) ^ 4 ∂P :=
      integral_congr_ae (this.mono fun ω hω => by simp [hω])
    simp [h0]
  have hvpos : (0 : ℝ) < v := by positivity
  set s : ℝ := Real.sqrt v with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hvpos
  have hss : s * s = v := Real.mul_self_sqrt hvpos.le
  have hint4 : Integrable (fun ω => X ω ^ 4) P := by
    have := (hX.memLp_comp (f := fun x : ℝ => x) (p := 4)
      (memLp_id_gaussianReal' 4 (by simp)))
    have h2 := this.integrable_norm_pow (p := 4) (by norm_num)
    simpa [Real.norm_eq_abs, pow_abs, abs_pow] using h2.congr (Filter.Eventually.of_forall
      fun ω => by simp [Even.pow_abs (by decide : Even 4)])
  have hiexp : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) P := fun t =>
    hX.integrable_comp (f := fun x => Real.exp (t * x)) (integrable_exp_mul_gaussianReal t)
  have hmgf : ∀ t : ℝ, ∫ ω, Real.exp (t * X ω) ∂P = Real.exp (v * t ^ 2 / 2) := by
    intro t
    have := mgf_gaussianReal hX t
    simpa [mgf] using this
  calc ∫ ω, X ω ^ 4 ∂P
      ≤ ∫ ω, 24 * (v : ℝ) ^ 2 * (Real.exp ((1 / s) * X ω) + Real.exp ((-1 / s) * X ω)) ∂P := by
        refine integral_mono hint4 (((hiexp (1 / s)).add (hiexp (-1 / s))).const_mul _) fun ω => ?_
        have := pow_four_le_exp_add (X ω / s)
        have e1 : (X ω / s) ^ 4 = X ω ^ 4 / (v : ℝ) ^ 2 := by
          rw [div_pow, ← hss]; ring
        have e2 : Real.exp (X ω / s) = Real.exp ((1 / s) * X ω) := by congr 1; ring
        have e3 : Real.exp (-(X ω / s)) = Real.exp ((-1 / s) * X ω) := by congr 1; ring
        rw [e1, e2, e3, div_le_iff₀ (by positivity)] at this
        linarith
    _ = 24 * (v : ℝ) ^ 2 * (Real.exp (v * (1 / s) ^ 2 / 2) + Real.exp (v * (-1 / s) ^ 2 / 2)) := by
        rw [integral_const_mul, integral_add (hiexp _) (hiexp _), hmgf, hmgf]
    _ ≤ 80 * (v : ℝ) ^ 2 := by
        have h1 : v * (1 / s) ^ 2 / 2 = 1 / 2 := by
          rw [div_pow, ← hss]; field_simp
        have h2 : v * (-1 / s) ^ 2 / 2 = 1 / 2 := by
          rw [div_pow, ← hss]; field_simp
        rw [h1, h2]
        have hexp : Real.exp (1 / 2) ≤ 5 / 3 := by
          have h := Real.exp_one_lt_d9
          have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
            rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos (1 / 2)]
        have : 0 ≤ (v : ℝ) ^ 2 := by positivity
        nlinarith

end ElboimSly.Brownian
