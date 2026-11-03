/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Probability.Moments.Basic

/-!
# Elementary inequalities

Elementary inequalities (Part I).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal Real ENNReal

namespace ElboimSly
namespace StrongApprox

/-- Elementary inequalities(a). -/
theorem abs_exp_sub_one_sub_le {u : ℝ} (hu : |u| ≤ 1) : |Real.exp u - 1 - u| ≤ 3 / 4 * u ^ 2 := by
  have h := Real.exp_bound hu (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.factorial] at h
  have e : Real.exp u - 1 - u = Real.exp u - (1 + u) := by ring
  rw [e]; linarith

/-- Elementary inequalities(a), the particular case `e - 2 ≤ 3/4`. -/
theorem exp_one_sub_two_le : Real.exp 1 - 2 ≤ 3 / 4 := by
  have := abs_exp_sub_one_sub_le (u := 1) (by norm_num)
  have := (abs_le.1 this).2
  norm_num at this; linarith

/-- Elementary inequalities(b). -/
theorem abs_log_sub_add_le {a : ℝ} (ha : |a| ≤ 1 / 2) :
    |Real.log ((1 - a) / (1 + a)) + 2 * a| ≤ 4 * |a| ^ 3 := by
  have h1 : |a| < 1 := by linarith
  have h2 : |-a| < 1 := by rw [abs_neg]; exact h1
  have e1 := Real.abs_log_sub_add_sum_range_le h1 2
  have e2 := Real.abs_log_sub_add_sum_range_le h2 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e1 e2
  rw [abs_neg] at e2
  have hpos : 0 < 1 - |a| := by linarith
  have h3 : |a| ^ 3 / (1 - |a|) ≤ 2 * |a| ^ 3 := by
    rw [div_le_iff₀ hpos]
    have : 0 ≤ |a| ^ 3 := by positivity
    nlinarith
  have ha1 : 0 < 1 - a := by linarith [le_abs_self a]
  have ha2 : 0 < 1 + a := by linarith [neg_abs_le a]
  rw [Real.log_div ha1.ne' ha2.ne']
  have e3 : Real.log (1 - -a) = Real.log (1 + a) := by ring_nf
  rw [e3] at e2
  norm_num at e1 e2
  have := abs_sub (a + a ^ 2 / 2 + Real.log (1 - a)) (-a + a ^ 2 / 2 + Real.log (1 + a))
  have e4 : Real.log (1 - a) - Real.log (1 + a) + 2 * a =
      (a + a ^ 2 / 2 + Real.log (1 - a)) - (-a + a ^ 2 / 2 + Real.log (1 + a)) := by ring
  rw [e4]; linarith

/-- The bound of the discrete layer cake: `e^c (1 + 2/(e^{κ-c} - 1))`. -/
noncomputable def layerCakeBound (κ c : ℝ) : ℝ := Real.exp c * (1 + 2 / (Real.exp (κ - c) - 1))

theorem layerCakeBound_eq {κ c : ℝ} (hκ : c < κ) :
    layerCakeBound κ c =
      Real.exp c * (1 + 2 * (Real.exp (-(κ - c)) / (1 - Real.exp (-(κ - c))))) := by
  unfold layerCakeBound
  have h1 : 1 < Real.exp (κ - c) := Real.one_lt_exp_iff.2 (by linarith)
  have h2 : Real.exp (-(κ - c)) = (Real.exp (κ - c))⁻¹ := Real.exp_neg _
  rw [h2]
  have h3 : Real.exp (κ - c) - 1 ≠ 0 := by linarith
  have h4 : (0 : ℝ) < Real.exp (κ - c) := by linarith
  have h5 : 1 - (Real.exp (κ - c))⁻¹ ≠ 0 := by
    have : (Real.exp (κ - c))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith
  field_simp

/-- The coefficients of the discrete layer cake. -/
noncomputable def layerCoeff (c r : ℝ) (k : ℕ) : ℝ := Real.exp c * (if k = 0 then 1 else 2 * r ^ k)

theorem summable_ite_geom {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun k : ℕ => (if k = 0 then (1 : ℝ) else 2 * r ^ k) := by
  rw [← summable_nat_add_iff 1]
  have : Summable fun k : ℕ => 2 * r * r ^ k := (summable_geometric_of_lt_one h0 h1).mul_left _
  refine this.congr fun k => ?_
  simp [pow_succ]; ring

theorem summable_layerCoeff (c : ℝ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (layerCoeff c r) := (summable_ite_geom h0 h1).mul_left _

theorem tsum_layerCoeff (c : ℝ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑' k, layerCoeff c r k = Real.exp c * (1 + 2 * (r / (1 - r))) := by
  unfold layerCoeff
  rw [tsum_mul_left]
  congr 1
  have hs := summable_ite_geom h0 h1
  rw [hs.tsum_eq_zero_add]
  simp only [ite_true, Nat.succ_ne_zero, ite_false]
  have : ∑' k : ℕ, 2 * r ^ (k + 1) = 2 * (r / (1 - r)) := by
    simp only [pow_succ]
    rw [show (fun k : ℕ => 2 * (r ^ k * r)) = fun k => (2 * r) * r ^ k by funext k; ring,
      tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
    field_simp
  simpa using this

/-- Elementary inequalities(c), in its `lintegral` form. -/
theorem lintegral_exp_le_layerCakeBound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) {c κ : ℝ}
    (hc : 0 ≤ c) (hκ : c < κ)
    (h : ∀ ρ, 0 ≤ ρ → P.real {ω | ρ ≤ Y ω} ≤ 2 * Real.exp (-(κ * ρ))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (c * Y ω)) ∂P ≤ ENNReal.ofReal (layerCakeBound κ c) := by
  set r := Real.exp (-(κ - c)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  let F : ℕ → Ω → ℝ≥0∞ := fun k =>
    {ω | (k : ℝ) ≤ Y ω}.indicator (fun _ => ENNReal.ofReal (Real.exp (c * (k + 1))))
  have hF : ∀ k, Measurable (F k) := fun k =>
    measurable_const.indicator (measurableSet_le measurable_const hY)
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (c * Y ω)) ≤ ∑' k, F k ω := by
    intro ω
    refine le_trans ?_ (ENNReal.le_tsum ⌊Y ω⌋₊)
    have hk : (⌊Y ω⌋₊ : ℝ) ≤ Y ω := Nat.floor_le (hY0 ω)
    have hk2 : Y ω < ⌊Y ω⌋₊ + 1 := Nat.lt_floor_add_one _
    simp only [F, indicator, mem_ofPred_eq, hk, ite_true]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  have hk : ∀ k : ℕ, ∫⁻ ω, F k ω ∂P ≤ ENNReal.ofReal (layerCoeff c r k) := by
    intro k
    simp only [F]
    rw [lintegral_indicator_const (measurableSet_le measurable_const hY)]
    have hPk : P {ω | (k : ℝ) ≤ Y ω} ≤ ENNReal.ofReal (if k = 0 then 1 else 2 * Real.exp (-(κ * k))) := by
      rw [← ofReal_measureReal]
      apply ENNReal.ofReal_le_ofReal
      split_ifs with hk0
      · exact measureReal_le_one
      · exact h k (Nat.cast_nonneg k)
    calc ENNReal.ofReal (Real.exp (c * (k + 1))) * P {ω | (k : ℝ) ≤ Y ω}
        ≤ ENNReal.ofReal (Real.exp (c * (k + 1))) *
          ENNReal.ofReal (if k = 0 then 1 else 2 * Real.exp (-(κ * k))) := by gcongr
      _ = ENNReal.ofReal (layerCoeff c r k) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        unfold layerCoeff
        by_cases hk0 : k = 0
        · subst hk0; simp
        · simp only [hk0, ite_false, hr]
          rw [← Real.exp_nat_mul, mul_comm (Real.exp c)]
          calc Real.exp (c * (k + 1)) * (2 * Real.exp (-(κ * k)))
              = 2 * (Real.exp (c * (k + 1)) * Real.exp (-(κ * k))) := by ring
            _ = 2 * Real.exp (c * (k + 1) + -(κ * k)) := by rw [Real.exp_add]
            _ = 2 * (Real.exp c * Real.exp (↑k * -(κ - c))) := by
                rw [← Real.exp_add]; congr 2; ring
            _ = _ := by ring
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (c * Y ω)) ∂P ≤ ∫⁻ ω, ∑' k, F k ω ∂P := lintegral_mono hpt
    _ = ∑' k, ∫⁻ ω, F k ω ∂P := lintegral_tsum fun k => (hF k).aemeasurable
    _ ≤ ∑' k, ENNReal.ofReal (layerCoeff c r k) := ENNReal.tsum_le_tsum hk
    _ = ENNReal.ofReal (∑' k, layerCoeff c r k) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun k => ?_) (summable_layerCoeff c hr0 hr1)]
        unfold layerCoeff
        have := Real.exp_pos c
        split_ifs <;> positivity
    _ = ENNReal.ofReal (layerCakeBound κ c) := by
        rw [tsum_layerCoeff c hr0 hr1, layerCakeBound_eq hκ]

/-- Elementary inequalities(c). -/
theorem integral_exp_le_layerCakeBound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) {c κ : ℝ}
    (hc : 0 ≤ c) (hκ : c < κ)
    (h : ∀ ρ, 0 ≤ ρ → P.real {ω | ρ ≤ Y ω} ≤ 2 * Real.exp (-(κ * ρ))) :
    Integrable (fun ω => Real.exp (c * Y ω)) P ∧
      ∫ ω, Real.exp (c * Y ω) ∂P ≤ layerCakeBound κ c := by
  have hl := lintegral_exp_le_layerCakeBound hY hY0 hc hκ h
  have hm : Measurable fun ω => Real.exp (c * Y ω) := Real.measurable_exp.comp (hY.const_mul c)
  have hint : Integrable (fun ω => Real.exp (c * Y ω)) P := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp only [Real.enorm_eq_ofReal (Real.exp_pos _).le]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have hnn : 0 ≤ layerCakeBound κ c := by
    unfold layerCakeBound
    have : 1 < Real.exp (κ - c) := Real.one_lt_exp_iff.2 (by linarith)
    have : 0 < Real.exp (κ - c) - 1 := by linarith
    positivity
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (Real.exp_pos _).le)
    hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hnn hl

theorem layerCakeBound_one_half_le : layerCakeBound 1 (1 / 2) ≤ 7 := by
  unfold layerCakeBound
  have hx : 8 / 5 ≤ Real.exp (1 / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
    linarith
  have hx2 : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [e]
  have h3 : 0 < Real.exp (1 / 2) - 1 := by linarith
  rw [show Real.exp (1 / 2) * (1 + 2 / (Real.exp (1 / 2) - 1)) =
    Real.exp (1 / 2) * (Real.exp (1 / 2) + 1) / (Real.exp (1 / 2) - 1) by field_simp; ring]
  rw [div_le_iff₀ h3]
  nlinarith

theorem layerCakeBound_quarter_le : layerCakeBound (1 / 4) (1 / 8) ≤ 19 := by
  unfold layerCakeBound
  have hx : 1.1328 ≤ Real.exp (1 / 8) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 1 / 8) (by norm_num)
    norm_num at this ⊢; linarith
  have hx2 : Real.exp (1 / 8) ≤ 2 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 8) (by norm_num) (by norm_num)
    norm_num at this; linarith
  have e : (1 : ℝ) / 4 - 1 / 8 = 1 / 8 := by norm_num
  rw [e]
  have h3 : 0 < Real.exp (1 / 8) - 1 := by linarith
  rw [show Real.exp (1 / 8) * (1 + 2 / (Real.exp (1 / 8) - 1)) =
    Real.exp (1 / 8) * (Real.exp (1 / 8) + 1) / (Real.exp (1 / 8) - 1) by field_simp; ring]
  rw [div_le_iff₀ h3]
  nlinarith

theorem layerCakeBound_mono {κ c c' : ℝ} (hcc : c ≤ c') (hκ : c' < κ) :
    layerCakeBound κ c ≤ layerCakeBound κ c' := by
  unfold layerCakeBound
  have h1 : Real.exp (κ - c') ≤ Real.exp (κ - c) := Real.exp_le_exp.2 (by linarith)
  have h2 : 1 < Real.exp (κ - c') := Real.one_lt_exp_iff.2 (by linarith)
  have h3 : 0 < Real.exp (κ - c') - 1 := by linarith
  have h4 : 2 / (Real.exp (κ - c) - 1) ≤ 2 / (Real.exp (κ - c') - 1) := by
    gcongr
  have h5 : 0 ≤ 2 / (Real.exp (κ - c) - 1) := by
    have : 0 < Real.exp (κ - c) - 1 := by linarith
    positivity
  calc _ ≤ Real.exp c' * (1 + 2 / (Real.exp (κ - c) - 1)) := by
        gcongr
    _ ≤ _ := by gcongr

end StrongApprox
end ElboimSly
