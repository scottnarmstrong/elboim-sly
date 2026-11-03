/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Standard normal law, density and distribution function

Standard normal law, density, distribution function; Gaussian facts (Part I).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Real

namespace ElboimSly
namespace StrongApprox

/-- Standard normal law, density, distribution function. The standard normal law. -/
noncomputable def saN : Measure ℝ := gaussianReal 0 1

/-- Standard normal law, density, distribution function. The standard normal density. -/
noncomputable def saphi (u : ℝ) : ℝ := gaussianPDFReal 0 1 u

/-- Standard normal law, density, distribution function. The standard normal distribution function. -/
noncomputable def saPhi (z : ℝ) : ℝ := saN.real (Iic z)

/-- Standard normal law, density, distribution function. The standard normal upper tail. -/
noncomputable def saPhib (z : ℝ) : ℝ := 1 - saPhi z

instance : IsProbabilityMeasure saN := by unfold saN; infer_instance

theorem saphi_eq (u : ℝ) : saphi u = (√(2 * π))⁻¹ * Real.exp (-(u ^ 2) / 2) := by
  simp [saphi, gaussianPDFReal]

theorem saphi_pos (u : ℝ) : 0 < saphi u := gaussianPDFReal_pos _ _ _ one_ne_zero

theorem saphi_le (u : ℝ) : saphi u ≤ (√(2 * π))⁻¹ := by
  rw [saphi_eq]
  have : Real.exp (-(u ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
  have h0 : 0 ≤ (√(2 * π))⁻¹ := by positivity
  calc _ ≤ (√(2 * π))⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

theorem integrable_saphi : Integrable saphi := integrable_gaussianPDFReal 0 1

@[fun_prop]
theorem continuous_saphi : Continuous saphi := by
  unfold saphi gaussianPDFReal; fun_prop

theorem saN_apply (s : Set ℝ) : saN s = ENNReal.ofReal (∫ x in s, saphi x) :=
  gaussianReal_apply_eq_integral 0 one_ne_zero s

theorem saPhi_eq_integral (z : ℝ) : saPhi z = ∫ x in Iic z, saphi x := by
  unfold saPhi
  rw [measureReal_def, saN_apply, ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Iic fun x _ => (saphi_pos x).le

theorem saPhi_sub {a b : ℝ} (_hab : a ≤ b) : saPhi b - saPhi a = ∫ x in a..b, saphi x := by
  rw [saPhi_eq_integral, saPhi_eq_integral]
  exact intervalIntegral.integral_Iic_sub_Iic integrable_saphi.integrableOn integrable_saphi.integrableOn

theorem saPhib_eq_integral (z : ℝ) : saPhib z = ∫ x in Ioi z, saphi x := by
  unfold saPhib
  rw [saPhi_eq_integral]
  have h := integral_add_compl (μ := volume) (f := saphi) (s := Iic z) measurableSet_Iic integrable_saphi
  have h1 : ∫ x, saphi x = 1 := by
    have := saN_apply univ
    simp only [measure_univ, Measure.restrict_univ] at this
    have h2 : (1 : ENNReal) = ENNReal.ofReal (∫ x, saphi x) := by simpa using this
    have h3 := congrArg ENNReal.toReal h2
    rw [ENNReal.toReal_ofReal (integral_nonneg fun x => (saphi_pos x).le)] at h3
    simpa using h3.symm
  rw [compl_Iic] at h
  linarith

theorem saPhib_sub {a b : ℝ} (hab : a ≤ b) : saPhib a - saPhib b = ∫ x in a..b, saphi x := by
  unfold saPhib; rw [← saPhi_sub hab]; ring

theorem integral_saphi_nonneg {a b : ℝ} (hab : a ≤ b) : 0 ≤ ∫ x in a..b, saphi x :=
  intervalIntegral.integral_nonneg hab fun x _ => (saphi_pos x).le

theorem integral_saphi_le {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, saphi x ≤ (b - a) * (√(2 * π))⁻¹ := by
  have := intervalIntegral.integral_mono_on hab (f := saphi) (g := fun _ => (√(2 * π))⁻¹)
    (integrable_saphi.intervalIntegrable) (by simp) (fun x _ => saphi_le x)
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  exact this

theorem integral_saphi_pos {a b : ℝ} (hab : a < b) : 0 < ∫ x in a..b, saphi x :=
  intervalIntegral.intervalIntegral_pos_of_pos_on integrable_saphi.intervalIntegrable
    (fun x _ => saphi_pos x) hab

/-! ### Lemma Gaussian facts -/

theorem saPhi_nonneg (z : ℝ) : 0 ≤ saPhi z := measureReal_nonneg

theorem saPhi_le_one (z : ℝ) : saPhi z ≤ 1 := measureReal_le_one

theorem saPhib_nonneg (z : ℝ) : 0 ≤ saPhib z := by unfold saPhib; linarith [saPhi_le_one z]

theorem saPhib_le_one (z : ℝ) : saPhib z ≤ 1 := by unfold saPhib; linarith [saPhi_nonneg z]

/-- Gaussian facts(a), first half. -/
theorem saPhi_sub_bounds {a b : ℝ} (hab : a ≤ b) :
    0 ≤ saPhi b - saPhi a ∧ saPhi b - saPhi a ≤ (b - a) * (√(2 * π))⁻¹ := by
  rw [saPhi_sub hab]
  exact ⟨integral_saphi_nonneg hab, integral_saphi_le hab⟩

/-- Gaussian facts(a), strict positivity. -/
theorem saPhi_lt_of_lt {a b : ℝ} (hab : a < b) : saPhi a < saPhi b := by
  have := integral_saphi_pos hab
  rw [← saPhi_sub hab.le] at this; linarith

theorem saPhi_strictMono : StrictMono saPhi := fun _ _ h => saPhi_lt_of_lt h

theorem saPhi_monotone : Monotone saPhi := saPhi_strictMono.monotone

theorem saPhib_antitone : Antitone saPhib := fun _ _ h => by
  unfold saPhib; linarith [saPhi_monotone h]

theorem saPhib_strictAnti : StrictAnti saPhib := fun _ _ h => by
  unfold saPhib; linarith [saPhi_strictMono h]

theorem continuous_saPhi : Continuous saPhi := by
  have hL : LipschitzWith (√(2 * π))⁻¹.toNNReal saPhi := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total x y with h | h
    · have := saPhi_sub_bounds h
      rw [abs_of_nonpos (by linarith [this.1]), abs_of_nonpos (by linarith)]
      rw [Real.coe_toNNReal _ (by positivity)]; nlinarith [this.2]
    · have := saPhi_sub_bounds h
      rw [abs_of_nonneg (by linarith [this.1]), abs_of_nonneg (by linarith)]
      rw [Real.coe_toNNReal _ (by positivity)]; nlinarith [this.2]
  exact hL.continuous

theorem saPhi_pos (z : ℝ) : 0 < saPhi z :=
  lt_of_le_of_lt (saPhi_nonneg (z - 1)) (saPhi_lt_of_lt (by linarith))

theorem saPhi_lt_one (z : ℝ) : saPhi z < 1 :=
  lt_of_lt_of_le (saPhi_lt_of_lt (show z < z + 1 by linarith)) (saPhi_le_one _)

theorem saPhi_eq_cdf : saPhi = cdf saN := by
  funext z; rw [cdf_eq_real]; rfl

theorem tendsto_saPhi_atBot : Tendsto saPhi atBot (𝓝 0) := by
  rw [saPhi_eq_cdf]; exact tendsto_cdf_atBot _

theorem tendsto_saPhi_atTop : Tendsto saPhi atTop (𝓝 1) := by
  rw [saPhi_eq_cdf]; exact tendsto_cdf_atTop _

/-- Gaussian facts(b). -/
theorem saphi_add (u b : ℝ) : saphi (u + b) = saphi u * Real.exp (-(u * b) - b ^ 2 / 2) := by
  rw [saphi_eq, saphi_eq, mul_assoc, ← Real.exp_add]
  congr 2; ring

theorem saphi_antitoneOn : AntitoneOn saphi (Ici 0) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  rw [saphi_eq, saphi_eq]
  gcongr

theorem saphi_neg (u : ℝ) : saphi (-u) = saphi u := by simp [saphi_eq]

theorem integral_Ioi_shift (g : ℝ → ℝ) (t : ℝ) :
    ∫ x in Ioi t, g x = ∫ r in Ioi 0, g (r + t) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun x => (Ioi t).indicator g x) t]
  congr 1; funext x
  by_cases hx : 0 < x
  · simp [indicator, hx, show t < x + t by linarith]
  · simp [indicator, hx, show ¬ t < x + t by intro h; exact hx (by linarith)]

/-- Gaussian facts(c), the upper bound. -/
theorem saPhib_le_sqrt {t : ℝ} (ht : 0 ≤ t) : saPhib t ≤ √(π / 2) * saphi t := by
  rw [saPhib_eq_integral, integral_Ioi_shift]
  have hint : IntegrableOn (fun r => saphi t * Real.exp (-(1 / 2) * r ^ 2)) (Ioi 0) :=
    (((integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul (saphi t))).integrableOn
  calc ∫ r in Ioi (0 : ℝ), saphi (r + t)
      ≤ ∫ r in Ioi (0 : ℝ), saphi t * Real.exp (-(1 / 2) * r ^ 2) := by
        refine setIntegral_mono_on (integrable_saphi.comp_add_right t).integrableOn hint
          measurableSet_Ioi fun r hr => ?_
        simp only [mem_Ioi] at hr
        rw [add_comm, saphi_add]
        have := saphi_pos t
        gcongr
        nlinarith [mul_nonneg ht hr.le, sq_nonneg t]
    _ = saphi t * (√(π / (1 / 2)) / 2) := by
        rw [integral_const_mul, integral_gaussian_Ioi]
    _ = √(π / 2) * saphi t := by
        have : √(π / (1 / 2)) / 2 = √(π / 2) := by
          rw [show π / (1 / 2) = 4 * (π / 2) by ring, Real.sqrt_mul (by norm_num),
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          ring
        rw [this, mul_comm]

theorem sqrt_pi_div_two_mul_saphi (t : ℝ) : √(π / 2) * saphi t = Real.exp (-(t ^ 2) / 2) / 2 := by
  rw [saphi_eq]
  have h : √(π / 2) * (√(2 * π))⁻¹ = 1 / 2 := by
    have h2 : √(2 * π) = 2 * √(π / 2) := by
      rw [show 2 * π = 4 * (π / 2) by ring, Real.sqrt_mul (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have : 0 < √(π / 2) := Real.sqrt_pos.2 (by positivity)
    rw [h2]; field_simp
  calc _ = (√(π / 2) * (√(2 * π))⁻¹) * Real.exp (-(t ^ 2) / 2) := by ring
    _ = _ := by rw [h]; ring

/-- Gaussian facts(c), the upper bound in closed form. -/
theorem saPhib_le_half_exp {t : ℝ} (ht : 0 ≤ t) : saPhib t ≤ Real.exp (-(t ^ 2) / 2) / 2 := by
  have := saPhib_le_sqrt ht
  rwa [sqrt_pi_div_two_mul_saphi] at this

/-- Gaussian facts(c), the lower bound `φ(t+1) ≤ Φ̄(t)`. -/
theorem saphi_add_one_le_saPhib {t : ℝ} (ht : 0 ≤ t) : saphi (t + 1) ≤ saPhib t := by
  have h1 := saPhib_sub (show t ≤ t + 1 by linarith)
  have h2 : (t + 1 - t) * saphi (t + 1) ≤ ∫ x in t..(t + 1), saphi x := by
    have := intervalIntegral.integral_mono_on (show t ≤ t + 1 by linarith)
      (f := fun _ => saphi (t + 1)) (g := saphi) (by simp) integrable_saphi.intervalIntegrable
      (fun x hx => saphi_antitoneOn (show (0 : ℝ) ≤ x from le_trans ht hx.1)
        (show (0 : ℝ) ≤ t + 1 by linarith) hx.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  have := saPhib_nonneg (t + 1)
  nlinarith

/-- Gaussian facts(c), the Gaussian-shaped lower bound. -/
theorem saphi_add_one_ge (t : ℝ) :
    (√(2 * π))⁻¹ * Real.exp (-1) * Real.exp (-(t ^ 2)) ≤ saphi (t + 1) := by
  rw [saphi_eq, mul_assoc, ← Real.exp_add]
  gcongr
  nlinarith [sq_nonneg (t - 1)]

theorem saPhib_ge_exp {t : ℝ} (ht : 0 ≤ t) :
    (√(2 * π))⁻¹ * Real.exp (-1) * Real.exp (-(t ^ 2)) ≤ saPhib t :=
  (saphi_add_one_ge t).trans (saphi_add_one_le_saPhib ht)

/-- Gaussian facts(d), first part. -/
theorem integral_exp_sq_saN {c : ℝ} (_h0 : 0 ≤ c) (h1 : c < 1 / 2) :
    ∫ y, Real.exp (c * y ^ 2) ∂saN = (√(1 - 2 * c))⁻¹ := by
  unfold saN
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  have hb : 0 < (1 - 2 * c) / 2 := by linarith
  have : (fun y : ℝ => gaussianPDFReal 0 1 y • Real.exp (c * y ^ 2))
      = fun y => (√(2 * π))⁻¹ * Real.exp (-((1 - 2 * c) / 2) * y ^ 2) := by
    funext y
    have := saphi_eq y
    simp only [saphi] at this
    rw [smul_eq_mul, this, mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [this, integral_const_mul, integral_gaussian]
  have h2 : π / ((1 - 2 * c) / 2) = (2 * π) * (1 / (1 - 2 * c)) := by
    field_simp
  rw [h2, Real.sqrt_mul (show 0 ≤ 2 * π by positivity) (1 / (1 - 2 * c)), one_div, Real.sqrt_inv]
  have : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have : 0 < √(1 - 2 * c) := Real.sqrt_pos.2 (by linarith)
  field_simp

theorem integral_exp_mul_saN (t : ℝ) : ∫ y, Real.exp (t * y) ∂saN = Real.exp (t ^ 2 / 2) := by
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [mgf, id] at this
  unfold saN
  rw [this]; simp

/-- Gaussian facts(d), second part. -/
theorem integral_exp_abs_saN_le {t : ℝ} (_ht : 0 ≤ t) :
    ∫ y, Real.exp (t * |y|) ∂saN ≤ 2 * Real.exp (t ^ 2 / 2) := by
  have h1 : Integrable (fun y => Real.exp (t * y)) saN := integrable_exp_mul_gaussianReal t
  have h2 : Integrable (fun y => Real.exp ((-t) * y)) saN := integrable_exp_mul_gaussianReal (-t)
  calc ∫ y, Real.exp (t * |y|) ∂saN
      ≤ ∫ y, (Real.exp (t * y) + Real.exp ((-t) * y)) ∂saN := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => (Real.exp_pos _).le) (h1.add h2)
          (ae_of_all _ fun y => ?_)
        show Real.exp (t * |y|) ≤ Real.exp (t * y) + Real.exp ((-t) * y)
        rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; linarith [Real.exp_pos ((-t) * y)]
        · rw [h]; have : t * -y = (-t) * y := by ring
          rw [this]; linarith [Real.exp_pos (t * y)]
    _ = 2 * Real.exp (t ^ 2 / 2) := by
        rw [integral_add h1 h2, integral_exp_mul_saN, integral_exp_mul_saN]
        simp only [neg_sq]; ring

/-- Gaussian facts(e). -/
theorem saN_real_saPhi_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    saN.real {y | saPhi y ≤ p} = p := by
  rcases hp1.eq_or_lt with rfl | hp1
  · have : {y | saPhi y ≤ 1} = univ := by ext y; simp [saPhi_le_one]
    rw [this]; simp
  rcases hp0.eq_or_lt with rfl | hp0
  · have : {y | saPhi y ≤ 0} = ∅ := by
      ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]; exact saPhi_pos y
    rw [this]; simp
  obtain ⟨a, ha⟩ : ∃ a, saPhi a ≤ p := by
    have := tendsto_saPhi_atBot.eventually (gt_mem_nhds hp0)
    exact (this.and (eventually_lt_atBot 0)).exists.imp fun a h => h.1.le
  obtain ⟨b, hb⟩ : ∃ b, p ≤ saPhi b := by
    have := tendsto_saPhi_atTop.eventually (lt_mem_nhds hp1)
    exact (this.and (eventually_gt_atTop 0)).exists.imp fun a h => h.1.le
  obtain ⟨t, ht⟩ := mem_range_of_exists_le_of_exists_ge continuous_saPhi ⟨a, ha⟩ ⟨b, hb⟩
  have : {y | saPhi y ≤ p} = Iic t := by
    ext y; simp only [mem_ofPred_eq, mem_Iic]
    rw [← ht]; exact saPhi_strictMono.le_iff_le
  rw [this]; exact ht

end StrongApprox
end ElboimSly
