/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Shift

/-!
# Perturbed Gaussian tails

Perturbed Gaussian tails (Part I).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal Real

namespace ElboimSly
namespace StrongApprox

theorem exp_neg_two_mul_le_one_sub {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    Real.exp (-(2 * t)) ≤ 1 - t := by
  have hpos : 0 < 1 - t := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : -(2 * t) ≤ Real.log (1 - t) := by
    refine le_trans ?_ h
    have : (1 - t)⁻¹ ≤ 1 + 2 * t := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]; nlinarith
    linarith
  exact (Real.le_log_iff_exp_le hpos).1 h2

/-- `φ(v) e^{a v³} ≤ φ(v - 2 a v²)`. -/
theorem saphi_mul_exp_le {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) (h : 2 * a * v ≤ 1) :
    saphi v * Real.exp (a * v ^ 3) ≤ saphi (v - 2 * a * v ^ 2) := by
  rw [saphi_eq, saphi_eq, mul_assoc, ← Real.exp_add]
  gcongr
  nlinarith [mul_nonneg (mul_nonneg ha (pow_nonneg hv 3)) (sub_nonneg.2 h)]

/-- `φ(v + 2 a v²) ≤ φ(v) e^{-a v³}`. -/
theorem saphi_le_mul_exp {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) :
    saphi (v + 2 * a * v ^ 2) ≤ saphi v * Real.exp (-(a * v ^ 3)) := by
  rw [saphi_eq, saphi_eq, mul_assoc (√(2 * π))⁻¹, ← Real.exp_add]
  gcongr
  nlinarith [mul_nonneg (mul_nonneg ha (pow_nonneg hv 3)) (mul_nonneg ha hv),
    mul_nonneg ha (pow_nonneg hv 3)]

theorem one_le_exp_mul_deriv {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) (hav : a * v ≤ 1 / 100) :
    1 ≤ Real.exp (41 / 5 * a * (v - 2 * a * v ^ 2)) * (1 - 4 * a * v) := by
  have hx : 0 ≤ a * v := mul_nonneg ha hv
  have h1 := exp_neg_two_mul_le_one_sub (t := 4 * a * v) (by positivity) (by nlinarith)
  have h2 : 1 ≤ Real.exp (41 / 5 * a * (v - 2 * a * v ^ 2)) * Real.exp (-(2 * (4 * a * v))) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    nlinarith [mul_nonneg hx (sub_nonneg.2 hav)]
  have h3 := Real.exp_pos (41 / 5 * a * (v - 2 * a * v ^ 2))
  calc 1 ≤ _ := h2
    _ ≤ _ := by gcongr

theorem perturb_pointwise_upper {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) (hav : a * v ≤ 1 / 100) :
    saphi v * Real.exp (a * (1 + v ^ 3)) ≤
      Real.exp a * ((saphi (v - 2 * a * v ^ 2) * Real.exp (41 / 5 * a * (v - 2 * a * v ^ 2)))
        * (1 - 4 * a * v)) := by
  have h1 := saphi_mul_exp_le ha hv (by nlinarith)
  have h2 := one_le_exp_mul_deriv ha hv hav
  have h3 := saphi_pos (v - 2 * a * v ^ 2)
  have h4 := Real.exp_pos a
  have e : Real.exp (a * (1 + v ^ 3)) = Real.exp a * Real.exp (a * v ^ 3) := by
    rw [← Real.exp_add]; ring_nf
  calc saphi v * Real.exp (a * (1 + v ^ 3))
      = Real.exp a * (saphi v * Real.exp (a * v ^ 3)) := by rw [e]; ring
    _ ≤ Real.exp a * saphi (v - 2 * a * v ^ 2) := by gcongr
    _ ≤ Real.exp a * (saphi (v - 2 * a * v ^ 2) *
          (Real.exp (41 / 5 * a * (v - 2 * a * v ^ 2)) * (1 - 4 * a * v))) := by
        gcongr; exact le_mul_of_one_le_right h3.le h2
    _ = _ := by ring

theorem perturb_pointwise_lower {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) :
    Real.exp (-a) * ((saphi (v + 2 * a * v ^ 2) * Real.exp (-(4 * a) * (v + 2 * a * v ^ 2)))
        * (1 + 4 * a * v)) ≤ saphi v * Real.exp (-(a * (1 + v ^ 3))) := by
  have h1 := saphi_le_mul_exp ha hv
  have h3 := saphi_pos (v + 2 * a * v ^ 2)
  have h4 := Real.exp_pos (-a)
  have h5 : (1 + 4 * a * v) * Real.exp (-(4 * a) * (v + 2 * a * v ^ 2)) ≤ 1 := by
    have h6 : 1 + 4 * a * v ≤ Real.exp (4 * a * v) := by linarith [Real.add_one_le_exp (4 * a * v)]
    have h7 : Real.exp (4 * a * v) * Real.exp (-(4 * a) * (v + 2 * a * v ^ 2)) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith [mul_nonneg (mul_nonneg ha ha) (pow_nonneg hv 2)]
    calc _ ≤ Real.exp (4 * a * v) * Real.exp (-(4 * a) * (v + 2 * a * v ^ 2)) := by
          gcongr
      _ ≤ 1 := h7
  have e : Real.exp (-(a * (1 + v ^ 3))) = Real.exp (-a) * Real.exp (-(a * v ^ 3)) := by
    rw [← Real.exp_add]; ring_nf
  calc _ = Real.exp (-a) * (saphi (v + 2 * a * v ^ 2) *
          ((1 + 4 * a * v) * Real.exp (-(4 * a) * (v + 2 * a * v ^ 2)))) := by ring
    _ ≤ Real.exp (-a) * (saphi (v + 2 * a * v ^ 2) * 1) := by gcongr
    _ ≤ Real.exp (-a) * (saphi v * Real.exp (-(a * v ^ 3))) := by rw [mul_one]; gcongr
    _ = _ := by rw [e]; ring

theorem integral_Ioc_le_Ioi {h : ℝ → ℝ} (hint : Integrable h) (hnn : ∀ x, 0 ≤ h x) {x y : ℝ}
    (hxy : x ≤ y) : ∫ u in x..y, h u ≤ ∫ u in Ioi x, h u := by
  rw [intervalIntegral.integral_of_le hxy]
  exact setIntegral_mono_set hint.integrableOn (ae_of_all _ fun u => hnn u)
    (Ioc_subset_Ioi_self.eventuallyLE)

theorem integral_Ioi_saphi_sub (b x : ℝ) : ∫ u in Ioi x, saphi (u - b) = saPhib (x - b) := by
  rw [saPhib_eq_integral, integral_Ioi_shift saphi (x - b), integral_Ioi_shift _ x]
  congr 1; funext r; congr 1; ring

theorem hasDerivAt_quad (a x : ℝ) : HasDerivAt (fun v : ℝ => v - 2 * a * v ^ 2) (1 - 4 * a * x) x := by
  have := (hasDerivAt_id x).sub ((hasDerivAt_pow 2 x).const_mul (2 * a))
  have e : (fun v : ℝ => v - 2 * a * v ^ 2) = id - fun y => 2 * a * y ^ 2 := by
    funext v; simp
  rw [e]; exact this.congr_deriv (by norm_num; ring)

theorem hasDerivAt_quad' (a x : ℝ) : HasDerivAt (fun v : ℝ => v + 2 * a * v ^ 2) (1 + 4 * a * x) x := by
  have := (hasDerivAt_id x).add ((hasDerivAt_pow 2 x).const_mul (2 * a))
  have e : (fun v : ℝ => v + 2 * a * v ^ 2) = id + fun y => 2 * a * y ^ 2 := by
    funext v; simp
  rw [e]; exact this.congr_deriv (by norm_num; ring)

theorem intervalIntegrable_perturb {a V : ℝ} {E : ℝ → ℝ} (hE : Measurable E)
    (hEb : ∀ v ∈ Icc 0 V, |E v| ≤ a * (1 + v ^ 3)) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ V) (ha : 0 ≤ a) :
    IntervalIntegrable (fun v => saphi v * Real.exp (E v)) volume x y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
  refine Measure.integrableOn_of_bounded (M := (√(2 * π))⁻¹ * Real.exp (a * (1 + V ^ 3)))
    (by simp) ?_ ?_
  · exact (continuous_saphi.measurable.mul (Real.measurable_exp.comp hE)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun v hv => ?_)
    have hv0 : 0 ≤ v := hx.trans hv.1
    have hvV : v ≤ V := hv.2.trans hy
    have h1 := hEb v ⟨hv0, hvV⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (saphi_pos v).le (Real.exp_pos _).le)]
    have h2 : E v ≤ a * (1 + V ^ 3) := by
      have := (le_abs_self (E v)).trans h1
      have h3 : v ^ 3 ≤ V ^ 3 := pow_le_pow_left₀ hv0 hvV 3
      nlinarith
    calc saphi v * Real.exp (E v) ≤ (√(2 * π))⁻¹ * Real.exp (a * (1 + V ^ 3)) := by
          gcongr
          · exact saphi_le v
      _ = _ := rfl

/-- Perturbed Gaussian tails(i). -/
theorem perturb_upper {a V : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 100) (haV : a * V ≤ 1 / 100)
    {E : ℝ → ℝ} (hE : Measurable E) (hEb : ∀ v ∈ Icc 0 V, |E v| ≤ a * (1 + v ^ 3))
    {v0 : ℝ} (hv0 : v0 ∈ Icc 0 V) :
    ∫ v in v0..V, saphi v * Real.exp (E v) ≤ saPhib (v0 - 17 * a * (1 + v0 ^ 2)) := by
  obtain ⟨h0, hV⟩ := hv0
  have hV0 : 0 ≤ V := h0.trans hV
  set b : ℝ := 41 / 5 * a with hb
  set w : ℝ → ℝ := fun v => v - 2 * a * v ^ 2 with hw
  set g : ℝ → ℝ := fun u => saphi u * Real.exp (b * u) with hg
  have hgc : Continuous g := by
    simp only [hg]; exact continuous_saphi.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hwc : Continuous w := by simp only [hw]; fun_prop
  have hav : ∀ v ∈ Icc v0 V, a * v ≤ 1 / 100 := fun v hv =>
    le_trans (mul_le_mul_of_nonneg_left hv.2 ha.le) haV
  -- Step 1
  have step1 : ∫ v in v0..V, saphi v * Real.exp (E v) ≤
      ∫ v in v0..V, Real.exp a * ((g ∘ w) v * (1 - 4 * a * v)) := by
    refine intervalIntegral.integral_mono_on hV (intervalIntegrable_perturb hE hEb h0 hV le_rfl ha.le)
      ?_ fun v hv => ?_
    · apply Continuous.intervalIntegrable
      simp only [Function.comp, hg]
      have := hwc
      fun_prop
    · have hv0' : 0 ≤ v := h0.trans hv.1
      have h1 := hEb v ⟨hv0', hv.2⟩
      have h2 : E v ≤ a * (1 + v ^ 3) := (le_abs_self _).trans h1
      have h3 := perturb_pointwise_upper ha.le hv0' (hav v hv)
      calc saphi v * Real.exp (E v) ≤ saphi v * Real.exp (a * (1 + v ^ 3)) := by
            have := saphi_pos v
            gcongr
        _ ≤ _ := h3
  have step2 : ∫ v in v0..V, Real.exp a * ((g ∘ w) v * (1 - 4 * a * v)) =
      Real.exp a * ∫ u in w v0..w V, g u := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_comp_mul_deriv (f := w) (f' := fun x => 1 - 4 * a * x) ?_ ?_ hgc
    · intro x _; exact hasDerivAt_quad a x
    · exact (by fun_prop : Continuous fun x : ℝ => 1 - 4 * a * x).continuousOn
  have hwmono : w v0 ≤ w V := by
    simp only [hw]; nlinarith [mul_nonneg ha.le (sub_nonneg.2 hV), mul_nonneg ha.le h0]
  have hgform : ∀ u, g u = Real.exp (b ^ 2 / 2) * saphi (u - b) := by
    intro u
    simp only [hg]
    have := saphi_add u (-b)
    rw [← sub_eq_add_neg] at this
    have e : Real.exp (b * u) =
        Real.exp (b ^ 2 / 2) * Real.exp (-(u * -b) - (-b) ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this, e]; ring
  have step3 : ∫ u in w v0..w V, g u ≤ Real.exp (b ^ 2 / 2) * saPhib (w v0 - b) := by
    have hint : Integrable g := by
      have : g = fun u => Real.exp (b ^ 2 / 2) * saphi (u - b) := funext hgform
      rw [this]; exact (integrable_saphi.comp_sub_right b).const_mul _
    refine (integral_Ioc_le_Ioi hint (fun x => ?_) hwmono).trans ?_
    · rw [hgform]; exact mul_nonneg (Real.exp_pos _).le (saphi_pos _).le
    · have : (fun u => g u) = fun u => Real.exp (b ^ 2 / 2) * saphi (u - b) := funext hgform
      simp only [this]
      rw [integral_const_mul, integral_Ioi_saphi_sub]
  -- conclusion
  have hwv0 : 0 ≤ w v0 := by simp only [hw]; nlinarith [mul_nonneg ha.le h0, mul_nonneg ha.le (mul_nonneg ha.le h0)]
  have hexp : Real.exp a * Real.exp (b ^ 2 / 2) ≤ Real.exp (6 * (7 / 5 * a) / 6) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    simp only [hb]; nlinarith
  have hPb := saPhib_nonneg (w v0 - b)
  have hshift := exp_mul_saPhib_le (t := w v0 - b) (c := 7 / 5 * a) (by simp only [hb]; linarith)
    (by positivity) (by linarith)
  have hexp2 : Real.exp a * Real.exp (b ^ 2 / 2) ≤ Real.exp (7 / 5 * a) := by
    refine hexp.trans (le_of_eq ?_); congr 1; ring
  calc ∫ v in v0..V, saphi v * Real.exp (E v)
      ≤ Real.exp a * (Real.exp (b ^ 2 / 2) * saPhib (w v0 - b)) := by
        refine step1.trans ?_
        rw [step2]; gcongr
    _ = (Real.exp a * Real.exp (b ^ 2 / 2)) * saPhib (w v0 - b) := by ring
    _ ≤ Real.exp (7 / 5 * a) * saPhib (w v0 - b) := by gcongr
    _ ≤ saPhib (w v0 - b - 6 * (7 / 5 * a)) := hshift
    _ ≤ saPhib (v0 - 17 * a * (1 + v0 ^ 2)) := by
        apply saPhib_antitone
        simp only [hw, hb]; nlinarith [mul_nonneg ha.le (sq_nonneg v0)]

/-- Perturbed Gaussian tails(ii). -/
theorem perturb_lower {a V : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 100) (_haV : a * V ≤ 1 / 100)
    {E : ℝ → ℝ} (hE : Measurable E) (hEb : ∀ v ∈ Icc 0 V, |E v| ≤ a * (1 + v ^ 3))
    {v0 : ℝ} (hv0 : v0 ∈ Icc 0 V) :
    saPhib (v0 + 10 * a * (1 + v0 ^ 2)) - saPhib V ≤ ∫ v in v0..V, saphi v * Real.exp (E v) := by
  obtain ⟨h0, hV⟩ := hv0
  have hV0 : 0 ≤ V := h0.trans hV
  set w : ℝ → ℝ := fun v => v + 2 * a * v ^ 2 with hw
  set g : ℝ → ℝ := fun u => saphi u * Real.exp (-(4 * a) * u) with hg
  have hgc : Continuous g := by
    simp only [hg]; exact continuous_saphi.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hwc : Continuous w := by simp only [hw]; fun_prop
  -- Step 1
  have step1 : ∫ v in v0..V, Real.exp (-a) * ((g ∘ w) v * (1 + 4 * a * v)) ≤
      ∫ v in v0..V, saphi v * Real.exp (E v) := by
    refine intervalIntegral.integral_mono_on hV ?_
      (intervalIntegrable_perturb hE hEb h0 hV le_rfl ha.le) fun v hv => ?_
    · apply Continuous.intervalIntegrable
      simp only [Function.comp, hg]
      have := hwc
      fun_prop
    · have hv0' : 0 ≤ v := h0.trans hv.1
      have h1 := hEb v ⟨hv0', hv.2⟩
      have h2 : -(a * (1 + v ^ 3)) ≤ E v := by have := neg_abs_le (E v); linarith
      have h3 := perturb_pointwise_lower ha.le hv0'
      calc _ ≤ saphi v * Real.exp (-(a * (1 + v ^ 3))) := h3
        _ ≤ saphi v * Real.exp (E v) := by
          have := saphi_pos v
          gcongr
  have step2 : ∫ v in v0..V, Real.exp (-a) * ((g ∘ w) v * (1 + 4 * a * v)) =
      Real.exp (-a) * ∫ u in w v0..w V, g u := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_comp_mul_deriv (f := w) (f' := fun x => 1 + 4 * a * x) ?_ ?_ hgc
    · intro x _; exact hasDerivAt_quad' a x
    · exact (by fun_prop : Continuous fun x : ℝ => 1 + 4 * a * x).continuousOn
  have hwmono : w v0 ≤ w V := by
    simp only [hw]; nlinarith [mul_nonneg ha.le (sub_nonneg.2 hV), mul_nonneg ha.le h0]
  have step3 : ∫ u in w v0..w V, saphi (u + 4 * a) ≤ ∫ u in w v0..w V, g u := by
    refine intervalIntegral.integral_mono_on hwmono
      (integrable_saphi.comp_add_right (4 * a)).intervalIntegrable
      (hgc.intervalIntegrable _ _) fun u _ => ?_
    simp only [hg]
    rw [saphi_add]
    have := saphi_pos u
    gcongr
    nlinarith [sq_nonneg (4 * a)]
  have step4 : ∫ u in w v0..w V, saphi (u + 4 * a) = saPhib (w v0 + 4 * a) - saPhib (w V + 4 * a) := by
    rw [intervalIntegral.integral_comp_add_right (fun x => saphi x) (4 * a)]
    exact (saPhib_sub (by linarith)).symm
  have hwv0 : 0 ≤ w v0 := by simp only [hw]; nlinarith [mul_nonneg ha.le h0, mul_nonneg ha.le (mul_nonneg ha.le h0)]
  have hVw : V ≤ w V + 4 * a := by simp only [hw]; nlinarith [mul_nonneg ha.le (sq_nonneg V)]
  have hshift := exp_neg_mul_saPhib_ge (t := w v0 + 4 * a) (c := a) (by linarith) ha.le (by linarith)
  have hA : saPhib (w V + 4 * a) ≤ saPhib V := saPhib_antitone hVw
  have hea : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hP := saPhib_nonneg (w V + 4 * a)
  have hlast : saPhib (v0 + 10 * a * (1 + v0 ^ 2)) ≤ saPhib (w v0 + 4 * a + 6 * a) := by
    apply saPhib_antitone
    simp only [hw]; nlinarith [mul_nonneg ha.le (sq_nonneg v0)]
  calc saPhib (v0 + 10 * a * (1 + v0 ^ 2)) - saPhib V
      ≤ Real.exp (-a) * saPhib (w v0 + 4 * a) - saPhib V := by linarith
    _ ≤ Real.exp (-a) * (saPhib (w v0 + 4 * a) - saPhib (w V + 4 * a)) := by nlinarith
    _ = Real.exp (-a) * ∫ u in w v0..w V, saphi (u + 4 * a) := by rw [step4]
    _ ≤ Real.exp (-a) * ∫ u in w v0..w V, g u := by gcongr
    _ = _ := step2.symm
    _ ≤ _ := step1

end StrongApprox
end ElboimSly
