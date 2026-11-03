/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Gaussian
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Absorbing a factor into a shift

Absorbing a factor into a shift (Part I).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal Real

namespace ElboimSly
namespace StrongApprox

theorem exp_half_le : Real.exp (1 / 2) ≤ 17 / 10 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  nlinarith

theorem sqrt_two_pi_le : √(2 * π) ≤ 251 / 100 := by
  have := Real.pi_lt_d2
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith

/-- A crude lower bound for the Gaussian density on `[-1, 1]`. -/
theorem one_fifth_le_saphi {u : ℝ} (hu : |u| ≤ 1) : 1 / 5 ≤ saphi u := by
  rw [saphi_eq]
  have h1 : Real.exp (-(1 / 2)) ≤ Real.exp (-(u ^ 2) / 2) := by
    apply Real.exp_le_exp.2
    have : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
    linarith
  have h2 : 10 / 17 ≤ Real.exp (-(1 / 2)) := by
    rw [Real.exp_neg]
    have := exp_half_le
    have h3 := Real.exp_pos (1 / 2)
    rw [le_inv_comm₀ (by norm_num) h3]; simpa using this
  have h4 := sqrt_two_pi_le
  have h5 : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  rw [inv_mul_eq_div, le_div_iff₀ h5]
  nlinarith

theorem exp_neg_three_halves_ge : 2 / 9 ≤ Real.exp (-(3 / 2)) := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h3 : 0 < Real.exp (3 / 2) := Real.exp_pos _
  have h4 : Real.exp (3 / 2) ≤ 9 / 2 := by
    have : Real.exp 1 ^ 3 < (27183 / 10000) ^ 3 := by
      gcongr; linarith
    nlinarith
  rw [Real.exp_neg]
  rw [le_inv_comm₀ (by norm_num) h3]; simpa using h4

theorem saPhib_add_le_one_sub {t δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    saPhib (t + δ) ≤ (1 - δ / 6) * saPhib t := by
  have h1 := saPhib_sub (show t ≤ t + δ by linarith)
  have h2 : (t + δ - t) * saphi (t + δ) ≤ ∫ x in t..(t + δ), saphi x := by
    have := intervalIntegral.integral_mono_on (show t ≤ t + δ by linarith)
      (f := fun _ => saphi (t + δ)) (g := saphi) (by simp) integrable_saphi.intervalIntegrable
      (fun x hx => saphi_antitoneOn (show (0 : ℝ) ≤ x from le_trans ht0 hx.1)
        (show (0 : ℝ) ≤ t + δ by linarith) hx.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  -- φ(t+δ) ≥ e^{-3/2} φ(t)
  have h3 : Real.exp (-(3 / 2)) * saphi t ≤ saphi (t + δ) := by
    rw [saphi_add]
    have : Real.exp (-(3 / 2)) ≤ Real.exp (-(t * δ) - δ ^ 2 / 2) :=
      Real.exp_le_exp.2 (by nlinarith)
    have := saphi_pos t
    nlinarith
  -- φ(t) ≥ 2 Φ̄(t) / √(2π)
  have h4 : 2 * saPhib t ≤ √(2 * π) * saphi t := by
    have := saPhib_le_half_exp ht0
    rw [saphi_eq]
    have h5 : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
    rw [← mul_assoc, mul_inv_cancel₀ h5.ne']
    linarith
  have h5 := sqrt_two_pi_le
  have h6 := exp_neg_three_halves_ge
  have h7 := saPhib_nonneg t
  have h8 := saphi_pos t
  have h9 : 0 ≤ saPhib (t + δ) := saPhib_nonneg _
  -- δ/6 * Φ̄(t) ≤ δ e^{-3/2} φ(t)
  have h10 : δ / 6 * saPhib t ≤ δ * (Real.exp (-(3 / 2)) * saphi t) := by
    have : saPhib t ≤ √(2 * π) * saphi t / 2 := by linarith
    have h11 : √(2 * π) / 2 / 6 ≤ Real.exp (-(3 / 2)) := by linarith
    calc δ / 6 * saPhib t ≤ δ / 6 * (√(2 * π) * saphi t / 2) := by gcongr
      _ = δ * ((√(2 * π) / 2 / 6) * saphi t) := by ring
      _ ≤ δ * (Real.exp (-(3 / 2)) * saphi t) := by gcongr
  have h12 : δ * saphi (t + δ) ≤ ∫ x in t..(t + δ), saphi x := by
    have : t + δ - t = δ := by ring
    rwa [this] at h2
  have h13 : δ * (Real.exp (-(3 / 2)) * saphi t) ≤ δ * saphi (t + δ) := by gcongr
  nlinarith

theorem saPhib_add_le_exp_of_one_le {t δ : ℝ} (ht : 1 ≤ t) (hδ0 : 0 ≤ δ) :
    saPhib (t + δ) ≤ Real.exp (-δ) * saPhib t := by
  rw [saPhib_eq_integral, saPhib_eq_integral, integral_Ioi_shift saphi (t + δ),
    integral_Ioi_shift saphi t, ← integral_const_mul]
  refine setIntegral_mono_on (integrable_saphi.comp_add_right _).integrableOn
    ((integrable_saphi.comp_add_right t).const_mul _).integrableOn measurableSet_Ioi
    fun r hr => ?_
  simp only [mem_Ioi] at hr
  have : r + (t + δ) = (r + t) + δ := by ring
  rw [this, saphi_add]
  have := saphi_pos (r + t)
  have h2 : Real.exp (-((r + t) * δ) - δ ^ 2 / 2) ≤ Real.exp (-δ) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg δ])
  rw [mul_comm (Real.exp (-δ))]
  gcongr

/-- Absorbing a factor into a shift(a). -/
theorem saPhib_add_le {t δ : ℝ} (ht : 0 ≤ t) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    saPhib (t + δ) ≤ Real.exp (-δ / 6) * saPhib t := by
  have hb := saPhib_nonneg t
  rcases le_total 1 t with h | h
  · refine (saPhib_add_le_exp_of_one_le h hδ0).trans ?_
    gcongr
    linarith
  · refine (saPhib_add_le_one_sub ht h hδ0 hδ1).trans ?_
    have := Real.add_one_le_exp (-δ / 6)
    have : 1 - δ / 6 ≤ Real.exp (-δ / 6) := by linarith
    gcongr

/-- Absorbing a factor into a shift(b). -/
theorem exp_neg_mul_saPhib_ge {t c : ℝ} (ht : 0 ≤ t) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 6) :
    saPhib (t + 6 * c) ≤ Real.exp (-c) * saPhib t := by
  have := saPhib_add_le ht (show 0 ≤ 6 * c by linarith) (by linarith)
  have e : -(6 * c) / 6 = -c := by ring
  rwa [e] at this

/-- Absorbing a factor into a shift(c). -/
theorem exp_mul_saPhib_le {t c : ℝ} (ht : -(1 / 4) ≤ t) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 8) :
    Real.exp c * saPhib t ≤ saPhib (t - 6 * c) := by
  rcases le_total (6 * c) t with h | h
  · have := saPhib_add_le (t := t - 6 * c) (δ := 6 * c) (by linarith) (by linarith) (by linarith)
    have e : -(6 * c) / 6 = -c := by ring
    rw [e, sub_add_cancel] at this
    have h2 : 0 < Real.exp c := Real.exp_pos c
    have h3 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp c * saPhib t ≤ Real.exp c * (Real.exp (-c) * saPhib (t - 6 * c)) := by gcongr
      _ = saPhib (t - 6 * c) := by rw [← mul_assoc, h3, one_mul]
  · -- small `t`
    have h1 := saPhib_sub (show t - 6 * c ≤ t by linarith)
    have h2 : (t - (t - 6 * c)) * (1 / 5) ≤ ∫ x in (t - 6 * c)..t, saphi x := by
      have := intervalIntegral.integral_mono_on (show t - 6 * c ≤ t by linarith)
        (f := fun _ => (1 / 5 : ℝ)) (g := saphi) (by simp) integrable_saphi.intervalIntegrable
        (fun x hx => one_fifth_le_saphi (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]))
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      exact this
    have h3 : Real.exp c - 1 ≤ c * Real.exp c := by
      have := Real.add_one_le_exp (-c)
      have h4 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
      have h5 := Real.exp_pos c
      nlinarith
    have h6 : Real.exp c ≤ 6 / 5 := by
      rcases hc0.eq_or_lt with rfl | hcp
      · norm_num
      have := Real.exp_bound_div_one_sub_of_interval' (x := c) hcp (by linarith)
      refine this.le.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h7 := saPhib_le_one t
    have h8 := saPhib_nonneg t
    have h9 : (Real.exp c - 1) * saPhib t ≤ Real.exp c - 1 := by
      have : 0 ≤ Real.exp c - 1 := by linarith [Real.add_one_le_exp c]
      nlinarith
    nlinarith

end StrongApprox
end ElboimSly
