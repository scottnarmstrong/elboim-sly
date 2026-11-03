/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.WindowExit
public import Mathlib

/-!
# One window

One window.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

theorem kernel1_univ_eq (r : ℝ≥0) (a b : ℤ) :
    kernel1 univ r a b = (srwP 1).real {ω | srwZ 1 ω r 0 = b - a} := by
  unfold kernel1 kernel
  congr 2
  ext ω
  simp only [kerSet, mem_ofPred_eq, mem_univ, implies_true, and_true]
  constructor
  · intro h
    have := congrFun h 0
    simp only [Pi.add_apply] at this
    omega
  · intro h
    funext i
    rw [Subsingleton.elim i 0]
    simp only [Pi.add_apply]
    omega

theorem kernel1_univ_le {r : ℝ≥0} (hr : 1 ≤ (r : ℝ)) (a b : ℤ) :
    kernel1 univ r a b ≤ 1 / √(π * r) := by
  rw [kernel1_univ_eq]
  have hY := srwZ_isSRW 1
  have h := hY.prob_eq_le hr (fun _ => b - a)
  have e : {ω | srwZ 1 ω r = fun _ => b - a} = {ω | srwZ 1 ω r 0 = b - a} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext i; rw [Subsingleton.elim i 0]; exact h
  rw [e] at h
  have hpos : 0 < π * (r : ℝ) := by
    have : (0 : ℝ) < r := by linarith
    positivity
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity), ← Real_inv_sqrt_pow 1 hpos] at this
  simpa [Measure.real] using this

theorem pi_gt_div : (25 / 8 : ℝ) ≤ π := by linarith [Real.pi_gt_d2]

theorem kernel1_univ_le_window {ρ : ℝ≥0} (hρ : 2 ≤ (ρ : ℝ)) (a b : ℤ) :
    kernel1 univ (ρ / 2) a b ≤ 4 / (5 * √(ρ : ℝ)) := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hcast : ((ρ / 2 : ℝ≥0) : ℝ) = (ρ : ℝ) / 2 := by push_cast; ring
  refine (kernel1_univ_le (by rw [hcast]; linarith) a b).trans ?_
  rw [hcast]
  have hs : 0 < √(ρ : ℝ) := Real.sqrt_pos.2 hρ0
  have hsq : √(ρ : ℝ) ^ 2 = ρ := Real.sq_sqrt hρ0.le
  have h1 : 5 * √(ρ : ℝ) / 4 ≤ √(π * ((ρ : ℝ) / 2)) := by
    refine Real.le_sqrt_of_sq_le ?_
    have := pi_gt_div
    nlinarith
  rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) h1) (by positivity)]
  nlinarith

/-- One window: one window. -/
theorem window {ρ : ℝ≥0} (hρ : 2 ≤ (ρ : ℝ)) {δ : ℤ} (hδ : |(δ : ℝ)| ≤ √(ρ : ℝ)) {ℓ : ℤ}
    (hℓ : 16 * √(ρ : ℝ) ≤ ℓ) :
    Real.exp (-4) / (5 * √(ρ : ℝ)) ≤ kernel1 (Icc (-ℓ) ℓ) ρ 0 δ := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hs : 0 < √(ρ : ℝ) := Real.sqrt_pos.2 hρ0
  set J : Set ℤ := Icc (-ℓ) ℓ with hJ
  have hrr : ρ = ρ / 2 + ρ / 2 := (add_halves ρ).symm
  set r : ℝ≥0 := ρ / 2 with hr
  have hM : ∀ a b, kernel1 univ r a b ≤ 4 / (5 * √(ρ : ℝ)) := fun a b =>
    kernel1_univ_le_window hρ a b
  set M := 4 / (5 * √(ρ : ℝ)) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hpq : ∀ a b, kernel1 J r a b ≤ kernel1 univ r a b := fun a b =>
    kernel1_mono (subset_univ _) r a b
  have hq0 := kernel1_nonneg J r
  have hsump : ∀ a, HasSum (fun b => kernel1 univ r a b) 1 := by
    intro a
    have h1 := kernel1_tsum univ r a
    have : {ω | ∀ s : ℝ≥0, s ≤ r → a + srwZ 1 ω s 0 ∈ (univ : Set ℤ)} = univ := by
      ext ω; simp
    rw [this] at h1
    have := (srwZ_isSRW 1).isProbabilityMeasure
    simp only [measure_univ, ENNReal.toReal_one] at h1
    rw [← h1]
    exact (summable_kernel1 univ r a).hasSum
  -- exit bound
  have hexit : ∀ x : ℤ, |(x : ℝ)| ≤ √(ρ : ℝ) →
      ∑' b, (kernel1 univ r x b - kernel1 J r x b) ≤ 4 * Real.exp (-10) := by
    intro x hx
    rw [(summable_kernel1 univ r x).tsum_sub (summable_kernel1 J r x), (hsump x).tsum_eq]
    exact exit_mass hρ hℓ hx
  have hex0 : ∀ x : ℤ, |(x : ℝ)| ≤ √(ρ : ℝ) →
      Summable fun b => kernel1 univ r x b - kernel1 J r x b := fun x _ =>
    (summable_kernel1 univ r x).sub (summable_kernel1 J r x)
  have h0 : |((0 : ℤ) : ℝ)| ≤ √(ρ : ℝ) := by simp
  -- Chapman-Kolmogorov
  have hCKp : kernel1 univ ρ 0 δ = ∑' w, kernel1 univ r 0 w * kernel1 univ r w δ := by
    conv_lhs => rw [hrr]
    exact kernel1_add univ r r 0 δ
  have hCKq : kernel1 J ρ 0 δ = ∑' w, kernel1 J r 0 w * kernel1 J r w δ := by
    conv_lhs => rw [hrr]
    exact kernel1_add J r r 0 δ
  have hdiff : kernel1 univ ρ 0 δ - kernel1 J ρ 0 δ ≤ M * (2 * (4 * Real.exp (-10))) := by
    rw [hCKp, hCKq, ← (summable_kernel1_mul univ r r 0 δ).tsum_sub
      (summable_kernel1_mul J r r 0 δ)]
    have hs1 := hex0 0 h0
    have hs2 := hex0 δ hδ
    have hterm : ∀ w, kernel1 univ r 0 w * kernel1 univ r w δ - kernel1 J r 0 w * kernel1 J r w δ ≤
        M * ((kernel1 univ r 0 w - kernel1 J r 0 w) + (kernel1 univ r δ w - kernel1 J r δ w)) := by
      intro w
      have e1 : kernel1 univ r w δ = kernel1 univ r δ w := kernel1_symm _ _ _ _
      have e2 : kernel1 J r w δ = kernel1 J r δ w := kernel1_symm _ _ _ _
      rw [e1, e2]
      have a1 := hM w δ
      have a2 := hM 0 w
      have a3 := hpq 0 w
      have a4 := hpq δ w
      have a5 := hq0 0 w
      have a6 := hq0 δ w
      have a7 := hM δ w
      nlinarith [mul_nonneg a5 (sub_nonneg.2 a4), mul_nonneg (sub_nonneg.2 a3) (sub_nonneg.2 a7),
        mul_nonneg (sub_nonneg.2 a4) (sub_nonneg.2 (a3.trans a2))]
    have hsumR : Summable fun w => M * ((kernel1 univ r 0 w - kernel1 J r 0 w) +
        (kernel1 univ r δ w - kernel1 J r δ w)) := (hs1.add hs2).mul_left M
    refine (((summable_kernel1_mul univ r r 0 δ).sub
      (summable_kernel1_mul J r r 0 δ)).tsum_le_tsum hterm hsumR).trans ?_
    rw [tsum_mul_left, hs1.tsum_add hs2]
    have := hexit 0 h0
    have := hexit δ hδ
    nlinarith
  have hlow := (srwZ_isSRW 1).local_lower (t := ρ) (by linarith) (k := δ) hδ
  have hpρ : kernel1 univ ρ 0 δ = (srwP 1).real {ω | srwZ 1 ω ρ 0 = δ} := by
    rw [kernel1_univ_eq]; simp
  rw [← hpρ] at hlow
  have hE : Real.exp (-10) ≤ Real.exp (-4) / 128 := by
    have h6 := exp_six_ge
    have : Real.exp (-10) = Real.exp (-4) * Real.exp (-6) := by rw [← Real.exp_add]; norm_num
    rw [this]
    have : Real.exp (-6) ≤ 1 / 128 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h6
    have := Real.exp_pos (-4)
    nlinarith
  have hX := Real.exp_pos (-4)
  have e1 : M * (2 * (4 * Real.exp (-10))) ≤ Real.exp (-4) / (20 * √(ρ : ℝ)) := by
    rw [hMdef]
    calc 4 / (5 * √(ρ : ℝ)) * (2 * (4 * Real.exp (-10)))
        ≤ 4 / (5 * √(ρ : ℝ)) * (2 * (4 * (Real.exp (-4) / 128))) := by gcongr
      _ = Real.exp (-4) / (20 * √(ρ : ℝ)) := by field_simp; ring
  have e2 : Real.exp (-4) / (4 * √(ρ : ℝ)) - Real.exp (-4) / (20 * √(ρ : ℝ)) =
      Real.exp (-4) / (5 * √(ρ : ℝ)) := by field_simp; ring
  linarith

end SRW
end ElboimSly
