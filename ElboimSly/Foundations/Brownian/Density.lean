/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Moments
import Mathlib

/-!
# Density bounds for Brownian motion

Density bounds.

* `bmDensity d t z = (2π t)^{-d/2} exp(-|z|²/(2t))`, the Gaussian density `p_t`;
* `IsStandardBrownianMotion.hasLaw_eval_density` and `bmDensity_le`: (a);
* `IsStandardBrownianMotion.measure_affine_le`: (b);
* `IsStandardBrownianMotion.measure_closedBall_le`: (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The Gaussian density `p_t(z) = (2π t)^{-d/2} exp(-|z|²/(2t))` on `ℝ^d`, `|z|` Euclidean. -/
noncomputable def bmDensity (d : ℕ) (t : ℝ≥0) (z : Fin d → ℝ) : ℝ :=
  (2 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(∑ i, z i ^ 2) / (2 * t))

lemma prod_gaussianPDFReal (t : ℝ≥0) (z : Fin d → ℝ) :
    ∏ i, gaussianPDFReal 0 t (z i) = bmDensity d t z := by
  unfold bmDensity gaussianPDFReal
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 1
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  · congr 1
    rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
    simp

lemma pi_gaussianReal_eq_withDensity (t : ℝ≥0) (ht : t ≠ 0) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 t) =
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun z => ENNReal.ofReal (∏ i, gaussianPDFReal 0 t (z i))) := by
  refine Measure.pi_eq (μ := fun _ : Fin d => gaussianReal 0 t) fun s hs => ?_
  have hpdf : ∀ i, Integrable (fun x : ℝ => (s i).indicator (gaussianPDFReal 0 t) x) volume :=
    fun i => (integrable_gaussianPDFReal 0 t).indicator (hs i)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have e : ∀ z : Fin d → ℝ, (Set.pi Set.univ s).indicator
      (fun z => ENNReal.ofReal (∏ i, gaussianPDFReal 0 t (z i))) z =
      ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 t) (z i)) := by
    intro z
    by_cases hz : z ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hz]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hz i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hz]
      have : ∃ i, z i ∉ s i := by
        by_contra hcon
        push Not at hcon
        exact hz fun i _ => hcon i
      obtain ⟨i, hi⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
      simp
  simp_rw [e]
  have hnn : ∀ z : Fin d → ℝ, 0 ≤ ∏ i, (s i).indicator (gaussianPDFReal 0 t) (z i) := fun z =>
    Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun x _ => gaussianPDFReal_nonneg 0 t x) _
  have hint : Integrable (fun z : Fin d → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 t) (z i))
      volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i x => (s i).indicator (gaussianPDFReal 0 t) x)
      (fun i => hpdf i)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  rw [volume_pi, integral_fintype_prod_eq_prod (μ := fun _ : Fin d => (volume : Measure ℝ))
    (fun i x => (s i).indicator (gaussianPDFReal 0 t) x), ENNReal.ofReal_prod_of_nonneg]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [gaussianReal_apply_eq_integral 0 ht, integral_indicator (hs i)]
  · intro i _
    exact integral_nonneg fun x => Set.indicator_nonneg (fun x _ => gaussianPDFReal_nonneg 0 t x) _

/-- Density bounds (a). For `t > 0`, `B(t)` has density `p_t` with respect to
Lebesgue measure. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.hasLaw_eval_density [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {t : ℝ≥0} (ht : t ≠ 0) :
    HasLaw (B t) ((volume : Measure (Fin d → ℝ)).withDensity
      (fun z => ENNReal.ofReal (bmDensity d t z))) P := by
  have := hB.hasLaw_eval t
  rw [pi_gaussianReal_eq_withDensity t ht] at this
  simpa only [prod_gaussianPDFReal] using this

/-- Density bounds (a), the pointwise bounds
`p_t(z) ≤ (2π t)^{-d/2} exp(-‖z‖²/(2t)) ≤ (2π t)^{-d/2}`. -/
lemma bmDensity_le (t : ℝ≥0) (z : Fin d → ℝ) :
    bmDensity d t z ≤ (2 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (2 * t)) := by
  unfold bmDensity
  gcongr
  have h := norm_pow_le_sum_abs_pow z (n := 2) (by norm_num)
  simp only [sq_abs] at h
  exact h

lemma bmDensity_le_const (t : ℝ≥0) (z : Fin d → ℝ) :
    bmDensity d t z ≤ (2 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
  refine (bmDensity_le t z).trans ?_
  have : Real.exp (-‖z‖ ^ 2 / (2 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ‖z‖]) (by positivity)
  have h0 : 0 ≤ (2 * Real.pi * t) ^ (-(d : ℝ) / 2) := by positivity
  nlinarith

/-- Density bounds (b). For `σ > 0`, `t ≠ 0` and measurable `A`:
`P(x + σ B(t) ∈ A) ≤ (2π σ² t)^{-d/2} Leb(A)`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.measure_affine_le [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {t : ℝ≥0} (ht : t ≠ 0)
    (x : Fin d → ℝ) {σ : ℝ} (hσ : 0 < σ) {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    P {ω | x + σ • B t ω ∈ A} ≤
      ENNReal.ofReal ((2 * Real.pi * (σ ^ 2 * t)) ^ (-(d : ℝ) / 2)) * volume A := by
  set S : Set (Fin d → ℝ) := {z | x + σ • z ∈ A} with hS
  have hSm : MeasurableSet S := by
    have : Measurable fun z : Fin d → ℝ => x + σ • z := by fun_prop
    exact this hA
  have hlaw := hB.hasLaw_eval_density ht
  have h1 : P {ω | x + σ • B t ω ∈ A} = (volume.withDensity
      (fun z => ENNReal.ofReal (bmDensity d t z))) S := by
    rw [← hlaw.map_eq, Measure.map_apply (hB.measurable t) hSm]; rfl
  have hvol : volume S = ENNReal.ofReal ((σ ^ d)⁻¹) * volume A := by
    have e : S = (fun z : Fin d → ℝ => σ • z) ⁻¹' ((fun y => x + y) ⁻¹' A) := rfl
    rw [e, Measure.addHaar_preimage_smul volume hσ.ne', measure_preimage_add]
    simp [abs_of_pos hσ]
  rw [h1, withDensity_apply _ hSm]
  calc ∫⁻ z in S, ENNReal.ofReal (bmDensity d t z)
      ≤ ∫⁻ _z in S, ENNReal.ofReal ((2 * Real.pi * t) ^ (-(d : ℝ) / 2)) :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (bmDensity_le_const t z)
    _ = ENNReal.ofReal ((2 * Real.pi * t) ^ (-(d : ℝ) / 2)) * volume S := by
        rw [setLIntegral_const]
    _ = _ := by
        rw [hvol, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        have ht0 : (0 : ℝ) < t := by positivity
        have e1 : (2 * Real.pi * (σ ^ 2 * t)) = (σ ^ 2) * (2 * Real.pi * t) := by ring
        have key : (σ ^ 2 * (2 * Real.pi * t)) ^ (-(d : ℝ) / 2) =
            (σ ^ d)⁻¹ * (2 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          congr 1
          rw [← Real.rpow_natCast σ 2, ← Real.rpow_mul hσ.le, ← Real.rpow_natCast σ d,
            ← Real.rpow_neg hσ.le]
          congr 1
          push_cast
          ring
        rw [e1, key]
        ring

/-- Density bounds (c). `P(‖x + σ B(t) - v‖ ≤ r) ≤ (2r)^d (2π σ² t)^{-d/2}`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.measure_closedBall_le [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {t : ℝ≥0} (ht : t ≠ 0)
    (x v : Fin d → ℝ) {σ : ℝ} (hσ : 0 < σ) {r : ℝ} (hr : 0 ≤ r) :
    P {ω | ‖x + σ • B t ω - v‖ ≤ r} ≤
      ENNReal.ofReal ((2 * r) ^ d * (2 * Real.pi * (σ ^ 2 * t)) ^ (-(d : ℝ) / 2)) := by
  have h := hB.measure_affine_le ht x hσ (A := Metric.closedBall v r) Metric.isClosed_closedBall.measurableSet
  have e : {ω | ‖x + σ • B t ω - v‖ ≤ r} = {ω | x + σ • B t ω ∈ Metric.closedBall v r} := by
    ext ω; simp [dist_eq_norm]
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Real.volume_pi_closedBall v hr, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  simp

end ElboimSly.Brownian
