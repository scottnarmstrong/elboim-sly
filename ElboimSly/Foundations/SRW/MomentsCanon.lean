/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Law1dFormula
public import ElboimSly.Foundations.SRW.PoissonTail
public import Mathlib

/-!
# Moments of the canonical walk at a fixed time

Moments and exponential moments, canonical walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

theorem hasLaw_cntN (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {t : ℝ} (ht : 0 ≤ t)
    (v : Dir d) : HasLaw (cntN N t v) (poissonMeasure t.toNNReal) P :=
  ⟨(measurable_cntN hN t v).aemeasurable, map_cntN hN ht v⟩

/-- The signed weight of the direction `v` against `θ`. -/
def dirWeight (θ : Fin d → ℝ) (v : Dir d) : ℝ := if v.2 then θ v.1 else -θ v.1

theorem inner_walk_ae (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (t : ℝ)
    (θ : Fin d → ℝ) :
    ∀ᵐ ω ∂P, ∑ i, θ i * (walk d (N ω) t i : ℝ) =
      ∑ v : Dir d, dirWeight θ v * (cntN N t v ω : ℝ) := by
  filter_upwards [ae_good hN] with ω hω
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [walk_apply hω, Fintype.sum_bool]
  simp only [dirWeight, ite_true, Bool.false_eq_true, ite_false, cntN]
  push_cast
  ring

/-- Moments and exponential moments: the exponential moment of the canonical walk. -/
theorem integral_exp_inner_canonical (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    {t : ℝ} (ht : 0 ≤ t) (θ : Fin d → ℝ) :
    ∫ ω, Real.exp (∑ i, θ i * (walk d (N ω) t i : ℝ)) ∂P =
      Real.exp (2 * t * ∑ i, (Real.cosh (θ i) - 1)) := by
  have := hN.isProbabilityMeasure
  have h1 : ∫ ω, Real.exp (∑ i, θ i * (walk d (N ω) t i : ℝ)) ∂P =
      ∫ ω, Real.exp (1 * (∑ v : Dir d, fun ω => dirWeight θ v * (cntN N t v ω : ℝ)) ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [inner_walk_ae hN t θ] with ω hω
    rw [hω, one_mul, Finset.sum_apply]
  rw [h1]
  change mgf (∑ v : Dir d, fun ω => dirWeight θ v * (cntN N t v ω : ℝ)) P 1 = _
  have hindep : iIndepFun (fun v : Dir d => fun ω => dirWeight θ v * (cntN N t v ω : ℝ)) P :=
    (iIndepFun_cntN hN t).comp (fun v n => dirWeight θ v * (n : ℝ))
      (fun v => Measurable.of_discrete)
  rw [hindep.mgf_sum (fun v => (Measurable.of_discrete (f := fun n : ℕ => dirWeight θ v * (n : ℝ))).comp
    (measurable_cntN hN t v))]
  have hv : ∀ v : Dir d, mgf (fun ω => dirWeight θ v * (cntN N t v ω : ℝ)) P 1 =
      Real.exp (t * (Real.exp (dirWeight θ v) - 1)) := by
    intro v
    have := poisson_mgf_eq (hasLaw_cntN hN ht v) (dirWeight θ v)
    rw [Real.coe_toNNReal _ ht] at this
    rw [mgf]
    simp only [one_mul]
    convert this using 3
  simp_rw [hv]
  rw [← Real.exp_sum, Fintype.sum_prod_type]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp only [dirWeight, ite_true, Bool.false_eq_true, ite_false, Real.cosh_eq]
  ring_nf

section Poly

variable {P' : Measure Ω} {A B : Ω → ℕ} {r : ℝ≥0}

theorem aesm_nat (hA : HasLaw A (poissonMeasure r) P') :
    AEStronglyMeasurable (fun ω => (A ω : ℝ)) P' :=
  ((Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp_aemeasurable
    hA.aemeasurable).aestronglyMeasurable

theorem poisson_integrable_nat (hA : HasLaw A (poissonMeasure r) P') :
    Integrable (fun ω => (A ω : ℝ)) P' := by
  refine ((poisson_integrable_exp hA 1).mono (aesm_nat hA)
    (Filter.Eventually.of_forall fun ω => ?_))
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
  have := Real.add_one_le_exp (A ω : ℝ)
  linarith

theorem poisson_integrable_sq (hA : HasLaw A (poissonMeasure r) P') :
    Integrable (fun ω => (A ω : ℝ) ^ 2) P' := by
  have h := (poisson_integrable_exp hA 1).const_mul 2
  refine (h.mono ((aesm_nat hA).pow 2)
    (Filter.Eventually.of_forall fun ω => ?_))
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  have := Real.pow_div_factorial_le_exp (A ω : ℝ) (Nat.cast_nonneg _) 2
  simp only [Nat.factorial] at this
  norm_num at this
  linarith

theorem integral_sq_sub (hAl : HasLaw A (poissonMeasure r) P') (hBl : HasLaw B (poissonMeasure r) P')
    (hind : IndepFun A B P') :
    ∫ ω, ((A ω : ℝ) - (B ω : ℝ)) ^ 2 ∂P' = 2 * (r : ℝ) := by
  have hind' : IndepFun (fun ω => (A ω : ℝ)) (fun ω => (B ω : ℝ)) P' :=
    hind.comp (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ)))
      (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ)))
  have hAB : Integrable (fun ω => (A ω : ℝ) * (B ω : ℝ)) P' :=
    hind'.integrable_mul (poisson_integrable_nat hAl) (poisson_integrable_nat hBl)
  have h1 : ∫ ω, ((A ω : ℝ) - (B ω : ℝ)) ^ 2 ∂P' =
      ∫ ω, (((A ω : ℝ) ^ 2 - 2 * ((A ω : ℝ) * (B ω : ℝ))) + (B ω : ℝ) ^ 2) ∂P' := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  have hI0 : Integrable (fun ω => 2 * ((A ω : ℝ) * (B ω : ℝ))) P' := hAB.const_mul 2
  have hI1 : Integrable (fun ω => (A ω : ℝ) ^ 2 - 2 * ((A ω : ℝ) * (B ω : ℝ))) P' :=
    (poisson_integrable_sq hAl).sub hI0
  have hI2 : Integrable (fun ω => (B ω : ℝ) ^ 2) P' := poisson_integrable_sq hBl
  rw [h1, integral_add hI1 hI2,
    integral_sub (poisson_integrable_sq hAl) hI0, integral_const_mul,
    hind'.integral_fun_mul_eq_mul_integral (aesm_nat hAl) (aesm_nat hBl),
    poisson_second hAl, poisson_second hBl, poisson_mean hAl, poisson_mean hBl]
  ring

end Poly

theorem integral_walk_canonical (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    {t : ℝ} (ht : 0 ≤ t) (i : Fin d) : ∫ ω, (walk d (N ω) t i : ℝ) ∂P = 0 := by
  have := hN.isProbabilityMeasure
  have h1 : ∫ ω, (walk d (N ω) t i : ℝ) ∂P =
      ∫ ω, ((cntN N t (i, true) ω : ℝ) - cntN N t (i, false) ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [ae_good hN] with ω hω
    rw [walk_apply hω]; push_cast; rfl
  rw [h1, integral_sub (poisson_integrable_nat (hasLaw_cntN hN ht _))
    (poisson_integrable_nat (hasLaw_cntN hN ht _)), poisson_mean (hasLaw_cntN hN ht _),
    poisson_mean (hasLaw_cntN hN ht _), sub_self]

theorem integral_walk_sq_canonical (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    {t : ℝ} (ht : 0 ≤ t) (i : Fin d) : ∫ ω, (walk d (N ω) t i : ℝ) ^ 2 ∂P = 2 * t := by
  have := hN.isProbabilityMeasure
  have h1 : ∫ ω, (walk d (N ω) t i : ℝ) ^ 2 ∂P =
      ∫ ω, ((cntN N t (i, true) ω : ℝ) - cntN N t (i, false) ω) ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [ae_good hN] with ω hω
    rw [walk_apply hω]; push_cast; rfl
  rw [h1, integral_sq_sub (hasLaw_cntN hN ht (i, true)) (hasLaw_cntN hN ht (i, false))
    ((iIndepFun_cntN hN t).indepFun (by simp)), Real.coe_toNNReal _ ht]

theorem integral_walk_mul_canonical (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    {t : ℝ} (ht : 0 ≤ t) {i j : Fin d} (hij : i ≠ j) :
    ∫ ω, (walk d (N ω) t i : ℝ) * (walk d (N ω) t j : ℝ) ∂P = 0 := by
  have := hN.isProbabilityMeasure
  have hind : IndepFun (fun ω => (coordY N t i ω : ℝ)) (fun ω => (coordY N t j ω : ℝ)) P :=
    ((iIndepFun_coordY hN t).indepFun hij).comp
      (Measurable.of_discrete (f := fun n : ℤ => (n : ℝ)))
      (Measurable.of_discrete (f := fun n : ℤ => (n : ℝ)))
  have hm : ∀ k, AEStronglyMeasurable (fun ω => (coordY N t k ω : ℝ)) P := fun k =>
    ((Measurable.of_discrete (f := fun n : ℤ => (n : ℝ))).comp
      (measurable_coordY hN t k)).aestronglyMeasurable
  have h1 : ∫ ω, (walk d (N ω) t i : ℝ) * (walk d (N ω) t j : ℝ) ∂P =
      ∫ ω, (coordY N t i ω : ℝ) * (coordY N t j ω : ℝ) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [walk_ae_eq hN t] with ω hω
    rw [hω i, hω j]
  have h0 : ∀ k, ∫ ω, (coordY N t k ω : ℝ) ∂P = 0 := by
    intro k
    rw [← integral_walk_canonical hN ht k]
    refine integral_congr_ae ?_
    filter_upwards [walk_ae_eq hN t] with ω hω
    rw [hω k]
  rw [h1, hind.integral_fun_mul_eq_mul_integral (hm i) (hm j), h0, h0, mul_zero]


end SRW
end ElboimSly
