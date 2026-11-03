/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Giry
public import Mathlib

/-!
# Characteristic-function computations for the mixed binomial process

Mixed binomial process (analytic ingredients).

* `integral_poissonMeasure_pow`: `∫ zⁿ dPo(r) = exp (r (z - 1))`.
* `charFunDual_poisson_single`: the characteristic function of `Po(ℝ, r)` along a functional.
* `exp_indicator_sum`: `exp(i ∑ⱼ tⱼ 1_{Aⱼ}) = 1 + ∑ⱼ 1_{Aⱼ} (exp(i tⱼ) - 1)` for disjoint `Aⱼ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal Nat

namespace ElboimSly

theorem integral_poissonMeasure_pow (r : ℝ≥0) (z : ℂ) :
    ∫ n : ℕ, z ^ n ∂(poissonMeasure r) = cexp (r * (z - 1)) := by
  rw [integral_poissonMeasure]
  calc ∑' a : ℕ, (Real.exp (-r) * r ^ a / a ! : ℝ) • z ^ a
      = ∑' a : ℕ, (Real.exp (-r) : ℂ) * ((r * z) ^ a / a !) := by
        congr with a
        rw [Complex.real_smul]
        push_cast
        rw [mul_pow]
        ring
    _ = (Real.exp (-r) : ℂ) * ∑' a : ℕ, ((r * z) ^ a / a !) := tsum_mul_left
    _ = cexp (r * (z - 1)) := by
        rw [(NormedSpace.expSeries_div_hasSum_exp (r * z : ℂ)).tsum_eq, ← Complex.exp_eq_exp_ℂ,
          Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        ring

/-- A continuous linear functional on `ℝ` is multiplication by a constant. -/
theorem strongDual_real_apply (L : StrongDual ℝ ℝ) (x : ℝ) : L x = x * L 1 := by
  have : L x = L (x • (1 : ℝ)) := by simp
  rw [this, map_smul, smul_eq_mul]

theorem charFunDual_poisson_real (r : ℝ≥0) (L : StrongDual ℝ ℝ) :
    charFunDual ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) L =
      cexp (r * (cexp ((L 1 : ℝ) * I) - 1)) := by
  rw [← charFun_map_cast_poissonMeasure, charFunDual_apply, charFun_apply_real]
  congr 1
  ext x
  rw [strongDual_real_apply L x]
  push_cast
  ring_nf

/-- For disjoint `A j`, `exp(i ∑ⱼ tⱼ 1_{Aⱼ} y) = 1 + ∑ⱼ 1_{Aⱼ} y (exp(i tⱼ) - 1)`. -/
theorem exp_indicator_sum {S : Type*} {n : ℕ} (A : Fin n → Set S)
    (hd : Pairwise (Function.onFun Disjoint A)) (t : Fin n → ℝ) (y : S) :
    cexp ((∑ j, t j * (A j).indicator (fun _ => (1 : ℝ)) y : ℝ) * I) =
      1 + ∑ j, (A j).indicator (fun _ => (1 : ℂ)) y * (cexp (t j * I) - 1) := by
  by_cases h : ∃ j0, y ∈ A j0
  · obtain ⟨j0, hj0⟩ := h
    have hother : ∀ j, j ≠ j0 → y ∉ A j := fun j hj hy =>
      Set.disjoint_left.1 (hd hj) hy hj0
    rw [Finset.sum_eq_single j0, Finset.sum_eq_single j0]
    · simp [Set.indicator_of_mem hj0]
    · intro j _ hj
      simp [Set.indicator_of_notMem (hother j hj)]
    · simp
    · intro j _ hj
      simp [Set.indicator_of_notMem (hother j hj)]
    · simp
  · push Not at h
    simp [Set.indicator_of_notMem (h _)]

end ElboimSly
