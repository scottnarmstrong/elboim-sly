/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.MomentsCanon
public import Mathlib

/-!
# Moments and exponential moments of an SRW

Moments and exponential moments.  For every SRW `X` in dimension `d`, `t ≥ 0` and `θ ∈ ℝ^d`,
`E exp ⟨θ, X(t)⟩ = exp (2t ∑ᵢ (cosh θᵢ - 1))`, `E Xᵢ(t) = 0` and `E Xᵢ(t) Xⱼ(t) = 2t δᵢⱼ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

theorem measurable_eval_real (t : ℝ≥0) (i : Fin d) :
    Measurable fun γ : PathSpace d => (γ t i : ℝ) :=
  (Measurable.of_discrete (f := fun n : ℤ => (n : ℝ))).comp
    ((measurable_pi_apply i).comp (measurable_pi_apply t))

/-- Moments and exponential moments: the exponential moment. -/
theorem IsSRW.integral_exp_inner (hZ : IsSRW P Z) (t : ℝ≥0) (θ : Fin d → ℝ) :
    ∫ ω, Real.exp (∑ i, θ i * (Z ω t i : ℝ)) ∂P =
      Real.exp (2 * t * ∑ i, (Real.cosh (θ i) - 1)) := by
  obtain ⟨Ω', _, P', N', hN', hE⟩ := hZ.exists_canonical_integral
  rw [hE (fun γ => Real.exp (∑ i, θ i * (γ t i : ℝ)))
    (Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
      (measurable_eval_real t i).const_mul _))]
  exact integral_exp_inner_canonical hN' t.2 θ

/-- Moments and exponential moments: `E X_i(t) = 0`. -/
theorem IsSRW.integral_eval (hZ : IsSRW P Z) (t : ℝ≥0) (i : Fin d) :
    ∫ ω, (Z ω t i : ℝ) ∂P = 0 := by
  obtain ⟨Ω', _, P', N', hN', hE⟩ := hZ.exists_canonical_integral
  rw [hE (fun γ => (γ t i : ℝ)) (measurable_eval_real t i)]
  exact integral_walk_canonical hN' t.2 i

/-- Moments and exponential moments: `E X_i(t) X_j(t) = 2 t δ_ij`. -/
theorem IsSRW.integral_eval_mul (hZ : IsSRW P Z) (t : ℝ≥0) (i j : Fin d) :
    ∫ ω, (Z ω t i : ℝ) * (Z ω t j : ℝ) ∂P = if i = j then 2 * (t : ℝ) else 0 := by
  obtain ⟨Ω', _, P', N', hN', hE⟩ := hZ.exists_canonical_integral
  rw [hE (fun γ => (γ t i : ℝ) * (γ t j : ℝ))
    ((measurable_eval_real t i).mul (measurable_eval_real t j))]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    have := integral_walk_sq_canonical hN' t.2 i
    simpa [pow_two, canonical] using this
  · simp only [hij, ite_false]
    exact integral_walk_mul_canonical hN' t.2 hij

end SRW
end ElboimSly
