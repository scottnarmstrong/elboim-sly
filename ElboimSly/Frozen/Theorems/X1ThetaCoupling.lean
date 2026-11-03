/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Provider.X1ThetaCoupling
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# X1ThetaCoupling

X1θ: strong approximation for bounded sign-symmetric vectors.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ElboimSly

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- X1θ: strong approximation for bounded sign-symmetric vectors. X1θ: strong approximation for bounded sign-symmetric vectors.
The norm on `Fin d → ℝ` is the sup norm (ℓ∞, D5). -/
theorem x1theta_coupling (d : ℕ) (hd : 1 ≤ d) :
    ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ M : ℝ, 1 ≤ M → M ≤ Real.log ℓ ^ 3 →
      ∀ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ →
        μ {x | ‖x‖ ≤ M} = 1 →
        (∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) → μ.map (fun x => ε * x) = μ) →
        (∀ k, ∫ x, x k ^ 2 ∂μ = 1) →
        ∃ Q : Measure ((Fin ℓ → Fin d → ℝ) × (Fin ℓ → Fin d → ℝ)), IsProbabilityMeasure Q ∧
          Q.map Prod.fst = Measure.pi (fun _ : Fin ℓ => μ) ∧
          Q.map Prod.snd = Measure.pi (fun _ : Fin ℓ =>
            Measure.pi (fun _ : Fin d => gaussianReal 0 1)) ∧
          Q.real {p | ∃ j : Fin ℓ,
              (ℓ : ℝ) ^ ((1 : ℝ) / 4) * Real.log ℓ ^ 12 ≤
                ‖∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - p.2 i)‖}
            ≤ Real.exp (-(Real.log ℓ ^ 3)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ElboimSly.Provider.x1ThetaCoupling
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ElboimSly

end
-- FROZEN_ANCHOR_SUFFIX_END
