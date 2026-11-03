/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.X1Explicit
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Provider for `X1ThetaCoupling`

Proof of the main theorem `ElboimSly.Frozen.Theorems.X1ThetaCoupling` (X1θ: strong approximation for bounded sign-symmetric vectors). The export is `ElboimSly.Provider.x1ThetaCoupling`; it is the explicit
version `ElboimSly.StrongApprox.x1_explicit` (X1θ with the explicit threshold ell_0(d)=max100,10d) with the
threshold `ℓ₀ = max (10^5) (10 d)`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ElboimSly.Provider

/-- X1θ: strong approximation for bounded sign-symmetric vectors. X1θ: strong approximation for bounded sign-symmetric vectors.
The norm on `Fin d → ℝ` is the sup norm (ℓ∞, D5). -/
theorem x1ThetaCoupling {d : ℕ} (_hd : 1 ≤ d := by assumption) :
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
  ⟨max (10 ^ 5) (10 * d), fun ℓ hℓ M hM1 hM μ hμ hsupp hsym hsq =>
    ElboimSly.StrongApprox.x1_explicit ℓ hℓ M hM1 hM μ hμ hsupp hsym hsq⟩

end ElboimSly.Provider

end
