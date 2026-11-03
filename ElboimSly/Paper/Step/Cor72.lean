/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.NaturalCoupling
public import ElboimSly.Paper.Step.Regime
public import ElboimSly.Paper.Step.Driven
public import ElboimSly.Paper.Heavy.Scales
public import ElboimSly.Foundations.SRW.SrwLaw
public import Mathlib

/-!
# The statement of Corollary 7.2 (isolated)

ES22 Corollary 7.2. `StepCor72 d cCat βCat` is the conclusion of Corollary 7.2, with constant
`c_cat = cCat` and threshold `β_cat(n₁) = βCat n₁`. It is **not** a proof of Corollary 7.2: it is
the hypothesis of the distinctly named conditional lemmas of the "travelling far" section
(ES22 Lemma 7.3, ES22 Lemma 7.4), to be discharged when ES22 Corollary 7.2 (which needs ES22 Theorem 6.1) lands.
-/

@[expose] public section

open MeasureTheory ElboimSly.SRW
open scoped NNReal

namespace ElboimSly.Paper

/-- The conclusion of ES22 Corollary 7.2 (isolated; see the module docstring). -/
def StepCor72 (d : ℕ) (cCat : ℝ) (βCat : ℕ → ℝ) : Prop :=
  ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βCat n₁ ≤ β →
    StepRegime d n₁ β n t₀ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → PathSpace d),
      IsSRW P Y → (∀ ω, Y ω ∈ StepPath d) →
      ∀ (a : ℝ≥0) (ℓ : ℕ) (s : ℕ → ℝ≥0), 1 ≤ ℓ → (∀ j, 0 < s j) →
        ((stepPartial s ℓ : ℝ≥0) : ℝ) ≤ indScale t₀ n →
        P.real {ω | ∃ u : ℝ≥0, u ≤ stepPartial s ℓ ∧
          (ℓ : ℝ) * indScale t₀ n ^ (2 * heavyEps d) ≤
            ‖stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s ℓ (Y ω) u‖} ≤
          ((ℓ : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3))

end ElboimSly.Paper
