/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lem71Det
public import ElboimSly.Paper.Step.Lem71Num
public import ElboimSly.Paper.Step.ZetaCount2
public import ElboimSly.Paper.Step.FastLaw
public import ElboimSly.Paper.Step.CfAe
public import ElboimSly.Paper.Step.Cor72Proof
public import ElboimSly.Paper.Heavy.Scales
public import Mathlib

/-!
# Lemma 7.1 (the concatenation coupling)

ES22 Lemma 7.1 (§7).

`StepEs61 d c6 β6` is the conclusion of ES22 Theorem 6.1 for the relaxed sets of the driven walks
(isolated: Theorem 6.1 is proved in `wip/paper-heavy-2`, in the environment picture). The theorem
`stepLem71_of_es61` is conditional on it: it is **not** a proof of ES22 Lemma 7.1 until `StepEs61` is
discharged, and it never stands in for that result.

Proof structure (see the module docstrings of the `Zeta*` files):
Step 0-1 `ZetaSeq`, `ZetaSRW`, Step 2 `ZetaCouple`, Step 4 `ZetaCount2`, Step 5 `ZetaGap`/`FastLaw`,
Step 3/6 `ZetaDet`/`Lem71Det`, numerics `Lem71Num`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- The conclusion of ES22 Theorem 6.1 (isolated; see the module docstring): with probability at least
`1 - e^{-c₆ n³}` every window `[t, t + t_n^ε] ⊆ [0, t_n]` carries at least `(0.9 + 2/n) t_n^ε` of the
relaxed times of the driven regenerated walk `W_reg^{θ_a Y}`. -/
def StepEs61 (d : ℕ) (c6 : ℝ) (β6 : ℕ → ℝ) : Prop :=
  ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), β6 n₁ ≤ β →
    StepRegime d n₁ β n t₀ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → PathSpace d),
      IsSRW P Y → (∀ ω, Y ω ∈ StepPath d) → ∀ a : ℝ≥0,
        P.real {ω | ¬ WinOK (indScale t₀ n) (indScale t₀ n ^ heavyEps d) n
          (stepRelaxedSet β (stepWr β a Y ω) (stepAr β a Y ω))} ≤
          Real.exp (-(c6 * (n : ℝ) ^ 3))

end ElboimSly.Paper.Step
