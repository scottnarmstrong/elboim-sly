/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Regime
public import ElboimSly.Frozen.Defs.IndH5
public import Mathlib

/-!
# The statement of Lemma 7.8 (isolated)

ES22 Lemma 7.8 (§7), consumed by (H5) at level n.
`StepPp d cPp βPp` is the conclusion of Lemma 7.8 with constant `c_pp = cPp` and threshold
`β_pp(n₁) = βPp n₁`: for `β ≥ β_pp(n₁)`, `SR(n₁; β, n, t₀)`, `n ≥ 1/c_pp`, a Poisson point process
`N` of intensity `μ_β`, `u ∈ ℤ^d` and `q ∈ [0, β]`, the event
`Ω(0,u,0,q;t'_n) ∩ {|𝔓_n(0,u,0,q)| ≥ 3.9^n}` has probability at most `e^{-c_pp n³}`.
The event is written exactly as in the frozen `IndH5` (with `u₁ = 0`, `q₁ = 0`).
-/

@[expose] public section

open MeasureTheory

namespace ElboimSly.Paper.Step

/-- The conclusion of Lemma 7.8 (ES22 Lemma 7.8). -/
def StepPp (d : ℕ) (cPp : ℝ) (βPp : ℕ → ℝ) : Prop :=
  0 < cPp ∧ ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βPp n₁ ≤ β →
    StepRegime d n₁ β n t₀ → 1 / cPp ≤ (n : ℝ) →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
      IsPoissonPointProcess N (ringIntensity d β) P →
      ∀ (u : Fin d → ℤ) (q : ℝ), q ∈ Set.Icc 0 β →
        P {ω | cycOmega (N ω) 0 u 0 q (indScaleReduced t₀ n) ∧
            ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
              volume {s₂ : ℝ | s₂ ∈ Set.Icc 0 (indScaleReduced t₀ n) ∧
                ∃ s₁ ∈ Set.Icc 0 (indScaleReduced t₀ n),
                  ‖cycWalk (N ω) 0 0 s₁ - cycWalk (N ω) u q s₂‖ ≤ (19 / 10 : ℝ) ^ n}} ≤
          ENNReal.ofReal (Real.exp (-(cPp * (n : ℝ) ^ 3)))

end ElboimSly.Paper.Step

end
