/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Regime
public import ElboimSly.Frozen.Defs.AdmitsBMCoupling
public import ElboimSly.Frozen.Defs.IndThetaH
public import ElboimSly.Frozen.Defs.RegenWalk
public import Mathlib

/-!
# The statement of Lemma 7.6 (isolated)

ES22 Lemma 7.6 (§7). `StepBm d cBm βBm` is the conclusion of
Lemma 7.6 with constant `c_bm = cBm` and threshold `β_bm(n₁) = βBm n₁`: for `β ≥ β_bm(n₁)` and
`SR(n₁; β, n, t₀)`, the regenerated walk admits a `(σ, t_n^{θ_H})`-coupling up to time `t_n` with
failure probability `e^{-c_bm n³}`, for some `σ` with
`|σ - √2| ≤ max {3β^{-1/16} - t_n^{-1/16}, 0}`.

It is used as a hypothesis by the distinctly named conditional `step_lemma77_of_cor72_bm`
(Lemma 7.7); `Lemma76.lean` proves it from `StepCor72`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- The conclusion of Lemma 7.6 (ES22 Lemma 7.6). -/
def StepBm (d : ℕ) (cBm : ℝ) (βBm : ℕ → ℝ) : Prop :=
  ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βBm n₁ ≤ β →
    StepRegime d n₁ β n t₀ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)),
      IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P →
      ∃ σ : ℝ, |σ - Real.sqrt 2| ≤
          max (3 * β ^ (-(1 : ℝ) / 16) - indScale t₀ n ^ (-(1 : ℝ) / 16)) 0 ∧
        AdmitsBMCoupling d (indScale t₀ n).toNNReal
          (P.map (fun ω (t : Set.Icc (0 : ℝ≥0) (indScale t₀ n).toNNReal) =>
            regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)))
          σ (indScale t₀ n ^ indThetaH) (Real.exp (-(cBm * (n : ℝ) ^ 3)))

end ElboimSly.Paper.Step

end
