/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.SecondMoment
public import ElboimSly.Paper.Step.RegenMeas
public import Mathlib

/-!
# Second moment of a truncated endpoint, unconditional

Second moment of a truncated endpoint. The measurability hypothesis of `step_second_moment_of_ae` is
discharged by `aemeasurable_regenWalk_Icc`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Second moment of a truncated endpoint (ES22 Lemmas 7.3 and 7.4). -/
theorem step_second_moment {n₁ n : ℕ} {t₀ : ℝ} (hR : StepRegime d n₁ β n t₀)
    (hβ : (12 : ℝ) ^ 16 ≤ β) {h : ℝ} (h1 : (4 : ℝ) ^ n₁ < h) (h2 : h ≤ 4 ^ n)
    {K : ℝ} (hK : 0 ≤ K)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β))
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    ∫⁻ ω, {ω | ⨆ r : Set.Icc (0 : ℝ) h,
        ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖ ≤ ENNReal.ofReal K}.indicator
      (fun ω => ENNReal.ofReal (‖regenWalk (fun k => copyEnv (N ω) k) h‖ ^ 2)) ω ∂P ≤
    ENNReal.ofReal (6 * d * h + 2 * h ^ (2 * indThetaH) +
      K ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2))) :=
  step_second_moment_of_ae hR hβ h1 h2 hK Ω P N hN (aemeasurable_regenWalk_Icc hN _)

end ElboimSly.Paper
