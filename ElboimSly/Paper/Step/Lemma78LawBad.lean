/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78LawCl
public import ElboimSly.Paper.Step.Lemma78LawV
public import ElboimSly.Paper.Step.Lemma78FarWin
public import ElboimSly.Paper.Step.AvoidStopping
public import Mathlib

/-!
# The law of the bad event `S_bad`

One excursion succeeds with probability at least frac12, "The other three events" and "Sum". The union of the closing,
hitting and far events has probability at most `2β⁻² + C₄₂ L^{-1/30} + (e^{-(n-1)²} + |Z| C_far (…)^{d-2})`
for the regenerated walk.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ}

/-- **`step78_law_Sbad`**: the total of the closing, `Sv` and `Sfar` laws. -/
theorem step78_law_Sbad (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₁ n : ℕ) (t₀ : ℝ),
      StepRegime d n₁ β n t₀ → (10 : ℝ) ^ 14 ≤ β → (4 : ℝ) ^ (n₁ + 2) ≤ β →
      ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {Pr₀ : Measure Ω₀} {N₀ : Ω₀ → Measure (CycS ℕ d β)},
        IsPoissonPointProcess N₀ (cycIntensity ℕ d β) Pr₀ →
      ∀ {L : ℝ}, (4 : ℝ) ^ (n₁ + 1) ≤ L → L ≤ (4 : ℝ) ^ n →
      ∀ (x : Fin d → ℤ) (V : Set (Fin d → ℤ)),
        (∀ u : Fin d → ℤ, (∃ v ∈ V, ‖x + u - v‖ ≤ 1) → L ≤ ‖u‖) →
        (∀ r : ℝ, L ≤ r → (({u : Fin d → ℤ | ∃ v ∈ V, ‖x + u - v‖ ≤ 1} ∩ {u | ‖u‖ ≤ r}).ncard : ℝ)
          ≤ r ^ (8 / 3 : ℝ)) →
      ∀ (Z : Finset (Fin d → ℤ)), (∀ v ∈ V, ∃ z ∈ Z, ‖v - z‖ ≤ (19 / 10 : ℝ) ^ n) →
        (Pr₀.map (avoidPath N₀)) (step78Sbad d β n x V) ≤
          ENNReal.ofReal (2 * (β ^ 2)⁻¹) + ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 30)) +
            (ENNReal.ofReal (Real.exp (-(((n - 1 : ℕ) : ℝ) ^ 2))) +
              (Z.card : ℝ≥0∞) * ENNReal.ofReal (ElboimSly.Brownian.Cfar d *
                (3 * (19 / 10 : ℝ) ^ n / Real.sqrt ((389 / 100 : ℝ) ^ n)) ^ (d - 2))) := by
  obtain ⟨C, hC, H⟩ := step78_law_Sv hd
  refine ⟨C, hC, fun β _ n₁ n t₀ hreg hβ14 hβ4 Ω₀ _ Pr₀ N₀ hN₀ L hL1 hL2 x V hA hcnt Z hcov => ?_⟩
  have hp := es4Params_of_stepRegime hd hreg hβ14 hβ4
  have hβ1 : 1 ≤ β := hreg.2.1.le
  have h1 := step78_law_cl hd hβ1 hreg hβ4 hN₀
  have h2 := H β n₁ n t₀ hp hN₀ hL1 hL2 x V hA hcnt
  have h3 := step78_law_Sfar hp hN₀ x V Z hcov
  unfold step78Sbad
  refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add h1 h2)) h3)

end ElboimSly.Paper.Step

end
