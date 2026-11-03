/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lem71
public import ElboimSly.Paper.Heavy.Es4Canon
public import ElboimSly.Paper.Heavy.ThrFinite
public import Mathlib

/-!
# Theorem 6.1 in the step regime, environment picture

ES22 Theorem 6.1, packaged for `StepEs61`.

* `StepEs61Env d c₆ β₆`: the conclusion of ES22 Theorem 6.1 for the regenerated walk of every Poisson
  environment, under the step regime `SR(n₁; β, n, t₀)` and `β ≥ β₆(n₁)`.
* `stepEs61Env_of_interface`: `StepEs61Env` from `es6_one_of_params`, conditional only on the
  interface `HeavyEscInterface` (the conclusion of interface with S6). The threshold
  `β₆(n₁)` forces `n > max (N₆, n₁)`, since `β < t₀ 4ⁿ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.Paper.Heavy

/-- ES22 Theorem 6.1 for Poisson environments under the step regime. -/
def StepEs61Env (d : ℕ) (c6 : ℝ) (β6 : ℕ → ℝ) : Prop :=
  ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), β6 n₁ ≤ β →
    StepRegime d n₁ β n t₀ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (Pe : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)),
      IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe →
      Pe {ω | ¬ ∀ t : ℝ, 0 ≤ t → t + indScale t₀ n ^ heavyEps d ≤ indScale t₀ n →
        ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * indScale t₀ n ^ heavyEps d) ≤
          volume ({s : ℝ | 0 ≤ s ∧ IsRelaxedTime (geoSlices N ω) s} ∩
            Icc t (t + indScale t₀ n ^ heavyEps d))} ≤
        ENNReal.ofReal (Real.exp (-(c6 * (n : ℝ) ^ 3)))

/-- The threshold `β₆(n₁)`. -/
noncomputable def stepBeta6 (d : ℕ) (E : HeavyEscConsts) (n₁ : ℕ) : ℝ :=
  max (max ((10 : ℝ) ^ 14) E.beta5) ((4 : ℝ) ^ (max (heavyN6 d n₁ E) n₁ + 1))

theorem stepEs61Env_of_interface {d : ℕ} (hd : 5 ≤ d) (E : HeavyEscConsts)
    (hI : ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ), HeavyEscInterface d β E n₀ n t₀) :
    StepEs61Env d (heavyC6 d E) (stepBeta6 d E) := by
  intro n₁ h8 β _ n t₀ hβ hR Ω _ Pe N hN
  obtain ⟨-, hβ1, -, ht, hlt, hind⟩ := hR
  set M := max (heavyN6 d n₁ E) n₁ with hM
  have hb1 : (4 : ℝ) ^ (M + 1) ≤ β := le_trans (le_max_right _ _) hβ
  have hb2 : (10 : ℝ) ^ 14 ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hβ
  have hb3 : E.beta5 ≤ β := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hβ
  have hnM : M < n := by
    by_contra h
    push Not at h
    have : indScale t₀ n ≤ (4 : ℝ) ^ (M + 1) := by
      unfold indScale
      have h1 : (4 : ℝ) ^ n * t₀ ≤ 4 * (4 : ℝ) ^ n := by
        nlinarith [ht.2, pow_pos (by norm_num : (0 : ℝ) < 4) n]
      have h2 : (4 : ℝ) ^ n ≤ 4 ^ M := pow_le_pow_right₀ (by norm_num) h
      calc _ ≤ 4 * (4 : ℝ) ^ n := h1
        _ ≤ 4 * 4 ^ M := by linarith
        _ = _ := by ring
    linarith
  have hp : Es4Params d β n₁ n t₀ :=
    ⟨hd, h8, lt_of_le_of_lt (le_max_right _ _) hnM, hb2, ht.1, ht.2, hlt,
      fun n' h1 h2 t' h3 h4 => hind n' h1 h2 t' ⟨h3, h4⟩⟩
  have hT : HeavyT d n₁ E n :=
    HeavyT.of_ge_N6 (by omega) (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hnM))
  exact es6_one_of_params (hI β n₁ n t₀) hN hp hT hb3

end ElboimSly.Paper.Step
