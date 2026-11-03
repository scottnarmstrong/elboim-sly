/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Claim3Final
public import Mathlib

/-!
# ES22 §4: Claims 4.2, 4.3 for processes, bad-event (cylinder) form

ES22 Claim 4.2; ES22 Claim 4.3 ("the same holds for every process with the law of `W`").
These are the upper bounds on the countable-time bad events of a right-continuous process `X`
with the law of `W`, used by ES22 Lemma 4.1.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

theorem es4_claim2_bad_process {d : ℕ} (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params d β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ d β)), IsPoissonPointProcess N (cycIntensity ℕ d β) Pr →
        ∀ {L : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ L → L ≤ (4 : ℝ) ^ n →
        ∀ {A : Set (Fin d → ℤ)}, (∀ u ∈ A, L ≤ ‖u‖) →
        (∀ r : ℝ, L ≤ r → ((A ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ)) →
        ∀ {Ω' : Type*} [MeasurableSpace Ω'] (Pr' : Measure Ω') (X : Ω' → ℝ≥0 → Fin d → ℤ),
          AEMeasurable X Pr' → Pr'.map X = Pr.map (avoidPath N) →
          Pr' {ω | ∃ q ∈ qSet 0 ((4 : ℝ) ^ n).toNNReal, X ω q ∈ A} ≤
            ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 30)) := by
  obtain ⟨C, hC, H⟩ := es4_claim2_bad hd
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN L hL1 hL2 A hA1 hA2 Ω' _ Pr' X hX hlaw
  have hbad := H β n₀ n t₀ hp Pr N hN hL1 hL2 hA1 hA2
  rw [prob_cyl_eq hX (aemeasurable_avoidPath hN) hlaw 0 _ (fun v => v ∈ A)]
  refine le_trans (measure_mono ?_) hbad
  rintro ω ⟨q, hq, hqA⟩
  have hb : (0 : ℝ≥0) ≤ ((4 : ℝ) ^ n).toNNReal := bot_le
  have := mem_qSet_Icc hb hq
  refine ⟨(q : ℝ), q.2, ?_, hqA⟩
  have h2 : (q : ℝ) ≤ ((((4 : ℝ) ^ n).toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast this.2
  rwa [Real.coe_toNNReal _ (by positivity)] at h2

theorem es4_claim3_bad_process {d : ℕ} (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params d β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ d β)), IsPoissonPointProcess N (cycIntensity ℕ d β) Pr →
        ∀ {t L : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ t → t ≤ (4 : ℝ) ^ n → t ^ indThetaH ≤ L →
        ∀ {Ω' : Type*} [MeasurableSpace Ω'] (Pr' : Measure Ω') (X : Ω' → ℝ≥0 → Fin d → ℤ),
          AEMeasurable X Pr' → Pr'.map X = Pr.map (avoidPath N) →
          Pr' {ω | ∃ q ∈ qSet t.toNNReal ((4 : ℝ) ^ n).toNNReal, ‖X ω q‖ < L} ≤
            ENNReal.ofReal (C * L ^ (d - 2) * t ^ (-((d - 2 : ℕ) : ℝ) / 2)) := by
  obtain ⟨C, hC, H⟩ := es4_claim3_bad hd
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN t L ht1 ht2 htL Ω' _ Pr' X hX hlaw
  have hbad := H β n₀ n t₀ hp Pr N hN ht1 ht2 htL
  have ht0 : 0 ≤ t := by
    have : (0 : ℝ) < 4 ^ (n₀ + 1) := by positivity
    linarith
  rw [prob_cyl_eq hX (aemeasurable_avoidPath hN) hlaw _ _ (fun v => ‖v‖ < L)]
  refine le_trans (measure_mono ?_) hbad
  have hab : t.toNNReal ≤ ((4 : ℝ) ^ n).toNNReal := Real.toNNReal_le_toNNReal ht2
  rintro ω ⟨q, hq, hqL⟩
  have := mem_qSet_Icc hab hq
  refine ⟨(q : ℝ), ?_, ?_, hqL⟩
  · have h2 : ((t.toNNReal : ℝ≥0) : ℝ) ≤ (q : ℝ) := by exact_mod_cast this.1
    rwa [Real.coe_toNNReal _ ht0] at h2
  · have h2 : (q : ℝ) ≤ ((((4 : ℝ) ^ n).toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast this.2
    rwa [Real.coe_toNNReal _ (by positivity)] at h2

end ElboimSly.Paper

end
